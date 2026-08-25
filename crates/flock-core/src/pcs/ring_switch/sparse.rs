//! Sparse equality tensors and their folding kernels.

use crate::bits::transpose_8x8_bits;
use crate::field::F128;
use crate::pcs::pack::LOG_PACKING;
use crate::zerocheck::univariate_skip::build_eq;
use rayon::prelude::*;

use super::fold::subset_sums_4;

// ---------------------------------------------------------------------------
// Sparse-tensor fast path.
//
// When the suffix `x_outer[1..]` has `k` coords exactly equal to `F128::ZERO`
// (as is the case for the hash-chain ẑ-opening, whose `x_inner_rest` is padded
// with trailing zeros), `build_eq` zeros out half the table per zero coord —
// so `1 − 2^{-k}` of the suffix tensor is zero and contributes nothing to
// `s_hat_v` (in `fold_1b_rows`) or `rs_eq_ind` (in `fold_b128_elems`). The
// sparse kernels touch only the `2^{-k}` support and produce byte-identical
// outputs to the dense kernels.
//
// Claims with fewer than `SPARSE_ZERO_THRESHOLD` zero coords stay on the dense
// (MFR / 8-wide) path; the crossover threshold of 3 is conservative — at 3
// zeros the support is 1/8 of the suffix length, plenty to amortize the
// sparse fold's per-entry overhead.
// ---------------------------------------------------------------------------

/// Minimum number of exactly-zero suffix coords for a claim to be routed
/// through the sparse kernels instead of the dense MFR fold.
pub(super) const SPARSE_ZERO_THRESHOLD: usize = 3;

/// Sparse representation of `build_eq(coords)` when `coords` contains exact
/// `F128::ZERO` entries: stores values at the compact (live) tensor positions
/// and a `live_positions` table that maps compact bit `j` → original coord
/// position. Avoids materializing the scattered `(full_idx, val)` pairs —
/// consumers compute the scattered idx on-the-fly via [`Self::scatter_idx`]
/// (a bit-deposit / pdep operation) at the point of use.
#[derive(Clone, Debug)]
pub struct SparseEqTensor {
    /// `build_eq(live_coords)` — length `2^live_positions.len()`.
    pub live_tensor: Vec<F128>,
    /// Original-coord positions of each live coord, ascending. So compact bit
    /// `j` of an enumeration index maps to bit `live_positions[j]` of the full
    /// scattered index.
    pub live_positions: Vec<usize>,
}

impl SparseEqTensor {
    /// Compact-to-scattered index translation: deposit the live bits of `c`
    /// into the original-coord positions. Inline so consumers' hot loops fuse
    /// this with their own per-entry work.
    ///
    /// (Tried backing this with per-byte 256-entry LUTs to reduce the
    /// 19-iteration loop to 3 LUT reads + ORs at chain scale. Measured wash
    /// on the keccak chain m=30 bench — LLVM auto-pipelines the iterative
    /// bit-deposit so aggressively that the per-entry scatter is already at
    /// the noise floor.)
    #[inline(always)]
    pub fn scatter_idx(&self, c: usize) -> usize {
        let mut full = 0usize;
        for (j, &pos) in self.live_positions.iter().enumerate() {
            full |= ((c >> j) & 1) << pos;
        }
        full
    }

    /// Materialize the scattered `(idx, val)` pairs. Test-oracle / external
    /// consumers that genuinely need the materialized form should call this;
    /// the prover hot path leaves the entries deferred via `scatter_idx`.
    pub fn materialize(&self) -> Vec<(usize, F128)> {
        self.live_tensor
            .iter()
            .enumerate()
            .map(|(c, &v)| (self.scatter_idx(c), v))
            .collect()
    }

    /// Number of scattered entries.
    pub fn len(&self) -> usize {
        self.live_tensor.len()
    }

    pub fn is_empty(&self) -> bool {
        self.live_tensor.is_empty()
    }
}

/// Build the sparse `build_eq(coords)` representation, skipping the zero-coord
/// halvings. The output's `live_tensor` is the `build_eq` table over only the
/// nonzero coords (length `2^live_count`); the scattered (full) index for
/// compact entry `c` is reconstructed lazily via [`SparseEqTensor::scatter_idx`].
///
/// O(2^live_count) time and memory, vs the dense `build_eq`'s `O(2^coords.len())`.
pub fn build_eq_sparse(coords: &[F128]) -> SparseEqTensor {
    let live_positions: Vec<usize> = coords
        .iter()
        .enumerate()
        .filter_map(|(i, &c)| if c == F128::ZERO { None } else { Some(i) })
        .collect();
    let live_coords: Vec<F128> = live_positions.iter().map(|&i| coords[i]).collect();
    // Sequential build_eq. `build_eq_parallel` *does* save ~0.4 ms on the build
    // itself at 19 live coords, but the downstream `fold_1b_rows_sparse` /
    // `fold_b128_elems_sparse_pairs` then pay cross-core L2/L3 traffic to
    // consume a tensor that was distributed across worker caches — net wash to
    // slight loss at the ring_switch level. Keep the tensor cache-local here.
    let live_tensor = build_eq(&live_coords);
    SparseEqTensor {
        live_tensor,
        live_positions,
    }
}

/// Sparse counterpart of one column of [`super::fold_1b_rows_multi`]: scans only the
/// nonzero entries of the suffix tensor. Iterates compact (live-only) tensor
/// indices and computes the scattered `packed_witness` index inline via
/// [`SparseEqTensor::scatter_idx`] — avoids materializing the scattered
/// `(idx, val)` pairs upfront.
///
/// Produces the same 128-entry `s_hat_v` as
/// `fold_1b_rows_naive(packed_witness, build_eq(coords))`, since `build_eq`'s
/// zero-coord halvings would otherwise contribute zero to every accumulator.
pub fn fold_1b_rows_sparse(packed_witness: &[F128], eq: &SparseEqTensor) -> Vec<F128> {
    // Tried: MFR fast path via `fold_1b_rows_sparse_mfr_block4` for the chain's
    // block-of-4 / stride-128 support pattern. **Measured a regression on
    // blake3 m=29** (~2.5 ms slower at chain proof level) and roughly break-
    // even on keccak. The subset-sum + transpose overhead doesn't amortize
    // over only 4 entries per group when packed_witness reads are scattered
    // (stride 128 = 2 KB jumps defeat the prefetcher). Kept the MFR helper +
    // detector in this module — they may be useful for future protocols with
    // a larger block_size (≥ 16) — but the dispatch is reverted to scalar.
    fold_1b_rows_sparse_scalar(packed_witness, eq)
}

/// Scalar bit-scan fallback for `fold_1b_rows_sparse`. One bit-scan per support
/// entry — used when the support's index pattern isn't a uniform stride-block.
fn fold_1b_rows_sparse_scalar(packed_witness: &[F128], eq: &SparseEqTensor) -> Vec<F128> {
    let n = 1 << LOG_PACKING;
    let zero_acc = || vec![F128::ZERO; n];

    eq.live_tensor
        .par_iter()
        .enumerate()
        .fold(zero_acc, |mut acc, (c, &val)| {
            // Scatter compact c → original index via the per-byte LUT (inlined).
            let idx = eq.scatter_idx(c);
            let elem = packed_witness[idx];
            let mut lo = elem.lo;
            while lo != 0 {
                let r = lo.trailing_zeros() as usize;
                acc[r] += val;
                lo &= lo - 1;
            }
            let mut hi = elem.hi;
            while hi != 0 {
                let r = hi.trailing_zeros() as usize;
                acc[64 | r] += val;
                hi &= hi - 1;
            }
            acc
        })
        .reduce(zero_acc, |mut a, b| {
            for r in 0..n {
                a[r] += b[r];
            }
            a
        })
}

/// Detect the regular block-of-N + stride pattern in a sparse support. Returns
/// `Some((block_size, stride))` if `support` has indices `g * stride + k` for
/// `g ∈ 0..num_groups, k ∈ 0..block_size` (ascending). Returns `None` otherwise
/// or when the support is too small to detect meaningfully.
///
/// For the hash-chain claim (zeros at suffix positions `region_log−k_skip+1`
/// through `k_log−k_skip−1`), the pattern is `block_size = 2^low_live_count`
/// (low live bits below the zero run) and `stride = 2^(zero_run_end+1)`.
///
/// Currently unused — see comment in [`fold_1b_rows_sparse`] for the MFR
/// regression rationale. Kept for future protocols with larger block sizes.
#[allow(dead_code)]
fn detect_block_stride(support: &[(usize, F128)]) -> Option<(usize, usize)> {
    if support.len() < 8 {
        return None;
    }
    // Block runs from index 0; count the contiguous prefix.
    if support[0].0 != 0 {
        return None;
    }
    let mut block_size = 1usize;
    while block_size < support.len() && support[block_size].0 == block_size {
        block_size += 1;
    }
    if block_size >= support.len() || !support.len().is_multiple_of(block_size) {
        return None;
    }
    let stride = support[block_size].0;
    if stride < block_size || !stride.is_power_of_two() {
        return None;
    }
    // Validate every group has the same shape.
    let num_groups = support.len() / block_size;
    for g in 0..num_groups {
        let base = g * stride;
        for k in 0..block_size {
            if support[g * block_size + k].0 != base + k {
                return None;
            }
        }
    }
    Some((block_size, stride))
}

/// MFR sparse fold for `block_size = 4` + arbitrary power-of-two stride.
/// Equivalent output to [`fold_1b_rows_sparse_scalar`] but uses the same
/// subset-sum / transpose machinery as [`fold_1b_rows_1way_mfr`], skipping the
/// zero entries between groups. Throughput per group is identical to the dense
/// 4-wide MFR kernel.
///
/// Currently unused — measured slower than scalar bit-scan for the chain
/// claim's 4-entries-per-group pattern (subset-sum table overhead doesn't
/// amortize over only 4 entries when packed_witness reads are scattered).
/// Kept for reference / future protocols with larger block sizes.
#[allow(dead_code)]
fn fold_1b_rows_sparse_mfr_block4(
    packed_witness: &[F128],
    support: &[(usize, F128)],
    stride: usize,
) -> Vec<F128> {
    let n = 1 << LOG_PACKING;
    debug_assert!(support.len().is_multiple_of(4));
    let num_groups = support.len() / 4;

    (0..num_groups)
        .into_par_iter()
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, g| {
                let base = g * stride;
                let m0 = packed_witness[base];
                let m1 = packed_witness[base + 1];
                let m2 = packed_witness[base + 2];
                let m3 = packed_witness[base + 3];
                let v: [F128; 4] = [
                    support[g * 4].1,
                    support[g * 4 + 1].1,
                    support[g * 4 + 2].1,
                    support[g * 4 + 3].1,
                ];
                let lookup = subset_sums_4(v);

                let m_bytes: [[u8; 16]; 4] = [
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m0.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m0.hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m1.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m1.hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m2.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m2.hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m3.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m3.hi.to_le_bytes());
                        b
                    },
                ];

                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24);
                    let transposed = transpose_8x8_bits(combined);
                    let tb = transposed.to_le_bytes();
                    let b = r_byte * 8;
                    acc[b] += lookup[(tb[0] & 0x0F) as usize];
                    acc[b + 1] += lookup[(tb[1] & 0x0F) as usize];
                    acc[b + 2] += lookup[(tb[2] & 0x0F) as usize];
                    acc[b + 3] += lookup[(tb[3] & 0x0F) as usize];
                    acc[b + 4] += lookup[(tb[4] & 0x0F) as usize];
                    acc[b + 5] += lookup[(tb[5] & 0x0F) as usize];
                    acc[b + 6] += lookup[(tb[6] & 0x0F) as usize];
                    acc[b + 7] += lookup[(tb[7] & 0x0F) as usize];
                }
                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n],
            |mut a, b| {
                for r in 0..n {
                    a[r] += b[r];
                }
                a
            },
        )
}

/// Sparse counterpart of [`super::fold_b128_elems`] returning **sparse pairs** instead
/// of a dense vector — skips the O(L) zero-init / scatter entirely. Each pair
/// `(idx, value)` has the same per-element bit-scan over `eq_r_dprime` as the
/// dense kernel computed at that index; positions absent from the output are
/// implicitly `F128::ZERO`. Consumers must handle the sparse representation
/// (see [`super::RsEqInd::Sparse`]).
///
/// Iterates compact tensor positions and scatters the index inline only at
/// emission — avoids materializing the scattered `(idx, val)` pairs upfront.
pub fn fold_b128_elems_sparse_pairs(
    eq: &SparseEqTensor,
    eq_r_dprime: &[F128],
) -> Vec<(usize, F128)> {
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    eq.live_tensor
        .par_iter()
        .enumerate()
        .map(|(c, &tensor_val)| {
            let mut acc = F128::ZERO;
            let mut lo = tensor_val.lo;
            while lo != 0 {
                let b = lo.trailing_zeros() as usize;
                acc += eq_r_dprime[b];
                lo &= lo - 1;
            }
            let mut hi = tensor_val.hi;
            while hi != 0 {
                let b = hi.trailing_zeros() as usize;
                acc += eq_r_dprime[64 | b];
                hi &= hi - 1;
            }
            // Scatter compact c → original index via per-byte LUT (inlined).
            (eq.scatter_idx(c), acc)
        })
        .collect()
}

/// Dense-output sparse fold — kept for tests/oracles. Returns a length-`len`
/// `Vec<F128>` that is zero outside the support. Prefer
/// [`fold_b128_elems_sparse_pairs`] in the prover hot path.
pub fn fold_b128_elems_sparse(len: usize, eq: &SparseEqTensor, eq_r_dprime: &[F128]) -> Vec<F128> {
    let pairs = fold_b128_elems_sparse_pairs(eq, eq_r_dprime);
    let mut out = vec![F128::ZERO; len];
    for (idx, val) in pairs {
        out[idx] = val;
    }
    out
}

//! Dense tensor construction and optimized folding kernels.

use crate::bits::transpose_8x8_bits;
use crate::field::F128;
use crate::pcs::pack::LOG_PACKING;
use crate::zerocheck::PaddingSpec;
use crate::zerocheck::multilinear::lagrange_weights_naive;
use rayon::prelude::*;

/// Per-block padding descriptor in F_{2^128} units. Computed once from a bit-
/// level [`PaddingSpec`] and reused across the fold kernels: any chunk whose
/// index modulo `chunks_per_block` is ≥ `useful_chunks_per_block` is fully
/// inside the zero-padded suffix of every block and can be skipped.
#[derive(Clone, Copy, Debug)]
struct ChunkPadding {
    /// `chunks_per_block - 1` for fast `idx % chunks_per_block` via AND;
    /// `usize::MAX` (= "no skip") when there is only one block (e.g. dense
    /// paddings).
    chunk_in_block_mask: usize,
    /// Index of the first fully-padding chunk within each block.
    useful_chunks_per_block: usize,
}

impl ChunkPadding {
    /// Build the per-chunk skip table for a given F128-chunk width
    /// (e.g. `chunk_width = 8` for the 8-wide MFR path). Returns a "no skip"
    /// descriptor if either (a) the spec covers the entire packed witness as
    /// one block, or (b) every chunk in a block is at least partially useful.
    fn new(padding: &PaddingSpec, chunk_width: usize) -> Self {
        // Block size in F128 elements = 2^(k_log - LOG_PACKING).
        if padding.k_log <= LOG_PACKING {
            // Block smaller than one F128 — no per-block structure to exploit.
            return Self::no_skip();
        }
        let block_size_f128 = 1usize << (padding.k_log - LOG_PACKING);
        if block_size_f128 < chunk_width {
            return Self::no_skip();
        }
        let chunks_per_block = block_size_f128 / chunk_width;
        let useful_f128 = padding.useful_bits_per_block.div_ceil(1 << LOG_PACKING);
        let useful_chunks_per_block = useful_f128.div_ceil(chunk_width).min(chunks_per_block);
        if useful_chunks_per_block == chunks_per_block {
            return Self::no_skip();
        }
        debug_assert!(chunks_per_block.is_power_of_two());
        Self {
            chunk_in_block_mask: chunks_per_block - 1,
            useful_chunks_per_block,
        }
    }

    fn no_skip() -> Self {
        Self {
            chunk_in_block_mask: usize::MAX,
            useful_chunks_per_block: usize::MAX,
        }
    }

    /// True iff the chunk at this global index is fully inside padding.
    #[inline(always)]
    fn skip(&self, chunk_idx: usize) -> bool {
        (chunk_idx & self.chunk_in_block_mask) >= self.useful_chunks_per_block
    }
}

/// Build the 128-entry weights vector for the verifier's ring-switching claim
/// check, given the zerocheck's `z_skip` (univariate-skip coord, absorbs 6
/// boolean coords via the φ_8 basis) and `x_outer_0` (the 7th prefix bit, a
/// fresh F_{2^128} multilinear coord).
///
/// ```text
/// weights[i] = ν_φ8(i & 63)(z_skip) · eq(x_outer_0, (i >> 6) & 1)
///            for i ∈ {0..128}
/// ```
///
/// `i & 63` selects the low 6 bits (LCH dimensions); `(i >> 6) & 1` is the 7th
/// bit (a standard multilinear coord).
pub fn build_claim_weights(z_skip: F128, x_outer_0: F128) -> Vec<F128> {
    const K_SKIP: usize = 6;
    let lambda = lagrange_weights_naive(K_SKIP, z_skip); // length 64
    debug_assert_eq!(lambda.len(), 1 << K_SKIP);

    let eq_lo = F128::ONE + x_outer_0; // eq(x_outer_0, 0)
    let eq_hi = x_outer_0; // eq(x_outer_0, 1)

    let n = 1 << LOG_PACKING; // 128
    let mut weights = Vec::with_capacity(n);
    // Layout: i ∈ {0..64} → bit-6 = 0 branch (eq_lo); i ∈ {64..128} → bit-6 = 1.
    for i in 0..n {
        let i_lo = i & 63;
        let bit_6 = (i >> 6) & 1;
        let eq_b6 = if bit_6 == 1 { eq_hi } else { eq_lo };
        weights.push(lambda[i_lo] * eq_b6);
    }
    weights
}

/// Batched version of [`fold_1b_rows_naive`]: compute `s_hat_v_k` for each
/// `suffix_tensors[k]` in a single bit-scan over `packed_witness`. Halves the
/// amortized bit-scanning cost vs calling `fold_1b_rows_naive` per suffix.
///
/// All suffix tensors must have the same length as `packed_witness`.
pub fn fold_1b_rows_multi(packed_witness: &[F128], suffix_tensors: &[&[F128]]) -> Vec<Vec<F128>> {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_multi_padded(packed_witness, suffix_tensors, &PaddingSpec::dense(m))
}

/// Padding-aware variant of [`fold_1b_rows_multi`]. Routes the k=2 MFR fast
/// paths through their `_padded` kernels; the scalar bit-scan fallback (k ≠ 2
/// or non-divisible len) is untouched — those `m` are tiny anyway.
pub fn fold_1b_rows_multi_padded(
    packed_witness: &[F128],
    suffix_tensors: &[&[F128]],
    padding: &PaddingSpec,
) -> Vec<Vec<F128>> {
    let k = suffix_tensors.len();
    let n = 1 << LOG_PACKING;
    assert!(
        suffix_tensors
            .iter()
            .all(|t| t.len() == packed_witness.len())
    );

    let zero_acc = || vec![vec![F128::ZERO; n]; k];

    // The k=2 case (one pair of outers) is the hot path used by `open_batch`
    // for zerocheck + lincheck claims. Method-of-four-Russians fold (ported
    // from Binius): process several elements at a time with subset-sum table
    // lookups per output bit, eliminating the scalar bit-scan's data-dependent
    // control flow. The 16-wide variant groups 16 elements (four 4-element
    // tables, 16-bit masks) so each acc entry is touched once per 16 elements,
    // halving acc RMW traffic (the fold is LSU-bound) for ~1.25× over 8-wide.
    // We run two *independent* 1-way 16-wide folds rather than one fused 2-way
    // fold: the fused kernel's two accumulators + eight tables cause register
    // pressure that eats most of the 16-wide win, and the shared bit-transpose
    // it would save is nearly free. Falls back to the fused 8-wide → 4-wide →
    // scalar as divisibility drops (only at toy m).
    if k == 2 {
        if packed_witness.len().is_multiple_of(16) {
            // x86_64: one fused 2-way scan (shares gather + bit-transpose).
            // aarch64: two independent 1-way scans (measured better there —
            // the fused kernel's register pressure ate the win on M-series).
            #[cfg(target_arch = "x86_64")]
            {
                let (a0, a1) = fold_1b_rows_2way_mfr_16wide_padded(
                    packed_witness,
                    suffix_tensors[0],
                    suffix_tensors[1],
                    padding,
                );
                return vec![a0, a1];
            }
            #[cfg(not(target_arch = "x86_64"))]
            {
                let a0 =
                    fold_1b_rows_1way_mfr_16wide_padded(packed_witness, suffix_tensors[0], padding);
                let a1 =
                    fold_1b_rows_1way_mfr_16wide_padded(packed_witness, suffix_tensors[1], padding);
                return vec![a0, a1];
            }
        }
        if packed_witness.len().is_multiple_of(8) {
            let (a0, a1) = fold_1b_rows_2way_mfr_8wide_padded(
                packed_witness,
                suffix_tensors[0],
                suffix_tensors[1],
                padding,
            );
            return vec![a0, a1];
        }
        if packed_witness.len().is_multiple_of(4) {
            let (a0, a1) = fold_1b_rows_2way_mfr_padded(
                packed_witness,
                suffix_tensors[0],
                suffix_tensors[1],
                padding,
            );
            return vec![a0, a1];
        }
    }

    packed_witness
        .par_iter()
        .enumerate()
        .fold(zero_acc, |mut acc, (i_rest, elem)| {
            // Single bit-scan, write into all k accumulators.
            let mut lo = elem.lo;
            while lo != 0 {
                let r = lo.trailing_zeros() as usize;
                for (j, t) in suffix_tensors.iter().enumerate() {
                    acc[j][r] += t[i_rest];
                }
                lo &= lo - 1;
            }
            let mut hi = elem.hi;
            while hi != 0 {
                let r = hi.trailing_zeros() as usize;
                for (j, t) in suffix_tensors.iter().enumerate() {
                    acc[j][64 | r] += t[i_rest];
                }
                hi &= hi - 1;
            }
            acc
        })
        .reduce(zero_acc, |mut a, b| {
            for (av, bv) in a.iter_mut().zip(b.iter()) {
                for (avi, bvi) in av.iter_mut().zip(bv.iter()) {
                    *avi += *bvi;
                }
            }
            a
        })
}

/// Parallel `build_eq` for ring-switching's suffix tensors. Same output as
/// [`crate::zerocheck::univariate_skip::build_eq`] (byte-identical), but
/// parallelizes the inner doubling loop across rayon threads.
///
/// Each level `i` doubles a table of size `2^i` → `2^(i+1)`: for each
/// `x ∈ 0..2^i`, write `t[x | (1<<i)] = t[x] * r_i` and
/// `t[x] = t[x] * (1-r_i)`. The iterations within one level are
/// independent and trivially parallelize. Earlier levels are tiny so
/// rayon's per-task overhead dominates; we keep them sequential and only
/// switch to parallel above a threshold.
pub(super) fn build_eq_parallel(r: &[F128]) -> Vec<F128> {
    let n = r.len();
    // Uninit alloc — at iter `i`, the loop reads from t[..2^i] (always written
    // by an earlier iter or the t[0] = ONE seed) and writes to t[2^i..2^(i+1)]
    // (purely written, never read first). So every slot is written before any
    // read; uninit is safe.
    let mut t = crate::alloc_uninit_f128_vec(1usize << n);
    t[0] = F128::ONE;
    // Threshold below which rayon dispatch overhead beats the parallel work.
    const PAR_THRESHOLD: usize = 1 << 12;
    for i in 0..n {
        let r_i = r[i];
        let one_minus_r = F128::ONE + r_i;
        let half = 1usize << i;
        let (lo, hi_rest) = t.split_at_mut(half);
        let hi = &mut hi_rest[..half];
        if half < PAR_THRESHOLD {
            for (lo_x, hi_x) in lo.iter_mut().zip(hi.iter_mut()) {
                let old = *lo_x;
                *hi_x = old * r_i;
                *lo_x = old * one_minus_r;
            }
        } else {
            lo.par_iter_mut()
                .zip(hi.par_iter_mut())
                .for_each(|(lo_x, hi_x)| {
                    let old = *lo_x;
                    *hi_x = old * r_i;
                    *lo_x = old * one_minus_r;
                });
        }
    }
    t
}

/// Tensor-factored `build_eq`: split the point `r` (length `n`) into a low
/// part `r[..n_lo]` and a high part `r[n_lo..]`, returning the two smaller
/// eq-tables `(eq_lo, eq_hi)` of lengths `2^n_lo` and `2^(n - n_lo)`.
///
/// The full tensor factors **exactly** (GF(2^128) is a field — multiply is
/// associative and has no rounding):
///
/// ```text
/// build_eq_parallel(r)[i] == eq_lo[i & (2^n_lo - 1)] * eq_hi[i >> n_lo]
/// ```
///
/// because round `j` of `build_eq` splits on bit `j` of the index and bit `j`
/// selects `r[j]`. So the low `n_lo` index bits depend only on `r[..n_lo]` and
/// the high bits only on `r[n_lo..]`.
///
/// Materializing the two factors costs `2^n_lo + 2^(n - n_lo)` entries instead
/// of `2^n`. Consumers either reconstruct each full entry on demand as one GF
/// multiply ([`fold_b128_elems_split`]) or never form it at all when the
/// consumer is linear in the tensor ([`fold_1b_rows_split`]).
pub fn build_eq_split(r: &[F128], n_lo: usize) -> (Vec<F128>, Vec<F128>) {
    assert!(n_lo <= r.len());
    let eq_lo = build_eq_parallel(&r[..n_lo]);
    let eq_hi = build_eq_parallel(&r[n_lo..]);
    (eq_lo, eq_hi)
}

/// Pick the low-split width `n_lo` for a suffix tensor of length `2^n`.
/// Balanced near `n/2` so both factors are ~`2^(n/2)` (L1/L2-resident), and
/// clamped to `[4, n]` so the low block `2^n_lo` is a whole number of 16-wide
/// MFR chunks (`n_lo ≥ 4` ⇒ block ≥ 16). The high part drives block-level
/// parallelism (`2^(n - n_lo)` blocks). Only meaningful for `n ≥ 4` (the
/// split path requires `len` divisible by 16).
pub fn split_n_lo(n: usize) -> usize {
    (n / 2).clamp(4, n)
}

/// Build the 16-entry subset-sum lookup table over 4 F128 elements.
///
/// `sums[mask]` = `Σ_{k=0..4 : bit_k(mask) = 1} elems[k]` for `mask ∈ 0..16`.
/// Cost: 15 F128 additions (8 + 4 + 2 + 1) via the standard doubling pattern.
#[inline(always)]
pub(super) fn subset_sums_4(elems: [F128; 4]) -> [F128; 16] {
    let mut sums = [F128::ZERO; 16];
    // After processing elem[i], sums[0..2^(i+1)] are populated with the
    // subset sums over elems[0..=i].
    for (i, &e) in elems.iter().enumerate() {
        let span_log = i + 1;
        let half = 1 << i;
        // sums[half..2*half] = sums[0..half] + e
        for k in 0..half {
            sums[half + k] = sums[k] + e;
        }
        let _ = span_log;
    }
    sums
}

/// Like `fold_1b_rows_multi` for `k=2`, but using the **method-of-four-Russians**
/// algorithm ported from Binius. Processes the packed witness in groups of 4
/// elements; per group, builds two 16-entry subset-sum lookup tables (one
/// per claim) and then for each output bit position `r ∈ 0..128` does **one
/// table lookup + one RMW** into the accumulator, regardless of bit density.
///
/// This replaces the scalar bit-scan, which is data-dependent (per set bit:
/// `trailing_zeros + RMW + branch`) with a constant-cost-per-`r` inner loop.
/// At ~50% set-bit density, this is ~2× fewer RMWs per element (128 per
/// group of 4 elements = 32 per element, vs ~64 set bits × 1 RMW per element
/// in the scalar path), and the OoO engine can pipeline the constant-cost
/// loop more aggressively than the bit-scan.
pub fn fold_1b_rows_2way_mfr(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
) -> (Vec<F128>, Vec<F128>) {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_2way_mfr_padded(packed_witness, t0, t1, &PaddingSpec::dense(m))
}

/// Padding-aware variant of [`fold_1b_rows_2way_mfr`]. Skips chunks of 4
/// F128s that fall entirely in the zero padding of every block.
pub fn fold_1b_rows_2way_mfr_padded(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    let n = 1 << LOG_PACKING; // 128
    assert_eq!(t0.len(), packed_witness.len());
    assert_eq!(t1.len(), packed_witness.len());
    assert!(
        packed_witness.len().is_multiple_of(4),
        "fold_1b_rows_2way_mfr requires len divisible by 4 (got {})",
        packed_witness.len()
    );
    let skip = ChunkPadding::new(padding, 4);

    let pair = packed_witness
        .par_chunks(4)
        .zip(t0.par_chunks(4))
        .zip(t1.par_chunks(4))
        .enumerate()
        .fold(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (chunk_idx, ((m_chunk, t0_chunk), t1_chunk))| {
                if skip.skip(chunk_idx) {
                    return (a0, a1);
                }
                let v0: [F128; 4] = [t0_chunk[0], t0_chunk[1], t0_chunk[2], t0_chunk[3]];
                let v1: [F128; 4] = [t1_chunk[0], t1_chunk[1], t1_chunk[2], t1_chunk[3]];

                // Build the two 16-entry subset-sum lookup tables.
                let lookup0 = subset_sums_4(v0);
                let lookup1 = subset_sums_4(v1);

                // Cache all 16 bytes of each m element for fast indexed access.
                let m_bytes: [[u8; 16]; 4] = [
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[0].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[0].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[1].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[1].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[2].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[2].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[3].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[3].hi.to_le_bytes());
                        b
                    },
                ];

                // For each byte position (16 total = bits [r_byte*8, r_byte*8+8)):
                //   - Gather the same byte from each of the 4 m elements.
                //   - Pack into a u64 with the 4 bytes occupying byte slots 0..4
                //     (slots 4..8 are zero).
                //   - Apply 8×8 bit transpose. After transpose, byte p of the
                //     u64 has its low-bit positions filled with
                //     (bit-p of m[0]'s r_byte, bit-p of m[1]'s, bit-p of m[2]'s,
                //      bit-p of m[3]'s) — that's exactly the 4-bit mask for
                //     output position r = r_byte*8 + p.
                //   - Look up the mask in the subset-sum tables and XOR into
                //     a0[r], a1[r].
                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24);
                    let transposed = transpose_8x8_bits(combined);
                    let tb = transposed.to_le_bytes();
                    let base = r_byte * 8;
                    // 8 unrolled lookups + RMWs. Each transposed byte's low
                    // 4 bits hold the mask; high 4 bits are always zero (the
                    // upper 4 byte-slots of `combined` were zero).
                    a0[base] += lookup0[(tb[0] & 0x0F) as usize];
                    a1[base] += lookup1[(tb[0] & 0x0F) as usize];
                    a0[base + 1] += lookup0[(tb[1] & 0x0F) as usize];
                    a1[base + 1] += lookup1[(tb[1] & 0x0F) as usize];
                    a0[base + 2] += lookup0[(tb[2] & 0x0F) as usize];
                    a1[base + 2] += lookup1[(tb[2] & 0x0F) as usize];
                    a0[base + 3] += lookup0[(tb[3] & 0x0F) as usize];
                    a1[base + 3] += lookup1[(tb[3] & 0x0F) as usize];
                    a0[base + 4] += lookup0[(tb[4] & 0x0F) as usize];
                    a1[base + 4] += lookup1[(tb[4] & 0x0F) as usize];
                    a0[base + 5] += lookup0[(tb[5] & 0x0F) as usize];
                    a1[base + 5] += lookup1[(tb[5] & 0x0F) as usize];
                    a0[base + 6] += lookup0[(tb[6] & 0x0F) as usize];
                    a1[base + 6] += lookup1[(tb[6] & 0x0F) as usize];
                    a0[base + 7] += lookup0[(tb[7] & 0x0F) as usize];
                    a1[base + 7] += lookup1[(tb[7] & 0x0F) as usize];
                }

                (a0, a1)
            },
        )
        .reduce(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (b0, b1)| {
                for r in 0..n {
                    a0[r] += b0[r];
                    a1[r] += b1[r];
                }
                (a0, a1)
            },
        );

    (pair.0, pair.1)
}

/// **Experimental** 8-wide / two-k=4-table version of [`fold_1b_rows_2way_mfr`].
/// Packs 8 witness elements per transpose group (the 4-wide version wastes the
/// upper 4 transpose rows). The single transpose is shared across both claims;
/// each claim uses two small 16-entry tables (low nibble = elems 0-3, high =
/// elems 4-7) XORed in-register before one acc RMW. Net vs the current 2-way:
/// transposes halved, acc-RMWs halved per claim, same small tables.
pub fn fold_1b_rows_2way_mfr_8wide(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
) -> (Vec<F128>, Vec<F128>) {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_2way_mfr_8wide_padded(packed_witness, t0, t1, &PaddingSpec::dense(m))
}

/// Padding-aware variant of [`fold_1b_rows_2way_mfr_8wide`]. Skips chunks of
/// 8 F128s that fall entirely in the zero padding of every block — those
/// chunks contribute nothing (witness bytes = 0 → subset-sum mask = 0 →
/// `lookup[0] = 0`).
pub fn fold_1b_rows_2way_mfr_8wide_padded(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    let n = 1 << LOG_PACKING;
    assert_eq!(t0.len(), packed_witness.len());
    assert_eq!(t1.len(), packed_witness.len());
    assert!(packed_witness.len().is_multiple_of(8));
    let skip = ChunkPadding::new(padding, 8);

    packed_witness
        .par_chunks(8)
        .zip(t0.par_chunks(8))
        .zip(t1.par_chunks(8))
        .enumerate()
        .fold(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (chunk_idx, ((m_chunk, t0_chunk), t1_chunk))| {
                if skip.skip(chunk_idx) {
                    return (a0, a1);
                }
                let t0_lo = subset_sums_4([t0_chunk[0], t0_chunk[1], t0_chunk[2], t0_chunk[3]]);
                let t0_hi = subset_sums_4([t0_chunk[4], t0_chunk[5], t0_chunk[6], t0_chunk[7]]);
                let t1_lo = subset_sums_4([t1_chunk[0], t1_chunk[1], t1_chunk[2], t1_chunk[3]]);
                let t1_hi = subset_sums_4([t1_chunk[4], t1_chunk[5], t1_chunk[6], t1_chunk[7]]);

                let mut m_bytes = [[0u8; 16]; 8];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let tb = transpose_8x8_bits(combined).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let mask = tb[p];
                        let lo = (mask & 0x0F) as usize;
                        let hi = (mask >> 4) as usize;
                        a0[base + p] += t0_lo[lo] + t0_hi[hi];
                        a1[base + p] += t1_lo[lo] + t1_hi[hi];
                    }
                }
                (a0, a1)
            },
        )
        .reduce(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (b0, b1)| {
                for r in 0..n {
                    a0[r] += b0[r];
                    a1[r] += b1[r];
                }
                (a0, a1)
            },
        )
}

/// Single-tensor (k=1) version of the method-of-four-Russians fold, mirroring
/// [`fold_1b_rows_2way_mfr`]. Same algorithm but maintains one subset-sum
/// table and one accumulator. Used by [`fold_1b_rows_naive`] for inputs
/// divisible by 4 (the standard case at any reasonable `m`).
pub fn fold_1b_rows_1way_mfr(packed_witness: &[F128], t: &[F128]) -> Vec<F128> {
    let n = 1 << LOG_PACKING; // 128
    assert_eq!(t.len(), packed_witness.len());
    assert!(
        packed_witness.len().is_multiple_of(4),
        "fold_1b_rows_1way_mfr requires len divisible by 4 (got {})",
        packed_witness.len()
    );

    packed_witness
        .par_chunks(4)
        .zip(t.par_chunks(4))
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (m_chunk, t_chunk)| {
                let v: [F128; 4] = [t_chunk[0], t_chunk[1], t_chunk[2], t_chunk[3]];
                let lookup = subset_sums_4(v);

                let m_bytes: [[u8; 16]; 4] = [
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[0].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[0].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[1].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[1].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[2].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[2].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[3].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[3].hi.to_le_bytes());
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
                    let base = r_byte * 8;
                    acc[base] += lookup[(tb[0] & 0x0F) as usize];
                    acc[base + 1] += lookup[(tb[1] & 0x0F) as usize];
                    acc[base + 2] += lookup[(tb[2] & 0x0F) as usize];
                    acc[base + 3] += lookup[(tb[3] & 0x0F) as usize];
                    acc[base + 4] += lookup[(tb[4] & 0x0F) as usize];
                    acc[base + 5] += lookup[(tb[5] & 0x0F) as usize];
                    acc[base + 6] += lookup[(tb[6] & 0x0F) as usize];
                    acc[base + 7] += lookup[(tb[7] & 0x0F) as usize];
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

/// **Experimental** 8-wide / two-k=4-table variant. Packs 8 elements per
/// transpose (vs the 4-wide version's wasted upper rows), but keeps two small
/// 16-entry tables (low nibble = elems 0-3, high nibble = elems 4-7). The two
/// lookups are XORed in-register before a single `acc` RMW — so vs the current
/// kernel this halves the transpose count AND halves the acc-RMW count, while
/// keeping the well-reused small tables.
pub fn fold_1b_rows_1way_mfr_8wide_k4(packed_witness: &[F128], t: &[F128]) -> Vec<F128> {
    let n = 1 << LOG_PACKING;
    assert_eq!(t.len(), packed_witness.len());
    assert!(packed_witness.len().is_multiple_of(8));

    packed_witness
        .par_chunks(8)
        .zip(t.par_chunks(8))
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (m_chunk, t_chunk)| {
                let lo_tbl = subset_sums_4([t_chunk[0], t_chunk[1], t_chunk[2], t_chunk[3]]);
                let hi_tbl = subset_sums_4([t_chunk[4], t_chunk[5], t_chunk[6], t_chunk[7]]);

                let mut m_bytes = [[0u8; 16]; 8];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let tb = transpose_8x8_bits(combined).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let mask = tb[p];
                        acc[base + p] +=
                            lo_tbl[(mask & 0x0F) as usize] + hi_tbl[(mask >> 4) as usize];
                    }
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

/// Single-tensor 16-wide method-of-four-Russians fold. Processes 16 witness
/// elements per group (four 4-element subset-sum tables, 16-bit per-position
/// masks) so each length-128 accumulator entry is touched once per 16 elements
/// instead of once per 8, halving acc load+store traffic. Gathers (32·N), eor3
/// count, and table-build adds match the 8-wide kernel; the only delta is fewer
/// acc RMWs. Measured ~1.25× over the 8-wide kernel (the fold is LSU-bound).
///
/// `open_batch`'s k=2 path runs this **twice** (once per suffix tensor) rather
/// than one fused 2-way fold: keeping a single length-128 accumulator + four
/// tables in flight avoids the register pressure of the 2-way's two
/// accumulators + eight tables, which ate most of the 16-wide win there. The
/// shared bit-transpose recomputed per call is nearly free (the fold is not
/// memory-bandwidth bound).
pub fn fold_1b_rows_1way_mfr_16wide_padded(
    packed_witness: &[F128],
    t: &[F128],
    padding: &PaddingSpec,
) -> Vec<F128> {
    let n = 1 << LOG_PACKING;
    assert_eq!(t.len(), packed_witness.len());
    assert!(packed_witness.len().is_multiple_of(16));
    let skip = ChunkPadding::new(padding, 16);

    packed_witness
        .par_chunks(16)
        .zip(t.par_chunks(16))
        .enumerate()
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (chunk_idx, (m_chunk, t_chunk))| {
                if skip.skip(chunk_idx) {
                    return acc;
                }
                let tbl0 = subset_sums_4([t_chunk[0], t_chunk[1], t_chunk[2], t_chunk[3]]);
                let tbl1 = subset_sums_4([t_chunk[4], t_chunk[5], t_chunk[6], t_chunk[7]]);
                let tbl2 = subset_sums_4([t_chunk[8], t_chunk[9], t_chunk[10], t_chunk[11]]);
                let tbl3 = subset_sums_4([t_chunk[12], t_chunk[13], t_chunk[14], t_chunk[15]]);

                let mut m_bytes = [[0u8; 16]; 16];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let lo8: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let hi8: u64 = (m_bytes[8][r_byte] as u64)
                        | ((m_bytes[9][r_byte] as u64) << 8)
                        | ((m_bytes[10][r_byte] as u64) << 16)
                        | ((m_bytes[11][r_byte] as u64) << 24)
                        | ((m_bytes[12][r_byte] as u64) << 32)
                        | ((m_bytes[13][r_byte] as u64) << 40)
                        | ((m_bytes[14][r_byte] as u64) << 48)
                        | ((m_bytes[15][r_byte] as u64) << 56);
                    let tlo = transpose_8x8_bits(lo8).to_le_bytes();
                    let thi = transpose_8x8_bits(hi8).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let m_lo = tlo[p];
                        let m_hi = thi[p];
                        acc[base + p] += tbl0[(m_lo & 0x0F) as usize]
                            + tbl1[(m_lo >> 4) as usize]
                            + tbl2[(m_hi & 0x0F) as usize]
                            + tbl3[(m_hi >> 4) as usize];
                    }
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

/// Dense (no-skip) wrapper over [`fold_1b_rows_1way_mfr_16wide_padded`]. Used by
/// [`fold_1b_rows_naive`] for inputs divisible by 16.
pub fn fold_1b_rows_1way_mfr_16wide_k4(packed_witness: &[F128], t: &[F128]) -> Vec<F128> {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_1way_mfr_16wide_padded(packed_witness, t, &PaddingSpec::dense(m))
}

pub fn fold_1b_rows_2way_mfr_16wide_padded(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    let n = 1 << LOG_PACKING;
    assert_eq!(t0.len(), packed_witness.len());
    assert_eq!(t1.len(), packed_witness.len());
    assert!(packed_witness.len().is_multiple_of(16));
    let skip = ChunkPadding::new(padding, 16);

    packed_witness
        .par_chunks(16)
        .zip(t0.par_chunks(16))
        .zip(t1.par_chunks(16))
        .enumerate()
        .fold(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (chunk_idx, ((m_chunk, t0_chunk), t1_chunk))| {
                if skip.skip(chunk_idx) {
                    return (a0, a1);
                }
                let t0_0 = subset_sums_4([t0_chunk[0], t0_chunk[1], t0_chunk[2], t0_chunk[3]]);
                let t0_1 = subset_sums_4([t0_chunk[4], t0_chunk[5], t0_chunk[6], t0_chunk[7]]);
                let t0_2 = subset_sums_4([t0_chunk[8], t0_chunk[9], t0_chunk[10], t0_chunk[11]]);
                let t0_3 = subset_sums_4([t0_chunk[12], t0_chunk[13], t0_chunk[14], t0_chunk[15]]);
                let t1_0 = subset_sums_4([t1_chunk[0], t1_chunk[1], t1_chunk[2], t1_chunk[3]]);
                let t1_1 = subset_sums_4([t1_chunk[4], t1_chunk[5], t1_chunk[6], t1_chunk[7]]);
                let t1_2 = subset_sums_4([t1_chunk[8], t1_chunk[9], t1_chunk[10], t1_chunk[11]]);
                let t1_3 = subset_sums_4([t1_chunk[12], t1_chunk[13], t1_chunk[14], t1_chunk[15]]);

                let mut m_bytes = [[0u8; 16]; 16];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let lo8: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let hi8: u64 = (m_bytes[8][r_byte] as u64)
                        | ((m_bytes[9][r_byte] as u64) << 8)
                        | ((m_bytes[10][r_byte] as u64) << 16)
                        | ((m_bytes[11][r_byte] as u64) << 24)
                        | ((m_bytes[12][r_byte] as u64) << 32)
                        | ((m_bytes[13][r_byte] as u64) << 40)
                        | ((m_bytes[14][r_byte] as u64) << 48)
                        | ((m_bytes[15][r_byte] as u64) << 56);
                    let tlo = transpose_8x8_bits(lo8).to_le_bytes();
                    let thi = transpose_8x8_bits(hi8).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let m_lo = tlo[p];
                        let m_hi = thi[p];
                        let lo_lo = (m_lo & 0x0F) as usize;
                        let lo_hi = (m_lo >> 4) as usize;
                        let hi_lo = (m_hi & 0x0F) as usize;
                        let hi_hi = (m_hi >> 4) as usize;
                        a0[base + p] += t0_0[lo_lo] + t0_1[lo_hi] + t0_2[hi_lo] + t0_3[hi_hi];
                        a1[base + p] += t1_0[lo_lo] + t1_1[lo_hi] + t1_2[hi_lo] + t1_3[hi_hi];
                    }
                }
                (a0, a1)
            },
        )
        .reduce(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (b0, b1)| {
                for r in 0..n {
                    a0[r] += b0[r];
                    a1[r] += b1[r];
                }
                (a0, a1)
            },
        )
}

/// Tensor-split sibling of [`fold_1b_rows_1way_mfr_16wide_padded`]. Instead of
/// streaming a fully-materialized length-`2^n` suffix tensor `t`, it takes the
/// two factors `(eq_lo, eq_hi)` from [`build_eq_split`] and reassociates the
/// fold as inner-then-outer:
///
/// ```text
/// s_hat_v[r] = Σ_i bit_r(W[i]) · t[i]
///            = Σ_{i_hi} eq_hi[i_hi] · ( Σ_{i_lo} bit_r(W[i_hi·B + i_lo]) · eq_lo[i_lo] )
/// ```
///
/// with `B = eq_lo.len()` (a multiple of 16) and `i = i_hi·B + i_lo`. The inner
/// sum is the same 16-wide method-of-four-Russians fold over one length-`B`
/// block against `eq_lo`; the outer step scales that length-128 block result by
/// `eq_hi[i_hi]` and XORs it into the global accumulator.
///
/// Result is **byte-identical** to
/// `fold_1b_rows_1way_mfr_16wide_padded(W, build_eq_parallel(r), padding)`:
/// GF(2^128) add is XOR (associative/commutative) and multiply is exact and
/// distributes, so the reassociation reproduces the same multiset of XOR terms.
/// Two wins over the materialized kernel:
///   1. The four MFR subset-sum tables per 16-element chunk are built from
///      `eq_lo` and are **identical for every block**, so they are precomputed
///      once and reused across all `2^(n - n_lo)` blocks (no per-chunk table
///      rebuilds).
///   2. The `2^n`-entry tensor is never streamed from RAM — only `eq_lo`
///      (+ its tables) and `eq_hi` are read, and they stay cache-resident.
///      Since the fold is LSU-bound, dropping that traffic is the main win.
pub fn fold_1b_rows_split(
    packed_witness: &[F128],
    eq_lo: &[F128],
    eq_hi: &[F128],
    padding: &PaddingSpec,
) -> Vec<F128> {
    let n = 1 << LOG_PACKING; // 128
    let b = eq_lo.len();
    assert!(
        b.is_multiple_of(16),
        "fold_1b_rows_split: eq_lo block size must be a multiple of 16 (got {b})"
    );
    assert_eq!(packed_witness.len(), b * eq_hi.len());
    let chunks_per_block = b / 16;
    let skip = ChunkPadding::new(padding, 16);

    // Precompute the eq_lo subset-sum tables once and reuse for every block.
    // `tables[c]` holds the four 16-entry tables for local chunk `c`'s 16 eq_lo
    // values — exactly what the materialized kernel rebuilds per chunk.
    let tables: Vec<[[F128; 16]; 4]> = (0..chunks_per_block)
        .map(|c| {
            let o = c * 16;
            [
                subset_sums_4([eq_lo[o], eq_lo[o + 1], eq_lo[o + 2], eq_lo[o + 3]]),
                subset_sums_4([eq_lo[o + 4], eq_lo[o + 5], eq_lo[o + 6], eq_lo[o + 7]]),
                subset_sums_4([eq_lo[o + 8], eq_lo[o + 9], eq_lo[o + 10], eq_lo[o + 11]]),
                subset_sums_4([eq_lo[o + 12], eq_lo[o + 13], eq_lo[o + 14], eq_lo[o + 15]]),
            ]
        })
        .collect();

    packed_witness
        .par_chunks(b)
        .enumerate()
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (i_hi, w_block)| {
                let mut inner = [F128::ZERO; 128];
                let base_chunk = i_hi * chunks_per_block;
                for c in 0..chunks_per_block {
                    // Same per-chunk skip predicate as the materialized kernel,
                    // evaluated at the identical global chunk index — so the two
                    // touch the exact same set of chunks.
                    if skip.skip(base_chunk + c) {
                        continue;
                    }
                    let m_chunk = &w_block[c * 16..c * 16 + 16];
                    let [tbl0, tbl1, tbl2, tbl3] = &tables[c];

                    let mut m_bytes = [[0u8; 16]; 16];
                    for (e, slot) in m_bytes.iter_mut().enumerate() {
                        slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                        slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                    }

                    for r_byte in 0..16 {
                        let lo8: u64 = (m_bytes[0][r_byte] as u64)
                            | ((m_bytes[1][r_byte] as u64) << 8)
                            | ((m_bytes[2][r_byte] as u64) << 16)
                            | ((m_bytes[3][r_byte] as u64) << 24)
                            | ((m_bytes[4][r_byte] as u64) << 32)
                            | ((m_bytes[5][r_byte] as u64) << 40)
                            | ((m_bytes[6][r_byte] as u64) << 48)
                            | ((m_bytes[7][r_byte] as u64) << 56);
                        let hi8: u64 = (m_bytes[8][r_byte] as u64)
                            | ((m_bytes[9][r_byte] as u64) << 8)
                            | ((m_bytes[10][r_byte] as u64) << 16)
                            | ((m_bytes[11][r_byte] as u64) << 24)
                            | ((m_bytes[12][r_byte] as u64) << 32)
                            | ((m_bytes[13][r_byte] as u64) << 40)
                            | ((m_bytes[14][r_byte] as u64) << 48)
                            | ((m_bytes[15][r_byte] as u64) << 56);
                        let tlo = transpose_8x8_bits(lo8).to_le_bytes();
                        let thi = transpose_8x8_bits(hi8).to_le_bytes();
                        let base = r_byte * 8;
                        for p in 0..8 {
                            let m_lo = tlo[p];
                            let m_hi = thi[p];
                            inner[base + p] += tbl0[(m_lo & 0x0F) as usize]
                                + tbl1[(m_lo >> 4) as usize]
                                + tbl2[(m_hi & 0x0F) as usize]
                                + tbl3[(m_hi >> 4) as usize];
                        }
                    }
                }
                // Outer: scale this block's length-128 partial by eq_hi[i_hi].
                // `e · (Σ eq_lo·bit) = Σ (e·eq_lo)·bit` distributes exactly, so
                // each term equals the materialized `t[i] = eq_lo·eq_hi` term.
                let e = eq_hi[i_hi];
                for r in 0..n {
                    acc[r] += e * inner[r];
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

/// Two-claim variant of [`fold_1b_rows_split`] with stack-allocated per-claim
/// inner accumulators. The common batched case (exactly 2 dense claims, e.g.
/// `[ab, c]` or `[ab, c]` alongside a sparse chain claim) hits this fast path.
///
/// Cross-claim sharing per chunk:
///   * one streaming read of the 16 packed_witness entries
///   * one bit transpose ([`transpose_8x8_bits`])
///   * per-claim subset-sum table lookups + per-claim inner accumulator update
///
/// Per-claim outputs are **byte-identical** to calling [`fold_1b_rows_split`]
/// twice — same chunk-skip predicate, same XOR multiset.
pub fn fold_1b_rows_split_2way(
    packed_witness: &[F128],
    eq_lo_0: &[F128],
    eq_hi_0: &[F128],
    eq_lo_1: &[F128],
    eq_hi_1: &[F128],
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    let n = 1 << LOG_PACKING; // 128
    let b = eq_lo_0.len();
    assert_eq!(eq_lo_1.len(), b);
    let n_hi = eq_hi_0.len();
    assert_eq!(eq_hi_1.len(), n_hi);
    assert!(
        b.is_multiple_of(16),
        "fold_1b_rows_split_2way: eq_lo block size must be a multiple of 16 (got {b})"
    );
    assert_eq!(packed_witness.len(), b * n_hi);
    let chunks_per_block = b / 16;
    let skip = ChunkPadding::new(padding, 16);

    // Precompute both claims' subset-sum tables once.
    let tables_0: Vec<[[F128; 16]; 4]> = (0..chunks_per_block)
        .map(|c| {
            let o = c * 16;
            [
                subset_sums_4([eq_lo_0[o], eq_lo_0[o + 1], eq_lo_0[o + 2], eq_lo_0[o + 3]]),
                subset_sums_4([
                    eq_lo_0[o + 4],
                    eq_lo_0[o + 5],
                    eq_lo_0[o + 6],
                    eq_lo_0[o + 7],
                ]),
                subset_sums_4([
                    eq_lo_0[o + 8],
                    eq_lo_0[o + 9],
                    eq_lo_0[o + 10],
                    eq_lo_0[o + 11],
                ]),
                subset_sums_4([
                    eq_lo_0[o + 12],
                    eq_lo_0[o + 13],
                    eq_lo_0[o + 14],
                    eq_lo_0[o + 15],
                ]),
            ]
        })
        .collect();
    let tables_1: Vec<[[F128; 16]; 4]> = (0..chunks_per_block)
        .map(|c| {
            let o = c * 16;
            [
                subset_sums_4([eq_lo_1[o], eq_lo_1[o + 1], eq_lo_1[o + 2], eq_lo_1[o + 3]]),
                subset_sums_4([
                    eq_lo_1[o + 4],
                    eq_lo_1[o + 5],
                    eq_lo_1[o + 6],
                    eq_lo_1[o + 7],
                ]),
                subset_sums_4([
                    eq_lo_1[o + 8],
                    eq_lo_1[o + 9],
                    eq_lo_1[o + 10],
                    eq_lo_1[o + 11],
                ]),
                subset_sums_4([
                    eq_lo_1[o + 12],
                    eq_lo_1[o + 13],
                    eq_lo_1[o + 14],
                    eq_lo_1[o + 15],
                ]),
            ]
        })
        .collect();

    let zero_acc = || (vec![F128::ZERO; n], vec![F128::ZERO; n]);

    packed_witness
        .par_chunks(b)
        .enumerate()
        .fold(zero_acc, |(mut acc0, mut acc1), (i_hi, w_block)| {
            // Two stack-allocated inner accumulators — identical layout to
            // the single-claim split path, just two of them.
            let mut inner0 = [F128::ZERO; 128];
            let mut inner1 = [F128::ZERO; 128];
            let base_chunk = i_hi * chunks_per_block;
            for c in 0..chunks_per_block {
                if skip.skip(base_chunk + c) {
                    continue;
                }
                let m_chunk = &w_block[c * 16..c * 16 + 16];
                let [t0a, t0b, t0c, t0d] = &tables_0[c];
                let [t1a, t1b, t1c, t1d] = &tables_1[c];

                let mut m_bytes = [[0u8; 16]; 16];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let lo8: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let hi8: u64 = (m_bytes[8][r_byte] as u64)
                        | ((m_bytes[9][r_byte] as u64) << 8)
                        | ((m_bytes[10][r_byte] as u64) << 16)
                        | ((m_bytes[11][r_byte] as u64) << 24)
                        | ((m_bytes[12][r_byte] as u64) << 32)
                        | ((m_bytes[13][r_byte] as u64) << 40)
                        | ((m_bytes[14][r_byte] as u64) << 48)
                        | ((m_bytes[15][r_byte] as u64) << 56);
                    let tlo = transpose_8x8_bits(lo8).to_le_bytes();
                    let thi = transpose_8x8_bits(hi8).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let m_lo = tlo[p];
                        let m_hi = thi[p];
                        let i_lo4 = (m_lo & 0x0F) as usize;
                        let i_hi4 = (m_lo >> 4) as usize;
                        let i_lo4h = (m_hi & 0x0F) as usize;
                        let i_hi4h = (m_hi >> 4) as usize;
                        inner0[base + p] += t0a[i_lo4] + t0b[i_hi4] + t0c[i_lo4h] + t0d[i_hi4h];
                        inner1[base + p] += t1a[i_lo4] + t1b[i_hi4] + t1c[i_lo4h] + t1d[i_hi4h];
                    }
                }
            }
            let e0 = eq_hi_0[i_hi];
            let e1 = eq_hi_1[i_hi];
            for r in 0..n {
                acc0[r] += e0 * inner0[r];
                acc1[r] += e1 * inner1[r];
            }
            (acc0, acc1)
        })
        .reduce(zero_acc, |(mut a0, mut a1), (b0, b1)| {
            for r in 0..n {
                a0[r] += b0[r];
                a1[r] += b1[r];
            }
            (a0, a1)
        })
}

/// AB-claim `s_hat_v` specialization that **skips `fold_1b_rows` entirely**
/// when the upstream layer has already produced
/// `z_vec[i_inner] = ẑ(i_inner, x_outer)` (length `2^k_log`) — the pre-sumcheck
/// partial fold lincheck builds via `partial_fold_packed_z`.
///
/// # Identity
///
/// For a PCS opening at point `(r_inner_skip, r_inner_rest, x_outer)` where
/// `x_outer` matches lincheck's, the AB-suffix tensor in `fold_1b_rows`
/// factors over the same axis decomposition that `z_vec` was built along:
///
/// ```text
/// s_hat_v[b] = Σ_{j ∈ {0,1}^(m−7)} eq(suffix, j) · bit_b(packed_witness[j])
///            = Σ_{k ∈ {0,1}^(k_log − LOG_PACKING)}
///                eq(r_inner_rest[1..], k) · z_vec[b + 2^LOG_PACKING · k]
/// ```
///
/// `r_inner_rest[0]` becomes ring-switch's `prefix0` (`x_outer_full[0]`);
/// `r_inner_rest[1..]` is the suffix's inner part. The witness's outer
/// coords were already folded into `z_vec` by the partial fold.
///
/// Output is **byte-identical** to
/// `fold_1b_rows(packed_witness, build_eq(suffix))` for the AB claim — same
/// algebraic identity, just reassociated to use the lincheck intermediate.
///
/// # Cost
///
/// `128 · 2^(k_log − LOG_PACKING)` F128 mul-adds + a tiny eq tensor build.
/// At keccak m=29, k_log=17: 128 · 1024 = 131k mul-adds — tens of µs MT, vs
/// the ~7 ms share that AB contributes to `fold_1b_rows_split_2way`.
///
/// # Panics
///
/// - if `z_vec.len() != 2^(LOG_PACKING + tail.len())`.
pub fn s_hat_v_from_z_vec(z_vec: &[F128], x_inner_rest_tail: &[F128]) -> Vec<F128> {
    let n_packed = 1usize << LOG_PACKING; // 128
    let n_tail = 1usize << x_inner_rest_tail.len();
    assert_eq!(
        z_vec.len(),
        n_packed * n_tail,
        "z_vec length {} mismatches 2^(LOG_PACKING + tail.len()) = {}",
        z_vec.len(),
        n_packed * n_tail,
    );

    if x_inner_rest_tail.is_empty() {
        // Degenerate case (k_log == LOG_PACKING): the LOG_PACKING boundary
        // ate the only inner-rest coord — z_vec IS the per-prefix-bit answer.
        return z_vec.to_vec();
    }

    let eq_tail = build_eq_parallel(x_inner_rest_tail);

    // Iterate over k outer (sequential per-thread → cache-friendly stride-1
    // reads of z_vec). Parallelize across k-ranges; each thread accumulates
    // a private length-128 buffer and the reduce step XORs them together.
    eq_tail
        .par_iter()
        .enumerate()
        .fold(
            || vec![F128::ZERO; n_packed],
            |mut acc, (k, &w)| {
                let block = &z_vec[k * n_packed..(k + 1) * n_packed];
                for b in 0..n_packed {
                    acc[b] += w * block[b];
                }
                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n_packed],
            |mut a, b| {
                for i in 0..n_packed {
                    a[i] += b[i];
                }
                a
            },
        )
}

/// Compute the slice-MLE vector `s_hat_v` (length 128) from a packed witness
/// and a tensor-expanded suffix point.
///
/// `packed_witness[i_rest] ∈ F_{2^128}` with `i_rest ∈ {0..2^L}` where
/// `L = log2(packed_witness.len())`. `suffix_tensor` is `eq_ind(suffix)` over a
/// suffix point of length `L`.
///
/// Output: `s_hat_v[i_skip] = Σ_{i_rest} (i_skip-th bit of packed_witness[i_rest]) · suffix_tensor[i_rest]`
/// for `i_skip ∈ {0..128}`. The bit-index uses the natural polynomial-basis
/// decomposition of F_{2^128} (i.e., bit-i of the u128 .lo:.hi).
///
/// O(2^L · 128) algorithm parallelized across packed-witness positions via
/// rayon: each thread folds a chunk into a per-thread length-128 partial
/// accumulator; the reduce step XORs partials elementwise into the final
/// output.
pub fn fold_1b_rows_naive(packed_witness: &[F128], suffix_tensor: &[F128]) -> Vec<F128> {
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    let n = 1 << LOG_PACKING;

    // Method-of-four-Russians fast path (standard case at any reasonable m).
    // 16-wide groups 16 elements per transpose pair so each acc entry is
    // touched once per 16 elements (~1.25× over 8-wide); fall back to 8-wide,
    // then 4-wide, then scalar as divisibility drops.
    if packed_witness.len().is_multiple_of(16) {
        return fold_1b_rows_1way_mfr_16wide_k4(packed_witness, suffix_tensor);
    }
    if packed_witness.len().is_multiple_of(8) {
        return fold_1b_rows_1way_mfr_8wide_k4(packed_witness, suffix_tensor);
    }
    if packed_witness.len() >= 4 && packed_witness.len().is_multiple_of(4) {
        return fold_1b_rows_1way_mfr(packed_witness, suffix_tensor);
    }

    // Partition into chunks; each chunk computes its own partial.
    // Empty accumulator allocator returns Vec<F128>(n) for the fold's init.
    let zero_acc = || vec![F128::ZERO; n];

    packed_witness
        .par_iter()
        .zip(suffix_tensor.par_iter())
        .fold(zero_acc, |mut acc, (elem, &w)| {
            // Bit r ∈ 0..64: from elem.lo.
            let mut lo = elem.lo;
            while lo != 0 {
                let r = lo.trailing_zeros() as usize;
                acc[r] += w;
                lo &= lo - 1;
            }
            // Bit r ∈ 64..128: from elem.hi.
            let mut hi = elem.hi;
            while hi != 0 {
                let r = hi.trailing_zeros() as usize;
                acc[64 | r] += w;
                hi &= hi - 1;
            }
            acc
        })
        .reduce(zero_acc, |mut a, b| {
            for (av, bv) in a.iter_mut().zip(b.iter()) {
                *av += *bv;
            }
            a
        })
}

/// Compute the 128 slice evaluations used by ring switching at `x_outer`.
pub fn s_hat_v_at_point(packed_witness: &[F128], x_outer: &[F128]) -> Vec<F128> {
    assert!(!x_outer.is_empty());
    assert_eq!(packed_witness.len(), 1usize << (x_outer.len() - 1));
    let suffix_tensor = build_eq_parallel(&x_outer[1..]);
    fold_1b_rows_naive(packed_witness, &suffix_tensor)
}

/// Apply packed-field multiplication to a ring-switch slice vector.
///
/// If `s` is computed from `g`, the result is the slice vector computed from
/// the packed vector whose entries are `scalar * g[i]`.
pub fn scale_s_hat_v(s: &[F128], scalar: F128) -> Vec<F128> {
    assert_eq!(s.len(), 1usize << LOG_PACKING);
    let mut out = vec![F128::ZERO; 1usize << LOG_PACKING];
    for (input_bit, value) in s.iter().enumerate() {
        let basis = if input_bit < 64 {
            F128::new(1u64 << input_bit, 0)
        } else {
            F128::new(0, 1u64 << (input_bit - 64))
        };
        let product = scalar * basis;
        let mut lo = product.lo;
        while lo != 0 {
            let output_bit = lo.trailing_zeros() as usize;
            out[output_bit] += *value;
            lo &= lo - 1;
        }
        let mut hi = product.hi;
        while hi != 0 {
            let output_bit = hi.trailing_zeros() as usize;
            out[64 + output_bit] += *value;
            hi &= hi - 1;
        }
    }
    out
}

/// Compute the verifier's claim check: `Σ_i weights[i] · s_hat_v[i]`.
pub fn claim_check(weights: &[F128], s_hat_v: &[F128]) -> F128 {
    inner_product(weights, s_hat_v)
}

/// Standard inner product `Σ_i a[i] · b[i]` over F_{2^128}.
pub fn inner_product(a: &[F128], b: &[F128]) -> F128 {
    assert_eq!(a.len(), b.len());
    let mut acc = F128::ZERO;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc += x * y;
    }
    acc
}

/// **TensorAlgebra transpose** (a.k.a. "bit transpose" of `s_hat_v`).
///
/// View `s_hat_v` (length 128) as a 128×128 binary matrix with row `i_skip` =
/// the 128 polynomial-basis bits of `s_hat_v[i_skip]`. Output `s_hat_u`
/// (length 128) is the transposed matrix re-packed: row `b` of `s_hat_u` =
/// column `b` of the input. Equivalently:
/// ```text
///     bit i_skip of s_hat_u[b]  ==  bit b of s_hat_v[i_skip]
/// ```
///
/// Used in the DP24 ring-switching: after computing `s_hat_v` (slice MLEs at
/// the suffix point), `s_hat_u = transpose(s_hat_v)` is the data viewed with
/// the "vertical" and "horizontal" dimensions swapped. The BaseFold target is
/// `T = ⟨s_hat_u, eq_ind(r'')⟩`.
///
/// Naive O(128²) bit-extract implementation. NEON acceleration via bit
/// transpose intrinsics is future work.
pub fn tensor_algebra_transpose(s_hat_v: &[F128]) -> Vec<F128> {
    assert_eq!(s_hat_v.len(), 1 << LOG_PACKING);
    let mut s_hat_u = vec![F128::ZERO; 1 << LOG_PACKING];
    for i_skip in 0..128 {
        let elem = s_hat_v[i_skip];
        // Iterate over the 128 bits b of `elem`; deposit into s_hat_u[b]'s bit i_skip.
        for b in 0..64 {
            if (elem.lo >> b) & 1 == 1 {
                if i_skip < 64 {
                    s_hat_u[b].lo |= 1u64 << i_skip;
                } else {
                    s_hat_u[b].hi |= 1u64 << (i_skip - 64);
                }
            }
        }
        for b in 0..64 {
            if (elem.hi >> b) & 1 == 1 {
                if i_skip < 64 {
                    s_hat_u[64 | b].lo |= 1u64 << i_skip;
                } else {
                    s_hat_u[64 | b].hi |= 1u64 << (i_skip - 64);
                }
            }
        }
    }
    s_hat_u
}

/// Compute `rs_eq_ind` (the "ring-switching equality indicator"), a transparent
/// multilinear of length `2^L` over the suffix domain.
///
/// `rs_eq_ind[i_rest] = Σ_b (bit b of suffix_tensor[i_rest]) · eq_r_dprime[b]`
///
/// Each `suffix_tensor[i_rest] ∈ F_{2^128}` is treated as 128 F_2-bits in the
/// polynomial basis; the inner product with `eq_r_dprime` (length 128) produces
/// one F_{2^128} value per suffix position. This is the transparent multilinear
/// the BaseFold protocol runs its sumcheck against.
///
/// O(128 · 2^L) parallelized across positions via rayon. Output positions are
/// independent — direct `par_iter` + `collect`.
pub fn fold_b128_elems_naive(suffix_tensor: &[F128], eq_r_dprime: &[F128]) -> Vec<F128> {
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    suffix_tensor
        .par_iter()
        .map(|&elem| {
            let mut acc = F128::ZERO;
            let mut lo = elem.lo;
            while lo != 0 {
                let b = lo.trailing_zeros() as usize;
                acc += eq_r_dprime[b];
                lo &= lo - 1;
            }
            let mut hi = elem.hi;
            while hi != 0 {
                let b = hi.trailing_zeros() as usize;
                acc += eq_r_dprime[64 | b];
                hi &= hi - 1;
            }
            acc
        })
        .collect()
}

/// Bit-table accelerated `fold_b128_elems`. Precomputes 16 lookup tables (one
/// per byte position), each with 256 entries: `T[byte_idx][value] = Σ eq_r_dprime[bit]`
/// over set bits in `value` (offset by `byte_idx * 8`). Per element: 16 table
/// lookups + 16 F128 XORs, no data-dependent bit-scan.
///
/// Tables: 16 × 256 × 16 B = 64 KB (fits in L1+L2). Target speedup ~3× vs the
/// `trailing_zeros` loop in `fold_b128_elems_naive`.
pub fn fold_b128_elems(suffix_tensor: &[F128], eq_r_dprime: &[F128]) -> Vec<F128> {
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    const N_BYTES: usize = 16; // bytes per F128
    const TABLE_SIZE: usize = 256;

    // Build the 16 byte-tables. `tables[byte_idx * 256 + value]` = the F128
    // sum of `eq_r_dprime[byte_idx*8 + bit]` over set bits in `value`.
    let mut tables = vec![F128::ZERO; N_BYTES * TABLE_SIZE];
    for byte_idx in 0..N_BYTES {
        let bit_base = byte_idx * 8;
        for value in 0..TABLE_SIZE {
            let mut acc = F128::ZERO;
            for bit_in_byte in 0..8 {
                if (value >> bit_in_byte) & 1 == 1 {
                    acc += eq_r_dprime[bit_base + bit_in_byte];
                }
            }
            tables[byte_idx * TABLE_SIZE + value] = acc;
        }
    }

    suffix_tensor
        .par_iter()
        .map(|&elem| {
            let tables_ptr = tables.as_ptr();
            let lo_bytes = elem.lo.to_le_bytes();
            let hi_bytes = elem.hi.to_le_bytes();
            // Tree reduction (depth 4) — see fold_b128_elems_split for the
            // pattern. Raw pointer access avoids per-lookup bounds checks
            // (max index = 15 * 256 + 255 = 4095 = N_BYTES * TABLE_SIZE - 1,
            // in bounds).
            let (l0, l1, l2, l3, l4, l5, l6, l7, h0, h1, h2, h3, h4, h5, h6, h7) = unsafe {
                (
                    *tables_ptr.add(lo_bytes[0] as usize),
                    *tables_ptr.add(TABLE_SIZE + lo_bytes[1] as usize),
                    *tables_ptr.add(2 * TABLE_SIZE + lo_bytes[2] as usize),
                    *tables_ptr.add(3 * TABLE_SIZE + lo_bytes[3] as usize),
                    *tables_ptr.add(4 * TABLE_SIZE + lo_bytes[4] as usize),
                    *tables_ptr.add(5 * TABLE_SIZE + lo_bytes[5] as usize),
                    *tables_ptr.add(6 * TABLE_SIZE + lo_bytes[6] as usize),
                    *tables_ptr.add(7 * TABLE_SIZE + lo_bytes[7] as usize),
                    *tables_ptr.add(8 * TABLE_SIZE + hi_bytes[0] as usize),
                    *tables_ptr.add(9 * TABLE_SIZE + hi_bytes[1] as usize),
                    *tables_ptr.add(10 * TABLE_SIZE + hi_bytes[2] as usize),
                    *tables_ptr.add(11 * TABLE_SIZE + hi_bytes[3] as usize),
                    *tables_ptr.add(12 * TABLE_SIZE + hi_bytes[4] as usize),
                    *tables_ptr.add(13 * TABLE_SIZE + hi_bytes[5] as usize),
                    *tables_ptr.add(14 * TABLE_SIZE + hi_bytes[6] as usize),
                    *tables_ptr.add(15 * TABLE_SIZE + hi_bytes[7] as usize),
                )
            };
            let p0 = l0 + l1;
            let p1 = l2 + l3;
            let p2 = l4 + l5;
            let p3 = l6 + l7;
            let p4 = h0 + h1;
            let p5 = h2 + h3;
            let p6 = h4 + h5;
            let p7 = h6 + h7;
            let q0 = p0 + p1;
            let q1 = p2 + p3;
            let q2 = p4 + p5;
            let q3 = p6 + p7;
            let r0 = q0 + q1;
            let r1 = q2 + q3;
            r0 + r1
        })
        .collect()
}

/// Tensor-split sibling of [`fold_b128_elems`]. Takes the two factors
/// `(eq_lo, eq_hi)` from [`build_eq_split`] instead of the materialized
/// suffix tensor. Each full entry `elem = eq_lo[i_lo] * eq_hi[i_hi]` is
/// reconstructed on the fly (one GF multiply per output position) and fed to
/// the same 16-byte-table lookup — the bit-decomposition the table indexes
/// does **not** factor through the `eq_lo`/`eq_hi` split, so the product must
/// be formed first.
///
/// Output order matches the materialized tensor: `out[i_hi·B + i_lo]` with
/// `B = eq_lo.len()`, so it is **byte-identical** to
/// `fold_b128_elems(build_eq_parallel(r), eq_r_dprime)` (field multiply is
/// exact, so `eq_lo[i_lo] * eq_hi[i_hi]` has the same bits as the
/// materialized entry).
/// Number of bytes in an `F128` (= lookup tables for the fold).
const FOLD_N_BYTES: usize = 16;
/// Entries per byte-lookup table.
const FOLD_TABLE_SIZE: usize = 256;

/// Build the 16×256 byte-lookup table the fold indexes: `table[k·256 + v]` =
/// `Σ_{bit b set in v} eq_r_dprime[k·8 + b]`. For the ring-switch fold,
/// `eq_r_dprime` already has γ_k baked in, so the table carries γ too.
pub(super) fn build_fold_byte_table(eq_r_dprime: &[F128]) -> Vec<F128> {
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    let mut tables = vec![F128::ZERO; FOLD_N_BYTES * FOLD_TABLE_SIZE];
    for byte_idx in 0..FOLD_N_BYTES {
        let bit_base = byte_idx * 8;
        for value in 0..FOLD_TABLE_SIZE {
            let mut acc = F128::ZERO;
            for bit_in_byte in 0..8 {
                if (value >> bit_in_byte) & 1 == 1 {
                    acc += eq_r_dprime[bit_base + bit_in_byte];
                }
            }
            tables[byte_idx * FOLD_TABLE_SIZE + value] = acc;
        }
    }
    tables
}

/// One folded output slot: `Σ_{k=0..16} tables[k·256 + byte_k(elem)]`, where
/// `byte_k` are the 16 little-endian bytes of `elem`. `tables` MUST be a
/// `build_fold_byte_table` output (length `16·256`). Tree-reduced (depth 4)
/// rather than a length-15 XOR chain so the adds pipeline.
#[inline(always)]
pub(crate) fn fold_one_slot(elem: F128, tables: &[F128]) -> F128 {
    debug_assert_eq!(tables.len(), FOLD_N_BYTES * FOLD_TABLE_SIZE);
    let lo_bytes = elem.lo.to_le_bytes();
    let hi_bytes = elem.hi.to_le_bytes();
    let tables_ptr = tables.as_ptr();
    // SAFETY: byte values are u8 (0..256); the max offset is
    // `15·256 + 255 = 4095 = 16·256 − 1`, in-bounds for the asserted length.
    let (l0, l1, l2, l3, l4, l5, l6, l7, h0, h1, h2, h3, h4, h5, h6, h7) = unsafe {
        (
            *tables_ptr.add(lo_bytes[0] as usize),
            *tables_ptr.add(FOLD_TABLE_SIZE + lo_bytes[1] as usize),
            *tables_ptr.add(2 * FOLD_TABLE_SIZE + lo_bytes[2] as usize),
            *tables_ptr.add(3 * FOLD_TABLE_SIZE + lo_bytes[3] as usize),
            *tables_ptr.add(4 * FOLD_TABLE_SIZE + lo_bytes[4] as usize),
            *tables_ptr.add(5 * FOLD_TABLE_SIZE + lo_bytes[5] as usize),
            *tables_ptr.add(6 * FOLD_TABLE_SIZE + lo_bytes[6] as usize),
            *tables_ptr.add(7 * FOLD_TABLE_SIZE + lo_bytes[7] as usize),
            *tables_ptr.add(8 * FOLD_TABLE_SIZE + hi_bytes[0] as usize),
            *tables_ptr.add(9 * FOLD_TABLE_SIZE + hi_bytes[1] as usize),
            *tables_ptr.add(10 * FOLD_TABLE_SIZE + hi_bytes[2] as usize),
            *tables_ptr.add(11 * FOLD_TABLE_SIZE + hi_bytes[3] as usize),
            *tables_ptr.add(12 * FOLD_TABLE_SIZE + hi_bytes[4] as usize),
            *tables_ptr.add(13 * FOLD_TABLE_SIZE + hi_bytes[5] as usize),
            *tables_ptr.add(14 * FOLD_TABLE_SIZE + hi_bytes[6] as usize),
            *tables_ptr.add(15 * FOLD_TABLE_SIZE + hi_bytes[7] as usize),
        )
    };
    // Level 1: 8 pair sums.
    let p0 = l0 + l1;
    let p1 = l2 + l3;
    let p2 = l4 + l5;
    let p3 = l6 + l7;
    let p4 = h0 + h1;
    let p5 = h2 + h3;
    let p6 = h4 + h5;
    let p7 = h6 + h7;
    // Level 2.
    let q0 = p0 + p1;
    let q1 = p2 + p3;
    let q2 = p4 + p5;
    let q3 = p6 + p7;
    // Level 3.
    let r0 = q0 + q1;
    let r1 = q2 + q3;
    // Level 4.
    r0 + r1
}

/// Per-output-index value of a [`super::RsEqInd::DeferredDense`] fold (the value the
/// materialized `fold_b128_elems_split` would store at position `j`):
/// `fold_one_slot(eq_lo[j & (B−1)] · eq_hi[j >> log2 B], table)`, `B = eq_lo.len()`.
#[inline(always)]
pub(crate) fn deferred_dense_value(
    eq_lo: &[F128],
    eq_hi: &[F128],
    table: &[F128],
    log_b: usize,
    j: usize,
) -> F128 {
    let mask = (1usize << log_b) - 1;
    fold_one_slot(eq_lo[j & mask] * eq_hi[j >> log_b], table)
}

pub fn fold_b128_elems_split(eq_lo: &[F128], eq_hi: &[F128], eq_r_dprime: &[F128]) -> Vec<F128> {
    let tables = build_fold_byte_table(eq_r_dprime);
    fold_b128_from_table(eq_lo, eq_hi, &tables)
}

/// Materialize a split-tensor fold from a prebuilt byte `tables`
/// (`build_fold_byte_table` output). Block-parallel over `eq_hi`: each rayon
/// task sweeps one `e_hi` over all of `eq_lo` (so `e_hi` is hoisted once per
/// block). Used to un-defer a [`super::RsEqInd::DeferredDense`] in the pcs combine's
/// general (mixed/sparse/packed-direct) fallback path.
pub(crate) fn fold_b128_from_table(eq_lo: &[F128], eq_hi: &[F128], tables: &[F128]) -> Vec<F128> {
    let b = eq_lo.len();
    // Each slot is written exactly once (`*slot = acc`) before any read.
    let mut out = crate::scratch::take_f128(b * eq_hi.len());
    out.par_chunks_mut(b)
        .zip(eq_hi.par_iter())
        .for_each(|(out_block, &e_hi)| {
            for (i_lo, slot) in out_block.iter_mut().enumerate() {
                *slot = fold_one_slot(eq_lo[i_lo] * e_hi, tables);
            }
        });
    out
}

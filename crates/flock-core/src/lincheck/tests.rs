//! Kernel-dispatch tests that reach into `lincheck`'s private surface:
//! `partial_fold_packed_z_best`, `n_log_ok_for_tile`, and `NEON_TILE_T`.
//! Tests that need only the public API live in `crates/flock-core/tests/lincheck.rs`.

use super::*;

use flock_test_util::Rng;

/// Field-element helpers over the shared [`Rng`]. They live here because a
/// foreign trait cannot be implemented for a foreign type, and `flock-test-util`
/// depends on nothing (see that crate's docs).
trait RngF128 {
    fn f128(&mut self) -> F128;
    fn f128_vec(&mut self, n: usize) -> Vec<F128>;
}

impl RngF128 for Rng {
    fn f128(&mut self) -> F128 {
        F128 {
            lo: self.next_u64(),
            hi: self.next_u64(),
        }
    }
    fn f128_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.f128()).collect()
    }
}
#[test]
fn partial_fold_dispatch_handles_small_k() {
    let (m, k_log) = (8usize, 2usize);
    let mut rng = Rng::new(1234);
    let z = rng.bits(1 << m);
    let z_packed = pack_z_lincheck(&z, m, k_log);
    let eq = build_eq_table(&rng.f128_vec(m - k_log));

    let serial = partial_fold_packed_z(&z_packed, m, k_log, &eq);
    let best = partial_fold_packed_z_best(&z_packed, m, k_log, 1 << k_log, &eq);
    assert_eq!(serial, best);
}

/// NEON single-matrix kernel matches the scalar reference.
#[cfg(target_arch = "aarch64")]
#[test]
fn partial_fold_neon_single_matches_serial() {
    for &(m, k_log) in &[(14usize, 4), (14, 5), (16, 5), (16, 8), (18, 10)] {
        if !n_log_ok_for_tile(m, k_log, NEON_TILE_T) {
            continue;
        }
        let mut rng = Rng::new(7000 + m as u64);
        let z = rng.bits(1 << m);
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let n_log = m - k_log;
        let p = rng.f128_vec(n_log);
        let eq = build_eq_table(&p);

        let serial = partial_fold_packed_z(&z_packed, m, k_log, &eq);
        let neon = partial_fold_packed_z_neon_single(&z_packed, m, k_log, &eq);
        assert_eq!(serial, neon, "at m={m}, k_log={k_log}");
        let iblock =
            partial_fold_packed_z_neon_iblock_padded(&z_packed, m, k_log, 1usize << k_log, &eq);
        assert_eq!(serial, iblock, "iblock at m={m}, k_log={k_log}");
    }
}

/// The default outer(tile)-partitioned fold is **bit-identical** to the legacy
/// i_inner-partitioned iblock kernel — dense (useful=k) and padded (useful<k,
/// including a non-byte-aligned shape) across tile-eligible sizes. GF(2¹²⁸) add
/// is XOR (associative + commutative), so the two partition strategies must
/// produce the exact same length-k vector.
#[cfg(target_arch = "aarch64")]
#[test]
fn partial_fold_oblock_matches_iblock() {
    // (m, k_log, useful_bits); mix of dense and padded, all tile-eligible.
    let cases: &[(usize, usize, usize)] = &[
        (14, 4, 1 << 4),   // dense, small k
        (16, 8, 1 << 8),   // dense
        (18, 10, 1 << 10), // dense
        (20, 10, 597),     // padded, non-byte-aligned
        (22, 14, 15_409),  // padded, non-byte-aligned (k=16384)
    ];
    for &(m, k_log, useful_bits) in cases {
        assert!(
            n_log_ok_for_tile(m, k_log, NEON_TILE_T),
            "case must be tile-eligible"
        );
        let k = 1usize << k_log;
        let n_log = m - k_log;
        let n_blocks = 1usize << n_log;
        let mut rng = Rng::new(7200 + (m * 31 + k_log) as u64);
        let mut z = rng.bits(1 << m);
        // Honest padding: zero rows [useful, k) of every block.
        for blk in 0..n_blocks {
            for j in useful_bits..k {
                z[blk * k + j] = false;
            }
        }
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let eq = build_eq_table(&rng.f128_vec(n_log));
        let want = partial_fold_packed_z_neon_iblock_padded(&z_packed, m, k_log, useful_bits, &eq);
        let got = partial_fold_packed_z_neon_oblock_padded(&z_packed, m, k_log, useful_bits, &eq);
        assert_eq!(want, got, "m={m} k_log={k_log} useful={useful_bits}");
    }
}

/// `useful_bits = k`, several tile-eligible sizes).
#[cfg(target_arch = "x86_64")]
#[test]
fn partial_fold_x86_tiled_matches_serial() {
    for &(m, k_log) in &[(14usize, 4), (14, 5), (16, 5), (16, 8), (18, 10)] {
        if !n_log_ok_for_tile(m, k_log, 8) {
            continue;
        }
        let mut rng = Rng::new(7100 + m as u64);
        let z = rng.bits(1 << m);
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let n_log = m - k_log;
        let p = rng.f128_vec(n_log);
        let eq = build_eq_table(&p);
        let k = 1usize << k_log;
        let serial = partial_fold_packed_z(&z_packed, m, k_log, &eq);
        let tiled = partial_fold_packed_z_x86_tiled_padded(&z_packed, m, k_log, k, &eq);
        assert_eq!(serial, tiled, "at m={m}, k_log={k_log}");
    }
}

/// **Padding skip is byte-identical to the dense partial fold.** On a
/// witness with honest zeros at rows `[useful_bits, 2^k_log)` of every
/// block, the padded kernels (fast + NEON single) must produce the
/// exact same `z_vec` as the dense kernels — and the dense scalar
/// reference is the ground truth.
///
/// Covers the three hash padding shapes plus a non-byte-aligned
/// `useful_bits` to exercise the NEON's boundary block (rounded up to
/// `BLOCK_K = 8`).
#[test]
fn partial_fold_padded_matches_dense() {
    // (m, k_log, useful_bits)
    let cases: &[(usize, usize, usize)] = &[
        // BLAKE3 (k_log=14, useful=15409 — boundary not byte-aligned).
        (17, 14, 15_409),
        // SHA-2  (k_log=15, useful=31401 — boundary not byte-aligned).
        (18, 15, 31_401),
        // Keccak (k_log=16, useful=42560 — exact byte boundary).
        (19, 16, 42_560),
    ];
    for &(m, k_log, useful_bits) in cases {
        let mut rng = Rng::new(0xBADD_BEEF_u64.wrapping_add((k_log * 31 + m) as u64));
        let total_bits = 1usize << m;
        let n_log = m - k_log;
        let block_size = 1usize << k_log;
        let n_blocks = 1usize << n_log;

        // Random witness with bits [useful_bits, block_size) of every block
        // zeroed — mirrors the hash-module layout.
        let mut z = rng.bits(total_bits);
        for blk in 0..n_blocks {
            for j in useful_bits..block_size {
                z[blk * block_size + j] = false;
            }
        }
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let outer_point = rng.f128_vec(n_log);
        let eq_outer = build_eq_table(&outer_point);

        let dense_fast = partial_fold_packed_z_fast(&z_packed, m, k_log, &eq_outer);
        let padded_fast =
            partial_fold_packed_z_fast_padded(&z_packed, m, k_log, useful_bits, &eq_outer);
        assert_eq!(
            dense_fast, padded_fast,
            "fast: m={m}, k_log={k_log}, useful={useful_bits}"
        );

        #[cfg(target_arch = "aarch64")]
        if n_log_ok_for_tile(m, k_log, NEON_TILE_T) {
            let dense_neon = partial_fold_packed_z_neon_single(&z_packed, m, k_log, &eq_outer);
            let padded_neon = partial_fold_packed_z_neon_single_padded(
                &z_packed,
                m,
                k_log,
                useful_bits,
                &eq_outer,
            );
            assert_eq!(
                dense_neon, padded_neon,
                "neon: m={m}, k_log={k_log}, useful={useful_bits}"
            );
            // i_inner-partitioned kernel: dense and padded must both match.
            let dense_iblock = partial_fold_packed_z_neon_iblock_padded(
                &z_packed,
                m,
                k_log,
                1usize << k_log,
                &eq_outer,
            );
            let padded_iblock = partial_fold_packed_z_neon_iblock_padded(
                &z_packed,
                m,
                k_log,
                useful_bits,
                &eq_outer,
            );
            assert_eq!(
                dense_neon, dense_iblock,
                "iblock dense: m={m}, k_log={k_log}, useful={useful_bits}"
            );
            assert_eq!(
                dense_neon, padded_iblock,
                "iblock padded: m={m}, k_log={k_log}, useful={useful_bits}"
            );
        }
    }
}

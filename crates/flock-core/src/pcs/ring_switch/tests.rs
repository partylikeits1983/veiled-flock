use super::*;
use crate::challenger::Challenger;
use crate::challenger::FsChallenger;
use crate::lincheck::{pack_z_lincheck, partial_fold_packed_z};
use crate::pcs::pack::pack_witness;
use crate::zerocheck::multilinear::lagrange_weights_naive;
use crate::zerocheck::univariate_skip::build_eq;

/// Binary-query specialization matches the general path bit-for-bit.
#[test]
fn eval_rs_eq_finish_binary_q_matches_general() {
    let mut rng = crate::challenger::RandomChallenger::new(0x_B17_0BBE);
    let log_n = 20usize;
    let prefix_len = 15usize;
    let suffix_len = log_n - prefix_len; // 5
    let z_vals: Vec<F128> = (0..log_n).map(|_| rng.sample_f128()).collect();
    let query_prefix: Vec<F128> = (0..prefix_len).map(|_| rng.sample_f128()).collect();
    let eq_r_dprime: Vec<F128> = (0..(1 << LOG_PACKING)).map(|_| rng.sample_f128()).collect();
    let prefix = eval_rs_eq_prefix(&z_vals[..prefix_len], &query_prefix);

    for y in 0..(1usize << suffix_len) {
        // General path: build a Vec<F128> with binary entries.
        let query_suffix: Vec<F128> = (0..suffix_len)
            .map(|j| {
                if (y >> j) & 1 == 1 {
                    F128::ONE
                } else {
                    F128::ZERO
                }
            })
            .collect();
        let general = eval_rs_eq_finish_from_prefix(
            &prefix,
            &z_vals[prefix_len..],
            &query_suffix,
            &eq_r_dprime,
        );
        let binary = eval_rs_eq_finish_from_prefix_binary_q(
            &prefix,
            &z_vals[prefix_len..],
            y as u32,
            &eq_r_dprime,
        );
        assert_eq!(general, binary, "y={y} mismatch");
    }
}

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.next_u64() & 1 == 1).collect()
    }
    fn f128(&mut self) -> F128 {
        F128 {
            lo: self.next_u64(),
            hi: self.next_u64(),
        }
    }
}

#[test]
fn packed_scaling_commutes_with_slice_evaluation() {
    let mut rng = Rng::new(0x5ca1e);
    let log_len = 6;
    let packed = (0..1usize << log_len)
        .map(|_| rng.f128())
        .collect::<Vec<_>>();
    let point = (0..=log_len).map(|_| rng.f128()).collect::<Vec<_>>();
    let scalar = rng.f128();
    let scaled_packed = packed
        .iter()
        .map(|value| scalar * *value)
        .collect::<Vec<_>>();

    let slices = s_hat_v_at_point(&packed, &point);
    let scaled_slices = scale_s_hat_v(&slices, scalar);
    assert_eq!(scaled_slices, s_hat_v_at_point(&scaled_packed, &point));
}

#[test]
fn distinct_scalars_act_differently_on_a_nonzero_slice_vector() {
    let mut slices = vec![F128::ZERO; 1usize << LOG_PACKING];
    slices[37] = F128::new(0x1234, 0x5678);
    let first = F128::new(0xaaaa, 0xbbbb);
    let second = F128::new(0xcccc, 0xdddd);

    assert_ne!(
        scale_s_hat_v(&slices, first),
        scale_s_hat_v(&slices, second)
    );
}

/// Reference: directly compute ẑ_skip(z_skip, x_outer) for a Boolean witness `z`.
///
/// `ẑ_skip(z_skip, x_outer) = Σ_{i_skip ∈ {0,1}^6} ν_φ8(i_skip)(z_skip)
///                          · Σ_{i_outer} eq(x_outer, i_outer)
///                                       · z[i_outer * 64 + i_skip]`
///
/// This is the polynomial that the zerocheck claims at value `v`.
fn zhat_skip_reference(z: &[bool], m: usize, z_skip: F128, x_outer: &[F128]) -> F128 {
    const K_SKIP: usize = 6;
    let ell = 1usize << K_SKIP;
    assert_eq!(z.len(), 1 << m);
    assert_eq!(x_outer.len(), m - K_SKIP);

    let lambda = lagrange_weights_naive(K_SKIP, z_skip); // 64 weights
    let eq_outer = build_eq(x_outer); // 2^(m-6) values

    // Index convention: z[i] for i ∈ 0..2^m, with low k_skip bits = i_skip and
    // high (m - k_skip) bits = i_outer (matching pack_bits in univariate_skip).
    let mut acc = F128::ZERO;
    for i_outer in 0..(1usize << (m - K_SKIP)) {
        let base = i_outer * ell;
        // Inner = Σ_{i_skip} λ[i_skip] · z[base + i_skip], where z bits are 0/1
        // lifted to F_{2^128}.
        let mut inner = F128::ZERO;
        for i_skip in 0..ell {
            if z[base + i_skip] {
                inner += lambda[i_skip];
            }
        }
        acc += eq_outer[i_outer] * inner;
    }
    acc
}

/// The key identity: with weights and s_hat_v constructed from the right
/// places, the claim-check yields `ẑ_skip(z_skip, x_outer)`.
#[test]
fn claim_check_recovers_zhat_skip() {
    let mut rng = Rng::new(0xAA7);
    // m must satisfy m ≥ LOG_PACKING = 7 AND m ≥ K_SKIP + 1 = 7 (for x_outer
    // to have at least one element so x_outer[0] is defined). m ≥ 7 suffices
    // when m == K_SKIP only x_outer is length 1, x_outer[0..0] = empty suffix.
    // But pack_witness needs m ≥ 7 (LOG_PACKING). Test at m in [8, 9, 10].
    for &m in &[8usize, 9, 10] {
        let z = rng.bits(1 << m);
        let z_skip = rng.f128();
        let x_outer: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();

        // Reference value: directly compute ẑ_skip.
        let expected = zhat_skip_reference(&z, m, z_skip, &x_outer);

        // Build PCS data: pack, then compute s_hat_v naively from the packed
        // witness and the suffix tensor (= eq_ind of x_outer[1..]).
        let packed = pack_witness(&z, m);
        let suffix_tensor = build_eq(&x_outer[1..]); // length 2^(m-7)
        assert_eq!(packed.len(), suffix_tensor.len());
        let s_hat_v = fold_1b_rows_naive(&packed, &suffix_tensor);

        // Build weights and run claim check.
        let weights = build_claim_weights(z_skip, x_outer[0]);
        let got = claim_check(&weights, &s_hat_v);

        assert_eq!(got, expected, "claim-check mismatch at m={m}");
    }
}

#[test]
fn weights_have_correct_length() {
    let w = build_claim_weights(F128 { lo: 1, hi: 0 }, F128 { lo: 2, hi: 0 });
    assert_eq!(w.len(), 128);
}

/// Round-trip: prove() and verify() with the same challenger seed must
/// produce identical (rs_eq_ind, sumcheck_claim).
#[test]
fn prove_verify_roundtrip() {
    let mut rng = Rng::new(0xBEEF);
    for &m in &[8usize, 9, 10, 11] {
        let z = rng.bits(1 << m);
        let z_skip = rng.f128();
        let x_outer: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();

        // Reference: directly compute ẑ_skip — this is the zerocheck's claim.
        let claim = zhat_skip_reference(&z, m, z_skip, &x_outer);

        let packed = pack_witness(&z, m);

        // Prover.
        let mut ch_p = FsChallenger::new(b"flock-test");
        let (proof, out_p) = prove(&packed, &x_outer, &mut ch_p);

        // Verifier (matched challenger).
        let mut ch_v = FsChallenger::new(b"flock-test");
        let out_v = verify(claim, z_skip, &x_outer, &proof, &mut ch_v)
            .unwrap_or_else(|e| panic!("verify rejected honest at m={m}: {e:?}"));

        assert_eq!(
            out_p.sumcheck_claim, out_v.sumcheck_claim,
            "sumcheck_claim mismatch at m={m}"
        );
        assert_eq!(
            out_p.rs_eq_ind, out_v.rs_eq_ind,
            "rs_eq_ind mismatch at m={m}"
        );
    }
}

/// DP24 identity: `⟨packed_witness, rs_eq_ind⟩ = sumcheck_claim`.
/// This is the *core* algebraic identity that makes BaseFold work.
#[test]
fn dp24_identity_holds() {
    let mut rng = Rng::new(0xABCD);
    for &m in &[8usize, 9, 10, 11] {
        let z = rng.bits(1 << m);
        let x_outer: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();

        let packed = pack_witness(&z, m);
        let mut ch = FsChallenger::new(b"flock-test");
        let (_proof, out) = prove(&packed, &x_outer, &mut ch);

        // The DP24 identity: T = ⟨packed_witness, rs_eq_ind⟩.
        let lhs = inner_product(&packed, &out.rs_eq_ind);
        assert_eq!(lhs, out.sumcheck_claim, "DP24 identity fails at m={m}");
    }
}

/// Mutation rejection: flipping one bit of the proof must cause verify to reject.
#[test]
fn verify_rejects_mutated_proof() {
    let m = 10usize;
    let mut rng = Rng::new(0x99);
    let z = rng.bits(1 << m);
    let z_skip = rng.f128();
    let x_outer: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
    let claim = zhat_skip_reference(&z, m, z_skip, &x_outer);
    let packed = pack_witness(&z, m);

    let mut ch_p = FsChallenger::new(b"flock-test");
    let (mut proof, _) = prove(&packed, &x_outer, &mut ch_p);
    // Flip one bit of s_hat_v.
    proof.s_hat_v[0].lo ^= 1;

    let mut ch_v = FsChallenger::new(b"flock-test");
    let res = verify(claim, z_skip, &x_outer, &proof, &mut ch_v);
    assert!(matches!(res, Err(VerifyError::ClaimMismatch)));
}

/// Tensor-algebra transpose is involutive (applying it twice returns the
/// original).
#[test]
fn transpose_is_involution() {
    let mut rng = Rng::new(0xDEAD);
    let s_hat_v: Vec<F128> = (0..128).map(|_| rng.f128()).collect();
    let twice = tensor_algebra_transpose(&tensor_algebra_transpose(&s_hat_v));
    assert_eq!(s_hat_v, twice);
}

#[test]
fn prove_batched_matches_sequential() {
    let mut rng = Rng::new(0x1234_5678);
    for &m in &[8usize, 9, 10, 11] {
        let z = rng.bits(1 << m);
        let x_a: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        let x_b: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        let packed = pack_witness(&z, m);

        // Sequential reference.
        let mut ch_seq = FsChallenger::new(b"flock-test");
        let (p_a, o_a) = prove(&packed, &x_a, &mut ch_seq);
        let (p_b, o_b) = prove(&packed, &x_b, &mut ch_seq);

        // Batched. After γ-baking, the batched transcript samples γ_rs
        // mid-loop, so it diverges from sequential `prove`. We can still
        // check `s_hat_v` matches (it's determined by transcript up to
        // its sample point, which is identical to sequential) and that
        // sumcheck_claim matches (γ doesn't enter sumcheck_claim).
        // rs_eq_ind has γ baked in, so it differs from sequential.
        let mut ch_batch = FsChallenger::new(b"flock-test");
        let (results, _gammas_rs) = prove_batched(&packed, &[&x_a, &x_b], &mut ch_batch);

        assert_eq!(results[0].0, p_a, "s_hat_v[0] mismatch at m={m}");
        assert_eq!(results[1].0, p_b, "s_hat_v[1] mismatch at m={m}");
        // sumcheck_claim is determined by s_hat_v + r''; both match.
        assert_eq!(results[0].1.sumcheck_claim, o_a.sumcheck_claim);
        assert_eq!(results[1].1.sumcheck_claim, o_b.sumcheck_claim);
        // rs_eq_ind shape check (γ-baked, so byte values differ from sequential).
        assert_eq!(results[0].1.rs_eq_ind.len(), o_a.rs_eq_ind.len());
        assert_eq!(results[1].1.rs_eq_ind.len(), o_b.rs_eq_ind.len());
    }
}

/// The method-of-four-Russians fold must produce byte-identical output
/// to the scalar bit-scan version, for both s_hat_v vectors at k=2.
#[test]
fn mfr_fold_matches_scalar_bit_scan() {
    let mut rng = Rng::new(0xBEEF_D00D);
    for &m in &[9usize, 11, 13, 14] {
        let l = m - 7;
        let pw_len = 1usize << l;
        // Need len divisible by 4 for MFR (true for l >= 2, i.e., m >= 9).
        let pw: Vec<F128> = (0..pw_len).map(|_| rng.f128()).collect();
        let suffix0: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let suffix1: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let tensor0 = build_eq(&suffix0);
        let tensor1 = build_eq(&suffix1);

        // Reference: naive bit-scan, k=2 path.
        let s0_ref = fold_1b_rows_naive(&pw, &tensor0);
        let s1_ref = fold_1b_rows_naive(&pw, &tensor1);

        // Under test: method-of-four-Russians.
        let (s0_mfr, s1_mfr) = fold_1b_rows_2way_mfr(&pw, &tensor0, &tensor1);

        assert_eq!(s0_mfr, s0_ref, "s_hat_v0 mismatch at m={m}");
        assert_eq!(s1_mfr, s1_ref, "s_hat_v1 mismatch at m={m}");
    }
}

/// The 8-wide (two-k=4-table) folds — both the 1-way and 2-way variants —
/// must match the naive bit-scan.
#[test]
fn mfr_fold_8wide_matches_scalar() {
    let mut rng = Rng::new(0x8888_1357);
    for &m in &[10usize, 12, 13, 16] {
        let l = m - 7;
        let pw_len = 1usize << l; // divisible by 8 for l >= 3 (m >= 10)
        let pw: Vec<F128> = (0..pw_len).map(|_| rng.f128()).collect();
        let suffix0: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let suffix1: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let t0 = build_eq(&suffix0);
        let t1 = build_eq(&suffix1);

        let s0_ref = fold_1b_rows_naive(&pw, &t0);
        let s1_ref = fold_1b_rows_naive(&pw, &t1);
        assert_eq!(
            fold_1b_rows_1way_mfr_8wide_k4(&pw, &t0),
            s0_ref,
            "1-way 8wide m={m}"
        );
        let (s0, s1) = fold_1b_rows_2way_mfr_8wide(&pw, &t0, &t1);
        assert_eq!(s0, s0_ref, "2-way 8wide s0 m={m}");
        assert_eq!(s1, s1_ref, "2-way 8wide s1 m={m}");
    }
}

/// Throughput A/B of the fold_1b_rows variants at m=29 scale. `#[ignore]`d
/// (allocates/folds 64 MB buffers many times); run explicitly with
/// `cargo test --release -- --ignored --nocapture zzz_bench_fold_1b`.
/// **Padding skip is byte-identical to the dense fold.** On a packed
/// witness whose every block has bits `[useful_bits, 2^k_log)` honestly
/// zero, the `_padded` kernels must produce the exact same `(a0, a1)` as
/// the dense kernels — every skipped chunk would have contributed
/// `lookup[0] = 0` to every output position.
///
/// Covers all three hash padding shapes for both the 8-wide and 4-wide
/// MFR kernels.
#[test]
fn fold_1b_padded_matches_dense() {
    // (m, k_log, useful_bits)
    let cases: &[(usize, usize, usize)] = &[
        // BLAKE3: k_log=14, useful=15409 (boundary not 128-aligned)
        (17, 14, 15_409),
        // SHA-2:  k_log=15, useful=31401 (boundary not 128-aligned)
        (18, 15, 31_401),
        // Keccak: k_log=16, useful=42560 (128-aligned; 35% of chunks skip)
        (19, 16, 42_560),
    ];
    for &(m, k_log, useful_bits) in cases {
        let mut rng = Rng::new(0xCAFE_FACE_u64.wrapping_add((k_log * 31 + m) as u64));
        let total_bits = 1usize << m;
        let block_size = 1usize << k_log;
        let n_blocks = 1usize << (m - k_log);

        // Random witness, then zero bits [useful_bits, block_size) of every
        // block.
        let mut z = rng.bits(total_bits);
        for blk in 0..n_blocks {
            for j in useful_bits..block_size {
                z[blk * block_size + j] = false;
            }
        }
        let packed = pack_witness(&z, m);

        // Random suffix tensors of the right length.
        let len = packed.len();
        let t0: Vec<F128> = (0..len).map(|_| rng.f128()).collect();
        let t1: Vec<F128> = (0..len).map(|_| rng.f128()).collect();
        let padding = PaddingSpec {
            k_log,
            useful_bits_per_block: useful_bits,
        };

        if packed.len().is_multiple_of(8) {
            let dense = fold_1b_rows_2way_mfr_8wide(&packed, &t0, &t1);
            let padded = fold_1b_rows_2way_mfr_8wide_padded(&packed, &t0, &t1, &padding);
            assert_eq!(
                dense, padded,
                "8-wide mismatch: m={m}, k_log={k_log}, useful={useful_bits}"
            );
        }
        if packed.len().is_multiple_of(4) {
            let dense = fold_1b_rows_2way_mfr(&packed, &t0, &t1);
            let padded = fold_1b_rows_2way_mfr_padded(&packed, &t0, &t1, &padding);
            assert_eq!(
                dense, padded,
                "4-wide mismatch: m={m}, k_log={k_log}, useful={useful_bits}"
            );
        }
    }
}

/// `build_eq_split` factors `build_eq` exactly: the outer product of the
/// two halves reconstructs every full-tensor entry bit-for-bit.
#[test]
fn build_eq_split_reconstructs_full() {
    let mut rng = Rng::new(0x9911);
    for &l in &[4usize, 7, 10] {
        let r: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let full = build_eq(&r);
        for n_lo in 0..=l {
            let (eq_lo, eq_hi) = build_eq_split(&r, n_lo);
            assert_eq!(eq_lo.len(), 1 << n_lo);
            assert_eq!(eq_hi.len(), 1 << (l - n_lo));
            let mask = (1usize << n_lo) - 1;
            for (i, &f) in full.iter().enumerate() {
                let recon = eq_lo[i & mask] * eq_hi[i >> n_lo];
                assert_eq!(recon, f, "reconstruct mismatch l={l} n_lo={n_lo} i={i}");
            }
        }
    }
}

/// `fold_1b_rows_split` is byte-identical to the materialized 16-wide
/// kernel for every split width, including padded (skip-engaging) shapes
/// and split blocks both smaller and larger than the padding block.
#[test]
fn fold_1b_rows_split_matches_16wide() {
    // (m, k_log, useful_bits): same padding shapes as
    // `fold_1b_padded_matches_dense`, so chunk-skip actually engages.
    let cases: &[(usize, usize, usize)] = &[(17, 14, 15_409), (18, 15, 31_401), (19, 16, 42_560)];
    for &(m, k_log, useful_bits) in cases {
        let l = m - LOG_PACKING;
        let len = 1usize << l;
        let mut rng = Rng::new(0x5757_u64.wrapping_add((m * 131 + k_log) as u64));
        let w: Vec<F128> = (0..len).map(|_| rng.f128()).collect();
        let r: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let full_eq = build_eq(&r);
        let padding = PaddingSpec {
            k_log,
            useful_bits_per_block: useful_bits,
        };

        let reference = fold_1b_rows_1way_mfr_16wide_padded(&w, &full_eq, &padding);
        // Sweep n_lo across, below, and equal to the padding block width so
        // the split-block vs padding-block alignment is exercised both ways.
        for n_lo in 4..=l {
            let (eq_lo, eq_hi) = build_eq_split(&r, n_lo);
            let got = fold_1b_rows_split(&w, &eq_lo, &eq_hi, &padding);
            assert_eq!(
                got, reference,
                "fold_1b_rows_split mismatch: m={m}, k_log={k_log}, n_lo={n_lo}"
            );
        }
        // The production chooser.
        let (eq_lo, eq_hi) = build_eq_split(&r, split_n_lo(l));
        assert_eq!(
            fold_1b_rows_split(&w, &eq_lo, &eq_hi, &padding),
            reference,
            "fold_1b_rows_split mismatch at split_n_lo: m={m}"
        );
    }
}

/// `fold_1b_rows_split_2way` matches two separate `fold_1b_rows_split`
/// calls byte-for-byte across the padded/skip shapes.
#[test]
fn fold_1b_rows_split_2way_matches_per_claim() {
    let cases: &[(usize, usize, usize)] = &[(17, 14, 15_409), (18, 15, 31_401), (19, 16, 42_560)];
    for &(m, k_log, useful_bits) in cases {
        let l = m - LOG_PACKING;
        let len = 1usize << l;
        let mut rng = Rng::new(0xBEEF_u64.wrapping_add((m * 131 + k_log) as u64));
        let w: Vec<F128> = (0..len).map(|_| rng.f128()).collect();
        let padding = PaddingSpec {
            k_log,
            useful_bits_per_block: useful_bits,
        };
        let n_lo = split_n_lo(l);
        let r0: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let r1: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let (lo0, hi0) = build_eq_split(&r0, n_lo);
        let (lo1, hi1) = build_eq_split(&r1, n_lo);
        let (got0, got1) = fold_1b_rows_split_2way(&w, &lo0, &hi0, &lo1, &hi1, &padding);
        let want0 = fold_1b_rows_split(&w, &lo0, &hi0, &padding);
        let want1 = fold_1b_rows_split(&w, &lo1, &hi1, &padding);
        assert_eq!(
            got0, want0,
            "fold_1b_rows_split_2way mismatch (claim 0) m={m}"
        );
        assert_eq!(
            got1, want1,
            "fold_1b_rows_split_2way mismatch (claim 1) m={m}"
        );
    }
}

/// `fold_b128_elems_split` reconstructs the suffix entry on the fly and
/// matches the materialized `fold_b128_elems` for every split width.
#[test]
fn fold_b128_elems_split_matches_dense() {
    let mut rng = Rng::new(0xB0B0);
    for &l in &[4usize, 8, 10] {
        let r: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let full_eq = build_eq(&r);
        let eq_r: Vec<F128> = (0..128).map(|_| rng.f128()).collect();
        let reference = fold_b128_elems(&full_eq, &eq_r);
        for n_lo in 4..=l {
            let (eq_lo, eq_hi) = build_eq_split(&r, n_lo);
            let got = fold_b128_elems_split(&eq_lo, &eq_hi, &eq_r);
            assert_eq!(
                got, reference,
                "fold_b128_elems_split mismatch l={l} n_lo={n_lo}"
            );
        }
    }
}

/// AB-claim s_hat_v computed via `s_hat_v_from_z_vec` (reusing lincheck's
/// pre-sumcheck partial fold of `z` at `x_outer`) is byte-identical to the
/// general-purpose `fold_1b_rows` over the materialized suffix tensor.
#[test]
fn s_hat_v_from_z_vec_matches_fold_1b_rows_ab() {
    const K_SKIP: usize = 6;
    // (m, k_log) — K_SKIP fixed at 6 (so x_inner_rest has k_log − 6 coords;
    // x_inner_rest[0] becomes ring-switch's prefix0 because
    // K_SKIP + 1 = LOG_PACKING = 7). n_log = m − k_log must be ≥ 3 for
    // partial_fold_packed_z's stripe layout.
    let cases: &[(usize, usize)] = &[(13, 10), (15, 11), (17, 13)];
    for &(m, k_log) in cases {
        assert!(k_log >= LOG_PACKING);
        assert!(k_log >= K_SKIP);
        let n_log = m - k_log;
        assert!(n_log >= 3);
        let mut rng = Rng::new(0xCAFE_u64.wrapping_add((m * 131 + k_log) as u64));

        // Boolean witness in standard logical (linear) layout.
        let z = rng.bits(1 << m);
        let packed = pack_witness(&z, m);
        let z_packed_lincheck = pack_z_lincheck(&z, m, k_log);

        // AB-shaped quirky point: x_inner_rest has k_log − K_SKIP coords;
        // x_outer has n_log coords.
        let x_inner_rest: Vec<F128> = (0..(k_log - K_SKIP)).map(|_| rng.f128()).collect();
        let x_outer: Vec<F128> = (0..n_log).map(|_| rng.f128()).collect();

        // Reference: ring-switch's fold_1b_rows over the materialized
        // suffix tensor, exactly the path open_batch hits today.
        let mut x_outer_full = Vec::with_capacity(x_inner_rest.len() + x_outer.len());
        x_outer_full.extend_from_slice(&x_inner_rest);
        x_outer_full.extend_from_slice(&x_outer);
        let suffix = &x_outer_full[1..];
        let suffix_tensor = build_eq(suffix);
        let want = fold_1b_rows_naive(&packed, &suffix_tensor);

        // New path: lincheck-shaped partial fold of z at x_outer, then a
        // strided fold against the inner-rest tail.
        let eq_x_outer = build_eq(&x_outer);
        let z_vec = partial_fold_packed_z(&z_packed_lincheck, m, k_log, &eq_x_outer);
        let got = s_hat_v_from_z_vec(&z_vec, &x_inner_rest[1..]);

        assert_eq!(got, want, "s_hat_v mismatch at m={m}, k_log={k_log}");
    }
}

/// `prove_batched_padded_with_precomputed` is byte-identical to the
/// no-precompute path when the supplied precomputed `s_hat_v` matches
/// what `fold_1b_rows` would have produced. Exercises every claim being
/// precomputed, the first being precomputed, and the second being
/// precomputed — covers the K=0, K=1 (claim 0 only), K=1 (claim 1 only),
/// and K=2 (no precompute) fold_1b_rows dispatch branches.
#[test]
fn prove_batched_with_precomputed_matches_unprecomputed() {
    let mut rng = Rng::new(0xF00D);
    for &m in &[8usize, 9, 10, 11] {
        let z = rng.bits(1 << m);
        let x_a: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        let x_b: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        let packed = pack_witness(&z, m);

        // Baseline: no precomputes.
        let mut ch_base = FsChallenger::new(b"flock-test");
        let (base, _) = prove_batched(&packed, &[&x_a, &x_b], &mut ch_base);
        let s_hat_v_a = base[0].0.s_hat_v.clone();
        let s_hat_v_b = base[1].0.s_hat_v.clone();

        // Padding spec — dense for tests (matches prove_batched).
        let padding = PaddingSpec::dense(m);

        for &(pre_a, pre_b) in &[
            (false, false), // K=2 path (no precompute)
            (true, false),  // K=1 path: only claim 1 needs fold
            (false, true),  // K=1 path: only claim 0 needs fold
            (true, true),   // K=0 path: both precomputed
        ] {
            let pa: Option<&[F128]> = if pre_a { Some(&s_hat_v_a) } else { None };
            let pb: Option<&[F128]> = if pre_b { Some(&s_hat_v_b) } else { None };
            let mut ch = FsChallenger::new(b"flock-test");
            let (got, _) = prove_batched_padded_with_precomputed(
                &packed,
                &[&x_a, &x_b],
                &[pa, pb],
                &padding,
                &mut ch,
            );
            assert_eq!(
                got[0].0, base[0].0,
                "proof[0] mismatch (pre_a={pre_a}, pre_b={pre_b}, m={m})"
            );
            assert_eq!(
                got[1].0, base[1].0,
                "proof[1] mismatch (pre_a={pre_a}, pre_b={pre_b}, m={m})"
            );
            assert_eq!(got[0].1.sumcheck_claim, base[0].1.sumcheck_claim);
            assert_eq!(got[1].1.sumcheck_claim, base[1].1.sumcheck_claim);
            assert_eq!(
                got[0].1.rs_eq_ind.to_dense(),
                base[0].1.rs_eq_ind.to_dense()
            );
            assert_eq!(
                got[1].1.rs_eq_ind.to_dense(),
                base[1].1.rs_eq_ind.to_dense()
            );
        }
    }
}

/// Degenerate path: when k_log == LOG_PACKING (so x_inner_rest is just
/// the single prefix0 coord), the kernel returns z_vec untouched.
#[test]
fn s_hat_v_from_z_vec_degenerate_tail() {
    let mut rng = Rng::new(0xDEAD);
    let z_vec: Vec<F128> = (0..(1 << LOG_PACKING)).map(|_| rng.f128()).collect();
    let got = s_hat_v_from_z_vec(&z_vec, &[]);
    assert_eq!(got, z_vec);
}

#[test]
#[ignore]
fn zzz_bench_fold_1b() {
    let l = 22; // m = 29
    let pw_len = 1usize << l;
    let mut rng = Rng::new(0x1111);
    let pw: Vec<F128> = (0..pw_len).map(|_| rng.f128()).collect();
    let t0 = build_eq(&(0..l).map(|_| rng.f128()).collect::<Vec<_>>());
    let t1 = build_eq(&(0..l).map(|_| rng.f128()).collect::<Vec<_>>());

    let iters = 20;
    let bench = |f: &dyn Fn()| {
        let t = std::time::Instant::now();
        for _ in 0..iters {
            f();
        }
        t.elapsed().as_secs_f64() * 1e3 / iters as f64
    };
    let t_k4 = bench(&|| {
        std::hint::black_box(fold_1b_rows_1way_mfr(&pw, &t0));
    });
    let t_8 = bench(&|| {
        std::hint::black_box(fold_1b_rows_1way_mfr_8wide_k4(&pw, &t0));
    });
    let t_2k4 = bench(&|| {
        std::hint::black_box(fold_1b_rows_2way_mfr(&pw, &t0, &t1));
    });
    let t_28 = bench(&|| {
        std::hint::black_box(fold_1b_rows_2way_mfr_8wide(&pw, &t0, &t1));
    });
    eprintln!(
        "\n  [fold_1b @ m=29] 1-way: {t_k4:5.2}→{t_8:5.2} ms ({:.2}x) | 2-way: {t_2k4:5.2}→{t_28:5.2} ms ({:.2}x)\n",
        t_k4 / t_8,
        t_2k4 / t_28,
    );
}

/// `subset_sums_4` matches the obvious specification.
#[test]
fn mfr_fold_16wide_2way_matches_scalar() {
    let mut rng = Rng::new(0x161616);
    for &m in &[11usize, 12, 14, 16] {
        let l = m - 7;
        let pw_len = 1usize << l; // divisible by 16 for l >= 4 (m >= 11)
        let pw: Vec<F128> = (0..pw_len).map(|_| rng.f128()).collect();
        let suffix0: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let suffix1: Vec<F128> = (0..l).map(|_| rng.f128()).collect();
        let t0 = build_eq(&suffix0);
        let t1 = build_eq(&suffix1);

        let s0_ref = fold_1b_rows_naive(&pw, &t0);
        let s1_ref = fold_1b_rows_naive(&pw, &t1);
        let dense = PaddingSpec::dense(m);
        let (s0, s1) = fold_1b_rows_2way_mfr_16wide_padded(&pw, &t0, &t1, &dense);
        assert_eq!(s0, s0_ref, "2-way 16wide s0 m={m}");
        assert_eq!(s1, s1_ref, "2-way 16wide s1 m={m}");
    }
}

#[test]
fn subset_sums_4_correctness() {
    let mut rng = Rng::new(0xABCD);
    let elems: [F128; 4] = [rng.f128(), rng.f128(), rng.f128(), rng.f128()];
    let sums = subset_sums_4(elems);
    assert_eq!(sums[0], F128::ZERO);
    for mask in 0..16 {
        let mut expected = F128::ZERO;
        for k in 0..4 {
            if (mask >> k) & 1 == 1 {
                expected += elems[k];
            }
        }
        assert_eq!(sums[mask], expected, "mask={mask:04b}");
    }
}

#[test]
fn fold_b128_elems_matches_naive() {
    let mut rng = Rng::new(0xF00D);
    for &l in &[1usize, 4, 8, 12] {
        let len = 1usize << l;
        let suffix: Vec<F128> = (0..len).map(|_| rng.f128()).collect();
        let eq_r: Vec<F128> = (0..128).map(|_| rng.f128()).collect();
        let a = fold_b128_elems_naive(&suffix, &eq_r);
        let b = fold_b128_elems(&suffix, &eq_r);
        assert_eq!(a, b, "fold_b128_elems mismatch at L={l}");
    }
}

#[test]
fn s_hat_v_is_linear_in_witness() {
    // fold_1b_rows is F_2-linear in packed_witness (additive in the bit-matrix
    // rows). XORing two witnesses XORs their s_hat_v.
    let mut rng = Rng::new(0x42);
    let m = 9;
    let z1 = rng.bits(1 << m);
    let z2 = rng.bits(1 << m);
    let z_xor: Vec<bool> = z1.iter().zip(&z2).map(|(a, b)| a ^ b).collect();
    let x_outer: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
    let suffix_tensor = build_eq(&x_outer[1..]);

    let s1 = fold_1b_rows_naive(&pack_witness(&z1, m), &suffix_tensor);
    let s2 = fold_1b_rows_naive(&pack_witness(&z2, m), &suffix_tensor);
    let sx = fold_1b_rows_naive(&pack_witness(&z_xor, m), &suffix_tensor);

    for (i, ((&a, &b), &c)) in s1.iter().zip(&s2).zip(&sx).enumerate() {
        assert_eq!(a + b, c, "linearity fails at i={i}");
    }
}

// -----------------------------------------------------------------------
// Sparse-tensor fast path: each sparse kernel must produce byte-identical
// output to its dense counterpart for any coord vector that mixes nonzero
// and exactly-zero entries.
// -----------------------------------------------------------------------

/// Build a coord vector with `n_zeros` exact-zero entries at the requested
/// positions and random F128s elsewhere.
fn mk_coords(rng: &mut Rng, n: usize, zero_positions: &[usize]) -> Vec<F128> {
    (0..n)
        .map(|i| {
            if zero_positions.contains(&i) {
                F128::ZERO
            } else {
                rng.f128()
            }
        })
        .collect()
}

#[test]
fn build_eq_sparse_matches_dense() {
    let mut rng = Rng::new(0xCAFE_F00D);
    let cases: &[(usize, &[usize])] = &[
        (1, &[0]),
        (4, &[1, 3]),
        (6, &[0, 1, 2, 3, 4]),
        (8, &[2, 3, 4, 5, 6]),
        (10, &[]),
        (10, &[0, 5, 9]),
    ];
    for &(n_coords, zero_pos) in cases {
        let coords = mk_coords(&mut rng, n_coords, zero_pos);
        let dense = build_eq(&coords);
        let sparse_eq = build_eq_sparse(&coords);
        let materialized = sparse_eq.materialize();

        // Sparse entries match the dense table; dense entries off the
        // sparse support are exactly zero.
        let mut covered = vec![false; dense.len()];
        for &(idx, val) in &materialized {
            assert_eq!(
                val, dense[idx],
                "sparse value mismatch at idx={idx} (n={n_coords}, zeros={zero_pos:?})"
            );
            assert_ne!(
                val,
                F128::ZERO,
                "sparse entry is zero — should have been skipped"
            );
            covered[idx] = true;
        }
        for (i, &c) in covered.iter().enumerate() {
            if !c {
                assert_eq!(
                    dense[i],
                    F128::ZERO,
                    "dense[{i}] nonzero but absent from sparse (n={n_coords}, zeros={zero_pos:?})"
                );
            }
        }
        // Support is in ascending index order.
        for w in materialized.windows(2) {
            assert!(w[0].0 < w[1].0, "support not strictly ascending");
        }
        // Support size = 2^live_count.
        let live_count = n_coords - zero_pos.len();
        assert_eq!(sparse_eq.len(), 1usize << live_count);
    }
}

#[test]
fn fold_1b_rows_sparse_matches_naive() {
    let mut rng = Rng::new(0x5EED_DEAD);
    // m large enough that the suffix has multiple coords, with a few zeros.
    for &m in &[9usize, 11, 13] {
        let l = m - 7;
        let pw_len = 1usize << l;
        let pw: Vec<F128> = (0..pw_len).map(|_| rng.f128()).collect();
        // Suffix length = l. Pin some coords to zero.
        let zero_pos: Vec<usize> = (0..l.min(3)).collect();
        let suffix = mk_coords(&mut rng, l, &zero_pos);

        let dense_tensor = build_eq(&suffix);
        let sparse_eq = build_eq_sparse(&suffix);

        let dense_s = fold_1b_rows_naive(&pw, &dense_tensor);
        let sparse_s = fold_1b_rows_sparse(&pw, &sparse_eq);

        assert_eq!(dense_s, sparse_s, "s_hat_v mismatch at m={m}");
    }
}

#[test]
fn fold_b128_elems_sparse_matches_dense() {
    let mut rng = Rng::new(0xC0DE_BABE);
    for &l in &[4usize, 8, 12] {
        let len = 1usize << l;
        let zero_pos: Vec<usize> = (0..l.min(3)).collect();
        let suffix = mk_coords(&mut rng, l, &zero_pos);
        let dense_tensor = build_eq(&suffix);
        let sparse_eq = build_eq_sparse(&suffix);
        let eq_r: Vec<F128> = (0..128).map(|_| rng.f128()).collect();

        let dense_out = fold_b128_elems(&dense_tensor, &eq_r);
        let sparse_out = fold_b128_elems_sparse(len, &sparse_eq, &eq_r);

        assert_eq!(dense_out, sparse_out, "rs_eq_ind mismatch at L={l}");
    }
}

/// `prove_batched` with a mix of sparse and dense claims must produce
/// byte-identical output to calling `prove` per claim (which uses only
/// the dense kernels).
#[test]
fn prove_batched_with_sparse_claim_matches_sequential() {
    let mut rng = Rng::new(0xBEEF_CAFE);
    for &m in &[10usize, 11, 12] {
        let z = rng.bits(1 << m);
        let packed = pack_witness(&z, m);
        // x has length m-6. Suffix is x[1..], length m-7. Zero out the
        // last 3 suffix coords to trip the sparse threshold.
        let mut x_chain: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        for j in 0..3 {
            x_chain[(m - 6) - 1 - j] = F128::ZERO;
        }
        let x_ab: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        let x_c: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();

        // Sequential reference (dense path only).
        let mut ch_seq = FsChallenger::new(b"flock-test-sparse");
        let (p_ab, o_ab) = prove(&packed, &x_ab, &mut ch_seq);
        let (p_c, o_c) = prove(&packed, &x_c, &mut ch_seq);
        let (p_chain, o_chain) = prove(&packed, &x_chain, &mut ch_seq);

        // Batched (sparse chain claim is routed through sparse kernels).
        // rs_eq_ind values have γ baked in, so don't byte-compare to
        // sequential `prove` output. Check s_hat_v (transcript-aligned)
        // and routing (Sparse vs Dense) instead.
        let mut ch_batch = FsChallenger::new(b"flock-test-sparse");
        let (results, _) = prove_batched(&packed, &[&x_ab, &x_c, &x_chain], &mut ch_batch);

        assert_eq!(results[0].0, p_ab, "s_hat_v[ab] mismatch at m={m}");
        assert_eq!(results[1].0, p_c, "s_hat_v[c]  mismatch at m={m}");
        assert_eq!(results[2].0, p_chain, "s_hat_v[chain] mismatch at m={m}");
        assert!(
            matches!(results[2].1.rs_eq_ind, RsEqInd::Sparse { .. }),
            "chain claim should be sparse"
        );
        // Dense routing = either the materialized `Dense` (non-split l) or
        // the fused `DeferredDense` (split l, l % 16 == 0).
        assert!(
            matches!(
                results[0].1.rs_eq_ind,
                RsEqInd::Dense(_) | RsEqInd::DeferredDense { .. }
            ),
            "ab claim should be dense"
        );
        assert!(
            matches!(
                results[1].1.rs_eq_ind,
                RsEqInd::Dense(_) | RsEqInd::DeferredDense { .. }
            ),
            "c claim should be dense"
        );
        assert_eq!(results[0].1.sumcheck_claim, o_ab.sumcheck_claim);
        assert_eq!(results[1].1.sumcheck_claim, o_c.sumcheck_claim);
        assert_eq!(results[2].1.sumcheck_claim, o_chain.sumcheck_claim);
        // Used to suppress unused warnings from sequential oracle.
        let _ = (&o_ab.rs_eq_ind, &o_c.rs_eq_ind, &o_chain.rs_eq_ind);
    }
}

/// Cross-check `eval_rs_eq` against the dense `mle_eval(fold_b128_elems(build_eq(z_vals)), query)`
/// path at several `ℓ' = |z_vals|` values. The two must agree bit-for-bit.
#[test]
fn eval_rs_eq_matches_dense() {
    fn mle_eval_naive(values: &[F128], r: &[F128]) -> F128 {
        assert_eq!(values.len(), 1 << r.len());
        let mut buf = values.to_vec();
        for &r_i in r.iter().rev() {
            let half = buf.len() / 2;
            for i in 0..half {
                let lo = buf[i];
                let hi = buf[i + half];
                buf[i] = lo + r_i * (lo + hi);
            }
            buf.truncate(half);
        }
        buf[0]
    }

    let mut rng = Rng::new(0xDEADBEEF);
    for &l_prime in &[3usize, 6, 10, 14] {
        for _trial in 0..3 {
            let z_vals: Vec<F128> = (0..l_prime).map(|_| rng.f128()).collect();
            let query: Vec<F128> = (0..l_prime).map(|_| rng.f128()).collect();
            let r_dprime: Vec<F128> = (0..LOG_PACKING).map(|_| rng.f128()).collect();
            let eq_r_dprime = build_eq(&r_dprime);

            // Dense path: build_eq(z_vals) → fold_b128_elems → mle_eval at query.
            let suffix_tensor = build_eq(&z_vals);
            let rs_eq_ind_dense = fold_b128_elems(&suffix_tensor, &eq_r_dprime);
            let dense_eval = mle_eval_naive(&rs_eq_ind_dense, &query);

            // Succinct path.
            let succinct_eval = eval_rs_eq(&z_vals, &query, &eq_r_dprime);

            assert_eq!(
                succinct_eval, dense_eval,
                "eval_rs_eq mismatch at l_prime={l_prime}"
            );
        }
    }
}

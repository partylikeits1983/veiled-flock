//! Integration tests for the chain layer: the region folds, the shift MLE,
//! the chain round trip and its rejection paths, and the extended-claim
//! (`|S| > 0`) variants.

use flock_core::challenger::RandomChallenger;
use flock_core::field::F128;
use flock_core::lincheck::build_eq_table;
use flock_core::zerocheck::multilinear::eq_eval;
use flock_prover::chain::*;
use flock_prover::r1cs_hashes::chain_common::ChainLayout;

/// Inner product `Σ eq[i]·vals[i]` — used to spot-check claims in tests.
fn dot(eq: &[F128], vals: &[F128]) -> F128 {
    debug_assert_eq!(eq.len(), vals.len());
    let mut acc = F128::ZERO;
    for i in 0..eq.len() {
        acc += eq[i] * vals[i];
    }
    acc
}

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
/// Build an LSB-first boolean point as F128 (0/1) of length `n` from index.
fn bool_point(idx: usize, n: usize) -> Vec<F128> {
    (0..n)
        .map(|j| {
            if (idx >> j) & 1 == 1 {
                F128::ONE
            } else {
                F128::ZERO
            }
        })
        .collect()
}

/// Pack a bool witness the way `pcs::pack` does (bit i_skip of out[i_rest] =
/// z[i_rest·128 + i_skip]).
fn pack(z: &[bool]) -> Vec<F128> {
    assert!(z.len().is_multiple_of(128));
    (0..z.len() / 128)
        .map(|i_rest| {
            let base = i_rest * 128;
            let mut lo = 0u64;
            let mut hi = 0u64;
            for r in 0..64 {
                if z[base + r] {
                    lo |= 1 << r;
                }
                if z[base + 64 + r] {
                    hi |= 1 << r;
                }
            }
            F128 { lo, hi }
        })
        .collect()
}

/// `fold_region_naive` reads the right bits and weights them: compare its
/// output against a direct fold over the bool witness.
#[test]
fn fold_region_naive_matches_direct() {
    let mut rng = Rng::new(0xF01D);
    // k_log = 5 (block = 32 bits), n = 3 (8 instances) → m = 8, 256 bits.
    let k_log = 5usize;
    let n = 3usize;
    let block = 1usize << k_log;
    let total = (1usize << n) * block;
    let z: Vec<bool> = (0..total).map(|_| rng.next_u64() & 1 == 1).collect();
    let packed = pack(&z);

    // Random taps: 10 region bits at distinct in-block positions, random w.
    let taps: Vec<(usize, F128)> = (0..10).map(|t| (3 * t % block, rng.f128())).collect();

    let got = fold_region_naive(&packed, k_log, &taps);
    assert_eq!(got.len(), 1 << n);
    for i in 0..(1 << n) {
        let mut want = F128::ZERO;
        for &(pos, w) in &taps {
            if z[i * block + pos] {
                want += w;
            }
        }
        assert_eq!(got[i], want, "instance {i}");
    }
}

/// `fold_contiguous_regions` (fused multi-region pass) matches calling
/// `fold_region_naive` once per region. Exercises 1, 2, and 3 regions.
#[test]
fn fold_contiguous_regions_matches_per_region() {
    let mut rng = Rng::new(0xC0DE_F00D);
    let k_log = 6usize; // block = 64 bits = 8 bytes
    let n = 4usize; // 16 instances
    let block = 1usize << k_log;
    let total = (1usize << n) * block;
    let z: Vec<bool> = (0..total).map(|_| rng.next_u64() & 1 == 1).collect();
    let packed = pack(&z);

    // Region: 16 contiguous bits = 2 bytes, with random weights.
    let region_bits = 16;
    let weights: Vec<F128> = (0..region_bits).map(|_| rng.f128()).collect();

    // Test with N regions at distinct byte-aligned offsets.
    for &offs in &[&[0usize] as &[usize], &[0, 2], &[0, 2, 4]] {
        let got = fold_contiguous_regions(&packed, k_log, offs, &weights);
        assert_eq!(got.len(), offs.len());
        for (r_idx, &off) in offs.iter().enumerate() {
            let taps: Vec<(usize, F128)> = (0..region_bits)
                .map(|p| (off * 8 + p, weights[p]))
                .collect();
            let want = fold_region_naive(&packed, k_log, &taps);
            assert_eq!(got[r_idx], want, "region {r_idx} (offset {off})");
        }
    }
}

/// `shift_mle` on boolean inputs is exactly the successor indicator.
#[test]
fn shift_mle_boolean_is_successor() {
    for n in 1..=6 {
        let n_total = 1usize << n;
        for a in 0..n_total {
            for b in 0..n_total {
                let av = bool_point(a, n);
                let bv = bool_point(b, n);
                let got = shift_mle(&av, &bv);
                let want = if b == a + 1 { F128::ONE } else { F128::ZERO };
                assert_eq!(got, want, "shift({a},{b}) n={n}");
            }
        }
    }
}

/// `shift(1ⁿ, ·) = 0` (no successor in range).
#[test]
fn shift_mle_top_has_no_successor() {
    let mut rng = Rng::new(7);
    for n in 1..=5 {
        let a = bool_point((1 << n) - 1, n);
        let b = rng.f128_vec(n);
        assert_eq!(shift_mle(&a, &b), F128::ZERO);
    }
}

/// `shift(τ, y) = eq(τ, y−1)` for boolean `y ≥ 1` and field `τ`.
#[test]
fn shift_equals_shifted_eq() {
    let mut rng = Rng::new(11);
    for n in 1..=5 {
        let n_total = 1usize << n;
        let tau = rng.f128_vec(n);
        let eqtau = build_eq_table(&tau);
        for y in 0..n_total {
            let yv = bool_point(y, n);
            let got = shift_mle(&tau, &yv);
            let want = if y == 0 { F128::ZERO } else { eqtau[y - 1] };
            assert_eq!(got, want, "y={y} n={n}");
        }
    }
}

/// Honest chained data: `In[i]=x_i`, `Out[i]=x_{i+1}`. Prove + verify must
/// accept, and the single returned claim must be the true merged MLE
/// `g(τ',s₀*) = (1+s₀*)·In(τ') + s₀*·Out(τ')` (what the PCS would enforce).
#[test]
fn honest_roundtrip_accepts() {
    for n in 3..=8 {
        let n_total = 1usize << n;
        let mut rng = Rng::new(100 + n as u64);
        // x_0 .. x_N  (N+1 chain values); In[i]=x_i, Out[i]=x_{i+1}.
        let chain: Vec<F128> = rng.f128_vec(n_total + 1);
        let in_vals: Vec<F128> = chain[..n_total].to_vec();
        let out_vals: Vec<F128> = chain[1..].to_vec();
        let x0_r = chain[0];
        let xlast_r = chain[n_total];

        let mut chp = RandomChallenger::new(42);
        let (proof, _claims) = prove_chain_shift(&in_vals, &out_vals, &mut chp);

        let mut chv = RandomChallenger::new(42);
        let claims = verify_chain_shift(&proof, x0_r, xlast_r, n, &mut chv)
            .expect("honest proof should verify");

        let eq_taup = build_eq_table(&claims.instance_point);
        let in_true = dot(&eq_taup, &in_vals);
        let out_true = dot(&eq_taup, &out_vals);
        let g_true = (F128::ONE + claims.sel0) * in_true + claims.sel0 * out_true;
        assert_eq!(claims.value, g_true, "merged claim n={n}");
    }
}

/// Breaking the chain at one index makes the sumcheck reject.
#[test]
fn broken_chain_rejects() {
    let n = 6;
    let n_total = 1usize << n;
    let mut rng = Rng::new(2024);
    let chain: Vec<F128> = rng.f128_vec(n_total + 1);
    let in_vals: Vec<F128> = chain[..n_total].to_vec();
    let mut out_vals: Vec<F128> = chain[1..].to_vec();
    let x0_r = chain[0];
    let xlast_r = chain[n_total];

    // Break the glue: Out[3] no longer equals In[4].
    out_vals[3] += F128::ONE;

    let mut chp = RandomChallenger::new(9);
    let (proof, _claims) = prove_chain_shift(&in_vals, &out_vals, &mut chp);
    let mut chv = RandomChallenger::new(9);
    let res = verify_chain_shift(&proof, x0_r, xlast_r, n, &mut chv);
    assert_eq!(res, Err(ChainError::SumcheckFinal));
}

/// A wrong public input endpoint is caught. It is batched (via α) into the
/// single claim, so the failure surfaces as a final-sumcheck mismatch.
#[test]
fn wrong_input_endpoint_rejects() {
    let n = 5;
    let n_total = 1usize << n;
    let mut rng = Rng::new(555);
    let chain: Vec<F128> = rng.f128_vec(n_total + 1);
    let in_vals: Vec<F128> = chain[..n_total].to_vec();
    let out_vals: Vec<F128> = chain[1..].to_vec();
    let xlast_r = chain[n_total];
    let wrong_x0 = chain[0] + F128::ONE;

    let mut chp = RandomChallenger::new(3);
    let (proof, _claims) = prove_chain_shift(&in_vals, &out_vals, &mut chp);
    let mut chv = RandomChallenger::new(3);
    let res = verify_chain_shift(&proof, wrong_x0, xlast_r, n, &mut chv);
    assert_eq!(res, Err(ChainError::SumcheckFinal));
}

/// A wrong public output endpoint is caught.
#[test]
fn wrong_output_endpoint_rejects() {
    let n = 5;
    let n_total = 1usize << n;
    let mut rng = Rng::new(777);
    let chain: Vec<F128> = rng.f128_vec(n_total + 1);
    let in_vals: Vec<F128> = chain[..n_total].to_vec();
    let out_vals: Vec<F128> = chain[1..].to_vec();
    let x0_r = chain[0];
    let wrong_xlast = chain[n_total] + F128::ONE;

    let mut chp = RandomChallenger::new(1);
    let (proof, _claims) = prove_chain_shift(&in_vals, &out_vals, &mut chp);
    let mut chv = RandomChallenger::new(1);
    let res = verify_chain_shift(&proof, x0_r, wrong_xlast, n, &mut chv);
    assert_eq!(res, Err(ChainError::SumcheckFinal));
}

// -- Extended shift sumcheck (Part 7b) ----------------------------------

/// At `S = ∅` the extension IS the base argument: identical transcript,
/// rounds, and claims.
#[test]
fn ext_at_empty_s_matches_base() {
    let n = 3;
    let n_total = 1usize << n;
    let mut rng = Rng::new(0xE47);
    let chain_vals = rng.f128_vec(n_total + 1);
    let in_vals = chain_vals[..n_total].to_vec();
    let out_vals = chain_vals[1..].to_vec();

    let mut chp = RandomChallenger::new(7);
    let (base_proof, base_claims) = prove_chain_shift(&in_vals, &out_vals, &mut chp);
    let mut chp = RandomChallenger::new(7);
    let tables = vec![(in_vals, out_vals)];
    let (ext_proof, ext_claims) = prove_chain_shift_ext(&tables, &mut chp);

    assert_eq!(ext_proof.rounds, base_proof.rounds);
    assert_eq!(ext_proof.g_at_point, base_proof.g_at_point);
    assert_eq!(ext_claims.instance_point, base_claims.instance_point);
    assert_eq!(ext_claims.sel0, base_claims.sel0);
    assert!(ext_claims.s_high.is_empty());
    assert_eq!(ext_claims.value, base_claims.value);
}

/// Synthetic geometry for the |S| = 2 tests: k_log = 10, region_log = 7,
/// high_zeros = 2, S = {0, 1}, mask pair at index 3, n_log = 2, RowMajor.
fn ext_fixture() -> (ChainLayout, Vec<F128>, F128, F128) {
    let layout = ChainLayout {
        k_log: 10,
        k_skip: 0,
        region_log: 7,
        region_bits: 128,
        input_byte_off: 0,
        output_byte_off: 16,
    };
    let mut rng = Rng::new(0x5C4B);
    let mut packed = rng.f128_vec(32);
    // Honest chain on pair 0: out word of instance y = in word of y + 1.
    // RowMajor word address = instance * 8 + word; in = word 0, out = word 1.
    for y in 0..3usize {
        packed[y * 8 + 1] = packed[(y + 1) * 8];
    }
    let x0_r = packed[0]; // in word of instance 0 (tau_pos fold = identity)
    let xlast_r = packed[3 * 8 + 1]; // out word of instance 3
    (layout, packed, x0_r, xlast_r)
}

/// |S| = 2 round-trip with two oracles: V equals the subcube combination of the
/// folded tables, and V equals the packed witness's MLE at the assembled point.
#[test]
fn ext_roundtrip_matches_mle_oracle() {
    let (layout, packed, x0_r, xlast_r) = ext_fixture();
    let s_coords = [0usize, 1];
    let fold = flock_prover::r1cs_hashes::chain_common::ChainFold::new(&layout, Vec::new());
    let tables = flock_prover::r1cs_hashes::chain_common::fold_in_out_subcube(
        &layout,
        flock_core::r1cs::WitnessLayout::RowMajor,
        &packed,
        &fold,
        &s_coords,
    );
    assert_eq!(tables.len(), 4);

    let mut chp = RandomChallenger::new(11);
    let (proof, claims) = prove_chain_shift_ext(&tables, &mut chp);
    let mut chv = RandomChallenger::new(11);
    let vclaims = verify_chain_shift_ext(&proof, x0_r, xlast_r, 2, 2, &mut chv)
        .expect("honest extended chain verifies");
    assert_eq!(vclaims, claims);

    // Oracle (a): V = sum_t eq(h*, t) * [(1+s0)*In_t(tau') + s0*Out_t(tau')].
    let taup = &claims.instance_point;
    let mle = |vals: &[F128]| -> F128 {
        (0..vals.len())
            .map(|y| eq_eval(taup, &bool_point(y, taup.len())) * vals[y])
            .fold(F128::ZERO, |a, b| a + b)
    };
    let mut expected = F128::ZERO;
    for (t, (in_vals, out_vals)) in tables.iter().enumerate() {
        let eq_h = eq_eval(&claims.s_high, &bool_point(t, 2));
        expected += eq_h * ((F128::ONE + claims.sel0) * mle(in_vals) + claims.sel0 * mle(out_vals));
    }
    assert_eq!(claims.value, expected, "subcube oracle");

    // Oracle (b): V = MLE of the packed witness at the assembled point.
    let point = flock_prover::r1cs_hashes::chain_common::build_chain_claim_point_ext(
        &layout,
        flock_core::r1cs::WitnessLayout::RowMajor,
        &fold,
        &claims,
        &s_coords,
    );
    assert_eq!(point.len(), 5);
    let mut eval = F128::ZERO;
    for (w, &z) in packed.iter().enumerate() {
        eval += eq_eval(&point, &bool_point(w, 5)) * z;
    }
    assert_eq!(claims.value, eval, "packed-MLE oracle");
}

/// The mask pair is genuinely inside the claim: zeroing its words
/// changes V under the same challenge schedule.
#[test]
fn ext_claim_includes_mask_pair() {
    let (layout, packed, _x0, _xl) = ext_fixture();
    let s_coords = [0usize, 1];
    let fold = flock_prover::r1cs_hashes::chain_common::ChainFold::new(&layout, Vec::new());
    let run = |packed: &[F128]| -> F128 {
        let tables = flock_prover::r1cs_hashes::chain_common::fold_in_out_subcube(
            &layout,
            flock_core::r1cs::WitnessLayout::RowMajor,
            packed,
            &fold,
            &s_coords,
        );
        let mut chp = RandomChallenger::new(13);
        prove_chain_shift_ext(&tables, &mut chp).1.value
    };
    let v_full = run(&packed);
    let mut zeroed = packed.clone();
    for inst in 0..4 {
        zeroed[inst * 8 + 6] = F128::ZERO; // mask pair = pair 3 = words 6, 7
        zeroed[inst * 8 + 7] = F128::ZERO;
    }
    assert_ne!(v_full, run(&zeroed), "mask pair must contribute to V");
}

/// The assembled point matches a hand-built one: h* values land at the
/// S positions of the high slot-address coords.
#[test]
fn ext_point_matches_hand_built() {
    let (layout, _packed, _x0, _xl) = ext_fixture();
    let s_coords = [0usize, 1];
    let fold = flock_prover::r1cs_hashes::chain_common::ChainFold::new(&layout, Vec::new());
    let mut rng = Rng::new(0x901);
    let claims = ChainClaimsExt {
        instance_point: rng.f128_vec(2),
        sel0: rng.f128(),
        s_high: rng.f128_vec(2),
        value: rng.f128(),
    };
    let point = flock_prover::r1cs_hashes::chain_common::build_chain_claim_point_ext(
        &layout,
        flock_core::r1cs::WitnessLayout::RowMajor,
        &fold,
        &claims,
        &s_coords,
    );
    // RowMajor, tau_pos empty: [sel0, high0 = h*_0, high1 = h*_1, inst...].
    let hand_built = vec![
        claims.sel0,
        claims.s_high[0],
        claims.s_high[1],
        claims.instance_point[0],
        claims.instance_point[1],
    ];
    assert_eq!(point, hand_built);

    // BatchMajor: instance coords lead: [inst..., sel0, h*_0, h*_1].
    let point_bm = flock_prover::r1cs_hashes::chain_common::build_chain_claim_point_ext(
        &layout,
        flock_core::r1cs::WitnessLayout::BatchMajor,
        &fold,
        &claims,
        &s_coords,
    );
    let hand_built_bm = vec![
        claims.instance_point[0],
        claims.instance_point[1],
        claims.sel0,
        claims.s_high[0],
        claims.s_high[1],
    ];
    assert_eq!(point_bm, hand_built_bm);
}

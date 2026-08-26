use super::*;
use crate::zerocheck::univariate_skip::pack_bits;
use crate::{
    challenger::{FsChallenger, RandomChallenger},
    ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8},
};

mod helpers;

use helpers::{Rng, RngMask, ScriptedEqChallenger};

const TEST_DOMAIN: &[u8] = b"flock-zerocheck-test-v0";
const ZK_TEST_DOMAIN: &[u8] = b"flock-zerocheck-zk-test-v0";
const ORDERING_TEST_DOMAIN: &[u8] = b"flock-zerocheck-ordering-test-v0";

#[test]
fn equality_point_rejects_noninvertible_outer_coordinates() {
    let mut challenger = ScriptedEqChallenger { vector_calls: 0 };
    let point = sample_eq_point(K_SKIP + N_INNER + 1, &mut challenger);
    assert_eq!(challenger.vector_calls, 3);
    assert_eq!(point.last(), Some(&F128::new(2, 0)));
    assert!(point[K_SKIP..].iter().all(|value| *value != F128::ONE));
}

#[test]
fn shared_round_weights_match_quadratic_reconstruction() {
    let running = F128::new(3, 5);
    let msg_1 = F128::new(7, 11);
    let msg_inf = F128::new(13, 17);
    let r_eq = F128::new(19, 23);
    let rho = F128::new(29, 31);
    let g0 = (running + r_eq * msg_1) * (F128::ONE + r_eq).inv();
    let expected = g0 * (F128::ONE + rho) + msg_1 * rho + msg_inf * rho * (F128::ONE + rho);
    assert_eq!(
        fold_sumcheck_round(running, msg_1, msg_inf, r_eq, rho),
        Some(expected)
    );
    assert_eq!(sumcheck_round_weights(F128::ONE, rho), None);
}

// Pack three Boolean vectors into the (a_packed, b_packed, c_packed)
// shape that `prove_packed` consumes.
fn pack_abc(a: &[bool], b: &[bool], c: &[bool]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    (pack_bits(a), pack_bits(b), pack_bits(c))
}

// An honest proof verifies, and the verifier returns the prover's claim.
#[test]
fn prove_verify_roundtrip_honest() {
    for &m in &[13usize, 14, 15, 16] {
        let mut rng = Rng::new(1000 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(TEST_DOMAIN);
        let (proof, claim_p) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        let mut ch_verify = FsChallenger::new(TEST_DOMAIN);
        let result = verify(m, &proof, &mut ch_verify);
        let claim_v = result.unwrap_or_else(|e| panic!("verify rejected at m={m}: {e:?}"));

        assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");
    }
}

// An honest combined masked proof verifies at each supported size.
#[test]
fn prove_verify_zk_roundtrip_honest() {
    for &m in &[13usize, 14, 15, 16] {
        let mut rng = Rng::new(2000 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let p_small = rng.field_mask(m);
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = FsChallenger::new(ZK_TEST_DOMAIN);
        let (proof, claim_p) = prove_packed_padded_zk(
            &a_p,
            &b_p,
            &c_p,
            &p_small,
            m,
            &PaddingSpec::dense(m),
            &mut ch_prove,
        );

        let mut ch_verify = FsChallenger::new(ZK_TEST_DOMAIN);
        let claim_v = verify_zk(m, &proof, &mut ch_verify)
            .unwrap_or_else(|e| panic!("verify_zk rejected honest proof at m={m}: {e:?}"));
        assert_eq!(claim_p, claim_v, "zk claim mismatch at m={m}");
    }
}

// Exercise zero, diagonal, and full round-1 masks independently.
#[test]
fn prove_verify_zk_round1_mask_roundtrip() {
    for &m in &[13usize, 14] {
        for stage in ["zero", "diagonal", "full"] {
            let mut rng = Rng::new(3000 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
            let p_small = rng.field_mask(m);
            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

            let zeros = vec![false; 1 << m];
            let sc_bits = if stage == "zero" {
                zeros.clone()
            } else {
                rng.bits(1 << m)
            };
            let sh_bits = if stage == "full" {
                rng.bits(1 << m)
            } else {
                zeros.clone()
            };
            let (sc_p, sh_p, _) = pack_abc(&sc_bits, &sh_bits, &zeros);

            let mut ch_prove = FsChallenger::new(ZK_TEST_DOMAIN);
            let (proof, claim_p, mt) = prove_packed_padded_zk_masked(
                &a_p,
                &b_p,
                &c_p,
                &p_small,
                m,
                &PaddingSpec::dense(m),
                Some(Round1Mask {
                    s_c_packed: &sc_p,
                    s_h_packed: &sh_p,
                }),
                &mut ch_prove,
            );
            let mt = mt.expect("mask transcript");

            let mut ch_verify = FsChallenger::new(ZK_TEST_DOMAIN);
            let claim_v =
                verify_zk_masked(m, &proof, Some((mt.mc_at_z, mt.h_at_z)), &mut ch_verify)
                    .unwrap_or_else(|e| panic!("stage={stage}, m={m}: {e:?}"));
            assert_eq!(claim_p, claim_v, "stage={stage}, m={m}");

            // A zero mask must return the unmasked c claim.
            let mut ch_ref = FsChallenger::new(ZK_TEST_DOMAIN);
            let (_, claim_ref) = prove_packed_padded_zk(
                &a_p,
                &b_p,
                &c_p,
                &p_small,
                m,
                &PaddingSpec::dense(m),
                &mut ch_ref,
            );
            if stage == "zero" {
                assert_eq!(claim_ref, claim_v, "m={m}");
            }
        }
    }
}

// The round-1 mask construction requires the C-side output to depend only on C.
#[test]
fn round1_c_output_is_independent_of_ab() {
    let m = 13usize;
    let k_skip = K_SKIP;
    let mut rng = Rng::new(24601);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let cc = rng.bits(1 << m);
    let zeros = vec![false; 1 << m];
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &cc);
    let (z_p, _, _) = pack_abc(&zeros, &zeros, &zeros);
    let r: Vec<F128> = (0..m)
        .map(|_| F128::new(rng.next_u64(), rng.next_u64()))
        .collect();
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let pad = PaddingSpec::dense(m);
    let (_, c_with_ab) = round1_shift_reduce_extract_c_packed_padded(
        &a_p, &b_p, &c_p, m, k_skip, &r, &inv_table, &pad,
    );
    let (_, c_without_ab) = round1_shift_reduce_extract_c_packed_padded(
        &z_p, &z_p, &c_p, m, k_skip, &r, &inv_table, &pad,
    );
    assert_eq!(c_with_ab, c_without_ab);
}

// Reject mutations to every masked-proof component.
#[test]
fn verify_zk_rejects_mutations() {
    let m = 14;
    let mut rng = Rng::new(7070);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let p_small = rng.field_mask(m);
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(ZK_TEST_DOMAIN);
    let (proof, _) = prove_packed_padded_zk(
        &a_p,
        &b_p,
        &c_p,
        &p_small,
        m,
        &PaddingSpec::dense(m),
        &mut ch_prove,
    );

    let bump = F128 { lo: 0xABCD, hi: 0 };
    let mutate = |f: &dyn Fn(&mut ZkZerocheckProof)| {
        let mut bad = proof.clone();
        f(&mut bad);
        let mut ch = FsChallenger::new(ZK_TEST_DOMAIN);
        assert!(verify_zk(m, &bad, &mut ch).is_err());
    };
    mutate(&|pr| pr.mask_init += bump);
    mutate(&|pr| pr.final_p_eval += bump);
    for i in 0..proof.multilinear_rounds.len() {
        mutate(&|pr| pr.multilinear_rounds[i].0 += bump);
        mutate(&|pr| pr.multilinear_rounds[i].1 += bump);
    }
    mutate(&|pr| pr.final_a_eval += bump);
    for k in [0usize, 1, 31, 63] {
        mutate(&|pr| pr.round1_ab[k] += bump);
        mutate(&|pr| pr.round1_c[k] += bump);
    }
    mutate(&|pr| pr.final_b_eval += bump);
    mutate(&|pr| pr.final_c_eval += bump);
    mutate(&|pr| {
        pr.multilinear_rounds.pop();
    });
    mutate(&|pr| {
        pr.round1_ab.pop();
    });
    mutate(&|pr| {
        pr.round1_c.truncate(1);
    });
}

// A masked proof must not make an invalid witness acceptable.
#[test]
fn zk_invalid_witness_rejected() {
    for &m in &[13usize, 14, 15] {
        let mut rng = Rng::new(0x1A50_0000 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        c[3] = !c[3];
        let p_small = rng.field_mask(m);
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = FsChallenger::new(ZK_TEST_DOMAIN);
        let (proof, _) = prove_packed_padded_zk(
            &a_p,
            &b_p,
            &c_p,
            &p_small,
            m,
            &PaddingSpec::dense(m),
            &mut ch_prove,
        );
        let mut ch_verify = FsChallenger::new(ZK_TEST_DOMAIN);
        let res = verify_zk(m, &proof, &mut ch_verify);
        assert!(res.is_err(), "m={m}");
    }
}

// Replay verify_zk's final residual with an overridden mask_init.
#[cfg(test)]
fn zk_final_residual(m: usize, proof: &ZkZerocheckProof, seed: u64, mask_init: F128) -> F128 {
    let k_skip = K_SKIP;
    let mut ch = RandomChallenger::new(seed);
    let r = sample_eq_point(m, &mut ch);
    let z = ch.sample_f128();

    let combined_at_lambda: Vec<F128> = proof
        .round1_ab
        .iter()
        .zip(&proof.round1_c)
        .map(|(x, y)| *x + *y)
        .collect();
    let combined_at_z = interpolate_at_z_combined(&combined_at_lambda, k_skip, z);
    let p_c_at_z = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
    let ab_init = combined_at_z + p_c_at_z;
    let gamma = ch.sample_f128();
    let mut c_running = ab_init + gamma * mask_init;
    let mut mlv_rhos = Vec::with_capacity(proof.multilinear_rounds.len());
    for (i, &(g1, g_inf)) in proof.multilinear_rounds.iter().enumerate() {
        let r_eq = r[k_skip + i];
        let rho = ch.sample_f128();
        mlv_rhos.push(rho);
        c_running = fold_sumcheck_round(c_running, g1, g_inf, r_eq, rho)
            .expect("sample_eq_point excludes r_eq = 1");
    }
    let expected = proof.final_a_eval * proof.final_b_eval
        + gamma * proof.final_p_eval * SmallMaskSpec::default().q_star_at(&mlv_rhos);
    c_running + expected
}

// Show that choosing σ_z after γ permits a unique cancellation, while
// Fiat--Shamir ordering rejects that cancellation except with probability 2^-128.
#[test]
fn zk_gamma_cancellation_unique_and_fs_ordering() {
    let m = 14;
    let seed = 0x6A77A_5EED;
    let mut rng = Rng::new(0xBAD_C0DE);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    c[7] = !c[7]; // invalid witness: nonzero zerocheck defect δ
    let p_small = rng.field_mask(m);
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

    // Prove under the fixed (observation-independent) challenge tuple.
    let mut ch_prove = RandomChallenger::new(seed);
    let (proof, _) = prove_packed_padded_zk(
        &a_p,
        &b_p,
        &c_p,
        &p_small,
        m,
        &PaddingSpec::dense(m),
        &mut ch_prove,
    );

    let mut ch = RandomChallenger::new(seed);
    assert!(verify_zk(m, &proof, &mut ch).is_err());

    // The residual is affine in σ_z; solve for the unique root σ*.
    let r0 = zk_final_residual(m, &proof, seed, proof.mask_init);
    let r1 = zk_final_residual(m, &proof, seed, proof.mask_init + F128::ONE);
    let slope = r0 + r1; // affine over char 2: R(x+1) + R(x) = slope
    assert_ne!(r0, F128::ZERO);
    assert_ne!(slope, F128::ZERO);
    let sigma_star = proof.mask_init + r0 * slope.inv();
    assert_eq!(zk_final_residual(m, &proof, seed, sigma_star), F128::ZERO);
    // Uniqueness: affine with nonzero slope ⇒ any other σ has nonzero
    // residual; spot-check a few.
    for k in 1..8u64 {
        let other = sigma_star
            + F128 {
                lo: k,
                hi: k.wrapping_mul(0x9E37),
            };
        assert_ne!(zk_final_residual(m, &proof, seed, other), F128::ZERO);
    }

    // With γ known in advance, the patched proof is accepted.
    let mut cheat = proof.clone();
    cheat.mask_init = sigma_star;
    let mut ch = RandomChallenger::new(seed);
    assert!(verify_zk(m, &cheat, &mut ch).is_ok());

    // Under Fiat–Shamir the same proof is rejected: γ is derived
    // after σ_z is absorbed, so the solved-for γ never occurs.
    let mut ch_fs = FsChallenger::new(ORDERING_TEST_DOMAIN);
    assert!(verify_zk(m, &cheat, &mut ch_fs).is_err());
}

// Reject mutations to every unmasked-proof component.
#[test]
fn verify_rejects_mutations() {
    let m = 14;
    let mut rng = Rng::new(5050);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(TEST_DOMAIN);
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    let bump = F128::ONE;
    let mutate = |f: &dyn Fn(&mut ZerocheckProof)| {
        let mut bad = proof.clone();
        f(&mut bad);
        let mut ch = FsChallenger::new(TEST_DOMAIN);
        assert!(verify(m, &bad, &mut ch).is_err());
    };
    mutate(&|pr| pr.round1_ab[0] += bump);
    mutate(&|pr| pr.round1_c[0] += bump);
    for i in 0..proof.multilinear_rounds.len() {
        mutate(&|pr| pr.multilinear_rounds[i].0 += bump);
        mutate(&|pr| pr.multilinear_rounds[i].1 += bump);
    }
    mutate(&|pr| pr.final_a_eval += bump);
    mutate(&|pr| pr.final_b_eval += bump);
    mutate(&|pr| pr.final_c_eval += bump);
}

// Reject malformed proof shapes before verification.
#[test]
fn verify_rejects_shape_errors() {
    let m = 14;
    let mut rng = Rng::new(606);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(TEST_DOMAIN);
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    // Truncate round1_ab.
    let mut bad = proof.clone();
    bad.round1_ab.pop();
    let mut ch = FsChallenger::new(TEST_DOMAIN);
    assert!(matches!(
        verify(m, &bad, &mut ch),
        Err(VerifyError::BadRound1Length { .. })
    ));

    // Truncate multilinear rounds.
    let mut bad = proof.clone();
    bad.multilinear_rounds.pop();
    let mut ch = FsChallenger::new(TEST_DOMAIN);
    assert!(matches!(
        verify(m, &bad, &mut ch),
        Err(VerifyError::BadMultilinearRoundsLength { .. })
    ));

    // log_n too small.
    let mut ch = FsChallenger::new(TEST_DOMAIN);
    assert!(matches!(
        verify(K_SKIP + 6, &proof, &mut ch),
        Err(VerifyError::LogNTooSmall { .. })
    ));
}

// Reject a false statement produced through the honest prover path.
#[test]
fn false_statement_rejected() {
    for &m in &[13usize, 14, 15] {
        let mut rng = Rng::new(7777 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        // Correct c, then corrupt one bit so a * b + c != 0 somewhere.
        let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        c[3] = !c[3];

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(TEST_DOMAIN);
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        let mut ch_verify = FsChallenger::new(TEST_DOMAIN);
        let res = verify(m, &proof, &mut ch_verify);
        assert!(res.is_err(), "m={m}");
    }
}

// Final A and B evaluations must affect the downstream Fiat--Shamir challenge.
#[test]
fn final_ab_claims_bound_to_transcript() {
    let m = 14;
    let mut rng = Rng::new(0xF1A7_5A11);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

    let mut ch_prove = FsChallenger::new(TEST_DOMAIN);
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    // Capture the next challenge, which lincheck uses as α.
    let mut ch_honest = FsChallenger::new(TEST_DOMAIN);
    assert!(verify(m, &proof, &mut ch_honest).is_ok());
    let alpha_honest = ch_honest.sample_f128();

    // Preserve final_a_eval * final_b_eval while changing both factors.
    let t = F128 {
        lo: 0x0123_4567_89ab_cdef,
        hi: 0xfedc_ba98_7654_3210,
    };
    assert!(t != F128::ZERO && t != F128::ONE);
    let mut bad = proof.clone();
    bad.final_a_eval *= t;
    bad.final_b_eval *= t.inv();
    assert_ne!(bad.final_a_eval, proof.final_a_eval);
    assert_ne!(bad.final_b_eval, proof.final_b_eval);
    assert_eq!(
        bad.final_a_eval * bad.final_b_eval,
        proof.final_a_eval * proof.final_b_eval
    );

    // Zerocheck checks only the product; transcript binding protects the
    // individual claims used downstream.
    let mut ch_tampered = FsChallenger::new(TEST_DOMAIN);
    assert!(verify(m, &bad, &mut ch_tampered).is_ok());
    let alpha_tampered = ch_tampered.sample_f128();

    // Observing both claims must change the downstream challenge.
    assert_ne!(alpha_honest, alpha_tampered);
}

// The proof is deterministic for a fixed witness and challenger seed.
#[test]
fn prove_deterministic() {
    let m = 14;
    let mut rng = Rng::new(99);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch1 = FsChallenger::new(TEST_DOMAIN);
    let mut ch2 = FsChallenger::new(TEST_DOMAIN);
    let (proof1, claim1) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch1);
    let (proof2, claim2) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch2);

    assert_eq!(proof1.round1_ab, proof2.round1_ab);
    assert_eq!(proof1.round1_c, proof2.round1_c);
    assert_eq!(proof1.multilinear_rounds, proof2.multilinear_rounds);
    assert_eq!(proof1.final_a_eval, proof2.final_a_eval);
    assert_eq!(proof1.final_b_eval, proof2.final_b_eval);
    assert_eq!(proof1.final_c_eval, proof2.final_c_eval);
    assert_eq!(claim1.z, claim2.z);
    assert_eq!(claim1.mlv_challenges, claim2.mlv_challenges);
}

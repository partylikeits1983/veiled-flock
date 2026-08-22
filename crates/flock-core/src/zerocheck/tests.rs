use super::*;
use crate::challenger::FsChallenger;

mod helpers;

use helpers::{Rng, ScriptedEqChallenger};

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

/// Pack three Boolean vectors into the (a_packed, b_packed, c_packed)
/// shape that `prove_packed` consumes.
fn pack_abc(a: &[bool], b: &[bool], c: &[bool]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    use univariate_skip::pack_bits;
    (pack_bits(a), pack_bits(b), pack_bits(c))
}

/// `prove` runs end-to-end at the smallest valid m (= k_skip + N_INNER = 13)
/// without panicking, and produces output of the right shape.
///
/// We can't yet check the proof is *accepted* (verify is a stub), but the
/// structural sanity here catches:
///   - mismatched challenger observe/sample sequence
///   - wrong slice lengths in r / mlv_arg / r_next at any round
///   - any unreachable assert in the underlying functions
#[test]
fn prove_runs_end_to_end() {
    for &m in &[13usize, 14, 15, 16] {
        let mut rng = Rng::new(m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        // Honest witness: c = a AND b, so a·b ⊕ c = 0 on the hypercube.
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut challenger = FsChallenger::new(b"flock-test-v0");
        let (proof, claim) = prove_packed(&a_p, &b_p, &c_p, m, &mut challenger);

        // Shape checks.
        assert_eq!(proof.round1_ab.len(), 1usize << K_SKIP, "m={m}");
        assert_eq!(proof.round1_c.len(), 1usize << K_SKIP, "m={m}");
        assert_eq!(proof.multilinear_rounds.len(), m - K_SKIP, "m={m}");
        assert_eq!(claim.mlv_challenges.len(), m - K_SKIP, "m={m}");

        // Claim's eval fields agree with the proof's final evals.
        assert_eq!(claim.a_eval, proof.final_a_eval, "m={m}");
        assert_eq!(claim.b_eval, proof.final_b_eval, "m={m}");
        assert_eq!(claim.c_eval, proof.final_c_eval, "m={m}");
    }
}

/// **Prove→verify roundtrip**: an honest proof verifies cleanly, and the
/// claim returned by `verify` is byte-for-byte equal to the claim returned
/// by `prove`.
#[test]
fn prove_verify_roundtrip_honest() {
    for &m in &[13usize, 14, 15, 16] {
        let mut rng = Rng::new(1000 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, claim_p) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        let mut ch_verify = FsChallenger::new(b"flock-test-v0");
        let result = verify(m, &proof, &mut ch_verify);
        let claim_v = result.unwrap_or_else(|e| panic!("verify rejected at m={m}: {e:?}"));

        assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");
    }
}

/// **A1′ combined masked zerocheck: prove→verify roundtrip.** With honest
/// (a,b,c=a*b), fresh field-valued P, and public Q-star, the combined proof
/// verifies under `verify_zk` (which checks the terminal masked equation).
/// The mask never breaks completeness — the round messages
/// carry `γ·M_j`, the initial claim carries `γ·σ_z`, and they telescope
/// consistently.
#[test]
fn prove_verify_zk_roundtrip_honest() {
    for &m in &[13usize, 14, 15, 16] {
        let mut rng = Rng::new(2000 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let p_small = rng.field_mask(m);
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = FsChallenger::new(b"flock-zk-test-v0");
        let (proof, claim_p) = prove_packed_padded_zk(
            &a_p,
            &b_p,
            &c_p,
            &p_small,
            m,
            &PaddingSpec::dense(m),
            &mut ch_prove,
        );

        let mut ch_verify = FsChallenger::new(b"flock-zk-test-v0");
        let claim_v = verify_zk(m, &proof, &mut ch_verify)
            .unwrap_or_else(|e| panic!("verify_zk rejected honest proof at m={m}: {e:?}"));
        assert_eq!(claim_p, claim_v, "zk claim mismatch at m={m}");
    }
}

/// **A3 round-1 mask: prove→verify roundtrip, staged.** Three mask
/// configurations, so a completeness break localizes itself:
/// zero cubes (must reduce exactly to the unmasked protocol), diagonal
/// only (`S_h = 0`, so the combined polynomial is untouched), and the
/// full off-diagonal pair.
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

            let mut ch_prove = FsChallenger::new(b"flock-zk-test-v0");
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

            let mut ch_verify = FsChallenger::new(b"flock-zk-test-v0");
            let claim_v =
                verify_zk_masked(m, &proof, Some((mt.mc_at_z, mt.h_at_z)), &mut ch_verify)
                    .unwrap_or_else(|e| {
                        panic!("A3 [{stage}] verify rejected honest proof at m={m}: {e:?}")
                    });
            assert_eq!(claim_p, claim_v, "A3 [{stage}] claim mismatch at m={m}");

            // The un-shifted c-claim must be the true ĉ(z, r_rest), i.e.
            // exactly what the unmasked protocol would have claimed.
            let mut ch_ref = FsChallenger::new(b"flock-zk-test-v0");
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
                assert_eq!(
                    claim_ref, claim_v,
                    "zero masks must reproduce the unmasked protocol at m={m}"
                );
            }
        }
    }
}

/// Does the round-1 C-side output depend on `a`,`b`? A3 computes a mask's
/// C-side message by calling the round-1 routine with zero `a`,`b`, which
/// is only valid if the C output is a function of `c_packed` alone.
#[test]
fn round1_c_output_is_independent_of_ab() {
    use crate::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
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
    assert_eq!(
        c_with_ab, c_without_ab,
        "the round-1 C output DEPENDS on a,b — A3 cannot derive a mask's \
             C-side message by zeroing them"
    );
}

/// **A1′ soundness spot-checks.** Tampering the mask sum `σ_z`, either
/// mask evaluation `P(ρ)`/`Q(ρ)`, or a combined round message must be
/// rejected by `verify_zk`.
#[test]
fn verify_zk_rejects_mutations() {
    let m = 14;
    let mut rng = Rng::new(7070);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let p_small = rng.field_mask(m);
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(b"flock-zk-test-v0");
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
        let mut ch = FsChallenger::new(b"flock-zk-test-v0");
        assert!(verify_zk(m, &bad, &mut ch).is_err());
    };
    mutate(&|pr| pr.mask_init += bump);
    mutate(&|pr| pr.final_p_eval += bump);
    mutate(&|pr| pr.multilinear_rounds[3].1 += bump);
    mutate(&|pr| pr.final_a_eval += bump);
    // Complete the matrix: every round pair, both components; round-1
    // entries on both vectors; the remaining finals; truncations.
    for i in 0..proof.multilinear_rounds.len() {
        mutate(&|pr| pr.multilinear_rounds[i].0 += bump);
        mutate(&|pr| pr.multilinear_rounds[i].1 += bump);
    }
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

/// **S1 — invalid witness rejected on the amended path.** The zk twin of
/// `audit_false_statement_rejected`: one flipped `c` bit (so
/// `a·b ⊕ c ≠ 0` somewhere) with an otherwise HONEST prover run and
/// honest fresh masks must be rejected by `verify_zk`. The masked
/// channel must not create an acceptance path for a false statement.
#[test]
fn zk_invalid_witness_rejected() {
    for &m in &[13usize, 14, 15] {
        let mut rng = Rng::new(0xA1_5000 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        c[3] = !c[3];
        let p_small = rng.field_mask(m);
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = FsChallenger::new(b"flock-zk-test-v0");
        let (proof, _) = prove_packed_padded_zk(
            &a_p,
            &b_p,
            &c_p,
            &p_small,
            m,
            &PaddingSpec::dense(m),
            &mut ch_prove,
        );
        let mut ch_verify = FsChallenger::new(b"flock-zk-test-v0");
        let res = verify_zk(m, &proof, &mut ch_verify);
        assert!(
            res.is_err(),
            "verify_zk ACCEPTED a false statement at m={m}: {res:?}"
        );
    }
}

/// Replay `verify_zk`'s final-check residual for a given proof under
/// `RandomChallenger(seed)`, with `mask_init` overridden. Uses the SAME
/// in-crate primitives as `verify_zk` (interpolation + the fixed inner
/// challenge schedule) — measurement instrumentation, not a parallel
/// verifier. Returns `c_running + expected` (zero ⇔ final check passes).
#[cfg(test)]
fn zk_final_residual(m: usize, proof: &ZkZerocheckProof, seed: u64, mask_init: F128) -> F128 {
    use crate::challenger::RandomChallenger;
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

/// **S2 + S3 — γ-batching soundness, constructively, on the real code.**
///
/// Lemma L6's content: for FIXED prover messages with zerocheck defect
/// δ and mask-channel defect δ′, the verifier's final residual is an
/// AFFINE function of `σ_z` with slope γ·Π(1+ρᵢ)/(1+r_eq,ᵢ) ≠ 0 —
/// so for a prover who already knows γ there is EXACTLY ONE σ_z that
/// cancels an invalid witness, and for a prover bound to send σ_z
/// before γ (Fiat–Shamir) the cancellation succeeds with probability
/// 2⁻¹²⁸. Demonstrated:
///  (a) an invalid-witness proof is rejected at its honest σ_z;
///  (b) the residual is affine in σ_z with nonzero slope — the solved
///      σ* is its unique root;
///  (c) under `RandomChallenger` (γ known in advance — the ordering
///      attack) the σ*-patched proof is ACCEPTED: choosing σ_z after γ
///      breaks soundness, so the transcript ordering is load-bearing;
///  (d) the SAME patched proof under `FsChallenger` is REJECTED — γ
///      re-derives from σ*, denying the prover the γ it solved against;
///  (e) at 100 fresh challenge tuples the patched proof is rejected
///      (the accepting tuple set is thin, as the 2⁻¹²⁸ bound predicts).
#[test]
fn zk_gamma_cancellation_unique_and_fs_ordering() {
    use crate::challenger::RandomChallenger;
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

    // (a) Rejected as-is.
    let mut ch = RandomChallenger::new(seed);
    assert!(
        verify_zk(m, &proof, &mut ch).is_err(),
        "invalid witness must be rejected at the honest σ_z"
    );

    // (b) Residual is affine in σ_z; solve for the unique root σ*.
    let r0 = zk_final_residual(m, &proof, seed, proof.mask_init);
    let r1 = zk_final_residual(m, &proof, seed, proof.mask_init + F128::ONE);
    let slope = r0 + r1; // affine over char 2: R(x+1) + R(x) = slope
    assert_ne!(r0, F128::ZERO, "defect must be visible in the residual");
    assert_ne!(
        slope,
        F128::ZERO,
        "σ_z slope γ·Π(1+ρ)/(1+r_eq) must be nonzero"
    );
    let sigma_star = proof.mask_init + r0 * slope.inv();
    assert_eq!(
        zk_final_residual(m, &proof, seed, sigma_star),
        F128::ZERO,
        "σ* must be the root"
    );
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

    // (c) The ordering attack: with γ known in advance, the patched
    // proof is ACCEPTED by the real verifier.
    let mut cheat = proof.clone();
    cheat.mask_init = sigma_star;
    let mut ch = RandomChallenger::new(seed);
    assert!(
        verify_zk(m, &cheat, &mut ch).is_ok(),
        "σ_z chosen AFTER γ must cancel the invalid witness under a \
             fixed-challenge (ordering-violating) verifier — this is the \
             attack Fiat–Shamir ordering exists to prevent"
    );

    // (d) Under Fiat–Shamir the same proof is rejected: γ is derived
    // after σ_z is absorbed, so the solved-for γ never occurs.
    let mut ch_fs = FsChallenger::new(b"flock-zk-order-v0");
    assert!(
        verify_zk(m, &cheat, &mut ch_fs).is_err(),
        "FS-derived γ must deny the σ_z-after-γ cancellation"
    );

    // (e) Thin accepting set: 100 fresh challenge tuples all reject.
    for s in 0..100u64 {
        let mut ch = RandomChallenger::new(0x51DE_0000 + s);
        assert!(
            verify_zk(m, &cheat, &mut ch).is_err(),
            "patched proof accepted at unrelated challenge tuple {s}"
        );
    }
}

/// **Verify rejects byte-mutated proofs.** Walk each component of the
/// proof and flip one F128 entry; the verifier must return an `Err`
/// (rather than panicking or silently accepting).
#[test]
fn verify_rejects_mutations() {
    let m = 14;
    let mut rng = Rng::new(5050);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let _seed: u64 = 0xDEAD_BEEF;
    let mut ch_prove = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    // Each closure returns a mutated copy; verify must reject all of them.
    let mutations: Vec<(&str, Box<dyn Fn(&ZerocheckProof) -> ZerocheckProof>)> = vec![
        (
            "round1_ab[0] bit-flip",
            Box::new(|p| {
                let mut q = p.clone();
                q.round1_ab[0].lo ^= 1;
                q
            }),
        ),
        (
            "round1_c[5] bit-flip",
            Box::new(|p| {
                let mut q = p.clone();
                q.round1_c[5].lo ^= 1;
                q
            }),
        ),
        (
            "multilinear_rounds[0].0 bit-flip",
            Box::new(|p| {
                let mut q = p.clone();
                q.multilinear_rounds[0].0.lo ^= 1;
                q
            }),
        ),
        (
            "multilinear_rounds[2].1 bit-flip",
            Box::new(|p| {
                let mut q = p.clone();
                let last = q.multilinear_rounds.len() / 2;
                q.multilinear_rounds[last].1.hi ^= 1;
                q
            }),
        ),
        (
            "final_a_eval bit-flip",
            Box::new(|p| {
                let mut q = p.clone();
                q.final_a_eval.lo ^= 1;
                q
            }),
        ),
        (
            "final_c_eval bit-flip",
            Box::new(|p| {
                let mut q = p.clone();
                q.final_c_eval.hi ^= 1;
                q
            }),
        ),
    ];

    for (label, mutate) in mutations {
        let bad = mutate(&proof);
        let mut ch = FsChallenger::new(b"flock-test-v0");
        let result = verify(m, &bad, &mut ch);
        assert!(
            result.is_err(),
            "verify accepted mutated proof ({label}) — should have rejected"
        );
    }
}

/// Shape rejections: too-short round1, wrong number of multilinear rounds.
#[test]
fn verify_rejects_shape_errors() {
    let m = 14;
    let mut rng = Rng::new(606);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    // Truncate round1_ab.
    let mut bad = proof.clone();
    bad.round1_ab.pop();
    let mut ch = FsChallenger::new(b"flock-test-v0");
    assert!(matches!(
        verify(m, &bad, &mut ch),
        Err(VerifyError::BadRound1Length { .. })
    ));

    // Truncate multilinear rounds.
    let mut bad = proof.clone();
    bad.multilinear_rounds.pop();
    let mut ch = FsChallenger::new(b"flock-test-v0");
    assert!(matches!(
        verify(m, &bad, &mut ch),
        Err(VerifyError::BadMultilinearRoundsLength { .. })
    ));

    // log_n too small.
    let mut ch = FsChallenger::new(b"flock-test-v0");
    assert!(matches!(
        verify(K_SKIP + 6, &proof, &mut ch),
        Err(VerifyError::LogNTooSmall { .. })
    ));
}

/// AUDIT: a FALSE statement (c ≠ a·b at some hypercube point) must be
/// rejected, even though the prover follows the honest algorithm on its
/// (dishonest) witness.
#[test]
fn audit_false_statement_rejected() {
    for &m in &[13usize, 14, 15] {
        let mut rng = Rng::new(7777 + m as u64);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        // Correct c, then corrupt ONE bit so a·b ⊕ c ≠ 0 somewhere.
        let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        c[3] = !c[3];

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        let mut ch_verify = FsChallenger::new(b"flock-test-v0");
        let res = verify(m, &proof, &mut ch_verify);
        assert!(
            res.is_err(),
            "verify ACCEPTED a false statement at m={m}: {res:?}"
        );
    }
}

/// AUDIT: flipping any round's `msg_inf` (the degree-2 / ∞ coefficient)
/// must be rejected. `msg_inf` is observed into the transcript, so the
/// tamper both reshuffles subsequent ρ challenges and breaks the
/// running-claim chain — either way the final check fails.
#[test]
fn audit_round_msg_inf_tamper_rejected() {
    let m = 14;
    let mut rng = Rng::new(424242);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    // For each round, flip msg_inf to a different value. Because msg_inf
    // is observed into the transcript, this reshuffles subsequent rho's;
    // a sound verifier should reject (overwhelming probability).
    for idx in 0..proof.multilinear_rounds.len() {
        let mut bad = proof.clone();
        bad.multilinear_rounds[idx].1 += F128::ONE;
        let mut ch = FsChallenger::new(b"flock-test-v0");
        let res = verify(m, &bad, &mut ch);
        assert!(res.is_err(), "msg_inf tamper at round {idx} ACCEPTED");
    }
}

/// AUDIT: the LAST round's `msg_inf` must be constrained — a common
/// off-by-one is to leave the final round's leading coefficient unchecked.
/// Kept separate from the all-rounds loop above so a regression here points
/// straight at the final-round binding.
#[test]
fn audit_last_round_inf_constrained() {
    let m = 13;
    let mut rng = Rng::new(98765);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    let last = proof.multilinear_rounds.len() - 1;
    let mut bad = proof.clone();
    bad.multilinear_rounds[last].1 += F128::ONE;
    let mut ch = FsChallenger::new(b"flock-test-v0");
    assert!(
        verify(m, &bad, &mut ch).is_err(),
        "last-round msg_inf unconstrained"
    );
}

/// AUDIT (Fiat–Shamir binding of the final â, b̂ claims). Regression test
/// for the gap where `final_a_eval`/`final_b_eval` were not observed into
/// the transcript.
///
/// Downstream, lincheck reduces these two claims via a *single* random-
/// linear-combination check (`target = α·v_a + v_b`). That batching is only
/// sound if α is sampled *after* the claims are bound to the transcript —
/// otherwise a prover that already knows α can pick (v_a, v_b) to satisfy
/// the one batched equation while violating the individual ties.
///
/// A *product-preserving* tamper `(â, b̂) → (â·t, b̂·t⁻¹)` leaves the
/// zerocheck's own final check `c_running == â·b̂` satisfied, so `verify`
/// still returns `Ok` — the zerocheck alone is blind to it. The defense is
/// that both claims are now observed last in the transcript, so the next
/// challenge (the slot lincheck draws α from) must diverge from the honest
/// run. This assertion FAILS before the observe was added (identical
/// post-state) and passes now.
#[test]
fn audit_final_ab_claims_bound_to_transcript() {
    let m = 14;
    let mut rng = Rng::new(0xF1A7_5A11);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

    let mut ch_prove = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

    // Honest verify, then capture the next challenge the transcript feeds
    // downstream — this is exactly the slot lincheck samples α from.
    let mut ch_honest = FsChallenger::new(b"flock-test-v0");
    assert!(
        verify(m, &proof, &mut ch_honest).is_ok(),
        "honest verify rejected"
    );
    let alpha_honest = ch_honest.sample_f128();

    // Product-preserving tamper: â' = â·t, b̂' = b̂·t⁻¹ ⇒ â'·b̂' = â·b̂, so the
    // zerocheck's `c_running == â·b̂` check still holds for the tampered pair.
    let t = F128 {
        lo: 0x0123_4567_89ab_cdef,
        hi: 0xfedc_ba98_7654_3210,
    };
    assert!(t != F128::ZERO && t != F128::ONE, "t must be nontrivial");
    let mut bad = proof.clone();
    bad.final_a_eval *= t;
    bad.final_b_eval *= t.inv();
    assert_ne!(bad.final_a_eval, proof.final_a_eval, "tamper must change â");
    assert_ne!(bad.final_b_eval, proof.final_b_eval, "tamper must change b̂");
    assert_eq!(
        bad.final_a_eval * bad.final_b_eval,
        proof.final_a_eval * proof.final_b_eval,
        "tamper must preserve the product",
    );

    // The zerocheck's own checks are blind to a product-preserving tamper:
    // verify still ACCEPTS. This is precisely the gap the FS binding closes —
    // the tamper is caught only because the claims now move the transcript.
    let mut ch_tampered = FsChallenger::new(b"flock-test-v0");
    assert!(
        verify(m, &bad, &mut ch_tampered).is_ok(),
        "product-preserving tamper rejected by zerocheck's own checks (unexpected)",
    );
    let alpha_tampered = ch_tampered.sample_f128();

    // The fix: observing â, b̂ makes the downstream challenge depend on them,
    // so lincheck's α (and everything after) diverges and rejects the
    // tampered pair. Before the fix these challenges were equal.
    assert_ne!(
        alpha_honest, alpha_tampered,
        "final â/b̂ claims are NOT bound into the transcript: a product-preserving \
             tamper leaves the downstream challenge unchanged, breaking lincheck's \
             α-batched reduction of (v_a, v_b)",
    );
}

/// AUDIT: many random false witnesses must all be rejected. Stronger than a
/// single corruption — exercises the full prove→verify path on statements
/// that are false at varying numbers of hypercube points.
#[test]
fn audit_many_false_statements_rejected() {
    let m = 13;
    for seed in 0..20u64 {
        let mut rng = Rng::new(0xBADC0DE ^ seed);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        // Flip a random number of bits (1..=4).
        let nflip = 1 + (rng.next_u64() as usize % 4);
        for _ in 0..nflip {
            let idx = rng.next_u64() as usize % c.len();
            c[idx] = !c[idx];
        }
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let mut ch_verify = FsChallenger::new(b"flock-test-v0");
        let res = verify(m, &proof, &mut ch_verify);
        assert!(
            res.is_err(),
            "false statement (seed={seed}) ACCEPTED: {res:?}"
        );
    }
}

/// AUDIT: tamper msg_1 in each round; must reject.
#[test]
fn audit_round_msg_1_tamper_rejected() {
    let m = 14;
    let mut rng = Rng::new(31415);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch_prove = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
    for idx in 0..proof.multilinear_rounds.len() {
        let mut bad = proof.clone();
        bad.multilinear_rounds[idx].0 += F128::ONE;
        let mut ch = FsChallenger::new(b"flock-test-v0");
        assert!(
            verify(m, &bad, &mut ch).is_err(),
            "msg_1 tamper round {idx} ACCEPTED"
        );
    }
}

/// Determinism: same witness + same challenger seed → same proof.
#[test]
fn prove_deterministic() {
    let m = 14;
    let mut rng = Rng::new(99);
    let a = rng.bits(1 << m);
    let b = rng.bits(1 << m);
    let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

    let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
    let mut ch1 = FsChallenger::new(b"flock-test-v0");
    let mut ch2 = FsChallenger::new(b"flock-test-v0");
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

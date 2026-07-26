//! End-to-end soundness suite for the A1′ reference path.
//!
//! Complements the in-crate zerocheck-layer tests (`zk_invalid_witness_rejected`,
//! `zk_gamma_cancellation_unique_and_fs_ordering`, `verify_zk_rejects_mutations`)
//! with whole-proof checks on the complete pipeline: the tamper matrix over
//! every proof component, commitment substitution, opening swaps, and the
//! fail-closed behaviour of the certificate-gated API.
//!
//! Runs on the m=15 fixture so the full matrix is CI-fast; the same matrix at
//! the certified m=22 shape runs in `scripts/zk-certify.sh`.

#![cfg(feature = "zk")]

use flock_core::challenger::FsChallenger;
use flock_core::field::F128;
use flock_core::pcs::Commitment;
use flock_core::zk::ZkRng;
use flock_prover::prover::R1csProofZkA1;
use flock_prover::zk_audit_support::FixtureA1M15;

struct Rng(u64);
impl Rng {
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
}

const DOMAIN: &[u8] = b"flock-a1-soundness";

fn honest(seed: u64, mask_seed: [u8; 32]) -> (FixtureA1M15, R1csProofZkA1, Commitment) {
    let fx = FixtureA1M15::new();
    let mut rng = Rng(seed);
    let payload = rng.bits(FixtureA1M15::N_PAYLOAD * FixtureA1M15::BLOCKS);
    let u_a = rng.bits(FixtureA1M15::A_BITS);
    let u_b = rng.bits(FixtureA1M15::B_BITS);
    let z = fx.witness(&payload, &u_a, &u_b);
    let mut zk_rng = ZkRng::from_seed(mask_seed);
    let mut ch = FsChallenger::new(DOMAIN);
    let (proof, comm) = fx.prove(z, &mut zk_rng, &mut ch);
    (fx, proof, comm)
}

#[test]
fn a1_honest_roundtrip_and_fresh_masks() {
    let (fx, proof, comm) = honest(0x5EED_01, [0x11; 32]);
    let mut chv = FsChallenger::new(DOMAIN);
    fx.verify(&proof, &comm, &mut chv).expect("honest A1′ proof must verify");

    // Fresh masks on the same witness ⇒ a different, still-verifying proof.
    let (_, proof2, comm2) = honest(0x5EED_01, [0x22; 32]);
    let mut chv2 = FsChallenger::new(DOMAIN);
    fx.verify(&proof2, &comm2, &mut chv2).expect("fresh-mask proof must verify");
    assert_ne!(comm.root, comm2.root, "fresh witness mask ⇒ fresh root");
    assert_ne!(proof.zerocheck.final_p_eval, proof2.zerocheck.final_p_eval);
    assert_ne!(proof.zerocheck.mask_init, proof2.zerocheck.mask_init);
}

/// The complete tamper matrix: every algebraic component of the proof, the
/// P/Q commitments (root and params), and the openings. Each mutation must
/// be rejected.
#[test]
fn a1_tamper_matrix_rejected() {
    let (fx, proof, comm) = honest(0x5EED_02, [0x33; 32]);
    let bump = F128 { lo: 0xABCD_1234, hi: 0x9 };

    let mut cases: Vec<(&str, Box<dyn Fn(&mut R1csProofZkA1)>)> = vec![
        ("zerocheck.mask_init", Box::new(move |p| p.zerocheck.mask_init += bump)),
        ("zerocheck.final_p_eval", Box::new(move |p| p.zerocheck.final_p_eval += bump)),
        ("zerocheck.final_q_eval", Box::new(move |p| p.zerocheck.final_q_eval += bump)),
        ("zerocheck.final_a_eval", Box::new(move |p| p.zerocheck.final_a_eval += bump)),
        ("zerocheck.final_b_eval", Box::new(move |p| p.zerocheck.final_b_eval += bump)),
        ("zerocheck.final_c_eval", Box::new(move |p| p.zerocheck.final_c_eval += bump)),
        ("zerocheck.round1_ab[0]", Box::new(move |p| p.zerocheck.round1_ab[0] += bump)),
        ("zerocheck.round1_ab[63]", Box::new(move |p| p.zerocheck.round1_ab[63] += bump)),
        ("zerocheck.round1_c[0]", Box::new(move |p| p.zerocheck.round1_c[0] += bump)),
        ("lincheck.rounds[0].0", Box::new(move |p| p.lincheck.rounds[0].0 += bump)),
        ("lincheck.rounds[0].1", Box::new(move |p| p.lincheck.rounds[0].1 += bump)),
        ("lincheck.z_partial[0]", Box::new(move |p| p.lincheck.z_partial[0] += bump)),
        ("comm_p.root", Box::new(|p| p.comm_p.root[0] ^= 1)),
        ("comm_q.root", Box::new(|p| p.comm_q.root[0] ^= 1)),
        ("comm_p.params.zk", Box::new(|p| p.comm_p.params.zk = false)),
        ("comm_q.params.m", Box::new(|p| p.comm_q.params.m += 1)),
        ("comm_p.params.log_inv_rate", Box::new(|p| p.comm_p.params.log_inv_rate += 1)),
        (
            "swap open_p/open_q",
            Box::new(|p| std::mem::swap(&mut p.open_p, &mut p.open_q)),
        ),
        (
            "swap comm_p/comm_q",
            Box::new(|p| std::mem::swap(&mut p.comm_p, &mut p.comm_q)),
        ),
        (
            "open_p.zk_blind.y_g",
            Box::new(move |p| {
                if let Some(b) = p.open_p.zk_blind.as_mut() {
                    b.y_g += bump;
                }
            }),
        ),
        (
            "open_q strip zk_blind",
            Box::new(|p| p.open_q.zk_blind = None),
        ),
        (
            "pcs_open.zk_blind.y_g",
            Box::new(move |p| {
                if let Some(b) = p.pcs_open.zk_blind.as_mut() {
                    b.y_g += bump;
                }
            }),
        ),
        (
            "open_p.ligerito.final_proof.yr[0]",
            Box::new(move |p| p.open_p.ligerito.final_proof.yr[0] += bump),
        ),
        (
            "pcs_open.ring_switches[0].s_hat_v[0]",
            Box::new(move |p| p.pcs_open.ring_switches[0].s_hat_v[0] += bump),
        ),
        (
            "open_q.ligerito.initial_root",
            Box::new(|p| p.open_q.ligerito.initial_root[0] ^= 1),
        ),
    ];
    // Every combined round pair, both components.
    for i in 0..proof.zerocheck.multilinear_rounds.len() {
        cases.push((
            "zerocheck.multilinear_rounds[i].0",
            Box::new(move |p| p.zerocheck.multilinear_rounds[i].0 += bump),
        ));
        cases.push((
            "zerocheck.multilinear_rounds[i].1",
            Box::new(move |p| p.zerocheck.multilinear_rounds[i].1 += bump),
        ));
    }

    for (name, mutate) in cases {
        let mut bad = proof.clone();
        mutate(&mut bad);
        let mut ch = FsChallenger::new(DOMAIN);
        let res = fx.verify(&bad, &comm, &mut ch);
        assert!(res.is_err(), "tamper `{name}` was ACCEPTED");
    }
}

/// A proof is bound to its own witness commitment: verifying it against a
/// different commitment (same shape, different witness/masks) must fail.
#[test]
fn a1_rejects_foreign_commitment() {
    let (fx, proof, _comm) = honest(0x5EED_03, [0x44; 32]);
    let (_, _proof2, comm2) = honest(0x5EED_04, [0x55; 32]);
    let mut ch = FsChallenger::new(DOMAIN);
    assert!(
        fx.verify(&proof, &comm2, &mut ch).is_err(),
        "proof must not verify against a foreign commitment"
    );
}

/// A proof does not transfer across Fiat–Shamir domains.
#[test]
fn a1_rejects_domain_substitution() {
    let (fx, proof, comm) = honest(0x5EED_05, [0x66; 32]);
    let mut ch = FsChallenger::new(b"flock-a1-other-domain");
    assert!(fx.verify(&proof, &comm, &mut ch).is_err());
}

/// The certificate gate rejects statement families that are out of scope —
/// including the hash-chain statement, which binds public endpoints and so
/// breaks the self-generated-witness simulator argument. This is enforced
/// structurally (no chain zk entry point exists) and by the gate's family
/// enum having exactly one variant; this test pins the gate's error path
/// for an uncertified BLAKE3 shape, the case that *is* reachable.
#[test]
fn zk_gate_rejects_uncertified_configuration() {
    use flock_core::pcs::PcsParams;
    use flock_prover::zk_certificate::{StatementFamily, ZkGateError, require_certified};

    let fx = FixtureA1M15::new();
    // The m=15 audit fixture is deliberately NOT a certified production
    // configuration — the gate must refuse it.
    let res = require_certified(StatementFamily::Blake3Batch, 8, &fx.r1cs, &fx.pcs_params);
    assert!(matches!(res, Err(ZkGateError::Uncertified { .. })), "audit fixture must not be certified");

    // Certified shape but a mismatched circuit digest is also refused.
    let params = PcsParams {
        m: 22,
        log_inv_rate: 1,
        log_batch_size: 6,
        profile: Default::default(),
        zk: true,
    };
    let res = require_certified(StatementFamily::Blake3Batch, 256, &fx.r1cs, &params);
    assert!(
        matches!(res, Err(ZkGateError::Uncertified { .. })),
        "digest mismatch must be refused even at a certified shape"
    );
}

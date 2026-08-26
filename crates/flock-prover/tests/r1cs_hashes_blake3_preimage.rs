//! Integration tests for the BLAKE3 preimage relation: the batch and zk
//! round trips, the rejection paths, the succinct-VEIL round trip, and the
//! simulator/oracle ledger checks.
//!
//! `honest_prover_on_the_patched_vector_is_rejected` reads the `pub(crate)`
//! helper `absorb_statement`, so it stays in
//! `crates/flock-prover/src/r1cs_hashes/blake3_preimage/tests.rs`.

#![cfg(feature = "zk")]

use flock_core::challenger::FsChallenger;
use flock_core::pcs::Commitment;
use flock_prover::preimage_simulator::simulate;
use flock_prover::r1cs_hashes::blake3::{
    Compression, ParamPinning, build_block_r1cs_pinned, generate_witness,
};
use flock_prover::r1cs_hashes::blake3_preimage::*;
use flock_prover::sim_game::{
    OracleQueryCounts, SimGameLedger, production_grinding_candidate_bound,
};
use flock_prover::sim_oracle::OracleChallenger;
use flock_prover::sim_oracle::shared_oracle;
use flock_prover::sim_seal::{SealedStatement, SimCoins};
use flock_prover::transcript_schema::{algebraic_vector, flatten_a1};

/// The smallest batch with a registered Ligerito config: m = k_log +
/// n_log = 14 + 8 = 22, the production shape.
const N_TEST: usize = 256;

fn msgs_of(seed: u64, n: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    let mut s = seed | 1;
    (0..n)
        .map(|_| {
            std::array::from_fn(|_| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                (s & 0xFF) as u8
            })
        })
        .collect()
}

#[cfg(feature = "veil")]
#[test]
fn succinct_veil_preimage_roundtrip_and_mutations() {
    // The hiding Ligerito layer's registered production geometry starts
    // at m=22, i.e. 256 BLAKE3 blocks.
    let n = N_TEST;
    let setup = Blake3PreimageZkSetup::new(n);
    let mut messages = msgs_of(0x51_CC_1C_7, n);
    // Detect accidental raw-witness serialization.
    messages[0] = [0xA5; MESSAGE_BYTES];
    let digests = Blake3PreimageSetup::digests_of(&messages);
    let mut rng = flock_core::zk::ZkRng::from_seed([0x51; 32]);
    let mut prover_challenger = FsChallenger::new(b"succinct-veil-preimage-test");
    let (proof, commitment) = setup
        .prove_succinct(&messages, &digests, &mut rng, &mut prover_challenger)
        .expect("prove succinct VEIL");

    let encoded = bincode::serialize(&(&commitment, &proof)).expect("serialize proof");
    assert!(
        encoded.len() <= 700_000,
        "succinct proof unexpectedly grew to {} bytes",
        encoded.len()
    );
    assert!(
        encoded
            .windows(MESSAGE_BYTES)
            .all(|window| window != &messages[0][..]),
        "serialized proof contains the raw preimage marker"
    );

    let mut verifier_challenger = FsChallenger::new(b"succinct-veil-preimage-test");
    setup
        .verify_succinct(&commitment, &proof, &digests, &mut verifier_challenger)
        .expect("verify succinct VEIL");

    let rejects = |candidate: &flock_prover::succinct_veil::SuccinctVeilProof,
                   candidate_commitment: &Commitment,
                   candidate_digests: &[[u8; DIGEST_BYTES]]| {
        let mut challenger = FsChallenger::new(b"succinct-veil-preimage-test");
        assert!(
            setup
                .verify_succinct(
                    candidate_commitment,
                    candidate,
                    candidate_digests,
                    &mut challenger,
                )
                .is_err()
        );
    };

    let mut changed_message = proof.clone();
    changed_message.masked_zerocheck.round1_ab[0] += flock_core::field::F128::ONE;
    rejects(&changed_message, &commitment, &digests);

    let mut changed_lincheck = proof.clone();
    changed_lincheck.masked_lincheck.z_partial[0] += flock_core::field::F128::ONE;
    rejects(&changed_lincheck, &commitment, &digests);

    let mut changed_claim = proof.clone();
    changed_claim.ab_value += flock_core::field::F128::ONE;
    rejects(&changed_claim, &commitment, &digests);

    let mut changed_veil = proof.clone();
    changed_veil.veil.linear.rlc_vector[0] += flock_core::field::F128::ONE;
    rejects(&changed_veil, &commitment, &digests);

    let mut changed_hadamard = proof.clone();
    changed_hadamard.veil.hadamard.phi[0] += flock_core::field::F128::ONE;
    rejects(&changed_hadamard, &commitment, &digests);

    let mut changed_pcs = proof.clone();
    changed_pcs.pcs_open.ligerito.initial_proof.opened_rows[0][0] += flock_core::field::F128::ONE;
    rejects(&changed_pcs, &commitment, &digests);

    let mut changed_nonce = proof.clone();
    changed_nonce.proof_nonce[0] ^= 1;
    rejects(&changed_nonce, &commitment, &digests);

    let mut changed_commitment = commitment.clone();
    changed_commitment.root[0] ^= 1;
    rejects(&proof, &changed_commitment, &digests);

    let mut wrong_digests = digests.clone();
    wrong_digests[0][0] ^= 1;
    rejects(&proof, &commitment, &wrong_digests);
}

#[cfg(feature = "veil")]
#[test]
fn succinct_output_claims_move_with_fresh_randomizers() {
    let setup = Blake3PreimageZkSetup::new_succinct(2);
    let messages = msgs_of(0x5A17, 2);
    let digests = Blake3PreimageSetup::digests_of(&messages);
    let prove = |seed: u8| {
        let mut rng = flock_core::zk::ZkRng::from_seed([seed; 32]);
        let mut challenger = FsChallenger::new(b"succinct-veil-claim-mask-test");
        setup
            .prove_succinct(&messages, &digests, &mut rng, &mut challenger)
            .expect("prove")
            .0
    };
    let first = prove(0x31);
    let second = prove(0x32);
    assert_ne!(first.ab_value, second.ab_value);
    assert_ne!(first.c_value, second.c_value);
}

#[cfg(feature = "veil")]
#[test]
fn succinct_veil_public_only_simulator_is_accepted() {
    const DOMAIN: &[u8] = b"succinct-veil-public-only-simulator-test";
    let setup = Blake3PreimageZkSetup::new_succinct(2);
    // Arbitrary public targets; the simulator API receives no messages
    // and makes no attempt to invert them.
    let digests = vec![[0x42; DIGEST_BYTES], [0xA7; DIGEST_BYTES]];
    let oracle = flock_prover::sim_oracle::shared_oracle();
    let simulated = setup
        .simulate_succinct(&digests, [0x93; 32], oracle.clone(), DOMAIN)
        .expect("simulate without a preimage");
    assert_eq!(
        simulated.programmed_points,
        1 + setup.r1cs.m - flock_core::zerocheck::K_SKIP
    );
    {
        let oracle = oracle.lock().unwrap_or_else(|error| error.into_inner());
        for channel in [
            flock_core::ro::RoChannel::Witness,
            flock_core::ro::RoChannel::VeilLinear,
            flock_core::ro::RoChannel::VeilHadamard,
        ] {
            assert!(
                oracle.channel_query_count(channel) > 0,
                "the shared oracle must receive {channel:?} hashes"
            );
        }
    }

    let mut verifier = flock_prover::sim_oracle::OracleChallenger::new(DOMAIN, oracle.clone());
    setup
        .verify_succinct(
            &simulated.commitment,
            &simulated.proof,
            &digests,
            &mut verifier,
        )
        .expect("the generic verifier accepts the simulated proof");
}

/// Honest proof round trip.
#[test]
fn preimage_roundtrip() {
    let n = N_TEST;
    let setup = Blake3PreimageSetup::new(n);
    let msgs = msgs_of(0xC0FFEE, n);
    let digests = Blake3PreimageSetup::digests_of(&msgs);
    // The digests really are BLAKE3 of the messages.
    for (m, d) in msgs.iter().zip(&digests) {
        assert_eq!(::blake3::hash(m).as_bytes(), d);
    }

    let mut ch = FsChallenger::new(b"b3-preimage");
    let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");
    let mut chv = FsChallenger::new(b"b3-preimage");
    setup
        .verify(&comm, &proof, &digests, &mut chv)
        .expect("honest preimage proof must verify");
}

#[test]
fn small_preimage_roundtrip_uses_explicit_ad_hoc_config() {
    let setup = Blake3PreimageSetup::new(1);
    assert_eq!(setup.pcs_params.log_batch_size, 3);
    let msgs = msgs_of(0x51_4d_41_4c_4c, 1);
    let digests = Blake3PreimageSetup::digests_of(&msgs);
    let mut prover = FsChallenger::new(b"b3-preimage-small");
    let (proof, commitment) = setup.prove(&msgs, &digests, &mut prover).unwrap();
    let mut verifier = FsChallenger::new(b"b3-preimage-small");
    setup
        .verify(&commitment, &proof, &digests, &mut verifier)
        .unwrap();
}

/// A proof is bound to its digest list: flipping one bit of one public
/// digest must make verification fail.
#[test]
fn wrong_digest_rejected() {
    let n = N_TEST;
    let setup = Blake3PreimageSetup::new(n);
    let msgs = msgs_of(0xBEEF, n);
    let digests = Blake3PreimageSetup::digests_of(&msgs);
    let mut ch = FsChallenger::new(b"b3-preimage");
    let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");

    let mut tampered = digests.clone();
    tampered[2][7] ^= 1;
    let mut chv = FsChallenger::new(b"b3-preimage");
    assert!(
        setup.verify(&comm, &proof, &tampered, &mut chv).is_err(),
        "a proof must not verify against a different digest list"
    );
}

/// Reordering the public digests is a different statement.
#[test]
fn reordered_digests_rejected() {
    let n = N_TEST;
    let setup = Blake3PreimageSetup::new(n);
    let msgs = msgs_of(0xFEED, n);
    let digests = Blake3PreimageSetup::digests_of(&msgs);
    let mut ch = FsChallenger::new(b"b3-preimage");
    let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");

    let mut swapped = digests.clone();
    swapped.swap(0, 3);
    let mut chv = FsChallenger::new(b"b3-preimage");
    assert!(
        setup.verify(&comm, &proof, &swapped, &mut chv).is_err(),
        "a proof must not verify against a permuted digest list"
    );
}

/// The prover refuses a witness that does not hash to the statement,
/// rather than emitting a proof that cannot verify.
#[test]
fn wrong_preimage_refused_by_prover() {
    let n = N_TEST;
    let setup = Blake3PreimageSetup::new(n);
    let msgs = msgs_of(0x1234, n);
    let mut digests = Blake3PreimageSetup::digests_of(&msgs);
    digests[1][0] ^= 0xFF;
    let mut ch = FsChallenger::new(b"b3-preimage");
    match setup.prove(&msgs, &digests, &mut ch) {
        Err(PreimageError::DigestMismatch { index }) => assert_eq!(index, 1),
        Err(e) => panic!("wrong error: {e}"),
        Ok(_) => panic!("prover accepted a witness that does not hash to the statement"),
    }
}

/// A prover who knows preimages of OTHER digests cannot pass off its
/// proof as one for this statement — the transcript binds the list.
#[test]
fn proof_for_other_digests_does_not_transfer() {
    let n = N_TEST;
    let setup = Blake3PreimageSetup::new(n);
    let mine = msgs_of(0xAAAA, n);
    let theirs = msgs_of(0xBBBB, n);
    let my_digests = Blake3PreimageSetup::digests_of(&mine);
    let their_digests = Blake3PreimageSetup::digests_of(&theirs);

    let mut ch = FsChallenger::new(b"b3-preimage");
    let (proof, comm) = setup
        .prove(&theirs, &their_digests, &mut ch)
        .expect("prove");
    let mut chv = FsChallenger::new(b"b3-preimage");
    assert!(
        setup.verify(&comm, &proof, &my_digests, &mut chv).is_err(),
        "a proof of other preimages must not verify against my digests"
    );
}

/// The masked (zk-mode) path proves and verifies the same statement.
#[test]
fn zk_preimage_roundtrip() {
    let setup = Blake3PreimageZkSetup::new(N_TEST);
    let msgs = msgs_of(0x2222_3333, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&msgs);
    let mut rng = flock_core::zk::ZkRng::from_seed([7u8; 32]);
    let mut ch = FsChallenger::new(b"b3-preimage-zk");
    let (proof, comm) = setup
        .prove(&msgs, &digests, &mut rng, &mut ch)
        .expect("zk prove");
    let mut chv = FsChallenger::new(b"b3-preimage-zk");
    setup
        .verify(&comm, &proof, &digests, &mut chv)
        .expect("honest masked preimage proof must verify");
}

/// Masking is live on the zk path: two proofs of the SAME statement and
/// witness under different mask draws differ in their commitment and in
/// witness-dependent transcript values. (This is a freshness check, not a
/// zero-knowledge claim — see the type's docs.)
#[test]
fn zk_preimage_masks_are_fresh() {
    let setup = Blake3PreimageZkSetup::new(N_TEST);
    let msgs = msgs_of(0x4444_5555, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&msgs);

    let go = |seed: u8| {
        let mut rng = flock_core::zk::ZkRng::from_seed([seed; 32]);
        let mut ch = FsChallenger::new(b"b3-preimage-zk");
        setup
            .prove(&msgs, &digests, &mut rng, &mut ch)
            .expect("prove")
    };
    let (p1, c1) = go(1);
    let (p2, c2) = go(2);
    assert_ne!(c1.root, c2.root, "fresh masks must move the commitment");
    assert_ne!(
        p1.zerocheck.final_a_eval, p2.zerocheck.final_a_eval,
        "fresh masks must move the witness-dependent evaluations"
    );
    // Both still verify against the same public digests.
    for (p, c) in [(&p1, &c1), (&p2, &c2)] {
        let mut chv = FsChallenger::new(b"b3-preimage-zk");
        setup.verify(c, p, &digests, &mut chv).expect("verify");
    }
}

/// The zk path is bound to its digest list too.
#[test]
fn zk_wrong_digest_rejected() {
    let setup = Blake3PreimageZkSetup::new(N_TEST);
    let msgs = msgs_of(0x6666_7777, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&msgs);
    let mut rng = flock_core::zk::ZkRng::from_seed([9u8; 32]);
    let mut ch = FsChallenger::new(b"b3-preimage-zk");
    let (proof, comm) = setup
        .prove(&msgs, &digests, &mut rng, &mut ch)
        .expect("prove");
    let mut tampered = digests.clone();
    tampered[0][31] ^= 0x80;
    let mut chv = FsChallenger::new(b"b3-preimage-zk");
    assert!(
        setup.verify(&comm, &proof, &tampered, &mut chv).is_err(),
        "masked proof must not verify against a different digest list"
    );
}

/// **The harness-faithfulness control.** A real proof, produced and
/// verified through the programmable-oracle challenger with NOTHING
/// programmed, must behave exactly as under plain Fiat–Shamir. Without
/// this, any later "the simulator's output verifies" result would be
/// meaningless — it could hold because the harness is a different
/// protocol rather than because the simulation works.
#[test]
fn oracle_harness_accepts_a_real_proof_unprogrammed() {
    let setup = Blake3PreimageSetup::new(N_TEST);
    let msgs = msgs_of(0x0AC1E_5EED, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&msgs);

    let oracle = shared_oracle();
    let mut ch = OracleChallenger::new(b"b3-preimage", oracle.clone());
    let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");
    assert!(
        oracle.lock().unwrap().is_empty(),
        "the control must run with an unprogrammed oracle"
    );

    let mut chv = OracleChallenger::new(b"b3-preimage", oracle.clone());
    setup
        .verify(&comm, &proof, &digests, &mut chv)
        .expect("a real proof must verify through the oracle harness");

    // And the same proof verifies under plain Fiat–Shamir, so the harness
    // is not merely self-consistent.
    let mut chf = FsChallenger::new(b"b3-preimage");
    setup
        .verify(&comm, &proof, &digests, &mut chf)
        .expect("the same proof must verify under plain Fiat-Shamir");

    // The oracle recorded a query transcript — the object a straightline
    // extractor reads.
    assert!(oracle.lock().unwrap().query_count() > 0);
}

/// **The zero-knowledge result: a proof with no preimage behind it.**
///
/// The simulator receives only the public digests. It never sees — and
/// never computes — a message hashing to any of them; the vector it
/// commits is an honest trace for messages of its own choosing whose
/// output region has been overwritten with the public digests, which is
/// not a satisfying assignment at all. The unmodified verifier accepts.
#[test]
fn simulator_produces_an_accepting_proof_without_any_preimage() {
    let setup = Blake3PreimageZkSetup::new(N_TEST);
    // The statement: digests of messages the simulator will never see.
    let secret = msgs_of(0x5EC1_5EC1, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&secret);
    let sealed = SealedStatement::new(&setup, &digests).expect("public statement");
    let oracle = shared_oracle();
    let sim = simulate(&sealed, SimCoins::new(0xC0FFEE), &oracle, b"b3-preimage-zk")
        .expect("simulation must succeed");

    println!("simulator programmed {} oracle points", sim.programmed);

    let mut chv = OracleChallenger::new(b"b3-preimage-zk", oracle.clone());
    let ro = flock_prover::sim_oracle::ro_context(sim.proof.proof_nonce, oracle.clone());
    setup
        .verify_with_ro(&sim.commitment, &sim.proof, &digests, &ro, &mut chv)
        .expect("the UNMODIFIED verifier must accept the simulated proof");
}

/// Record every production-shape oracle call made by the simulator and
/// verifier. The artifact pins deterministic non-grinding counts; the
/// security ledger replaces the observed geometric PoW attempts with an
/// analytical 128-bit-tail budget.
#[test]
fn production_random_oracle_ledger_matches_artifact() {
    let setup = Blake3PreimageZkSetup::new(N_TEST);
    let secret = msgs_of(0xA11C_E5E5, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&secret);
    let sealed = SealedStatement::new(&setup, &digests).expect("public statement");
    let oracle = shared_oracle();
    let sim = simulate(
        &sealed,
        SimCoins::new(0x51A7_E001),
        &oracle,
        b"b3-preimage-zk",
    )
    .expect("simulate");
    assert_eq!(sim.programmed, 18);

    let prover_points = oracle.lock().unwrap().queries().to_vec();
    let prover = OracleQueryCounts::classify(&prover_points);
    let mut chv = OracleChallenger::new(b"b3-preimage-zk", oracle.clone());
    let ro = flock_prover::sim_oracle::ro_context(sim.proof.proof_nonce, oracle.clone());
    setup
        .verify_with_ro(&sim.commitment, &sim.proof, &digests, &ro, &mut chv)
        .expect("simulated proof verifies");
    let all_points = oracle.lock().unwrap().queries().to_vec();
    let verifier = OracleQueryCounts::classify(&all_points[prover_points.len()..]);
    assert_eq!(
        verifier.pow_candidates,
        flock_prover::sim_game::PRODUCTION_PCS_OPENINGS
            * flock_prover::sim_game::PRODUCTION_GRIND_BITS_PER_OPENING.len() as u64,
        "recorded verifier grind sites must match the production schedule",
    );

    println!("prover oracle counts: {prover:?}");
    println!("verifier oracle counts: {verifier:?}");
    let pow_bound = production_grinding_candidate_bound(128);
    let protocol_bound = prover.non_pow_calls() + pow_bound + verifier.total_calls;
    println!("pow candidate bound: {pow_bound}");
    println!("protocol query bound: {protocol_bound}");
    println!(
        "final zk bits: {:.15}",
        SimGameLedger::production(64, protocol_bound).final_bits()
    );

    let artifact: serde_json::Value = serde_json::from_str(include_str!(
        "../../../docs/artifacts/sim_game_error_table.json"
    ))
    .expect("game artifact");
    let pinned = &artifact["random_oracle_ledger"];
    assert_eq!(pinned["prover_total_calls"], prover.total_calls);
    assert_eq!(pinned["prover_non_pow_calls"], prover.non_pow_calls());
    assert_eq!(pinned["verifier_total_calls"], verifier.total_calls);
    assert_eq!(pinned["grinding_candidate_bound"], pow_bound);
    assert_eq!(pinned["protocol_query_bound"], protocol_bound);
}

/// **Control 1: the vector the simulator commits is not a witness.**
/// Overwriting the output region destroys the compression relation, so
/// the patched vector fails the R1CS — which is the whole reason the
/// zerocheck had to be simulated rather than run.
#[test]
fn the_simulators_committed_vector_is_not_a_valid_witness() {
    let n_log = 3usize;
    let r1cs = build_block_r1cs_pinned(n_log, ParamPinning::RootHash64);
    let own = msgs_of(0x1111, 1);
    let target = Blake3PreimageSetup::digests_of(&msgs_of(0x2222, 1));

    let mut all: Vec<Compression> = own.iter().map(message_compression).collect();
    all.resize(
        1usize << n_log,
        ParamPinning::RootHash64.padding_compression(),
    );
    let mut z = generate_witness(&all, n_log);
    assert!(r1cs.satisfies(&z), "the unpatched trace is a valid witness");

    // Patch out_lo of block 0 to the target digest.
    for w in 0..8usize {
        let word = u32::from_le_bytes(target[0][w * 4..w * 4 + 4].try_into().unwrap());
        for b in 0..32usize {
            z[256 + w * 32 + b] = (word >> b) & 1 == 1;
        }
    }
    assert!(
        !r1cs.satisfies(&z),
        "patching the output region must break the R1CS — otherwise the \
         simulator would not need to fabricate the zerocheck at all"
    );
}

/// **Measurement: how far is the simulated transcript from an honest one?**
///
/// Acceptance is necessary, not sufficient — a simulator whose output
/// verifies but is distributed differently is still a broken simulator.
/// This compares, coordinate by coordinate, a simulated proof against an
/// honest one for the same statement, and reports which classes differ
/// *structurally* (always, in a way a distinguisher could test) rather
/// than merely by value (as fresh randomness would).
///
/// It is a diagnostic, not a proof: it can find a discrepancy but cannot
/// certify the absence of one.
#[test]
#[ignore = "diagnostic; run explicitly"]
fn measure_simulated_vs_honest_transcript() {
    let setup = Blake3PreimageZkSetup::new(N_TEST);
    let secret = msgs_of(0xD1F_0001, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&secret);

    // Honest proof of the same statement (the party that knows the
    // preimages).
    let mut hrng = flock_core::zk::ZkRng::from_seed([21u8; 32]);
    let mut hch = FsChallenger::new(b"b3-preimage-zk");
    let (hproof, hcomm) = setup
        .prove(&secret, &digests, &mut hrng, &mut hch)
        .expect("honest prove");

    // Simulated proof of the same public statement.
    let sealed = SealedStatement::new(&setup, &digests).expect("public statement");
    let oracle = shared_oracle();
    let sim =
        simulate(&sealed, SimCoins::new(0xD1FF), &oracle, b"b3-preimage-zk").expect("simulate");

    let hv = algebraic_vector(&flatten_a1(&hcomm, &hproof));
    let sv = algebraic_vector(&flatten_a1(&sim.commitment, &sim.proof));
    assert_eq!(
        hv.len(),
        sv.len(),
        "simulated and honest transcripts must have the SAME SHAPE — a \
         length difference is a distinguisher on its own"
    );
    let differing = hv.iter().zip(&sv).filter(|(a, b)| a != b).count();
    println!(
        "transcript coordinates: {} total, {} differ by value \
         (fresh randomness makes near-total difference expected)",
        hv.len(),
        differing
    );
    // Same shape is the checkable invariant here; per-class distribution
    // equality needs the coverage certificates, not this diagnostic.
    assert!(
        differing > hv.len() / 2,
        "an almost-identical transcript would mean the simulator is \
         reproducing witness-dependent values, not masking them"
    );
}

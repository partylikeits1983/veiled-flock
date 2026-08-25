use super::*;
use crate::r1cs_hashes::{
    blake3::build_block_r1cs_zk,
    blake3_preimage::{Blake3PreimageZkSetup, MESSAGE_BYTES, absorb_statement},
};
use flock_core::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    proof::bind_statement,
    zk::{MaskSampler, ZkRng},
};

#[test]
fn succinct_shape_rejects_nonidentity_c() {
    let mut r1cs = build_block_r1cs_zk(3);
    assert!(MaskLayout::new(&r1cs).is_ok());
    r1cs.c_0.rows[0].clear();
    assert!(matches!(
        MaskLayout::new(&r1cs),
        Err(SuccinctVeilError::InvalidShape("R1CS mask geometry"))
    ));
}

#[test]
fn succinct_profile_validation_accepts_only_the_supported_circuit_and_pcs() {
    let setup = Blake3PreimageZkSetup::new_succinct(2);
    validate_succinct_parameters(&setup.r1cs, &setup.pcs_params)
        .expect("supported succinct profile");

    let unsupported_shape = Blake3PreimageZkSetup::new(2);
    assert!(matches!(
        validate_succinct_parameters(&unsupported_shape.r1cs, &unsupported_shape.pcs_params),
        Err(SuccinctVeilError::InvalidParameters)
    ));

    let mut modified_circuit = setup.r1cs.clone();
    modified_circuit.a_0.rows[0].push(0);
    assert!(matches!(
        validate_succinct_parameters(&modified_circuit, &setup.pcs_params),
        Err(SuccinctVeilError::InvalidParameters)
    ));

    let mut unsupported_pcs = setup.pcs_params.clone();
    unsupported_pcs.log_inv_rate = 2;
    assert!(matches!(
        validate_succinct_parameters(&setup.r1cs, &unsupported_pcs),
        Err(SuccinctVeilError::InvalidParameters)
    ));
}

fn sequence(start: u64, length: usize) -> Vec<F128> {
    (0..length)
        .map(|index| F128::new(start + index as u64, !(start + index as u64)))
        .collect()
}

fn flatten_masked_piop(zc: &MaskedZerocheckProof, lc: &LincheckProof) -> Vec<F128> {
    let mut values = Vec::new();
    values.extend_from_slice(&zc.round1_ab);
    values.extend_from_slice(&zc.round1_c);
    values.extend(
        zc.multilinear_rounds
            .iter()
            .flat_map(|(one, infinity)| [*one, *infinity]),
    );
    values.push(zc.final_a_eval);
    values.push(zc.final_b_eval);
    values.extend(
        lc.rounds
            .iter()
            .flat_map(|(one, infinity)| [*one, *infinity]),
    );
    values.extend_from_slice(&lc.z_partial);
    values
}

#[test]
fn mask_proof_wire_order_covers_every_observed_piop_value_once() {
    let r1cs = build_block_r1cs_zk(8);
    let layout = MaskLayout::new(&r1cs).unwrap();
    let honest_values = sequence(1, layout.observed_count());
    let masks = sequence(10_000, layout.observed_count());
    let mut cursor = 0;
    let mut take = |length: usize| {
        let values = honest_values[cursor..cursor + length].to_vec();
        cursor += length;
        values
    };
    let round1_ab = take(layout.ell);
    let round1_c = take(layout.ell);
    let zc_round_values = take(2 * layout.zc_rounds);
    let final_values = take(2);
    let lc_round_values = take(2 * layout.lc_rounds);
    let z_partial = take(layout.z_partial);
    assert_eq!(cursor, layout.observed_count());

    let honest_zc = ZerocheckProof {
        round1_ab,
        round1_c,
        multilinear_rounds: zc_round_values
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| (pair[0], pair[1]))
            .collect(),
        final_a_eval: final_values[0],
        final_b_eval: final_values[1],
        // `final_c_eval` is derived by the verifier and is not part of the
        // Fiat--Shamir transcript, so it has no corresponding mask.
        final_c_eval: F128::new(u64::MAX, u64::MAX),
    };
    let honest_lc = LincheckProof {
        rounds: lc_round_values
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| (pair[0], pair[1]))
            .collect(),
        z_partial,
    };
    let (masked_zc, masked_lc) = mask_proofs(&honest_zc, &honest_lc, &masks);
    let masked_values = flatten_masked_piop(&masked_zc, &masked_lc);
    assert_eq!(masked_values.len(), layout.observed_count());
    assert_eq!(
        masked_values,
        honest_values
            .iter()
            .zip(&masks)
            .map(|(value, mask)| *value + *mask)
            .collect::<Vec<_>>()
    );
}

#[test]
fn shifted_verifier_accepts_the_committed_mask_vector() {
    const DOMAIN: &[u8] = b"succinct-veil-shifted-equivalence-test";
    const SEED: [u8; 32] = [0x6D; 32];

    let setup = Blake3PreimageZkSetup::new_succinct(2);
    let messages = vec![
        std::array::from_fn::<_, MESSAGE_BYTES, _>(|index| index as u8),
        std::array::from_fn::<_, MESSAGE_BYTES, _>(|index| (255 - index) as u8),
    ];
    let digests = messages
        .iter()
        .map(|message| *blake3::hash(message).as_bytes())
        .collect::<Vec<_>>();
    let mut rng = ZkRng::from_seed(SEED);
    let mut prover = FsChallenger::new(DOMAIN);
    let (proof, commitment) = setup
        .prove_succinct(&messages, &digests, &mut rng, &mut prover)
        .expect("prove succinct VEIL");

    let statement = setup.statement(&digests);
    let mut replay = FsChallenger::new(DOMAIN);
    absorb_statement(&mut replay, &statement);
    bind_statement(&mut replay, &setup.r1cs, &commitment, &proof.proof_nonce);
    replay.observe_label(MASK_ROOT_LABEL);
    replay.observe_bytes(&proof.veil.linear.commitment);
    let (circuit, ab, c) = shifted_verifier_circuit(
        &setup.r1cs,
        &proof.masked_zerocheck,
        &proof.masked_lincheck,
        proof.ab_value,
        proof.c_value,
        setup.r1cs.csc_lincheck_circuit(),
        &mut replay,
    )
    .expect("construct shifted verifier");
    assert_eq!(ab.value, proof.ab_value);
    assert_eq!(c.value, proof.c_value);

    // Recreate the same domain-separated RNG forks used by `prove_succinct`.
    let mut replay_rng = ZkRng::from_seed(SEED);
    let _witness_randomizers = replay_rng.fork(b"succinct-preimage-witness-randomizers");
    let mut mask_rng = replay_rng.fork(b"succinct-veil-transcript-masks");
    let mut masks = vec![F128::ZERO; MaskLayout::new(&setup.r1cs).unwrap().observed_count()];
    mask_rng.fill_f128(&mut masks);
    assert!(
        circuit
            .is_satisfied(&masks)
            .expect("evaluate shifted circuit"),
        "the committed mask vector must satisfy the shifted verifier"
    );

    let mut verifier = FsChallenger::new(DOMAIN);
    setup
        .verify_succinct(&commitment, &proof, &digests, &mut verifier)
        .expect("verify succinct VEIL");
}

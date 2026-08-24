use super::{MaskLayout, SuccinctVeilError};
use crate::r1cs_hashes::blake3::build_block_r1cs_zk;

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

// -- ChainMaskShape (Part 7a) -----------------------------------------------

/// Pin keccak's (p, |S|) across the permitted batch range. `sized_for`
/// retunes move the pair; this test fails loudly instead of silently.
#[test]
fn chain_mask_shape_keccak_pinned_across_batch_range() {
    for n_log in [6usize, 8, 12, 19] {
        let layout = crate::r1cs_hashes::keccak::zk_layout(16 + n_log);
        let shape = super::ChainMaskShape::from_layout(&layout, 16);
        assert_eq!(shape.pair_index, 11, "n_log = {n_log}");
        assert_eq!(shape.s_coords, vec![0, 1, 3], "n_log = {n_log}");
        assert_eq!(shape.extra_rounds(), 3);
    }
}

/// Pin blake3's (p, |S|): its zk_config takes no m, so they are constants.
#[test]
fn chain_mask_shape_blake3_pinned() {
    let layout = crate::r1cs_hashes::blake3::zk_layout();
    let shape = super::ChainMaskShape::from_layout(&layout, 14);
    assert_eq!(shape.pair_index, 31);
    assert_eq!(shape.s_coords, vec![0, 1, 2, 3, 4]);
    assert_eq!(shape.extra_rounds(), 5);
}

#[test]
#[should_panic(expected = "chain-mask slot pair")]
fn chain_mask_shape_rejects_layout_without_pair() {
    let cfg = flock_core::zk::ZkConfig {
        rand_chunks_a: 1,
        rand_chunks_b: 1,
        chain_mask: false,
    };
    let layout = flock_core::zk::ZkBlockLayout::new(14, 1024, None, &cfg);
    let _ = super::ChainMaskShape::from_layout(&layout, 14);
}

/// The chain section is CONDITIONAL: absent, the layout is byte-identical
/// to the chainless one; present, observed_count grows by exactly
/// 2 * (n_log + 1 + |S|).
#[test]
fn mask_layout_chain_section_is_conditional() {
    let r1cs = crate::r1cs_hashes::keccak::build_block_r1cs_zk(6);
    let base = MaskLayout::new(&r1cs).expect("chainless layout");
    let same = MaskLayout::with_chain(&r1cs, None).expect("with_chain(None)");
    assert_eq!(base.observed_count(), same.observed_count());

    let zk = r1cs.zk.expect("zk r1cs carries a layout");
    let shape = super::ChainMaskShape::from_layout(&zk, r1cs.k_log);
    let chained = MaskLayout::with_chain(&r1cs, Some(&shape)).expect("chain layout");
    // n_log = 22 - 16 = 6; rounds = 6 + 1 + 3 = 10; two values per round.
    assert_eq!(
        chained.observed_count(),
        base.observed_count() + 2 * (6 + 1 + 3),
    );
}

// -- Succinct chain composition (Part 7c) -----------------------------------

/// Full succinct-chain round-trip on keccak at the m = 22 floor: honest
/// chain witness, endpoints-only public statement, in-circuit linkage.
/// Tampered endpoints and a tampered public chain value must reject.
#[test]
fn succinct_chain_roundtrip_and_tamper() {
    use crate::r1cs_hashes::keccak;
    use flock_core::challenger::FsChallenger;
    use flock_core::zk::MaskSampler;

    let n_log = 6usize;
    let n = 1usize << n_log;
    let r1cs = keccak::build_block_r1cs_zk(n_log);
    let pcs_params = flock_core::pcs::PcsParams {
        m: r1cs.m,
        log_inv_rate: 1,
        log_batch_size: 6,
        profile: flock_core::pcs::ligerito::LigeritoProfile::Fast,
        zk: true,
    };
    let layout = r1cs.zk.expect("zk r1cs");
    let shape = super::ChainMaskShape::from_layout(&layout, r1cs.k_log);

    // Honest chain: inputs[i + 1] = keccak_f(inputs[i]).
    let mut seed = 0x0501_7C3Au64;
    let mut next_bit = || {
        seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z & 1 == 1
    };
    let mut x0 = [false; keccak::STATE_BITS];
    for b in x0.iter_mut() {
        *b = next_bit();
    }
    let mut inputs = Vec::with_capacity(n);
    let mut cur = x0;
    for _ in 0..n {
        inputs.push(cur);
        keccak::keccak_f(&mut cur);
    }
    let x_last = cur;

    let mut rng = flock_core::zk::ZkRng::from_seed([0x77; 32]);
    let mut witness_rng = rng.fork(b"test-witness-randomizers");
    let mut rand_words =
        vec![0u64; n * crate::r1cs_hashes::common::zk_rand_words_per_block(&layout)];
    witness_rng.fill_u64s(&mut rand_words);
    let (z, a, b, z_lincheck) = keccak::generate_witness_with_ab_packed_and_lincheck_zk(
        &inputs,
        n_log,
        &layout,
        &rand_words,
    );

    let circuit =
        flock_core::lincheck::ZkLincheckCircuit::new(&keccak::KeccakLincheckCircuit, &layout);
    let lig_prover = flock_core::pcs::ligerito::prover_config_for(
        pcs_params.log_msg_len(),
        pcs_params.log_batch_size,
        pcs_params.profile,
    )
    .expect("m = 22 prover config");
    let lig_verifier = flock_core::pcs::ligerito::verifier_config_for(
        pcs_params.log_msg_len(),
        pcs_params.log_batch_size,
        pcs_params.profile,
    )
    .expect("m = 22 verifier config");

    let x0_phys = keccak::state_to_phys_bits(&x0);
    let xlast_phys = keccak::state_to_phys_bits(&x_last);

    let mut chp = FsChallenger::new(b"succinct-chain-test-v0");
    let (proof, commitment) = super::prove_succinct_chain_veil_r1cs(
        &r1cs,
        &pcs_params,
        z,
        a,
        b,
        z_lincheck,
        &circuit,
        &keccak::CHAIN_LAYOUT,
        &shape,
        &x0_phys,
        &xlast_phys,
        &lig_prover,
        &mut rng,
        &mut chp,
    )
    .expect("honest succinct chain prove");

    let mut chv = FsChallenger::new(b"succinct-chain-test-v0");
    super::verify_succinct_chain_veil_r1cs(
        &r1cs,
        &pcs_params,
        &proof,
        &commitment,
        &circuit,
        &keccak::CHAIN_LAYOUT,
        &shape,
        &x0_phys,
        &xlast_phys,
        &lig_verifier,
        &mut chv,
    )
    .expect("honest succinct chain verify");

    // Tampered x_last: one flipped endpoint bit must reject.
    let mut bad_xlast = xlast_phys.clone();
    bad_xlast[0] ^= true;
    let mut ch = FsChallenger::new(b"succinct-chain-test-v0");
    assert!(
        super::verify_succinct_chain_veil_r1cs(
            &r1cs,
            &pcs_params,
            &proof,
            &commitment,
            &circuit,
            &keccak::CHAIN_LAYOUT,
            &shape,
            &x0_phys,
            &bad_xlast,
            &lig_verifier,
            &mut ch,
        )
        .is_err(),
        "tampered x_last must reject",
    );

    // Tampered x_0.
    let mut bad_x0 = x0_phys.clone();
    bad_x0[7] ^= true;
    let mut ch = FsChallenger::new(b"succinct-chain-test-v0");
    assert!(
        super::verify_succinct_chain_veil_r1cs(
            &r1cs,
            &pcs_params,
            &proof,
            &commitment,
            &circuit,
            &keccak::CHAIN_LAYOUT,
            &shape,
            &bad_x0,
            &xlast_phys,
            &lig_verifier,
            &mut ch,
        )
        .is_err(),
        "tampered x_0 must reject",
    );

    // Tampered public chain value: the PCS must catch the mismatch.
    let mut bad_proof = proof.clone();
    bad_proof.chain_value += flock_core::field::F128::ONE;
    let mut ch = FsChallenger::new(b"succinct-chain-test-v0");
    assert!(
        super::verify_succinct_chain_veil_r1cs(
            &r1cs,
            &pcs_params,
            &bad_proof,
            &commitment,
            &circuit,
            &keccak::CHAIN_LAYOUT,
            &shape,
            &x0_phys,
            &xlast_phys,
            &lig_verifier,
            &mut ch,
        )
        .is_err(),
        "tampered chain value must reject",
    );

    // Tampered masked chain round message.
    let mut bad_proof = proof.clone();
    bad_proof.masked_chain.rounds[0].0 += flock_core::field::F128::ONE;
    let mut ch = FsChallenger::new(b"succinct-chain-test-v0");
    assert!(
        super::verify_succinct_chain_veil_r1cs(
            &r1cs,
            &pcs_params,
            &bad_proof,
            &commitment,
            &circuit,
            &keccak::CHAIN_LAYOUT,
            &shape,
            &x0_phys,
            &xlast_phys,
            &lig_verifier,
            &mut ch,
        )
        .is_err(),
        "tampered chain round message must reject",
    );
}

/// Chain-value mask coverage (Part 7e, scoped audit): the chain claim's eq
/// weight on the mask-pair words is nonzero, so the pair's committed
/// uniform bits one-time-pad the opened value. One nonzero F128
/// coefficient `c` suffices: `{c * basis_b}` over the 128 field basis
/// elements spans F128 over F2, so a single mask WORD with nonzero weight
/// makes `chain_value` uniform. The JOINT uniformity of
/// (ab_value, c_value, chain_value) over the shared pool remains a
/// certification-scope audit — the path is EXPERIMENTAL and uncertified.
#[test]
fn chain_value_has_nonzero_mask_pair_weight() {
    use flock_core::zerocheck::multilinear::eq_eval;
    let layout = crate::r1cs_hashes::keccak::zk_layout(22);
    let shape = super::ChainMaskShape::from_layout(&layout, 16);
    let chain_layout = &crate::r1cs_hashes::keccak::CHAIN_LAYOUT;
    let fold = crate::r1cs_hashes::chain_common::ChainFold::new(
        chain_layout,
        (0..chain_layout.tau_pos_len())
            .map(|i| flock_core::field::F128 {
                lo: 0x1111 * (i as u64 + 3),
                hi: 0x7,
            })
            .collect(),
    );
    // Pseudo-random bound challenges standing in for the FS transcript.
    let claims = crate::chain::ChainClaimsExt {
        instance_point: (0..6)
            .map(|i| flock_core::field::F128 {
                lo: 0xABCD + i as u64,
                hi: 0x99,
            })
            .collect(),
        sel0: flock_core::field::F128 { lo: 0x5, hi: 0x1 },
        s_high: (0..shape.extra_rounds())
            .map(|i| flock_core::field::F128 {
                lo: 0xF0F0 + i as u64,
                hi: 0x3,
            })
            .collect(),
        value: flock_core::field::F128::ZERO,
    };
    let point = crate::r1cs_hashes::chain_common::build_chain_claim_point_ext(
        chain_layout,
        flock_core::r1cs::WitnessLayout::RowMajor,
        &fold,
        &claims,
        &shape.s_coords,
    );
    assert_eq!(point.len(), 22 - 7);

    // First word of the mask pair's IN slot, instance 0 (RowMajor):
    // within-block word index = pair_index * 2 * words_per_region.
    let words_per_region = 1usize << chain_layout.tau_pos_len();
    let word = shape.pair_index * 2 * words_per_region;
    let word_bits: Vec<flock_core::field::F128> = (0..point.len())
        .map(|j| {
            if (word >> j) & 1 == 1 {
                flock_core::field::F128::ONE
            } else {
                flock_core::field::F128::ZERO
            }
        })
        .collect();
    let weight = eq_eval(&point, &word_bits);
    assert_ne!(
        weight,
        flock_core::field::F128::ZERO,
        "the chain claim must reach the mask pair",
    );
}

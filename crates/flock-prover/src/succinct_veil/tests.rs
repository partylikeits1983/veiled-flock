use super::{
    MaskLayout, RING_WIDTH, SuccinctVeilError, certify_flock_piop_soundness,
    certify_shifted_veil_soundness, scale_ring_expressions, solve_sumcheck_messages,
    validate_batch_opening, validate_l0_hiding_budget, validate_succinct_parameters,
};
use crate::r1cs_hashes::blake3::build_block_r1cs_zk;
use crate::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup;
use flock_core::field::F128;
use veil_f128::LinearCombination;

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
fn production_entry_point_is_pinned_to_the_certified_relation_and_secure_pcs() {
    let setup = Blake3PreimageZkSetup::new(2);
    assert!(super::supported_mask_count(&setup.r1cs).is_some());
    validate_succinct_parameters(&setup.r1cs, &setup.pcs_params).unwrap();
    let piop = certify_flock_piop_soundness(&setup.r1cs, setup.r1cs.csc_lincheck_circuit())
        .expect("production PIOP soundness certificate");
    assert_eq!(piop.friendly_coordinate_rank_f2, 7);
    assert!(piop.bits() > 119.0);
    assert!(piop.bits() < 121.0);
    let veil = certify_shifted_veil_soundness(&setup.r1cs).unwrap();
    assert!(veil.bits() > 100.0);
    assert!(veil.bits() < 110.0);

    let mut wrong_relation = setup.r1cs.clone();
    wrong_relation.a_0.rows[0].push(0);
    assert_eq!(
        validate_succinct_parameters(&wrong_relation, &setup.pcs_params),
        Err(SuccinctVeilError::InvalidParameters)
    );

    let mut wrong_profile = setup.pcs_params.clone();
    wrong_profile.profile = flock_core::pcs::ligerito::LigeritoProfile::Fast;
    assert_eq!(
        validate_succinct_parameters(&setup.r1cs, &wrong_profile),
        Err(SuccinctVeilError::InvalidParameters)
    );
}

#[test]
fn every_registered_batch_shape_has_checked_mask_and_soundness_parameters() {
    for (blocks, m, masks) in [
        (256, 22, 754),
        (512, 23, 756),
        (1024, 24, 758),
        (2048, 25, 760),
    ] {
        let setup = Blake3PreimageZkSetup::new(blocks);
        assert_eq!(setup.r1cs.m, m);
        assert_eq!(super::supported_mask_count(&setup.r1cs), Some(masks));
        validate_succinct_parameters(&setup.r1cs, &setup.pcs_params).unwrap();
        assert_eq!(
            MaskLayout::new(&setup.r1cs).unwrap().observed_count(),
            masks
        );
        assert!(
            certify_flock_piop_soundness(&setup.r1cs, setup.r1cs.csc_lincheck_circuit())
                .unwrap()
                .bits()
                > 110.0
        );
        assert!(certify_shifted_veil_soundness(&setup.r1cs).unwrap().bits() > 100.0);
    }
}

#[test]
fn production_mask_layout_matches_every_visible_private_coordinate() {
    let r1cs = build_block_r1cs_zk(8);
    let layout = MaskLayout::new(&r1cs).unwrap();
    assert_eq!(layout.piop_count(), 242);
    assert_eq!(2 * super::RING_CLAIM_COUNT * RING_WIDTH, 512);
    assert_eq!(layout.observed_count(), 754);

    let shifted = layout.shifted_circuit_certificate(true);
    assert_eq!(shifted.private_inputs, 754);
    assert_eq!(shifted.flock_multiplications, 1);
    assert_eq!(shifted.lincheck_linear_constraints, 1);
    assert_eq!(shifted.ring_scale_linear_constraints, 2 * RING_WIDTH);
    assert_eq!(shifted.ring_claim_linear_constraints, 2);
    assert_eq!(shifted.linear_constraints(), 259);
}

#[test]
fn l0_hiding_budget_fails_closed_above_the_mask_dimension() {
    let params = flock_core::pcs::PcsParams {
        m: 22,
        log_inv_rate: 1,
        log_batch_size: 6,
        profile: flock_core::pcs::ligerito::LigeritoProfile::Secure,
        zk: true,
    };
    assert!(validate_l0_hiding_budget(&params, &[512]).is_ok());
    validate_batch_opening(&params, &[512], &[0], &[1]).unwrap();
    assert!(matches!(
        validate_l0_hiding_budget(&params, &[513]),
        Err(SuccinctVeilError::InvalidShape("L0 hiding query budget"))
    ));
    assert!(matches!(
        validate_batch_opening(&params, &[512], &[1], &[1]),
        Err(SuccinctVeilError::InvalidShape("bounded grinding schedule"))
    ));
    assert!(matches!(
        validate_batch_opening(
            &params,
            &[512],
            &[0],
            &[super::MAX_LIGERITO_GRINDING_BITS + 1]
        ),
        Err(SuccinctVeilError::InvalidShape("bounded grinding schedule"))
    ));
}

#[test]
fn ring_constraint_map_matches_packed_field_scaling() {
    let slices = (0..RING_WIDTH)
        .map(|i| F128::new(i as u64 * 0x9e37 + 1, (i as u64).rotate_left(17)))
        .collect::<Vec<_>>();
    let scalar = F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let expressions = (0..RING_WIDTH)
        .map(LinearCombination::variable)
        .collect::<Vec<_>>();
    let evaluated = scale_ring_expressions(&expressions, scalar)
        .iter()
        .map(|expression| expression.evaluate(&slices).unwrap())
        .collect::<Vec<_>>();

    assert_eq!(
        evaluated,
        flock_core::pcs::ring_switch::scale_s_hat_v(&slices, scalar)
    );
}

#[test]
fn simulator_sumcheck_solve_preserves_uniform_zero_and_one_challenges() {
    let running = F128::new(0x1234, 0x5678);
    let target = F128::new(0x9abc, 0xdef0);
    let random_g1 = F128::new(11, 12);
    let random_g_inf = F128::new(13, 14);
    for (r_eq, rho) in [
        (F128::new(9, 0), F128::ZERO),
        (F128::ZERO, F128::ONE),
        (F128::new(9, 0), F128::ONE),
        (F128::new(9, 0), F128::new(7, 0)),
    ] {
        let (g1, g_inf) =
            solve_sumcheck_messages(running, target, r_eq, rho, random_g1, random_g_inf)
                .expect("non-identity round is solvable");
        let weights = flock_core::zerocheck::sumcheck_round_weights(r_eq, rho).unwrap();
        assert_eq!(
            weights[0] * running + weights[1] * g1 + weights[2] * g_inf,
            target
        );
    }

    assert!(matches!(
        solve_sumcheck_messages(
            running,
            target,
            F128::ZERO,
            F128::ZERO,
            random_g1,
            random_g_inf,
        ),
        Err(SuccinctVeilError::DegenerateSimulation)
    ));
}

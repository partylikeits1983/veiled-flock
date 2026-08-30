#![cfg(feature = "symbolic")]

use flock_core::field::F128;
use flock_core::linalg::F128Mat;
use flock_core::pcs::commit::PcsParams;
use flock_core::pcs::ligerito::{LigeritoProfile, ProverConfig, prover_config_for};
use flock_core::pcs::symbolic_opening::{
    certify_l0_query_rank, encode_zk_linear, l0_entropy_bound, translate_joint_view_for_queries,
    translate_mask_for_queries,
};
use flock_core::zerocheck::univariate_skip::build_eq;

fn tiny_params() -> PcsParams {
    PcsParams {
        m: 13,
        log_inv_rate: 1,
        log_batch_size: 2,
        profile: LigeritoProfile::Fast,
        zk: true,
    }
}

fn tiny_config() -> ProverConfig {
    ProverConfig {
        log_inv_rates: vec![1, 2, 3],
        recursive_steps: 2,
        initial_log_msg_cols: 5,
        initial_log_num_interleaved: 2,
        initial_k: 2,
        recursive_log_msg_cols: vec![3, 1],
        recursive_ks: vec![2, 2],
        queries: vec![6, 4, 4],
        grinding_bits: vec![0; 3],
        fold_grinding_bits: vec![0; 3],
        ood_samples: vec![0; 3],
    }
}

fn rank_test_params() -> PcsParams {
    PcsParams {
        m: 9,
        log_inv_rate: 1,
        log_batch_size: 0,
        profile: LigeritoProfile::Fast,
        zk: true,
    }
}

fn low_mask_evaluation_matrix(params: &PcsParams, queries: &[usize]) -> F128Mat {
    let witness_slots = 1usize << params.witness_log_msg_len();
    let mask_symbols = witness_slots / params.num_ntts();
    assert_eq!(params.num_ntts(), 1, "test helper is single-lane");
    let zero_witness = vec![F128::ZERO; witness_slots];
    let zero_blinder = vec![F128::ZERO; 2 * witness_slots];
    let mut data = vec![F128::ZERO; queries.len() * mask_symbols];
    for column in 0..mask_symbols {
        let mut mask = vec![F128::ZERO; witness_slots];
        mask[column] = F128::ONE;
        let encoded = encode_zk_linear(params, &mask, &zero_witness, &zero_blinder);
        for (row, &query) in queries.iter().enumerate() {
            data[row * mask_symbols + column] = encoded[query * 2];
        }
    }
    F128Mat::new(queries.len(), mask_symbols, data)
}

#[test]
fn structural_l0_rank_certificate_matches_actual_ntt_on_every_small_query_set() {
    let params = rank_test_params();
    let domain = params.n_positions();
    let mask_symbols = (1usize << params.witness_log_msg_len()) / params.num_ntts();
    assert_eq!((domain, mask_symbols), (16, 4));

    for subset in 0usize..(1usize << domain) {
        if subset.count_ones() as usize > mask_symbols {
            continue;
        }
        let queries = (0..domain)
            .filter(|index| (subset >> index) & 1 == 1)
            .collect::<Vec<_>>();
        let certificate = certify_l0_query_rank(&params, &queries)
            .expect("every distinct query set below the dimension is certified");
        assert_eq!(certificate.opened_positions, queries.len());
        assert_eq!(certificate.mask_symbols_per_lane, mask_symbols);
        assert_eq!(
            low_mask_evaluation_matrix(&params, &queries).rank(),
            queries.len(),
            "actual additive-NTT matrix disagrees for {queries:?}"
        );
    }

    assert!(certify_l0_query_rank(&params, &[1, 1]).is_none());
    assert!(certify_l0_query_rank(&params, &[domain]).is_none());
    assert!(certify_l0_query_rank(&params, &[0, 1, 2, 3, 4]).is_none());
}

#[test]
fn closed_form_translation_preserves_open_rows_and_combined_vector() {
    let params = tiny_params();
    let w = 1usize << params.witness_log_msg_len();
    let point = (0..params.witness_log_msg_len())
        .map(|index| F128::new(0x8123 + index as u64, 0x9917 * (index as u64 + 1)))
        .collect::<Vec<_>>();
    let basis = build_eq(&point);
    assert!(basis.iter().all(|value| *value != F128::ZERO));
    let mut delta = vec![F128::ZERO; w];
    delta[0] = basis[0].inv();
    delta[17] = basis[17].inv();
    assert_eq!(
        delta
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (value, weight)| acc + *value * *weight),
        F128::ZERO,
        "test direction must preserve the public opening claim"
    );

    let c = F128::new(0xd1ce_cafe_1234_5678, 0x900d_f00d_7766_5544);
    let queries = [1, 7, 11, 22, 39, 55];
    let translation = translate_joint_view_for_queries(&params, c, &queries, &delta, &[&basis])
        .expect("the complete L0/direct-functional view must be jointly translatable");
    for index in 0..w {
        assert_eq!(
            translation.delta_mu[index] + c * translation.delta_g_lo[index],
            F128::ZERO
        );
        assert_eq!(
            delta[index] + c * translation.delta_g_top[index],
            F128::ZERO
        );
    }
    assert_eq!(
        translation
            .delta_g_top
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (value, weight)| acc + *value * *weight),
        F128::ZERO,
        "the public-functional blinder value is invariant under the coupling"
    );

    let delta_g = translation
        .delta_g_lo
        .iter()
        .chain(&translation.delta_g_top)
        .copied()
        .collect::<Vec<_>>();
    let encoded = encode_zk_linear(&params, &translation.delta_mu, &delta, &delta_g);
    let wide = 2 * params.num_ntts();
    for query in queries {
        assert!(
            encoded[query * wide..(query + 1) * wide]
                .iter()
                .all(|value| *value == F128::ZERO)
        );
    }
    assert!(translate_mask_for_queries(&params, F128::ZERO, &queries, &delta).is_none());
    let mut non_public_basis = basis.clone();
    non_public_basis[0] += F128::ONE;
    assert!(
        translate_joint_view_for_queries(&params, c, &queries, &delta, &[&non_public_basis])
            .is_none(),
        "a witness-private direct functional must fail closed"
    );
}

#[test]
fn l0_entropy_counting_gate_holds_for_fixture_and_production() {
    let tiny = tiny_params();
    let tiny_cfg = tiny_config();
    let tiny_bound = l0_entropy_bound(&tiny, tiny_cfg.queries[0]).unwrap();
    assert_eq!(tiny_bound.mask_symbols_per_lane, 16);
    assert_eq!(tiny_bound.conditional_bits_per_fresh_leaf, 1024);

    let production = PcsParams {
        m: 22,
        log_inv_rate: 1,
        log_batch_size: 6,
        profile: LigeritoProfile::Secure,
        zk: true,
    };
    let config = prover_config_for(
        production.log_msg_len(),
        production.log_batch_size,
        production.profile,
    )
    .expect("production Ligerito profile must be registered");
    let bound = l0_entropy_bound(&production, config.queries[0])
        .expect("production L0 queries must fit below the mask subcode dimension");
    assert_eq!(bound.mask_symbols_per_lane, 512);
    assert!(bound.conditional_bits_per_fresh_leaf >= 128);
    let representative_queries = (0..config.queries[0]).collect::<Vec<_>>();
    let rank_certificate = certify_l0_query_rank(&production, &representative_queries)
        .expect("every registered distinct query set must satisfy the structural rank criterion");
    assert_eq!(rank_certificate.opened_positions, 294);
    assert_eq!(rank_certificate.mask_symbols_per_lane, 512);
    assert_eq!(bound.opened_positions, 294);
    assert_eq!(bound.conditional_bits_per_fresh_leaf, 16_384);
}

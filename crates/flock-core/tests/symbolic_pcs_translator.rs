#![cfg(feature = "symbolic")]

use flock_core::field::F128;
use flock_core::pcs::commit::PcsParams;
use flock_core::pcs::ligerito::{LigeritoProfile, ProverConfig, prover_config_for};
use flock_core::pcs::symbolic_opening::{
    OPENING_FUNCTIONAL_MANIFEST, encode_zk_linear, l0_entropy_bound, translate_mask_for_queries,
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
    let translation = translate_mask_for_queries(&params, c, &queries, &delta)
        .expect("the L0 query equations must be solvable");
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
        profile: LigeritoProfile::Fast,
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

    let manifest: serde_json::Value = serde_json::from_str(include_str!(
        "../../../docs/artifacts/s3_opening_functionals.json"
    ))
    .unwrap();
    let entries = manifest["functionals"].as_array().unwrap();
    assert_eq!(entries.len(), OPENING_FUNCTIONAL_MANIFEST.len());
    for (pinned, current) in entries.iter().zip(OPENING_FUNCTIONAL_MANIFEST) {
        assert_eq!(pinned["proof_path"], current.proof_path);
        assert_eq!(pinned["category"], current.category);
        assert_eq!(pinned["disposition"], current.disposition);
    }

    let entropy: serde_json::Value = serde_json::from_str(include_str!(
        "../../../docs/artifacts/s3_minentropy_table.json"
    ))
    .unwrap();
    assert_eq!(
        entropy["profiles"][0]["conditional_bits_per_fresh_leaf"],
        1024
    );
    assert_eq!(
        entropy["profiles"][1]["conditional_bits_per_fresh_leaf"],
        bound.conditional_bits_per_fresh_leaf
    );
}

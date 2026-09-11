//! Compare the public ZK and non-ZK BLAKE3-preimage APIs.
//! Reports medians after one warm-up. Timings exclude setup and serialization;
//! sizes count proof objects only. Both configurations target the same composed
//! interactive soundness floor; the non-ZK default is unchanged.

use std::time::{Duration, Instant};

use flock_core::challenger::FsChallenger;
use flock_core::pcs::ligerito::{
    LigeritoSecurityConfig, ProverConfig, VerifierConfig, embedded_security_config,
};
use flock_prover::r1cs_hashes::blake3_preimage::{
    Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES,
};

const SOUNDNESS_BITS: usize = 100;
const SIZES: [usize; 7] = [64, 128, 256, 512, 1024, 2048, 4096];
const FLOCK_BENCHMARK_DOMAIN: &[u8] = b"flock-blake3-preimage-scaling";

#[derive(Clone, Copy)]
struct Sample {
    prove: Duration,
    verify: Duration,
    proof_bytes: usize,
}

fn main() {
    flock_prover::init_perf_thread_pool();
    let mut args = std::env::args().skip(1);
    let samples = args
        .next()
        .map(|value| {
            value
                .parse::<usize>()
                .expect("sample count must be a positive integer")
        })
        .unwrap_or(5);
    assert!(samples > 0, "sample count must be positive");
    let selected_size = args.next().map(|value| {
        let size = value.parse::<usize>().expect("size must be an integer");
        assert!(SIZES.contains(&size), "unsupported benchmark size");
        size
    });
    assert!(
        args.next().is_none(),
        "usage: preimage_scaling [samples] [size]"
    );

    println!(
        "hashes,protocol,prove_ms_median,verify_ms_median,proof_bytes_median,proof_bytes_min,proof_bytes_max"
    );
    for size in SIZES {
        if selected_size.is_none_or(|selected| selected == size) {
            benchmark_size(size, samples);
        }
    }
}

fn benchmark_size(size: usize, samples: usize) {
    let messages = messages(size);
    let digests = Blake3PreimageSetup::digests_of(&messages);

    let zk = Blake3PreimageZkSetup::new(size);
    let zk_bound = zk.interactive_soundness_bound().expect("ZK composed bound");
    assert!(zk_bound.bits() >= SOUNDNESS_BITS as f64);
    let mut flock = Blake3PreimageSetup::new(size);
    // The ZK PIOP ledger conservatively covers the smaller non-ZK circuit,
    // including its ring/direct claim batching and public digest check.
    assert!(flock.r1cs.m <= zk.r1cs.m && flock.r1cs.k_log <= zk.r1cs.k_log);
    let piop_probability = zk_bound.flock_piop_probability + zk_bound.digest_binding_probability;
    let security = matched_flock_config(&mut flock, piop_probability);
    let pcs_bound = security
        .aggregate_soundness_bound()
        .expect("FLOCK PCS bound");
    eprintln!(
        "{size} hashes: FLOCK PCS {:.6}, composed {:.6} bits; ZK PCS {:.6}, composed {:.6} bits; FLOCK queries {:?}, fold grinding {:?}",
        pcs_bound.bits(),
        -(pcs_bound.probability() + piop_probability).log2(),
        zk.ligerito_aggregate_soundness_bits()
            .expect("ZK PCS bound"),
        zk_bound.bits(),
        security
            .levels
            .iter()
            .map(|level| level.queries)
            .collect::<Vec<_>>(),
        security
            .levels
            .iter()
            .map(|level| level.fold_grinding_bits)
            .collect::<Vec<_>>(),
    );
    let (prover_config, verifier_config) =
        security.to_prover_verifier_configs().expect("PCS configs");
    let _warm_up = sample_flock(
        &flock,
        &messages,
        &digests,
        &prover_config,
        &verifier_config,
    );
    let _warm_up = sample_zk(&zk, &messages, &digests);
    let mut flock_samples = Vec::with_capacity(samples);
    let mut zk_samples = Vec::with_capacity(samples);
    for i in 0..samples {
        let mut run_flock = || {
            flock_samples.push(sample_flock(
                &flock,
                &messages,
                &digests,
                &prover_config,
                &verifier_config,
            ))
        };
        let mut run_zk = || zk_samples.push(sample_zk(&zk, &messages, &digests));
        if i % 2 == 0 {
            run_flock();
            run_zk();
        } else {
            run_zk();
            run_flock();
        }
    }
    print_samples(size, "FLOCK-non-ZK", &mut flock_samples);
    print_samples(size, "VEIL-FLOCK-full-ZK", &mut zk_samples);
}

fn matched_flock_config(
    setup: &mut Blake3PreimageSetup,
    piop_probability: f64,
) -> LigeritoSecurityConfig {
    loop {
        let mut config = if let Some(source) =
            embedded_security_config(setup.pcs_params.m, setup.pcs_params.profile)
        {
            LigeritoSecurityConfig::from_toml_str(source).expect("FLOCK registered schedule")
        } else {
            LigeritoSecurityConfig::derive_paper_compatible_with_interleaving(
                setup.pcs_params.m,
                setup.pcs_params.log_batch_size,
                setup.pcs_params.profile.log_inv_rate(),
                SOUNDNESS_BITS,
            )
            .expect("small-batch FLOCK schedule")
        };
        assert_eq!(config.initial_k, setup.pcs_params.log_batch_size);
        config.target_security_bits = SOUNDNESS_BITS;
        for level in &mut config.levels {
            level.target_security_bits = SOUNDNESS_BITS;
            level.fold_grinding_bits = (SOUNDNESS_BITS as f64 - level.paper_predicted_bits().0)
                .ceil()
                .max(0.0) as usize;
        }
        let bound = config
            .aggregate_soundness_bound()
            .expect("initial PCS bound");
        let query_budget = (2f64.powi(-(SOUNDNESS_BITS as i32))
            - piop_probability
            - bound.proximity_probability
            - bound.ood_probability)
            / config.levels.len() as f64;
        assert!(query_budget > 0.0);
        for level in &mut config.levels {
            let per_query_bits = level.paper_predicted_bits().1 / level.queries as f64;
            level.queries = (-query_budget.log2() / per_query_bits).ceil() as usize;
            level.expected_eps_query_bits = level.paper_predicted_bits().1;
        }
        if config
            .levels
            .iter()
            .any(|level| level.queries > 1usize << (level.log_msg_cols + level.log_inv_rate))
        {
            // A smaller interleaving leaves enough distinct rows for small batches.
            assert!(setup.pcs_params.log_batch_size > 0);
            setup.pcs_params.log_batch_size -= 1;
            continue;
        }
        let composed = config
            .aggregate_soundness_bound()
            .expect("matched PCS bound")
            .probability()
            + piop_probability;
        assert!(-composed.log2() >= SOUNDNESS_BITS as f64);
        return config;
    }
}

fn sample_flock(
    setup: &Blake3PreimageSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
    prover_config: &ProverConfig,
    verifier_config: &VerifierConfig,
) -> Sample {
    let mut prover_challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove_with_pcs_config(messages, digests, prover_config, &mut prover_challenger)
        .expect("non-ZK FLOCK proof generation");
    let prove = started.elapsed();

    let mut verifier_challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    setup
        .verify_with_pcs_config(
            &commitment,
            &proof,
            digests,
            verifier_config,
            &mut verifier_challenger,
        )
        .expect("non-ZK FLOCK verification");
    let verify = started.elapsed();

    let proof_bytes =
        bincode::serialized_size(&proof).expect("serialize non-ZK FLOCK proof") as usize;
    Sample {
        prove,
        verify,
        proof_bytes,
    }
}

fn sample_zk(
    setup: &Blake3PreimageZkSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
) -> Sample {
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove(messages, digests)
        .expect("full-ZK VEIL-FLOCK proof generation");
    let prove = started.elapsed();

    let started = Instant::now();
    setup
        .verify(&commitment, &proof, digests)
        .expect("full-ZK VEIL-FLOCK verification");
    let verify = started.elapsed();

    let proof_bytes = bincode::serialized_size(&proof).expect("serialize full-ZK proof") as usize;
    Sample {
        prove,
        verify,
        proof_bytes,
    }
}

fn print_samples(size: usize, protocol: &str, samples: &mut [Sample]) {
    samples.sort_unstable_by_key(|sample| sample.prove);
    let prove = samples[samples.len() / 2].prove.as_secs_f64() * 1000.0;
    samples.sort_unstable_by_key(|sample| sample.verify);
    let verify = samples[samples.len() / 2].verify.as_secs_f64() * 1000.0;
    samples.sort_unstable_by_key(|sample| sample.proof_bytes);
    let proof_bytes = samples[samples.len() / 2].proof_bytes;

    println!(
        "{size},{protocol},{prove:.3},{verify:.3},{proof_bytes},{},{}",
        samples.first().expect("at least one sample").proof_bytes,
        samples.last().expect("at least one sample").proof_bytes,
    );
}

fn messages(size: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    (0..size)
        .map(|message_index| {
            std::array::from_fn(|byte_index| {
                let word = (message_index as u64)
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .rotate_left((byte_index % 64) as u32)
                    ^ byte_index as u64;
                word as u8
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matched_schedules_reach_composed_floor_and_fit_their_codewords() {
        for size in SIZES {
            let zk = Blake3PreimageZkSetup::new(size);
            let bound = zk.interactive_soundness_bound().unwrap();
            let piop = bound.flock_piop_probability + bound.digest_binding_probability;
            let mut flock = Blake3PreimageSetup::new(size);
            let original = flock.pcs_params.clone();
            let config = matched_flock_config(&mut flock, piop);
            let composed = config.aggregate_soundness_bound().unwrap().probability() + piop;
            assert!((-composed.log2()) >= SOUNDNESS_BITS as f64);
            assert!((-composed.log2()) < SOUNDNESS_BITS as f64 + 1.0);
            assert_eq!(flock.pcs_params.profile, original.profile);
            for level in &config.levels {
                assert!(level.queries <= 1 << (level.log_msg_cols + level.log_inv_rate));
            }
            if let Some(source) = embedded_security_config(original.m, original.profile) {
                let stock = LigeritoSecurityConfig::from_toml_str(source).unwrap();
                let (mut stock_prover, _) = stock.to_prover_verifier_configs().unwrap();
                let (matched_prover, _) = config.to_prover_verifier_configs().unwrap();
                stock_prover.queries.clone_from(&matched_prover.queries);
                stock_prover
                    .fold_grinding_bits
                    .clone_from(&matched_prover.fold_grinding_bits);
                assert_eq!(stock_prover, matched_prover);
                assert_eq!(flock.pcs_params.log_batch_size, original.log_batch_size);
            }
        }
    }

    #[test]
    fn matched_proof_requires_the_selected_verifier_schedule() {
        let size = 256;
        let zk = Blake3PreimageZkSetup::new(size);
        let bound = zk.interactive_soundness_bound().unwrap();
        let mut setup = Blake3PreimageSetup::new(size);
        let config = matched_flock_config(
            &mut setup,
            bound.flock_piop_probability + bound.digest_binding_probability,
        );
        let (prover, verifier) = config.to_prover_verifier_configs().unwrap();
        let messages = messages(size);
        let digests = Blake3PreimageSetup::digests_of(&messages);
        let (proof, commitment) = setup
            .prove_with_pcs_config(
                &messages,
                &digests,
                &prover,
                &mut FsChallenger::new(FLOCK_BENCHMARK_DOMAIN),
            )
            .unwrap();
        setup
            .verify_with_pcs_config(
                &commitment,
                &proof,
                &digests,
                &verifier,
                &mut FsChallenger::new(FLOCK_BENCHMARK_DOMAIN),
            )
            .unwrap();
        assert!(
            setup
                .verify(
                    &commitment,
                    &proof,
                    &digests,
                    &mut FsChallenger::new(FLOCK_BENCHMARK_DOMAIN),
                )
                .is_err()
        );
    }
}

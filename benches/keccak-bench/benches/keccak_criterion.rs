//! Criterion stage-timing target for the cheap keccak stages.
//! Scope, run command, e2e divergences: `benches/keccak-bench/README.md`.

use std::time::Duration;

use criterion::{BatchSize, Criterion, SamplingMode, criterion_group, criterion_main};

use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::keccak::{KeccakSetup, KeccakZkSetup};
use flock_prover::zk::ZkRng;
use keccak_bench::{
    CHAIN_SEED, DOMAIN, ZK_SEED, chain_outputs, keccak_honest_chain, verify_state_linkage,
};

/// Witness generation at the smoke shape. The bit-level `keccak_f` makes this
/// ms-scale: ~1.5 ms/iter needs 8 s, not criterion's default 5 s window.
fn witness(c: &mut Criterion) {
    // Idempotent, and required in every group: without it criterion would
    // measure a default rayon pool while the e2e bin measures the perf pool.
    flock_prover::init_perf_thread_pool();
    let mut group = c.benchmark_group("witness");
    group.measurement_time(Duration::from_secs(8));
    group.bench_function("keccak_honest_chain/n=64", |b| {
        // Large-drop variant: the returned Vec teardown stays outside the
        // timed window, matching time_best's hygiene.
        b.iter_with_large_drop(|| keccak_honest_chain(64, CHAIN_SEED))
    });
    group.finish();
}

/// Native chain verify on one hoisted proof at n = 64. A FRESH challenger per
/// iteration is mandatory: verify consumes the Fiat–Shamir transcript.
fn verify_native(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let setup = KeccakSetup::new(64);
    let (inputs, x0, x_last) = keccak_honest_chain(64, CHAIN_SEED);
    let (proof, commitment) = {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup.prove_chain(&inputs, &mut challenger)
    };
    let mut group = c.benchmark_group("verify-native");
    group.bench_function("n=64", |b| {
        b.iter_batched(
            || FsChallenger::new(DOMAIN),
            |mut challenger| {
                setup
                    .verify_chain(&commitment, &proof, &x0, &x_last, &mut challenger)
                    .expect("native chain verify of a hoisted proof")
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

/// Succinct public-chain verify at n = 64, linkage check included — matching the
/// e2e `verify` column. DELIBERATE divergence from blake3; see the crate README.
fn verify_succinct(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let setup = KeccakZkSetup::new(64);
    let (inputs, _x0, x_last) = keccak_honest_chain(64, CHAIN_SEED);
    let outputs = chain_outputs(&inputs, &x_last);
    let (proof, commitment) = {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct(&inputs, &outputs, &mut rng, &mut challenger)
            .expect("succinct prove on an honest witness")
    };
    let mut group = c.benchmark_group("verify-succinct");
    group.bench_function("n=64", |b| {
        b.iter_batched(
            || FsChallenger::new(DOMAIN),
            |mut challenger| {
                setup
                    .verify_succinct(&commitment, &proof, &inputs, &outputs, &mut challenger)
                    .expect("succinct verify of a hoisted proof");
                assert!(verify_state_linkage(&inputs, &outputs), "public linkage");
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

/// Succinct chain verify (in-circuit linkage) on one hoisted proof at
/// n = 64. Endpoints only — no linkage recompute exists to include.
fn verify_succinct_chain(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let setup = KeccakZkSetup::new(64);
    let (inputs, x0, x_last) = keccak_honest_chain(64, CHAIN_SEED);
    let (proof, commitment) = {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct_chain(&inputs, &mut rng, &mut challenger)
            .expect("succinct chain prove on an honest witness")
    };
    let mut group = c.benchmark_group("verify-succinct-chain");
    group.bench_function("n=64", |b| {
        b.iter_batched(
            || FsChallenger::new(DOMAIN),
            |mut challenger| {
                setup
                    .verify_succinct_chain(&commitment, &proof, &x0, &x_last, &mut challenger)
                    .expect("succinct chain verify of a hoisted proof")
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

/// Succinct chain prove, ONE shape at n = 64. Reuses a hoisted setup: WARM-setup
/// steady-state, not the e2e `prove` column. `Flat` + `sample_size(10)`.
fn prove_succinct_chain(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let setup = KeccakZkSetup::new(64);
    let (inputs, _x0, _x_last) = keccak_honest_chain(64, CHAIN_SEED);
    let mut group = c.benchmark_group("prove-succinct-chain");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(5));
    group.bench_function("n=64", |b| {
        b.iter_batched(
            || (ZkRng::from_seed(ZK_SEED), FsChallenger::new(DOMAIN)),
            |(mut rng, mut challenger)| {
                setup
                    .prove_succinct_chain(&inputs, &mut rng, &mut challenger)
                    .expect("succinct chain prove on an honest witness")
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

criterion_group!(
    benches,
    witness,
    verify_native,
    verify_succinct,
    verify_succinct_chain,
    prove_succinct_chain
);
criterion_main!(benches);

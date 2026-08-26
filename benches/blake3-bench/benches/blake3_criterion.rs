//! Criterion stage-timing target for the cheap BLAKE3 stages.
//! Scope, run command, e2e divergences: `benches/blake3-bench/README.md`.

use std::time::Duration;

use criterion::{BatchSize, Criterion, SamplingMode, criterion_group, criterion_main};

use blake3_bench::{CHAIN_SEED, DOMAIN, ZK_SEED, blake3_chain};
use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup;
use flock_prover::veiled_preimage::VeiledBlake3Setup;
use flock_prover::zk::ZkRng;

/// Witness generation at the 256-slot succinct floor. µs-scale.
fn witness(c: &mut Criterion) {
    // Idempotent, and required in every group: without it criterion would
    // measure a default rayon pool while the e2e bin measures the perf pool.
    flock_prover::init_perf_thread_pool();
    let mut group = c.benchmark_group("witness");
    group.bench_function("blake3_chain/n=256", |b| {
        // Large-drop variant: the returned (Vec, Vec) teardown stays
        // outside the timed window, matching time_best's hygiene.
        b.iter_with_large_drop(|| blake3_chain(256, CHAIN_SEED))
    });
    group.finish();
}

/// Framed verify on one hoisted proof at n = 2. A FRESH challenger per iteration
/// is mandatory; times the circuit verify ONLY, so it is not the e2e `verify`.
fn verify_framed(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let setup = VeiledBlake3Setup::new(2);
    let (messages, digests) = blake3_chain(2, CHAIN_SEED);
    let proof = {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove(&messages, &digests, &mut rng, &mut challenger)
            .expect("framed prove on an honest witness")
    };
    let mut group = c.benchmark_group("verify-framed");
    // ~80 ms/iter measured: the default 5 s window cannot hold 100 samples.
    // 9 s buys headroom against criterion's own drifting 8.1 s suggestion.
    group.measurement_time(Duration::from_secs(9));
    group.bench_function("n=2", |b| {
        b.iter_batched(
            || FsChallenger::new(DOMAIN),
            |mut challenger| {
                setup
                    .verify(&proof, &digests, &mut challenger)
                    .expect("framed verify of a hoisted proof")
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

/// Succinct verify on one hoisted (commitment, proof) pair at n = 256. Circuit
/// verify ONLY — not the e2e `verify` column (~0.4% difference at n = 256).
fn verify_succinct(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let setup = Blake3PreimageZkSetup::new_succinct(256);
    let (messages, digests) = blake3_chain(256, CHAIN_SEED);
    let (proof, commitment) = {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct(&messages, &digests, &mut rng, &mut challenger)
            .expect("succinct prove on an honest witness")
    };
    let mut group = c.benchmark_group("verify-succinct");
    group.bench_function("n=256", |b| {
        b.iter_batched(
            || FsChallenger::new(DOMAIN),
            |mut challenger| {
                setup
                    .verify_succinct(&commitment, &proof, &digests, &mut challenger)
                    .expect("succinct verify of a hoisted proof")
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

/// Succinct prove, ONE shape at the 256-slot floor (n = 64 and n = 256 pad to the
/// SAME shape). WARM-setup steady-state, not the e2e `prove`. `Flat`, 10 samples.
fn prove_succinct(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let setup = Blake3PreimageZkSetup::new_succinct(256);
    let (messages, digests) = blake3_chain(256, CHAIN_SEED);
    let mut group = c.benchmark_group("prove-succinct");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(5));
    group.bench_function("n=256", |b| {
        b.iter_batched(
            || (ZkRng::from_seed(ZK_SEED), FsChallenger::new(DOMAIN)),
            |(mut rng, mut challenger)| {
                setup
                    .prove_succinct(&messages, &digests, &mut rng, &mut challenger)
                    .expect("succinct prove on an honest witness")
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

criterion_group!(
    benches,
    witness,
    verify_framed,
    verify_succinct,
    prove_succinct
);
criterion_main!(benches);

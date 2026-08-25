//! Criterion stage-timing target for the cheap keccak stages.
//!
//! Criterion COMPLEMENTS the e2e bin, it does not replace it: the e2e
//! rows are multi-metric records (four timed sections, proof size,
//! params, cross-row slowdown) with an end-to-end verify gate, which
//! criterion's single-metric closures cannot express. Only stages with
//! cheap iterations run here — witness generation, the three verifies,
//! and one succinct-chain prove shape. The native chain prove and the
//! succinct public-chain prove stay in the e2e bin: their expensive
//! iterations gain nothing from criterion's 10-sample floor.
//!
//! Run: `cargo bench -p keccak-bench -- --save-baseline <name>`.
//!
//! Every group calls `init_perf_thread_pool()` first (idempotent):
//! without it, criterion would measure a default-sized rayon pool while
//! the e2e bin measures the perf pool, and baselines would drift.

use std::time::Duration;

use criterion::{BatchSize, Criterion, SamplingMode, criterion_group, criterion_main};

use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::keccak::{KeccakSetup, KeccakZkSetup};
use flock_prover::zk::ZkRng;
use keccak_bench::{chain_outputs, keccak_honest_chain, verify_state_linkage};

// Mirrors of the e2e consts (src/keccak.rs). Each group proves and
// verifies with its own copies, so the values only need to agree within
// this target; they match the e2e ones to keep artifacts comparable.
const DOMAIN: &[u8] = b"veiled-flock-bench-keccak-e2e-v0";
const CHAIN_SEED: u64 = 0xC0FFEE_43;
const ZK_SEED: [u8; 32] = [0x43; 32];

/// Witness generation at the smoke shape.
///
/// The bit-level `keccak_f` makes this ms-scale (unlike blake3's µs-scale
/// witness): ~1.5 ms/iter needs more than the default 5 s window for 100
/// linear samples. 8 s fits (criterion's own suggestion).
fn witness(c: &mut Criterion) {
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

/// Native chain verify on one hoisted proof at n = 64.
///
/// A FRESH challenger per iteration is mandatory: verify consumes the
/// Fiat–Shamir transcript, so a reused challenger fails from iteration 2.
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

/// Succinct public-chain verify on one hoisted proof at n = 64.
///
/// The `verify_state_linkage` equality check comes along, exactly as in
/// the e2e verify closure — with every state public it is part of the
/// measured relation (and it is noise-level next to the circuit verify).
/// DELIBERATE divergence from blake3's criterion convention: blake3's
/// verify groups time the circuit verify ONLY and exclude the linkage
/// recompute (a real hash per link there); this group matches the e2e
/// `verify` column instead, because keccak's linkage check is a pure
/// equality.
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

/// Succinct chain prove: ONE shape at n = 64 (the smoke shape; chain
/// setups fill their slots, so every n is its own shape).
///
/// Like the blake3 prove group, this reuses one hoisted setup, so it
/// measures the WARM-setup steady-state prove; the e2e row pays any lazy
/// first-prove cost. Do not compare this number against the e2e `prove`
/// column.
///
/// Sampling: `Flat` + `sample_size(10)` keeps the iteration count fixed
/// per sample. A criterion "unable to complete N samples" warning here
/// is a config error to fix, not a pass.
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

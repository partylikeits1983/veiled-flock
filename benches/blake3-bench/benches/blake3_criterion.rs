//! Criterion stage-timing target for the cheap BLAKE3 stages.
//!
//! Criterion COMPLEMENTS the e2e bin, it does not replace it: the e2e
//! rows are multi-metric records (four timed sections, proof size,
//! params, cross-row slowdown) with an end-to-end verify gate, which
//! criterion's single-metric closures cannot express. Only stages with
//! cheap iterations run here — witness generation, framed verify,
//! succinct verify, and one succinct prove shape. The framed prove stays
//! in the e2e bin: its multi-second iterations gain nothing from
//! criterion's 10-sample floor.
//!
//! Run: `cargo bench -p blake3-bench -- --save-baseline <name>`.
//!
//! Every group calls `init_perf_thread_pool()` first (idempotent):
//! without it, criterion would measure a default-sized rayon pool while
//! the e2e bin measures the perf pool, and baselines would drift.

use std::time::Duration;

use criterion::{BatchSize, Criterion, SamplingMode, criterion_group, criterion_main};

use blake3_bench::blake3_chain;
use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup;
use flock_prover::veiled_preimage::VeiledBlake3Setup;
use flock_prover::zk::ZkRng;

// Mirrors of the e2e consts (src/blake3.rs). Each group proves and
// verifies with its own copies, so the values only need to agree within
// this target; they match the e2e ones to keep artifacts comparable.
const DOMAIN: &[u8] = b"veiled-flock-bench-blake3-e2e-v0";
const CHAIN_SEED: u64 = 0xC0FFEE_42;
const ZK_SEED: [u8; 32] = [0x42; 32];

/// Witness generation at the 256-slot succinct floor. µs-scale.
fn witness(c: &mut Criterion) {
    flock_prover::init_perf_thread_pool();
    let mut group = c.benchmark_group("witness");
    group.bench_function("blake3_chain/n=256", |b| {
        // Large-drop variant: the returned (Vec, Vec) teardown stays
        // outside the timed window, matching time_best's hygiene.
        b.iter_with_large_drop(|| blake3_chain(256, CHAIN_SEED))
    });
    group.finish();
}

/// Framed verify on one hoisted proof at n = 2.
///
/// A FRESH challenger per iteration is mandatory: verify consumes the
/// Fiat–Shamir transcript, so a reused challenger fails from iteration 2.
///
/// Unlike the e2e `verify` column, this group times the circuit verify
/// ONLY — the public chain-linkage recompute (`verify_chain_linkage`)
/// stays out, so the two numbers are slightly different statistics.
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
    // ~80 ms/iter measured: the default 5 s window cannot hold 100
    // samples and criterion warns. 8 s fit when this landed, then a
    // ~79-80 ms/iter run nudged criterion's own suggestion to 8.1 s —
    // 9 s buys headroom against that drift.
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

/// Succinct verify on one hoisted (commitment, proof) pair at n = 256.
///
/// Like `verify_framed`, this times the circuit verify ONLY — no
/// chain-linkage recompute — so do not read it as the e2e `verify`
/// column (~0.4% difference at n = 256).
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

/// Succinct prove: ONE shape at the 256-slot floor. (n = 64 and n = 256
/// resolve to the SAME padded shape — never give them separate IDs.)
///
/// MEASURED SEMANTIC (2026-08-25): this group reuses one hoisted setup,
/// so it measures the WARM-setup steady-state prove — ~15 ms/iter. The
/// first prove on a fresh setup pays a lazy one-time cost (~0.4 s) and
/// that is what the e2e row reports; both proofs verify (checked). Do
/// not compare this number against the e2e `prove` column.
///
/// Sampling: `Flat` + `sample_size(10)` keeps the iteration count fixed
/// per sample. A criterion "unable to complete N samples" warning here
/// is a config error to fix, not a pass.
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

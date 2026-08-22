//! Apples-to-apples benchmark for the fixed-digest BLAKE3-64 relation.
//!
//! Both modes prove the same ordered batch of public digests. `flock` uses
//! the regular zerocheck/lincheck/Ligerito pipeline; `zk-flock` keeps a hiding
//! Ligerito witness opening and applies native-F128 VEIL only to FLOCK's small
//! algebraic verifier transcript. Setup and witness generation inputs are
//! shared, while prove/verify wall time and complete serialized proof size are
//! measured separately.

use std::time::Instant;

use flock_core::challenger::FsChallenger;
use flock_prover::{
    proof_io::R1csProofBundleLigerito,
    r1cs_hashes::blake3_preimage::{Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES},
    zk::ZkRng,
};

const FLOCK_DOMAIN: &[u8] = b"veil-vs-flock-benchmark-flock-v0";
const VEIL_DOMAIN: &[u8] = b"veil-vs-flock-benchmark-veil-v1";

#[derive(Clone, Copy)]
struct Measurement {
    prove_s: f64,
    verify_s: f64,
    proof_bytes: usize,
}

fn messages(batch: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    (0..batch)
        .map(|item| {
            std::array::from_fn(|byte| {
                (item as u64)
                    .wrapping_mul(131)
                    .wrapping_add((byte as u64).wrapping_mul(17)) as u8
            })
        })
        .collect()
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(f64::total_cmp);
    values[values.len() / 2]
}

fn median_usize(values: &mut [usize]) -> usize {
    values.sort_unstable();
    values[values.len() / 2]
}

fn bench_flock(
    setup: &Blake3PreimageSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
    runs: usize,
) -> Measurement {
    let mut prove_times = Vec::with_capacity(runs);
    let mut verify_times = Vec::with_capacity(runs);
    let mut proof_sizes = Vec::with_capacity(runs);
    for run in 0..=runs {
        let mut prover = FsChallenger::new(FLOCK_DOMAIN);
        let started = Instant::now();
        let (proof, commitment) = setup.prove(messages, digests, &mut prover).unwrap();
        let prove_s = started.elapsed().as_secs_f64();

        let mut verifier = FsChallenger::new(FLOCK_DOMAIN);
        let started = Instant::now();
        setup
            .verify(&commitment, &proof, digests, &mut verifier)
            .unwrap();
        let verify_s = started.elapsed().as_secs_f64();
        let proof_bytes = R1csProofBundleLigerito { commitment, proof }
            .to_bytes()
            .len();

        // The first pass warms code, allocations, and thread pools.
        if run > 0 {
            prove_times.push(prove_s);
            verify_times.push(verify_s);
            proof_sizes.push(proof_bytes);
        }
    }
    Measurement {
        prove_s: median(&mut prove_times),
        verify_s: median(&mut verify_times),
        proof_bytes: median_usize(&mut proof_sizes),
    }
}

fn bench_veil(
    setup: &Blake3PreimageZkSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
    runs: usize,
) -> Measurement {
    let mut prove_times = Vec::with_capacity(runs);
    let mut verify_times = Vec::with_capacity(runs);
    let mut proof_sizes = Vec::with_capacity(runs);
    for run in 0..=runs {
        let mut rng = ZkRng::from_seed([run as u8 + 1; 32]);
        let mut prover = FsChallenger::new(VEIL_DOMAIN);
        let started = Instant::now();
        let (proof, commitment) = setup
            .prove_succinct(messages, digests, &mut rng, &mut prover)
            .unwrap();
        let prove_s = started.elapsed().as_secs_f64();

        let mut verifier = FsChallenger::new(VEIL_DOMAIN);
        let started = Instant::now();
        setup
            .verify_succinct(&commitment, &proof, digests, &mut verifier)
            .unwrap();
        let verify_s = started.elapsed().as_secs_f64();
        let proof_bytes = bincode::serialize(&(commitment, proof)).unwrap().len();

        if run > 0 {
            prove_times.push(prove_s);
            verify_times.push(verify_s);
            proof_sizes.push(proof_bytes);
        }
    }
    Measurement {
        prove_s: median(&mut prove_times),
        verify_s: median(&mut verify_times),
        proof_bytes: median_usize(&mut proof_sizes),
    }
}

fn main() {
    flock_prover::init_perf_thread_pool();
    let batch = std::env::var("VEIL_BENCH_BATCH")
        .map_or(256, |value| value.parse().expect("VEIL_BENCH_BATCH"));
    let runs =
        std::env::var("VEIL_BENCH_RUNS").map_or(3, |value| value.parse().expect("VEIL_BENCH_RUNS"));
    assert!(batch > 0 && runs > 0);

    let messages = messages(batch);
    let digests = messages
        .iter()
        .map(|message| *blake3::hash(message).as_bytes())
        .collect::<Vec<_>>();
    let flock_setup = Blake3PreimageSetup::new(batch);
    let veil_setup = Blake3PreimageZkSetup::new(batch);

    let flock = bench_flock(&flock_setup, &messages, &digests, runs);
    let veil = bench_veil(&veil_setup, &messages, &digests, runs);
    println!("fixed-digest BLAKE3-64, batch {batch}, median of {runs}");
    println!("mode\tprove_s\tverify_s\tproof_bytes");
    println!(
        "flock\t{:.6}\t{:.6}\t{}",
        flock.prove_s, flock.verify_s, flock.proof_bytes
    );
    println!(
        "zk-flock\t{:.6}\t{:.6}\t{}",
        veil.prove_s, veil.verify_s, veil.proof_bytes
    );
    println!(
        "overhead\t{:.2}x\t{:.2}x\t{:.2}x",
        veil.prove_s / flock.prove_s,
        veil.verify_s / flock.verify_s,
        veil.proof_bytes as f64 / flock.proof_bytes as f64
    );
}

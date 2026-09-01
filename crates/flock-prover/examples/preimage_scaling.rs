//! Reproducible release benchmark for the pinned 64-byte BLAKE3-preimage
//! relation.
//!
//! Compares full-ZK VEIL-FLOCK with non-ZK FLOCK using the Secure Ligerito
//! profile. Setup construction, message generation, digest generation, and
//! serialization are excluded from the prove/verify timings; checks performed
//! by the public prove APIs remain included. One untimed warm-up precedes the
//! reported median samples.

use std::time::{Duration, Instant};

use flock_core::challenger::FsChallenger;
use flock_prover::{
    proof_io::{R1csProofBundleLigerito, VeilFlockProofBundle},
    r1cs_hashes::blake3_preimage::{Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES},
};

const SIZES: [usize; 7] = [64, 128, 256, 512, 1024, 2048, 4096];
const FLOCK_BENCHMARK_DOMAIN: &[u8] = b"flock-blake3-preimage-scaling";

#[derive(Clone, Copy)]
struct Sample {
    prove: Duration,
    verify: Duration,
    bundle_bytes: usize,
}

fn main() {
    flock_prover::init_perf_thread_pool();
    let samples = std::env::args()
        .nth(1)
        .map(|value| {
            value
                .parse::<usize>()
                .expect("sample count must be a positive integer")
        })
        .unwrap_or(5);
    assert!(samples > 0, "sample count must be positive");

    println!(
        "hashes,protocol,prove_ms_median,verify_ms_median,bundle_bytes_median,bundle_bytes_min,bundle_bytes_max"
    );
    for size in SIZES {
        benchmark_size(size, samples);
    }
}

fn benchmark_size(size: usize, samples: usize) {
    let messages = messages(size);
    let digests = Blake3PreimageSetup::digests_of(&messages);

    let flock = Blake3PreimageSetup::new(size);
    let _warm_up = sample_flock(&flock, &messages, &digests);
    let mut flock_samples = (0..samples)
        .map(|_| sample_flock(&flock, &messages, &digests))
        .collect::<Vec<_>>();
    print_samples(size, "FLOCK-non-ZK-Secure", &mut flock_samples);
    drop(flock);

    let zk = Blake3PreimageZkSetup::new(size).expect("valid ZK setup");
    let _warm_up = sample_zk(&zk, &messages, &digests);
    let mut zk_samples = (0..samples)
        .map(|_| sample_zk(&zk, &messages, &digests))
        .collect::<Vec<_>>();
    print_samples(size, "VEIL-FLOCK-full-ZK", &mut zk_samples);
}

fn sample_flock(
    setup: &Blake3PreimageSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
) -> Sample {
    let mut prover_challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove(messages, digests, &mut prover_challenger)
        .expect("non-ZK FLOCK proof generation");
    let prove = started.elapsed();

    let mut verifier_challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    setup
        .verify(&commitment, &proof, digests, &mut verifier_challenger)
        .expect("non-ZK FLOCK verification");
    let verify = started.elapsed();

    let bundle_bytes = R1csProofBundleLigerito { commitment, proof }
        .to_bytes()
        .len();
    Sample {
        prove,
        verify,
        bundle_bytes,
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

    let bundle_bytes = VeilFlockProofBundle::new(digests.to_vec(), commitment, proof)
        .to_bytes()
        .expect("serialize full-ZK bundle")
        .len();
    Sample {
        prove,
        verify,
        bundle_bytes,
    }
}

fn print_samples(size: usize, protocol: &str, samples: &mut [Sample]) {
    samples.sort_unstable_by_key(|sample| sample.prove);
    let prove = samples[samples.len() / 2].prove.as_secs_f64() * 1000.0;
    samples.sort_unstable_by_key(|sample| sample.verify);
    let verify = samples[samples.len() / 2].verify.as_secs_f64() * 1000.0;
    samples.sort_unstable_by_key(|sample| sample.bundle_bytes);
    let bundle_bytes = samples[samples.len() / 2].bundle_bytes;

    println!(
        "{size},{protocol},{prove:.3},{verify:.3},{bundle_bytes},{},{}",
        samples.first().expect("at least one sample").bundle_bytes,
        samples.last().expect("at least one sample").bundle_bytes,
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

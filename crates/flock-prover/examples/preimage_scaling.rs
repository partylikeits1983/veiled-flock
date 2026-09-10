//! Reproducible release benchmark for the pinned 64-byte BLAKE3-preimage
//! relation.
//!
//! With `--features experimental-zk`, pass `--experimental-100` after the
//! sample count to benchmark the opt-in rate-1/8, 100-bit schedule instead.
//!
//! By default, compares full-ZK VEIL-FLOCK with non-ZK FLOCK. Both select the Secure
//! Ligerito profile at rate 1/2. The full-ZK path uses registered configs;
//! non-ZK batches below the registry floor use ad hoc configs. Full-ZK
//! batches below 256 hashes are padded to 256 slots. Sizes count serialized
//! proof objects, excluding commitments, public digests, and bundle framing.
//! Setup construction, message
//! generation, digest generation, and serialization are excluded from the
//! prove/verify timings; checks performed by the public prove APIs remain
//! included. One untimed warm-up precedes the reported median samples.

use std::time::{Duration, Instant};

use flock_core::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3_preimage::{
    Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES,
};

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
    let experimental = match args.next().as_deref() {
        None => false,
        Some("--experimental-100") => true,
        Some(_) => panic!("usage: preimage_scaling [samples] [--experimental-100]"),
    };
    assert!(args.next().is_none(), "unexpected extra argument");
    assert!(
        !experimental || cfg!(feature = "experimental-zk"),
        "--experimental-100 requires --features experimental-zk"
    );

    println!(
        "hashes,protocol,prove_ms_median,verify_ms_median,proof_bytes_median,proof_bytes_min,proof_bytes_max"
    );
    for size in SIZES {
        benchmark_size(size, samples, experimental);
    }
}

fn benchmark_size(size: usize, samples: usize, experimental: bool) {
    let messages = messages(size);
    let digests = Blake3PreimageSetup::digests_of(&messages);

    let flock = Blake3PreimageSetup::new(size);
    let _warm_up = sample_flock(&flock, &messages, &digests);
    let mut flock_samples = (0..samples)
        .map(|_| sample_flock(&flock, &messages, &digests))
        .collect::<Vec<_>>();
    print_samples(size, "FLOCK-non-ZK-Secure", &mut flock_samples);
    drop(flock);

    let zk = if experimental {
        #[cfg(feature = "experimental-zk")]
        {
            Blake3PreimageZkSetup::experimental_100_bit(size)
        }
        #[cfg(not(feature = "experimental-zk"))]
        {
            unreachable!("experimental flag rejected before benchmarking")
        }
    } else {
        Blake3PreimageZkSetup::new(size)
    };
    if experimental {
        eprintln!(
            "{size} hashes: PCS {:.6} bits; composed interactive {:.6} bits",
            zk.ligerito_aggregate_soundness_bits().expect("PCS bound"),
            zk.interactive_soundness_bound()
                .expect("composed bound")
                .bits()
        );
    }
    let _warm_up = sample_zk(&zk, &messages, &digests);
    let mut zk_samples = (0..samples)
        .map(|_| sample_zk(&zk, &messages, &digests))
        .collect::<Vec<_>>();
    print_samples(
        size,
        if experimental {
            "VEIL-FLOCK-experimental-ZK100"
        } else {
            "VEIL-FLOCK-full-ZK"
        },
        &mut zk_samples,
    );
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

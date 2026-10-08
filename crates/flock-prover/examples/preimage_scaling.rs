//! Release benchmark and explicit overhead gate for the pinned BLAKE3 relation.
//!
//! Both protocols select Secure PCS parameters at rate 1/2. Only registered
//! power-of-two shapes at or above 256 hashes are eligible for the gate.
//! Setup, input generation and serialization are excluded from timing; public
//! prove API checks are included. Each proof is verified. After warming both
//! protocols, sample order alternates to reduce systematic order bias.

use std::{
    process::ExitCode,
    time::{Duration, Instant},
};

use flock_core::{challenger::FsChallenger, pcs::ligerito::LigeritoProof};
use flock_prover::{
    proof_io::{R1csProofBundleLigerito, VeilFlockProofBundle},
    r1cs_hashes::blake3_preimage::{Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES},
};

const SIZES: [usize; 7] = [64, 128, 256, 512, 1024, 2048, 4096];
const FLOCK_BENCHMARK_DOMAIN: &[u8] = b"flock-blake3-preimage-scaling";
const USAGE: &str = "preimage_scaling [samples] [--sizes 256,1024,4096] [--check-targets]\n\
    --check-targets requires <=10% median proving-time overhead and <=12%\n\
    maximum sampled proof-transport overhead for every selected shape.\n\
    Select shapes >=256 for this check. Public digests are reported separately.";

#[derive(Debug, PartialEq, Eq)]
struct Options {
    samples: usize,
    sizes: Vec<usize>,
    check_targets: bool,
}

impl Options {
    fn parse(arguments: impl IntoIterator<Item = String>) -> Result<Self, String> {
        let mut result = Self {
            samples: 5,
            sizes: SIZES.to_vec(),
            check_targets: false,
        };
        let mut arguments = arguments.into_iter().peekable();
        if arguments
            .peek()
            .is_some_and(|value| !value.starts_with('-'))
        {
            result.samples = arguments
                .next()
                .unwrap()
                .parse()
                .map_err(|_| USAGE.to_owned())?;
        }
        while let Some(argument) = arguments.next() {
            match argument.as_str() {
                "--sizes" => {
                    result.sizes = arguments
                        .next()
                        .ok_or(USAGE)?
                        .split(',')
                        .map(|value| value.parse::<usize>().map_err(|_| USAGE.to_owned()))
                        .collect::<Result<Vec<_>, _>>()?;
                }
                "--check-targets" => result.check_targets = true,
                _ => return Err(USAGE.to_owned()),
            }
        }
        if result.samples == 0
            || result.sizes.is_empty()
            || result.sizes.iter().any(|size| !SIZES.contains(size))
            || (result.check_targets && result.sizes.iter().any(|size| *size < 256))
        {
            return Err(USAGE.to_owned());
        }
        Ok(result)
    }
}

#[derive(Clone, Copy, Default)]
struct Sample {
    prove: Duration,
    verify: Duration,
    proof_bytes: usize,
    proof_transport_bytes: usize,
    pcs_bytes: usize,
    veil_bytes: usize,
    transcript_bytes: usize,
    l0_rows_bytes: usize,
}

struct Summary {
    prove: Duration,
    max_transport_bytes: usize,
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let options = Options::parse(std::env::args().skip(1))?;
    flock_prover::init_perf_thread_pool();
    eprintln!(
        "samples={}, threads={}, proving_target=10%, proof_size_target=12%",
        options.samples,
        rayon::current_num_threads()
    );
    println!(
        "hashes,protocol,prove_ms_median,verify_ms_median,proof_bytes_median,proof_bytes_min,proof_bytes_max,proof_transport_bytes_median,proof_transport_bytes_max,public_statement_bytes,l0_rows_bytes,pcs_bytes,veil_bytes,transcript_bytes"
    );
    let mut passed = true;
    for size in options.sizes {
        let (flock, zk) = benchmark_size(size, options.samples);
        let meets = targets_met(&flock, &zk);
        eprintln!(
            "hashes={size}, prove_overhead={:.2}%, proof_size_overhead={:.2}%, targets={}",
            100.0 * (zk.prove.as_secs_f64() / flock.prove.as_secs_f64() - 1.0),
            100.0 * (zk.max_transport_bytes as f64 / flock.max_transport_bytes as f64 - 1.0),
            if size < 256 {
                "not-comparable"
            } else if meets {
                "pass"
            } else {
                "fail"
            }
        );
        passed &= meets;
    }
    if options.check_targets && !passed {
        return Err("overhead targets not met".to_owned());
    }
    Ok(())
}

fn benchmark_size(size: usize, samples: usize) -> (Summary, Summary) {
    let messages = messages(size);
    let digests = Blake3PreimageSetup::digests_of(&messages);
    let flock = Blake3PreimageSetup::new(size);
    let zk = Blake3PreimageZkSetup::new(size);
    if size >= 256 {
        assert_eq!(
            flock.r1cs.m, zk.r1cs.m,
            "benchmark circuit dimensions must match"
        );
    }
    let _ = sample_flock(&flock, &messages, &digests);
    let _ = sample_zk(&zk, &messages, &digests);
    let mut flock_samples = Vec::with_capacity(samples);
    let mut zk_samples = Vec::with_capacity(samples);
    for index in 0..samples {
        if index % 2 == 0 {
            flock_samples.push(sample_flock(&flock, &messages, &digests));
            zk_samples.push(sample_zk(&zk, &messages, &digests));
        } else {
            zk_samples.push(sample_zk(&zk, &messages, &digests));
            flock_samples.push(sample_flock(&flock, &messages, &digests));
        }
    }
    (
        print_samples(size, "FLOCK-non-ZK-Secure", &mut flock_samples),
        print_samples(size, "VEIL-FLOCK-full-ZK", &mut zk_samples),
    )
}

fn serialized_size(value: &impl serde::Serialize) -> usize {
    bincode::serialized_size(value).expect("serialize proof component") as usize
}

fn l0_rows_bytes(proof: &LigeritoProof) -> usize {
    proof
        .initial_proof
        .opened_rows
        .iter()
        .map(|row| row.len() * 16)
        .sum()
}

fn sample_flock(
    setup: &Blake3PreimageSetup,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; 32]],
) -> Sample {
    let mut challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    let (proof, commitment) = setup
        .prove(messages, digests, &mut challenger)
        .expect("non-ZK proof generation");
    let prove = started.elapsed();
    let mut challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
    let started = Instant::now();
    setup
        .verify(&commitment, &proof, digests, &mut challenger)
        .expect("non-ZK verification");
    let verify = started.elapsed();
    let proof_bytes = serialized_size(&proof);
    let pcs_bytes = serialized_size(&proof.pcs_open);
    let l0_rows_bytes = l0_rows_bytes(&proof.pcs_open.ligerito);
    let proof_transport_bytes = R1csProofBundleLigerito { commitment, proof }
        .to_bytes()
        .len();
    Sample {
        prove,
        verify,
        proof_bytes,
        proof_transport_bytes,
        pcs_bytes,
        veil_bytes: 0,
        transcript_bytes: proof_bytes - pcs_bytes,
        l0_rows_bytes,
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
        .expect("full-ZK proof generation");
    let prove = started.elapsed();
    let started = Instant::now();
    setup
        .verify(&commitment, &proof, digests)
        .expect("full-ZK verification");
    let verify = started.elapsed();
    let proof_bytes = serialized_size(&proof);
    let pcs_bytes = serialized_size(&proof.pcs_open);
    let veil_bytes = serialized_size(&proof.veil);
    let l0_rows_bytes = l0_rows_bytes(&proof.pcs_open.ligerito);
    let public_statement_bytes = serialized_size(&digests.to_vec());
    let proof_transport_bytes = VeilFlockProofBundle::new(digests.to_vec(), commitment, proof)
        .to_bytes()
        .expect("serialize ZK bundle")
        .len()
        - public_statement_bytes;
    Sample {
        prove,
        verify,
        proof_bytes,
        proof_transport_bytes,
        pcs_bytes,
        veil_bytes,
        transcript_bytes: proof_bytes - pcs_bytes - veil_bytes,
        l0_rows_bytes,
    }
}

fn print_samples(size: usize, protocol: &str, samples: &mut [Sample]) -> Summary {
    samples.sort_unstable_by_key(|sample| sample.prove);
    let prove = samples[samples.len() / 2].prove;
    samples.sort_unstable_by_key(|sample| sample.verify);
    let verify = samples[samples.len() / 2].verify;
    samples.sort_unstable_by_key(|sample| sample.proof_bytes);
    let median = samples[samples.len() / 2];
    let max_transport_bytes = samples
        .iter()
        .map(|sample| sample.proof_transport_bytes)
        .max()
        .unwrap();
    println!(
        "{size},{protocol},{:.3},{:.3},{},{},{},{},{},{},{},{},{},{}",
        prove.as_secs_f64() * 1000.0,
        verify.as_secs_f64() * 1000.0,
        median.proof_bytes,
        samples[0].proof_bytes,
        samples.last().unwrap().proof_bytes,
        median.proof_transport_bytes,
        max_transport_bytes,
        8 + size * 32,
        median.l0_rows_bytes,
        median.pcs_bytes,
        median.veil_bytes,
        median.transcript_bytes
    );
    Summary {
        prove,
        max_transport_bytes,
    }
}

fn targets_met(flock: &Summary, zk: &Summary) -> bool {
    flock.prove > Duration::ZERO
        && flock.max_transport_bytes > 0
        && zk.prove.as_nanos() * 10 <= flock.prove.as_nanos() * 11
        && zk.max_transport_bytes as u128 * 25 <= flock.max_transport_bytes as u128 * 28
}

fn messages(size: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    (0..size)
        .map(|index| {
            std::array::from_fn(|byte| {
                let word = (index as u64)
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .rotate_left((byte % 64) as u32)
                    ^ byte as u64;
                word as u8
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gate_accepts_exact_limits_and_rejects_either_excess() {
        let summary = |milliseconds, bytes| Summary {
            prove: Duration::from_millis(milliseconds),
            max_transport_bytes: bytes,
        };
        let baseline = summary(100, 1000);
        assert!(targets_met(&baseline, &summary(110, 1120)));
        assert!(!targets_met(&baseline, &summary(111, 1120)));
        assert!(!targets_met(&baseline, &summary(110, 1121)));
    }

    #[test]
    fn options_reject_noncomparable_and_unsupported_shapes() {
        let parse =
            |arguments: &[&str]| Options::parse(arguments.iter().map(|value| (*value).to_owned()));
        assert!(parse(&["0"]).is_err());
        assert!(parse(&["--sizes", "8192"]).is_err());
        assert!(parse(&["--check-targets"]).is_err());
        assert_eq!(
            parse(&["15", "--sizes", "256,4096", "--check-targets"]).unwrap(),
            Options {
                samples: 15,
                sizes: vec![256, 4096],
                check_targets: true
            }
        );
    }
}

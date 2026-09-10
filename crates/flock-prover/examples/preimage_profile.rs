//! Whole-process profiling workload for the `preimage_scaling` release benchmark.
//!
//! Preparation, one warm-up, fresh challengers, proof destruction, and final
//! validation remain visible in the process profile. Verification rotates through
//! an eight-proof warm-cache corpus. Proving validates the warm-up and final
//! output; the separate timing benchmark validates every generated output.

use std::ffi::OsString;
use std::fs::{self, OpenOptions};
use std::hint::black_box;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use flock_core::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3_preimage::{Blake3PreimageSetup, Blake3PreimageZkSetup};
use serde::Serialize;

mod support;
use support::{FLOCK_BENCHMARK_DOMAIN, SIZES, messages};
const MEASUREMENT_ENV: &str = include_str!("../../../tools/performance/measurement-env.json");
const VERIFY_CORPUS_SIZE: usize = 8;
const USAGE: &str = "preimage_profile --protocol flock|full-zk --operation prove|verify \
    --hashes 64|128|256|512|1024|2048|4096 --seconds <positive-seconds> \
    --attempt-id <id> --metadata <path>";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Protocol {
    Flock,
    FullZk,
}

impl Protocol {
    fn as_str(self) -> &'static str {
        match self {
            Self::Flock => "flock",
            Self::FullZk => "full-zk",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operation {
    Prove,
    Verify,
}

impl Operation {
    fn as_str(self) -> &'static str {
        match self {
            Self::Prove => "prove",
            Self::Verify => "verify",
        }
    }
}

#[derive(Debug)]
struct Config {
    protocol: Protocol,
    operation: Operation,
    hashes: usize,
    duration: Duration,
    requested_seconds: f64,
    attempt_id: String,
    metadata: PathBuf,
}

impl Config {
    fn parse(arguments: impl IntoIterator<Item = OsString>) -> Result<Self, String> {
        let mut arguments = arguments.into_iter();
        let mut values = std::collections::BTreeMap::new();
        while let Some(flag) = arguments.next() {
            let flag = flag.into_string().map_err(|_| "non-Unicode option")?;
            if !matches!(
                flag.as_str(),
                "--protocol"
                    | "--operation"
                    | "--hashes"
                    | "--seconds"
                    | "--attempt-id"
                    | "--metadata"
            ) {
                return Err(format!("unknown option {flag:?}; usage: {USAGE}"));
            }
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing value for {flag}"))?;
            if values.insert(flag.clone(), value).is_some() {
                return Err(format!("duplicate option {flag}"));
            }
        }
        let mut take = |key: &str| {
            values
                .remove(key)
                .ok_or_else(|| format!("missing {key}; usage: {USAGE}"))
        };
        let protocol = match take("--protocol")?.to_str() {
            Some("flock") => Protocol::Flock,
            Some("full-zk") => Protocol::FullZk,
            _ => return Err("--protocol must be flock or full-zk".into()),
        };
        let operation = match take("--operation")?.to_str() {
            Some("prove") => Operation::Prove,
            Some("verify") => Operation::Verify,
            _ => return Err("--operation must be prove or verify".into()),
        };
        let hashes = take("--hashes")?
            .to_str()
            .and_then(|value| value.parse().ok())
            .filter(|value| SIZES.contains(value))
            .ok_or("--hashes must be one of 64,128,256,512,1024,2048,4096")?;
        let requested_seconds = take("--seconds")?
            .to_str()
            .and_then(|value| value.parse::<f64>().ok())
            .filter(|value| value.is_finite() && *value > 0.0)
            .ok_or("--seconds must be positive and finite")?;
        let duration = Duration::try_from_secs_f64(requested_seconds)
            .map_err(|_| "--seconds is outside the supported duration range")?;
        if duration.is_zero() {
            return Err("--seconds must be at least one nanosecond".into());
        }
        let attempt_id = take("--attempt-id")?
            .into_string()
            .map_err(|_| "--attempt-id must be Unicode")?;
        if attempt_id.is_empty() {
            return Err("--attempt-id cannot be empty".into());
        }
        let metadata = PathBuf::from(take("--metadata")?);
        if metadata.as_os_str().is_empty() {
            return Err("--metadata cannot be empty".into());
        }
        Ok(Self {
            protocol,
            operation,
            hashes,
            duration,
            requested_seconds,
            attempt_id,
            metadata,
        })
    }
}

#[derive(Serialize)]
struct Metadata {
    schema_version: u32,
    process_id: u32,
    attempt_id: String,
    protocol: &'static str,
    operation: &'static str,
    hashes: usize,
    requested_seconds: f64,
    loop_seconds: f64,
    completed_calls: u64,
    final_validation: bool,
    environment_absent: bool,
    environment_keys: Vec<String>,
    thread_count: usize,
    verifier_thread_count: usize,
    corpus_size: usize,
    preparation_seconds: f64,
    validation_seconds: f64,
    cleanup_seconds: f64,
    validation_scope: &'static str,
}

struct Measurement {
    loop_seconds: f64,
    completed_calls: u64,
    corpus_size: usize,
    preparation_seconds: f64,
    validation_seconds: f64,
    cleanup_seconds: f64,
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("preimage_profile: {error}");
            std::process::ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let config = Config::parse(std::env::args_os().skip(1))?;
    let environment_keys: Vec<String> = serde_json::from_str(MEASUREMENT_ENV)
        .map_err(|error| format!("invalid compiled measurement environment policy: {error}"))?;
    validate_environment(&environment_keys, |key| std::env::var_os(key))?;
    if config
        .metadata
        .try_exists()
        .map_err(|error| error.to_string())?
    {
        return Err(format!(
            "metadata already exists: {}",
            config.metadata.display()
        ));
    }

    // The environment check above must precede all pool and setup construction.
    let preparation_started = Instant::now();
    flock_prover::init_perf_thread_pool();
    let thread_count = rayon::current_num_threads();
    let messages = messages(config.hashes);
    let digests = Blake3PreimageSetup::digests_of(&messages);
    let measurement = match config.protocol {
        Protocol::Flock => measure(
            &config,
            (Blake3PreimageSetup::new(config.hashes), messages, digests),
            |(setup, messages, digests)| {
                let mut challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
                setup
                    .prove(black_box(messages), black_box(digests), &mut challenger)
                    .map_err(|error| format!("FLOCK prove failed: {error:?}"))
            },
            |(setup, _, digests), (proof, commitment)| {
                let mut challenger = FsChallenger::new(FLOCK_BENCHMARK_DOMAIN);
                setup
                    .verify(
                        black_box(commitment),
                        black_box(proof),
                        black_box(digests),
                        &mut challenger,
                    )
                    .map_err(|error| format!("FLOCK verify failed: {error:?}"))
            },
            preparation_started,
        )?,
        Protocol::FullZk => measure(
            &config,
            (Blake3PreimageZkSetup::new(config.hashes), messages, digests),
            |(setup, messages, digests)| {
                // Preserve fresh OS-seeded randomness inside the public API.
                setup
                    .prove(black_box(messages), black_box(digests))
                    .map_err(|error| format!("full-ZK prove failed: {error:?}"))
            },
            |(setup, _, digests), (proof, commitment)| {
                setup
                    .verify(black_box(commitment), black_box(proof), black_box(digests))
                    .map_err(|error| format!("full-ZK verify failed: {error:?}"))
            },
            preparation_started,
        )?,
    };
    let metadata = Metadata {
        schema_version: 1,
        process_id: std::process::id(),
        attempt_id: config.attempt_id,
        protocol: config.protocol.as_str(),
        operation: config.operation.as_str(),
        hashes: config.hashes,
        requested_seconds: config.requested_seconds,
        loop_seconds: measurement.loop_seconds,
        completed_calls: measurement.completed_calls,
        final_validation: true,
        environment_absent: true,
        environment_keys,
        thread_count,
        // The public verifier's private flock-verify pool is fixed to one
        // worker in flock-core/src/verifier.rs; do not replace that pool.
        verifier_thread_count: 1,
        corpus_size: measurement.corpus_size,
        preparation_seconds: measurement.preparation_seconds,
        validation_seconds: measurement.validation_seconds,
        cleanup_seconds: measurement.cleanup_seconds,
        validation_scope: match config.operation {
            Operation::Prove => "warm-up and final proof",
            Operation::Verify => "entire corpus, every loop call, and final verification",
        },
    };
    publish_metadata(&config.metadata, &metadata)
        .map_err(|error| format!("cannot publish metadata: {error}"))?;
    println!(
        "{} {} {}: {} calls in {:.6} seconds; validated",
        metadata.protocol,
        metadata.operation,
        metadata.hashes,
        metadata.completed_calls,
        metadata.loop_seconds,
    );
    Ok(())
}

fn validate_environment(
    keys: &[String],
    mut get: impl FnMut(&str) -> Option<OsString>,
) -> Result<(), String> {
    let present: Vec<&str> = keys
        .iter()
        .filter(|key| get(key).is_some())
        .map(String::as_str)
        .collect();
    if present.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "measurement policy requires absent environment variables: {}",
            present.join(", ")
        ))
    }
}

fn measure<W, P>(
    config: &Config,
    workload: W,
    mut prove: impl FnMut(&W) -> Result<P, String>,
    mut verify: impl FnMut(&W, &P) -> Result<(), String>,
    preparation_started: Instant,
) -> Result<Measurement, String> {
    let warm_up = black_box(prove(black_box(&workload))?);
    verify(black_box(&workload), black_box(&warm_up))?;
    let corpus_size = match config.operation {
        Operation::Prove => 1,
        Operation::Verify => VERIFY_CORPUS_SIZE,
    };
    let mut proofs = Vec::with_capacity(corpus_size);
    proofs.push(warm_up);
    for _ in 1..corpus_size {
        let proof = black_box(prove(black_box(&workload))?);
        verify(black_box(&workload), black_box(&proof))?;
        proofs.push(proof);
    }
    let preparation_seconds = preparation_started.elapsed().as_secs_f64();
    let mut completed_calls = 0;
    let started = Instant::now();
    match config.operation {
        Operation::Prove => loop {
            // Assignment drops the previous proof; memory stays bounded.
            proofs[0] = black_box(prove(black_box(&workload))?);
            completed_calls += 1;
            if started.elapsed() >= config.duration {
                break;
            }
        },
        Operation::Verify => {
            let mut index = 0;
            loop {
                black_box(verify(black_box(&workload), black_box(&proofs[index])))?;
                completed_calls += 1;
                index = (index + 1) % proofs.len();
                if started.elapsed() >= config.duration {
                    break;
                }
            }
        }
    }
    let loop_seconds = started.elapsed().as_secs_f64();
    let validation_started = Instant::now();
    verify(black_box(&workload), black_box(&proofs[0]))?;
    let validation_seconds = validation_started.elapsed().as_secs_f64();
    let cleanup_started = Instant::now();
    drop(proofs);
    drop(workload);
    let cleanup_seconds = cleanup_started.elapsed().as_secs_f64();
    Ok(Measurement {
        loop_seconds,
        completed_calls,
        corpus_size,
        preparation_seconds,
        validation_seconds,
        cleanup_seconds,
    })
}

fn publish_metadata(path: &Path, metadata: &Metadata) -> std::io::Result<()> {
    let mut name = path.as_os_str().to_owned();
    name.push(format!(".{}.tmp", std::process::id()));
    let temporary = PathBuf::from(name);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)?;
    let result = (|| {
        serde_json::to_writer_pretty(&mut file, metadata)?;
        file.write_all(b"\n")?;
        file.sync_all()?;
        // Publishing a hard link is atomic and fails if the destination exists;
        // unlike rename on Unix, it cannot overwrite an earlier attempt.
        fs::hard_link(&temporary, path)
    })();
    drop(file);
    let cleanup = fs::remove_file(&temporary);
    result.and(cleanup)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config(operation: &str, seconds: &str) -> Config {
        Config::parse(
            [
                "--protocol",
                "flock",
                "--operation",
                operation,
                "--hashes",
                "64",
                "--seconds",
                seconds,
                "--attempt-id",
                "unit-test",
                "--metadata",
                "unused.json",
            ]
            .map(OsString::from),
        )
        .unwrap()
    }

    #[test]
    fn rejects_invalid_and_duplicate_arguments() {
        for seconds in ["0", "-1", "NaN", "inf", "1e99", "1e-99"] {
            let arguments = [
                "--protocol",
                "flock",
                "--operation",
                "prove",
                "--hashes",
                "64",
                "--seconds",
                seconds,
                "--attempt-id",
                "test",
                "--metadata",
                "out.json",
            ];
            assert!(Config::parse(arguments.map(OsString::from)).is_err());
        }
        assert!(Config::parse(["--seconds", "1", "--seconds", "2"].map(OsString::from)).is_err());
        assert!(Config::parse(["--unknown", "1"].map(OsString::from)).is_err());
    }

    #[test]
    fn environment_policy_tests_presence_including_empty_and_non_unicode() {
        let keys: Vec<String> = serde_json::from_str(MEASUREMENT_ENV).unwrap();
        assert_eq!(keys.len(), 12);
        assert!(validate_environment(&keys, |_| None).is_ok());
        let mut values = vec![OsString::new(), OsString::from("0"), OsString::from("1")];
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStringExt;
            values.push(OsString::from_vec(vec![0xff]));
        }
        for key in &keys {
            for value in &values {
                assert!(
                    validate_environment(&keys, |candidate| {
                        (candidate == key).then(|| value.clone())
                    })
                    .is_err()
                );
            }
        }
    }

    #[test]
    fn prove_bounds_retention_and_validates_final_output() {
        use std::cell::Cell;
        use std::rc::Rc;

        struct Proof(Rc<Cell<usize>>);
        impl Drop for Proof {
            fn drop(&mut self) {
                self.0.set(self.0.get() - 1);
            }
        }
        let live = Rc::new(Cell::new(0));
        let peak = Cell::new(0);
        let verifies = Cell::new(0);
        let measurement = measure(
            &config("prove", "0.00001"),
            (),
            |_| {
                live.set(live.get() + 1);
                peak.set(peak.get().max(live.get()));
                Ok(Proof(Rc::clone(&live)))
            },
            |_, _| {
                verifies.set(verifies.get() + 1);
                Ok(())
            },
            Instant::now(),
        )
        .unwrap();
        assert!(measurement.completed_calls > 0);
        assert_eq!(verifies.get(), 2);
        assert_eq!(live.get(), 0);
        assert_eq!(peak.get(), 2);
    }

    #[test]
    fn verify_rotates_corpus_without_reproving_inside_loop() {
        use std::cell::Cell;
        const STOP: &str = "verified two complete test rotations";
        let mut config = config("verify", "0.00001");
        config.duration = Duration::MAX;
        let generated = Cell::new(0);
        let mut verified = Vec::new();
        let result = measure(
            &config,
            (),
            |_| {
                generated.set(generated.get() + 1);
                Ok(generated.get())
            },
            |_, proof| {
                if verified.len() >= VERIFY_CORPUS_SIZE {
                    assert_eq!(generated.get(), VERIFY_CORPUS_SIZE);
                }
                if verified.len() == 3 * VERIFY_CORPUS_SIZE {
                    return Err(STOP.to_owned());
                }
                let expected = verified.len() % VERIFY_CORPUS_SIZE + 1;
                assert_eq!(*proof, expected);
                verified.push(*proof);
                Ok(())
            },
            Instant::now(),
        );
        assert_eq!(result.err().as_deref(), Some(STOP));
        assert_eq!(generated.get(), VERIFY_CORPUS_SIZE);
        assert_eq!(
            verified,
            (1..=VERIFY_CORPUS_SIZE)
                .cycle()
                .take(3 * VERIFY_CORPUS_SIZE)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn verify_completion_validates_the_first_corpus_entry_and_counts_calls() {
        use std::cell::Cell;
        let generated = Cell::new(0);
        let mut verified = Vec::new();
        let measurement = measure(
            &config("verify", "0.00001"),
            (),
            |_| {
                generated.set(generated.get() + 1);
                Ok(generated.get())
            },
            |_, proof| {
                verified.push(*proof);
                Ok(())
            },
            Instant::now(),
        )
        .unwrap();
        assert!(measurement.completed_calls > 0);
        assert_eq!(generated.get(), VERIFY_CORPUS_SIZE);
        assert_eq!(
            verified.len() as u64,
            measurement.completed_calls + VERIFY_CORPUS_SIZE as u64 + 1
        );
        let final_proof = verified.pop().unwrap();
        assert_eq!(final_proof, 1);
        assert_eq!(
            verified,
            (1..=VERIFY_CORPUS_SIZE)
                .cycle()
                .take(VERIFY_CORPUS_SIZE + measurement.completed_calls as usize)
                .collect::<Vec<_>>()
        );
    }

    fn literal_metadata() -> Metadata {
        Metadata {
            schema_version: 1,
            process_id: 1234,
            attempt_id: "literal-v1-prove".into(),
            protocol: Protocol::Flock.as_str(),
            operation: Operation::Prove.as_str(),
            hashes: 64,
            requested_seconds: 0.125,
            loop_seconds: 0.13,
            completed_calls: 7,
            final_validation: true,
            environment_absent: true,
            environment_keys: serde_json::from_str(MEASUREMENT_ENV).unwrap(),
            thread_count: 2,
            verifier_thread_count: 1,
            corpus_size: 1,
            preparation_seconds: 0.25,
            validation_seconds: 0.0,
            cleanup_seconds: 0.0,
            validation_scope: "warm-up and final proof",
        }
    }

    #[test]
    fn metadata_serialization_matches_the_literal_v1_contract() {
        let expected: serde_json::Value = serde_json::from_str(include_str!(
            "../../../tools/performance/tests/fixtures/harness-v1.json"
        ))
        .unwrap();
        assert_eq!(serde_json::to_value(literal_metadata()).unwrap(), expected);
    }

    #[test]
    fn metadata_publication_is_exclusive_and_cleans_its_temporary_file() {
        struct Directory(PathBuf);
        impl Drop for Directory {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let root = Directory(std::env::temp_dir().join(format!(
            "flock metadata test {} {}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        )));
        fs::create_dir(&root.0).unwrap();
        let path = root.0.join("harness.json");
        let metadata = literal_metadata();
        publish_metadata(&path, &metadata).unwrap();
        let original = fs::read(&path).unwrap();
        assert_eq!(
            serde_json::from_slice::<serde_json::Value>(&original).unwrap(),
            serde_json::to_value(&metadata).unwrap()
        );
        let mut different = metadata;
        different.attempt_id = "must not replace the accepted metadata".into();
        assert_eq!(
            publish_metadata(&path, &different).unwrap_err().kind(),
            std::io::ErrorKind::AlreadyExists
        );
        assert_eq!(fs::read(&path).unwrap(), original);
        assert_eq!(fs::read_dir(&root.0).unwrap().count(), 1);
    }

    #[test]
    fn final_verification_failure_rejects_workload() {
        let mut verifications = 0;
        let result = measure(
            &config("prove", "0.00001"),
            (),
            |_| Ok(()),
            |_, _| {
                verifications += 1;
                if verifications == 1 {
                    Ok(())
                } else {
                    Err("invalid final proof".to_string())
                }
            },
            Instant::now(),
        );
        assert_eq!(verifications, 2);
        assert_eq!(result.err().as_deref(), Some("invalid final proof"));
    }
}

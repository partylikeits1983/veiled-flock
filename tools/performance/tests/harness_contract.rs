#![cfg(unix)]

mod common;

use common::Temporary;
use flock_performance::records::{
    Case, HarnessMetadata, SIZES, all_cases, endpoints, read_harness,
};
use flock_performance::{Result, command, environment_keys, sha256};
use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};

const V1: &str = include_str!("fixtures/harness-v1.json");
const INPUTS: &str =
    include_str!("../../../crates/flock-prover/examples/support/preimage-vectors.json");
const CSV_HEADER: &str = "hashes,protocol,prove_ms_median,verify_ms_median,proof_bytes_median,proof_bytes_min,proof_bytes_max";

#[test]
fn independently_recorded_v1_producer_fixture_is_accepted() -> Result<()> {
    // The producer's unit test compares actual serialization with this same
    // literal, independently of the consumer type and serializer.
    let metadata: HarnessMetadata = serde_json::from_str(V1)?;
    let policy = metadata.environment_keys.clone();
    metadata.validate(
        &Case::new("flock", "prove", 64)?,
        "literal-v1-prove",
        0.125,
        &policy,
    )?;
    assert_eq!(metadata.thread_count, 2); // Not tied to the development Mac.
    assert_eq!(metadata.verifier_thread_count, 1); // Declared v1 pool policy.
    assert_eq!(metadata.validation_seconds, 0.0);
    Ok(())
}

#[test]
fn tool_matrix_agrees_with_the_examples_literal_specification() -> Result<()> {
    let inputs: Value = serde_json::from_str(INPUTS)?;
    assert_eq!(serde_json::to_value(SIZES)?, inputs["sizes"]);
    let expected = SIZES
        .into_iter()
        .flat_map(|size| {
            ["flock", "full-zk"].into_iter().flat_map(move |protocol| {
                ["prove", "verify"]
                    .into_iter()
                    .map(move |operation| (protocol, operation, size))
            })
        })
        .collect::<Vec<_>>();
    let actual = all_cases()
        .iter()
        .map(|case| (case.protocol.as_str(), case.operation.as_str(), case.hashes))
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
    Ok(())
}

fn required_binary(variable: &str) -> Result<PathBuf> {
    let value = std::env::var_os(variable)
        .ok_or_else(|| format!("set {variable} to the freshly built release example"))?;
    let path = fs::canonicalize(workspace_path(PathBuf::from(value)))?;
    if !path.is_file() {
        return Err(format!("{variable} must identify an executable file").into());
    }
    Ok(path)
}

// Cargo executes integration tests from the package directory. Interpret the
// documented relative artifact paths from the workspace, independent of that.
fn workspace_path(path: PathBuf) -> PathBuf {
    if path.is_absolute() {
        path
    } else {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(path)
    }
}

#[test]
#[ignore = "requires freshly built release examples in FLOCK_PREIMAGE_PROFILE_BIN and FLOCK_PREIMAGE_SCALING_BIN"]
fn short_endpoint_workloads_and_baseline_keep_the_v1_contract() -> Result<()> {
    let profile = required_binary("FLOCK_PREIMAGE_PROFILE_BIN")?;
    let scaling = required_binary("FLOCK_PREIMAGE_SCALING_BIN")?;
    let temporary = Temporary::new("flock preimage correctness")?;
    let output_dir = if let Some(path) = std::env::var_os("FLOCK_PREIMAGE_CHECK_OUTPUT") {
        let path = workspace_path(PathBuf::from(path));
        // A reused destination would mix binaries or attempts in this evidence.
        fs::create_dir(&path)?;
        fs::canonicalize(path)?
    } else {
        temporary.path().to_owned()
    };
    fs::write(
        output_dir.join("binaries.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "purpose": "short unprofiled correctness checks, not performance measurements",
            "profile": {"path": profile, "sha256": sha256(&profile)?},
            "scaling": {"path": scaling, "sha256": sha256(&scaling)?}
        }))?,
    )?;
    let policy = environment_keys();
    for case in endpoints() {
        let id = format!("correctness-{case}");
        let metadata_path = output_dir.join(format!("{id}.json"));
        let arguments = [
            "--protocol".to_owned(),
            case.protocol.as_str().to_owned(),
            "--operation".to_owned(),
            case.operation.as_str().to_owned(),
            "--hashes".to_owned(),
            case.hashes.to_string(),
            "--seconds".to_owned(),
            "0.01".to_owned(),
            "--attempt-id".to_owned(),
            id.clone(),
        ];
        let output = command(&profile)
            .args(&arguments)
            .arg("--metadata")
            .arg(&metadata_path)
            .output()?;
        fs::write(output_dir.join(format!("{id}.stdout")), &output.stdout)?;
        fs::write(output_dir.join(format!("{id}.stderr")), &output.stderr)?;
        assert!(output.status.success(), "{id}: {output:?}");
        let metadata = read_harness(&metadata_path, &case, &id, 0.01, &policy)?;
        println!(
            "{case}: {} calls, final validation passed, corpus {}",
            metadata.completed_calls, metadata.corpus_size
        );

        // Exercise the real executable's exclusive publication guard.
        let accepted_bytes = fs::read(&metadata_path)?;
        let duplicate = command(&profile)
            .args(&arguments)
            .arg("--metadata")
            .arg(&metadata_path)
            .output()?;
        assert!(!duplicate.status.success(), "duplicate attempt accepted");
        assert!(String::from_utf8_lossy(&duplicate.stderr).contains("metadata already exists"));
        assert_eq!(fs::read(&metadata_path)?, accepted_bytes);
    }

    // The presence test and child sanitation tests have independent coverage;
    // this probe confirms the actual harness still rejects reintroduction.
    let rejected_path = output_dir.join("diagnostic-reintroduced.json");
    let rejected = command(&profile)
        .env("FLOCK_COMMIT_TIMING", "0")
        .args([
            "--protocol",
            "flock",
            "--operation",
            "prove",
            "--hashes",
            "64",
            "--seconds",
            "0.01",
            "--attempt-id",
            "diagnostic-reintroduced",
            "--metadata",
        ])
        .arg(&rejected_path)
        .output()?;
    fs::write(
        output_dir.join("diagnostic-reintroduced.stderr"),
        &rejected.stderr,
    )?;
    assert!(!rejected.status.success());
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains("requires absent environment variables")
    );
    assert!(!rejected_path.exists());

    let output = command(&scaling).arg("1").output()?;
    fs::write(output_dir.join("baseline.csv"), &output.stdout)?;
    fs::write(output_dir.join("baseline.stderr"), &output.stderr)?;
    assert!(output.status.success(), "baseline: {output:?}");
    let csv = String::from_utf8(output.stdout)?;
    let mut lines = csv.lines();
    assert_eq!(lines.next(), Some(CSV_HEADER));
    let rows = lines.collect::<Vec<_>>();
    assert_eq!(rows.len(), 14);
    for (index, line) in rows.into_iter().enumerate() {
        let fields = line.split(',').collect::<Vec<_>>();
        assert_eq!(fields.len(), 7);
        assert_eq!(fields[0].parse::<usize>()?, SIZES[index / 2]);
        assert_eq!(
            fields[1],
            ["FLOCK-non-ZK-Secure", "VEIL-FLOCK-full-ZK"][index % 2]
        );
        for timing in &fields[2..4] {
            let milliseconds = timing.parse::<f64>()?;
            assert!(milliseconds.is_finite() && milliseconds > 0.0);
        }
        let median = fields[4].parse::<u64>()?;
        let min = fields[5].parse::<u64>()?;
        let max = fields[6].parse::<u64>()?;
        assert!(min > 0 && min <= median && median <= max);
    }
    assert_eq!(
        flock_performance::report::read_baseline(&output_dir.join("baseline.csv"))?.len(),
        14
    );
    println!("baseline: 14 ordered rows, exact CSV header and proof-size fields passed");
    println!("correctness evidence: {}", output_dir.display());
    Ok(())
}

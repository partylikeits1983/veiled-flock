#![cfg(unix)]

mod common;

use common::Temporary;
use flock_performance::Result;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

// Include directory entries so rejection cannot create an empty output either.
fn contents(root: &Path) -> Result<BTreeMap<PathBuf, Option<Vec<u8>>>> {
    fn visit(
        root: &Path,
        path: &Path,
        output: &mut BTreeMap<PathBuf, Option<Vec<u8>>>,
    ) -> Result<()> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if entry.file_type()?.is_dir() {
                output.insert(path.strip_prefix(root)?.into(), None);
                visit(root, &path, output)?;
            } else {
                output.insert(path.strip_prefix(root)?.into(), Some(fs::read(&path)?));
            }
        }
        Ok(())
    }
    let mut result = BTreeMap::new();
    visit(root, root, &mut result)?;
    Ok(result)
}

fn evidence(root: &Path) -> Result<PathBuf> {
    let evidence = root.join("evidence with spaces");
    fs::create_dir(&evidence)?;
    fs::write(evidence.join("complete.json"), b"{\"schema_version\":1}\n")?;
    fs::write(
        evidence.join("report.md"),
        b"Reviewed findings and power caveat.\n",
    )?;
    fs::write(evidence.join("analysis.json"), b"{\"historical\":true}\n")?;
    Ok(evidence)
}

fn report(evidence: &Path, output: Option<&Path>) -> Result<Output> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_profile_preimages"));
    command.arg("--report").arg(evidence);
    if let Some(output) = output {
        command.arg("--output").arg(output);
    }
    Ok(command.output()?)
}

#[test]
fn report_requires_separate_output_without_changing_evidence() -> Result<()> {
    let root = Temporary::new("flock report CLI missing output")?;
    let evidence = evidence(root.path())?;
    let before = contents(root.path())?;
    let rejected = report(&evidence, None)?;
    assert!(!rejected.status.success());
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("requires a separate --output"));
    assert_eq!(contents(root.path())?, before);
    Ok(())
}

#[test]
fn report_rejects_same_ancestor_and_descendant_outputs_before_writing() -> Result<()> {
    let root = Temporary::new("flock report CLI overlap")?;
    let evidence = evidence(root.path())?;
    let before = contents(root.path())?;
    for output in [&evidence, root.path(), &evidence.join("new publication")] {
        let rejected = report(&evidence, Some(output))?;
        assert!(!rejected.status.success(), "overlap accepted: {output:?}");
        assert!(String::from_utf8_lossy(&rejected.stderr).contains("overlap"));
        assert_eq!(contents(root.path())?, before);
    }
    Ok(())
}

#[test]
fn report_rejects_incomplete_processing_without_creating_output() -> Result<()> {
    let root = Temporary::new("flock report CLI incomplete processing")?;
    let evidence = evidence(root.path())?;
    let output = root.join("new publication");
    for status in ["in_progress", "partial_failure", "failed", "unknown"] {
        fs::write(
            evidence.join("report-processing.json"),
            serde_json::to_vec(&serde_json::json!({"status":status}))?,
        )?;
        let before = contents(root.path())?;
        let rejected = report(&evidence, Some(&output))?;
        assert!(
            !rejected.status.success(),
            "incomplete state accepted: {status}"
        );
        assert!(String::from_utf8_lossy(&rejected.stderr).contains("processing is incomplete"));
        assert!(!output.exists());
        assert_eq!(contents(root.path())?, before);
    }
    Ok(())
}

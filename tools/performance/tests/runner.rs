#![cfg(unix)]

mod common;

use common::{Temporary, init_git, remove_sealed};
use flock_performance::{Result, sha256, snapshot};
use serde_json::json;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::AtomicU64;

struct Fixture {
    _root: Temporary,
    snapshot: snapshot::Snapshot,
    report: PathBuf,
    target: PathBuf,
}

impl Fixture {
    fn new() -> Result<Self> {
        let root = Temporary::new("flock runner test")?;
        let editing = root.join("editing checkout");
        fs::create_dir_all(&editing)?;
        fs::write(editing.join("Cargo.toml"), "[workspace]\nmembers = []\n")?;
        init_git(&editing)?;
        let report = root.join("report output");
        let snapshot = snapshot::prepare(&editing, &report)?;
        let target = root
            .join("custom Cargo target with spaces")
            .join("tools/release");
        fs::create_dir_all(&target)?;
        Ok(Self {
            _root: root,
            snapshot,
            report,
            target,
        })
    }

    fn config(&self, executable: &Path, digest: &str) -> Result<PathBuf> {
        let config = self.report.join("manifest.json");
        fs::write(
            &config,
            serde_json::to_vec_pretty(&json!({
                "schema_version": 1,
                "output": self.report,
                "snapshot": self.snapshot,
                "target_root": self.target,
                "seconds": 30.0,
                "artifacts": {
                    "profile_preimages": {"path": executable, "sha256": digest}
                },
                "tools": {},
                "environment": {},
                "branch": "chore/isolated-test",
                "revision": self.snapshot.base_revision
            }))?,
        )?;
        Ok(config)
    }

    fn assert_no_measurements(&self) {
        for path in [
            "cases",
            "svg",
            "baseline-before.csv",
            "baseline-after.csv",
            "report.md",
            "complete.json",
        ] {
            assert!(
                !self.report.join(path).exists(),
                "unexpected accepted output {path}"
            );
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        remove_sealed(&self.snapshot.root);
    }
}

#[test]
fn temporary_root_skips_occupied_name_without_modifying_its_contents() -> Result<()> {
    let occupied = Temporary::with_counter("occupied runner fixture", &AtomicU64::new(0))?;
    let sentinel = occupied.join("belongs-to-earlier-test");
    fs::write(&sentinel, "preserve existing fixture")?;
    let replacement = Temporary::with_counter("occupied runner fixture", &AtomicU64::new(0))?;
    assert_ne!(occupied.path(), replacement.path());
    drop(replacement);
    assert_eq!(fs::read_to_string(sentinel)?, "preserve existing fixture");
    Ok(())
}

#[test]
fn frozen_run_rejects_byte_identical_runner_from_unregistered_location() -> Result<()> {
    let fixture = Fixture::new()?;
    let runner = Path::new(env!("CARGO_BIN_EXE_profile_preimages")).canonicalize()?;
    let registered = fixture.target.join("profile_preimages");
    fs::copy(&runner, &registered)?;
    let config = fixture.config(&registered.canonicalize()?, &sha256(&runner)?)?;
    let output = Command::new(&runner)
        .arg("--frozen-run")
        .arg(config)
        .output()?;
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("frozen mode must run the registered snapshot-built runner"),
        "{output:?}"
    );
    fixture.assert_no_measurements();
    Ok(())
}

#[test]
fn frozen_run_rejects_changed_executable_before_launching_any_capture() -> Result<()> {
    let fixture = Fixture::new()?;
    let runner = Path::new(env!("CARGO_BIN_EXE_profile_preimages")).canonicalize()?;
    let config = fixture.config(&runner, &"0".repeat(64))?;
    let output = Command::new(&runner)
        .arg("--frozen-run")
        .arg(config)
        .output()?;
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("registered profile_preimages executable changed"),
        "{output:?}"
    );
    fixture.assert_no_measurements();
    Ok(())
}

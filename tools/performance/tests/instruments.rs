//! Explicit preparation only: the frozen runner owns actual smoke capture.
#![cfg(target_os = "macos")]

use flock_performance::records::ArtifactIdentity;
use flock_performance::{Result, atomic_json, command, environment_keys, process, snapshot};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::AtomicBool;
use std::time::Duration;

fn text(mut command: Command) -> Result<String> {
    let output = command.output()?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned().into());
    }
    Ok(String::from_utf8(output.stdout)?.trim().to_owned())
}

fn query(program: &str, args: &[&str]) -> Result<String> {
    let mut child = command(program);
    child.args(args);
    text(child)
}

struct Preparation {
    source: snapshot::Snapshot,
    output: PathBuf,
    tools: BTreeMap<String, ArtifactIdentity>,
    channel: String,
}

impl Preparation {
    fn cargo(&self, target: &Path, symbols: bool) -> Result<Command> {
        let cargo = &self.tools["cargo"].path;
        let mut child = command(cargo);
        let mut paths = vec![
            cargo
                .parent()
                .ok_or("Cargo binary has no parent")?
                .to_owned(),
        ];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        child
            .current_dir(&self.source.root)
            .env("RUSTUP_TOOLCHAIN", &self.channel)
            .env("CARGO_TARGET_DIR", target)
            .env("CARGO_NET_OFFLINE", "true")
            .env("PATH", std::env::join_paths(paths)?)
            .env_remove("CARGO_PROFILE_RELEASE_DEBUG")
            .env_remove("CARGO_PROFILE_RELEASE_STRIP");
        if symbols {
            child
                .env("CARGO_PROFILE_RELEASE_DEBUG", "2")
                .env("CARGO_PROFILE_RELEASE_STRIP", "none");
        }
        Ok(child)
    }

    fn checked(&self, child: &mut Command, label: &str) -> Result<()> {
        snapshot::verify(&self.source)?;
        for tool in self.tools.values() {
            tool.verify()?;
        }
        let outcome = process::logged(
            child,
            &self.output.join("logs"),
            label,
            &AtomicBool::new(false),
            Duration::from_secs(10),
        )?;
        snapshot::verify(&self.source)?;
        for tool in self.tools.values() {
            tool.verify()?;
        }
        outcome.ensure_success()
    }

    fn build(
        &self,
        target: &Path,
        symbols: bool,
        package: &str,
        extra: &[&str],
        label: &str,
    ) -> Result<BTreeMap<String, ArtifactIdentity>> {
        let mut child = self.cargo(target, symbols)?;
        child
            .args([
                "build",
                "--locked",
                "--offline",
                "--release",
                "--message-format",
                "json-render-diagnostics",
                "--manifest-path",
            ])
            .arg(self.source.root.join("Cargo.toml"))
            .args(["-p", package])
            .args(extra);
        self.checked(&mut child, label)?;
        let mut artifacts = BTreeMap::new();
        for line in
            fs::read_to_string(self.output.join("logs").join(format!("{label}.stdout")))?.lines()
        {
            if let Ok(record) = serde_json::from_str::<Value>(line)
                && record["reason"] == "compiler-artifact"
                && let (Some(name), Some(path)) = (
                    record["target"]["name"].as_str(),
                    record["executable"].as_str(),
                )
            {
                let artifact = ArtifactIdentity::register(Path::new(path))?;
                if !artifact.path.starts_with(target.canonicalize()?) {
                    return Err("Cargo artifact escaped target root".into());
                }
                artifacts.insert(name.to_owned(), artifact);
            }
        }
        Ok(artifacts)
    }
}

#[test]
#[ignore = "explicit preparation after final checks: requires a new FLOCK_PREIMAGE_SMOKE_OUTPUT, Xcode and pinned profiler; does not capture"]
fn prepare_frozen_instruments_smoke() -> Result<()> {
    let editing = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()?;
    let requested = PathBuf::from(
        std::env::var_os("FLOCK_PREIMAGE_SMOKE_OUTPUT")
            .ok_or("set FLOCK_PREIMAGE_SMOKE_OUTPUT to a new directory")?,
    );
    let output = if requested.is_absolute() {
        requested
    } else {
        editing.join(requested)
    };
    fs::create_dir(&output)?;
    let output = output.canonicalize()?;
    fs::create_dir(output.join("logs"))?;
    let source = snapshot::prepare(&editing, &output)?;
    let config: toml::Value =
        fs::read_to_string(source.root.join("rust-toolchain.toml"))?.parse()?;
    let channel = config["toolchain"]["channel"]
        .as_str()
        .ok_or("missing pinned toolchain")?
        .to_owned();
    let profiler = editing.join("target/profiling-tools/flamegraph-0.6.13/bin/cargo-flamegraph");
    let mut version = command(&profiler);
    version.args(["flamegraph", "--version"]);
    let profiler_version = text(version)?;
    if profiler_version.split_whitespace().last() != Some("0.6.13") {
        return Err("integration check requires flamegraph 0.6.13".into());
    }
    let mut tools = BTreeMap::new();
    tools.insert("profiler".into(), ArtifactIdentity::register(&profiler)?);
    for name in ["cargo", "rustc"] {
        let path = query("rustup", &["which", "--toolchain", &channel, name])?;
        tools.insert(name.into(), ArtifactIdentity::register(Path::new(&path))?);
    }
    for name in ["xctrace", "dsymutil"] {
        let path = query("xcrun", &["-f", name])?;
        tools.insert(name.into(), ArtifactIdentity::register(Path::new(&path))?);
    }
    tools.insert(
        "svg-renderer".into(),
        ArtifactIdentity::register(Path::new(&query("which", &["rsvg-convert"])?))?,
    );
    let prep = Preparation {
        source,
        output,
        tools,
        channel,
    };
    let target = prep.output.join("target");
    let mut checks = prep.cargo(&target.join("checks"), false)?;
    checks.args([
        "test",
        "--locked",
        "--offline",
        "--release",
        "-p",
        "flock-performance",
    ]);
    prep.checked(&mut checks, "frozen-helper-tests")?;
    let mut harness = prep.cargo(&target.join("checks"), false)?;
    harness.args([
        "test",
        "--locked",
        "--offline",
        "--release",
        "-p",
        "flock-prover",
        "--features",
        "veil",
        "--example",
        "preimage_profile",
        "--example",
        "preimage_scaling",
    ]);
    prep.checked(&mut harness, "frozen-harness-tests")?;
    let mut artifacts = prep.build(
        &target.join("tools"),
        false,
        "flock-performance",
        &["--bins"],
        "build-frozen-tools",
    )?;
    let examples = prep.build(
        &target.join("performance-symbols"),
        true,
        "flock-prover",
        &["--features", "veil", "--example", "preimage_profile"],
        "build-frozen-symbols",
    )?;
    artifacts.insert(
        "preimage_profile".into(),
        examples
            .get("preimage_profile")
            .ok_or("profile example was not built")?
            .clone(),
    );
    for name in ["profile_preimages", "xctrace_capture", "folded_capture"] {
        if !artifacts.contains_key(name) {
            return Err(format!("missing helper executable {name}").into());
        }
    }
    fs::create_dir(prep.output.join("build-artifacts"))?;
    fs::copy(
        &artifacts["preimage_profile"].path,
        prep.output.join("build-artifacts/preimage_profile"),
    )?;
    let mut symbols = command(&prep.tools["dsymutil"].path);
    symbols
        .arg(&artifacts["preimage_profile"].path)
        .arg("-o")
        .arg(prep.output.join("build-artifacts/preimage_profile.dSYM"));
    prep.checked(&mut symbols, "archive-debug-symbols")?;
    snapshot::verify(&prep.source)?;
    for artifact in artifacts.values() {
        artifact.verify()?;
    }
    let mut rustc = command(&prep.tools["rustc"].path);
    rustc.arg("-vV");
    let mut cargo = command(&prep.tools["cargo"].path);
    cargo.arg("-V");
    let manifest = prep.output.join("manifest.json");
    atomic_json(
        &manifest,
        &json!({
            "schema_version":2, "output":prep.output, "snapshot":prep.source,
            "target_root":target, "seconds":5.0, "artifacts":artifacts, "tools":prep.tools,
            "environment":{
                "toolchain":prep.channel, "profiler":profiler_version,
                "rustc":text(rustc)?, "cargo":text(cargo)?,
                "measurement_environment_removed":environment_keys(),
                "purpose":"four short Instruments integration checks, not performance measurements"
            },
            "branch":query("git", &["branch", "--show-current"])?,
            "revision":prep.source.base_revision, "power_policy":"require-ac", "publication_root":null
        }),
    )?;
    atomic_json(
        &prep.output.join("preparation.json"),
        &json!({
            "schema_version":1, "status":"ready", "captures_started":false,
            "bootstrap":ArtifactIdentity::register(&std::env::current_exe()?)?,
            "manifest":ArtifactIdentity::register(&manifest)?
        }),
    )?;
    println!("Prepared frozen manifest: {}", manifest.display());
    println!(
        "Frozen runner: {}",
        artifacts["profile_preimages"].path.display()
    );
    println!(
        "Before launching, restore the exact presence and values in manifest.snapshot.build_environment; Cargo may inject CARGO_HOME and RUSTUP_HOME that are absent in a plain shell."
    );
    println!(
        "Recorded build environment: {}",
        serde_json::to_string_pretty(&prep.source.build_environment)?
    );
    println!(
        "Remove extra build settings instead of changing the accepted manifest. The frozen runner verifies this environment before capture."
    );
    println!(
        "Capture is separate: invoke the frozen runner with --integration-smoke-frozen <manifest> after all build/edit activity stops."
    );
    Ok(())
}

//! Reproducible, local-only preimage profiling orchestration.
use std::{
    collections::BTreeMap,
    env,
    ffi::OsStr,
    fs,
    os::unix::fs::MetadataExt,
    os::unix::process::CommandExt,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use crate::{
    Result, atomic_json, command, environment_keys, evidence, host, process, records, report,
    sha256, snapshot,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use records::{ArtifactIdentity as Artifact, SIZES};
mod measurement;

fn toolchain() -> &'static str {
    static CHANNEL: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    CHANNEL.get_or_init(|| {
        let config: toml::Value = toml::from_str(include_str!("../../../rust-toolchain.toml"))
            .expect("validated toolchain configuration");
        config["toolchain"]["channel"]
            .as_str()
            .expect("pinned toolchain")
            .to_owned()
    })
}
static INTERRUPTED: AtomicBool = AtomicBool::new(false);

extern "C" fn interrupt(_: libc::c_int) {
    INTERRUPTED.store(true, Ordering::SeqCst);
}

#[derive(Serialize, Deserialize)]
struct Run {
    schema_version: u32,
    output: PathBuf,
    snapshot: snapshot::Snapshot,
    target_root: PathBuf,
    seconds: f64,
    artifacts: BTreeMap<String, Artifact>,
    tools: BTreeMap<String, Artifact>,
    environment: Value,
    branch: String,
    revision: String,
    #[serde(default)]
    power_policy: Option<host::PowerPolicy>,
    #[serde(default)]
    publication_root: Option<PathBuf>,
}

#[derive(Serialize, Deserialize)]
struct Resume {
    measurement_manifest: Artifact,
    controller: Run,
    preserved_evidence: BTreeMap<PathBuf, Artifact>,
}

#[derive(Serialize, Deserialize)]
struct ReportJob {
    evidence: PathBuf,
    output: PathBuf,
    findings: Option<PathBuf>,
    controller: Run,
}

/// A legacy-compatible CLI adapter: publishing always requires its own root.
pub fn report_command(args: &[std::ffi::OsString]) -> Result<()> {
    let evidence = args
        .first()
        .ok_or("--report requires an evidence root and separate --output")?;
    let mut output = None;
    let mut findings = None;
    let mut flags = args[1..].iter();
    while let Some(flag) = flags.next() {
        match flag.to_str() {
            Some("--output") if output.is_none() => {
                output = Some(PathBuf::from(
                    flags.next().ok_or("missing publication root")?,
                ))
            }
            Some("--findings") if findings.is_none() => {
                findings = Some(fs::canonicalize(
                    flags.next().ok_or("missing findings path")?,
                )?)
            }
            _ => return Err(
                "usage: --report <evidence-root> --output <publication-root> [--findings <file>]"
                    .into(),
            ),
        }
    }
    let output =
        output.ok_or("--report requires a separate --output; existing reports are read-only")?;
    let evidence = fs::canonicalize(evidence)?;
    let output = crate::canonical_output(&output)?;
    crate::reject_overlap(&evidence, &output)?;
    // Reject incomplete measurement/processing input before creating controller
    // directories. Rendering never repairs a marker in the evidence root.
    if !evidence.join("complete.json").exists()
        && !evidence.join("measurements-complete.json").exists()
    {
        return Err("report requires completed measurements".into());
    }
    let processing = evidence.join("report-processing.json");
    if processing.exists() {
        let marker: Value = serde_json::from_slice(&fs::read(processing)?)?;
        if marker["status"] != "complete" {
            return Err("legacy processing is incomplete; refusing publication".into());
        }
    }
    let ownership = evidence::WriterLock::acquire(&output)?;
    let edit =
        PathBuf::from(capture_text(command("git").args(["rev-parse", "--show-toplevel"]))?.trim());
    let id = unique_id("processor");
    let controller_output = output.join("processors").join(&id);
    fs::create_dir_all(&controller_output)?;
    let frozen = snapshot::prepare(&edit, &controller_output)?;
    let metadata: Value =
        serde_json::from_str(&capture_text(command("cargo").current_dir(&edit).args([
            "metadata",
            "--locked",
            "--offline",
            "--no-deps",
            "--format-version",
            "1",
        ]))?)?;
    let target_root = PathBuf::from(
        metadata["target_directory"]
            .as_str()
            .ok_or("target directory missing")?,
    )
    .join("preimage-processors")
    .join(&id);
    fs::create_dir_all(&target_root)?;
    let mut tools = BTreeMap::new();
    for name in ["cargo", "rustc"] {
        let path = PathBuf::from(
            capture_text(command("rustup").args(["which", "--toolchain", toolchain(), name]))?
                .trim(),
        );
        tools.insert(name.into(), artifact(&path)?);
    }
    let controller = Run {
        schema_version: 2,
        output: controller_output,
        snapshot: frozen,
        target_root,
        seconds: 30.0,
        artifacts: BTreeMap::new(),
        tools,
        environment: json!({"toolchain":toolchain()}),
        branch: capture_text(
            command("git")
                .current_dir(&edit)
                .args(["branch", "--show-current"]),
        )?
        .trim()
        .into(),
        revision: capture_text(
            command("git")
                .current_dir(&edit)
                .args(["rev-parse", "HEAD"]),
        )?
        .trim()
        .into(),
        power_policy: None,
        publication_root: Some(output.clone()),
    };
    let mut job = ReportJob {
        evidence,
        output,
        findings,
        controller,
    };
    let mut test = cargo_command(
        &job.controller,
        &job.controller.target_root.join("checks"),
        false,
    );
    test.args(["test", "--locked", "--offline", "-p", "flock-performance"]);
    checked(&job.controller, &mut test, "processor-tests")?;
    let binaries = build(
        &job.controller,
        &job.controller.target_root.join("tools"),
        false,
        "flock-performance",
        &["--bin", "profile_preimages"],
        "build-processor",
    )?;
    job.controller.artifacts.insert(
        "profile_preimages".into(),
        artifact(&binaries["profile_preimages"])?,
    );
    let manifest = job.controller.output.join("manifest.json");
    atomic_json(&manifest, &job)?;
    let mut child = command(&job.controller.artifacts["profile_preimages"].path);
    child
        .current_dir(&job.controller.snapshot.root)
        .arg("--report-frozen")
        .arg(&manifest);
    drop(ownership);
    logged(
        &mut child,
        &job.controller.output.join("logs"),
        "frozen-publication",
    )
}

fn report_frozen(path: &Path) -> Result<()> {
    let job: ReportJob = serde_json::from_slice(&fs::read(path)?)?;
    verify_run(&job.controller)?;
    if fs::canonicalize(env::current_exe()?)? != job.controller.artifacts["profile_preimages"].path
    {
        return Err("report requires the registered frozen processing executable".into());
    }
    let processor = snapshot::ProcessorIdentity::register(
        &job.controller.snapshot,
        &job.controller.output.join("source"),
        &job.controller.artifacts["profile_preimages"].path,
    )?;
    let gallery = crate::publication::publish(
        &job.evidence,
        &job.output,
        job.findings.as_deref(),
        &processor,
    )?;
    verify_run(&job.controller)?;
    eprintln!("Published: {}", gallery.display());
    Ok(())
}

pub fn main() {
    // The handler only stores an atomic flag; child status and evidence are also checked.
    unsafe {
        libc::signal(libc::SIGINT, interrupt as *const () as libc::sighandler_t);
        libc::signal(libc::SIGTERM, interrupt as *const () as libc::sighandler_t);
    }
    if let Err(error) = main_result() {
        eprintln!("profile_preimages: {error}");
        std::process::exit(1);
    }
}

fn main_result() -> Result<()> {
    let args: Vec<_> = env::args_os().skip(1).collect();
    if args.first().is_some_and(|a| a == "--current") && args.len() == 2 {
        println!(
            "{}",
            crate::publication::current(Path::new(&args[1]))?.display()
        );
        return Ok(());
    }
    if args.first().is_some_and(|a| a == "--recover-publication")
        && args.len() == 4
        && args[2] == "--generation"
    {
        println!(
            "{}",
            crate::publication::recover_ready(
                Path::new(&args[1]),
                args[3].to_str().ok_or("generation ID must be Unicode")?
            )?
            .display()
        );
        return Ok(());
    }
    if args.first().is_some_and(|a| a == "--resume") && args.len() == 2 {
        return bootstrap_resume(Path::new(&args[1]));
    }
    if args.first().is_some_and(|a| a == "--resume-frozen") && args.len() == 2 {
        let resume: Resume = serde_json::from_slice(&fs::read(&args[1])?)?;
        verify_run(&resume.controller)?;
        if fs::canonicalize(env::current_exe()?)?
            != resume.controller.artifacts["profile_preimages"].path
        {
            return Err("resume mode requires the registered snapshot-built controller".into());
        }
        if resume
            .controller
            .output
            .join("measurement-started.json")
            .exists()
        {
            return Err(
                "controller already started an episode; --resume allocates a fresh controller"
                    .into(),
            );
        }
        atomic_json(
            &resume.controller.output.join("measurement-started.json"),
            &json!({"started_unix_seconds":epoch()}),
        )?;
        let outcome = measurement::resume(&resume);
        if let Err(error) = &outcome {
            preserve_failure(
                &resume.controller.output,
                "resume-controller",
                &error.to_string(),
            )?;
        }
        return outcome;
    }
    if args.first().is_some_and(|a| a == "--frozen-run") && args.len() == 2 {
        let run: Run = serde_json::from_slice(&fs::read(&args[1])?)?;
        verify_run(&run)?;
        let own = fs::canonicalize(env::current_exe()?)?;
        if own != run.artifacts["profile_preimages"].path {
            return Err("frozen mode must run the registered snapshot-built runner".into());
        }
        if run.output.join("episodes").exists()
            || run.output.join("complete.json").exists()
            || run.output.join("measurements-complete.json").exists()
        {
            return Err(
                "frozen run already started; use --resume or --report for the recorded state"
                    .into(),
            );
        }
        let outcome = measurement::execute(&run, &run, &PathBuf::from(&args[1]));
        if let Err(error) = &outcome {
            preserve_failure(&run.output, "measurement-controller", &error.to_string())?;
        }
        return outcome;
    }
    if args
        .first()
        .is_some_and(|a| a == "--integration-smoke-frozen")
        && args.len() == 2
    {
        return measurement::integration_smoke(Path::new(&args[1]));
    }
    if args.first().is_some_and(|a| a == "--report") {
        return report_command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "--report-frozen") && args.len() == 2 {
        return report_frozen(Path::new(&args[1]));
    }
    let mut seconds: f64 = 30.0;
    let mut output = None;
    let mut power_policy = host::PowerPolicy::RequireAc;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.to_str() {
            Some("--seconds") => {
                seconds = it
                    .next()
                    .ok_or("missing seconds")?
                    .to_str()
                    .ok_or("invalid seconds")?
                    .parse()?
            }
            Some("--output") => output = Some(PathBuf::from(it.next().ok_or("missing output")?)),
            Some("--power-policy") => {
                power_policy = match it.next().and_then(|s| s.to_str()) {
                    Some("require-ac") => host::PowerPolicy::RequireAc,
                    Some("observe-only") => host::PowerPolicy::ObserveOnly,
                    _ => return Err("--power-policy requires require-ac or observe-only".into()),
                };
            }
            _ => {
                return Err(
                    "usage: profile_preimages --seconds 30 --output <new-directory>".into(),
                );
            }
        }
    }
    if !seconds.is_finite() || seconds < 30.0 {
        return Err("primary captures require finite --seconds >= 30".into());
    }
    let edit =
        PathBuf::from(capture_text(command("git").args(["rev-parse", "--show-toplevel"]))?.trim());
    let requested = output.ok_or("--output is required")?;
    let output = if requested.is_absolute() {
        requested
    } else {
        edit.join(requested)
    };
    fs::create_dir_all(output.parent().ok_or("output needs a parent")?)?;
    fs::create_dir(&output)?;
    let output = fs::canonicalize(output)?;
    fs::create_dir(output.join("logs"))?;
    let prepared = bootstrap(&edit, &output, seconds, power_policy);
    if let Err(error) = &prepared {
        atomic_json(
            &output.join("bootstrap-failure.json"),
            &json!({"stage":"bootstrap","error":error.to_string(),"time":epoch()}),
        )?;
        preserve_failure(&output, "bootstrap", &error.to_string())?;
    }
    prepared
}

fn read_measurement(resume: &Resume) -> Result<Run> {
    if sha256(&resume.measurement_manifest.path)? != resume.measurement_manifest.sha256 {
        return Err("original measurement manifest changed".into());
    }
    let run: Run = serde_json::from_slice(&fs::read(&resume.measurement_manifest.path)?)?;
    verify_run(&run)?;
    Ok(run)
}

fn preserved_evidence(root: &Path) -> Result<BTreeMap<PathBuf, Artifact>> {
    let mut files = BTreeMap::new();
    for prefix in ["cases", "episodes"] {
        let directory = root.join(prefix);
        if !directory.exists() {
            continue;
        }
        for (relative, identity) in evidence::inventory(&directory, &[])?.files {
            let name = PathBuf::from(prefix).join(relative);
            if name.file_name().is_some_and(|file| file == "attempt.json") {
                let value: Value = serde_json::from_slice(&fs::read(root.join(&name))?)?;
                if value["status"] == "validated" {
                    let attempt = serde_json::from_value(value)?;
                    records::verify_recorded_evidence(
                        root.join(&name).parent().ok_or("attempt parent missing")?,
                        &attempt,
                    )?;
                }
            }
            files.insert(
                name.clone(),
                Artifact {
                    path: root.join(name).canonicalize()?,
                    sha256: identity.sha256,
                },
            );
        }
    }
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let name = entry.file_name();
        if (name.to_string_lossy().starts_with("baseline-") || name == "incomplete.json")
            && entry.file_type()?.is_file()
        {
            files.insert(PathBuf::from(name), artifact(&entry.path())?);
        }
    }
    Ok(files)
}

fn verify_preserved(resume: &Resume) -> Result<()> {
    for (name, original) in &resume.preserved_evidence {
        if sha256(&original.path)? != original.sha256 {
            return Err(format!("saved measurement evidence changed: {}", name.display()).into());
        }
    }
    Ok(())
}

fn bootstrap_resume(manifest: &Path) -> Result<()> {
    let measurement_manifest = artifact(manifest)?;
    let run: Run = serde_json::from_slice(&fs::read(&measurement_manifest.path)?)?;
    if measurement_manifest.path != fs::canonicalize(run.output.join("manifest.json"))? {
        return Err("resume manifest must be the original output manifest".into());
    }
    verify_run(&run)?;
    measurement::validate_resume(&run)?;
    let ownership = evidence::WriterLock::acquire(&run.output)?;
    measurement::validate_resume(&run)?;
    let edit = &run.snapshot.editing_root;
    let branch = capture_text(
        command("git")
            .current_dir(edit)
            .args(["branch", "--show-current"]),
    )?
    .trim()
    .to_owned();
    let revision = capture_text(command("git").current_dir(edit).args(["rev-parse", "HEAD"]))?
        .trim()
        .to_owned();
    if !branch.starts_with("chore/") || revision != run.revision {
        return Err("resume requires the original revision and task chore/ branch".into());
    }
    let id = unique_id("controller");
    let output = run.output.join("controllers").join(&id);
    fs::create_dir_all(output.parent().ok_or("controller parent missing")?)?;
    fs::create_dir(&output)?;
    fs::create_dir(output.join("logs"))?;
    let target_root = run.target_root.join(&id);
    fs::create_dir(&target_root)?;
    for role in ["checks", "tools"] {
        fs::create_dir(target_root.join(role))?;
    }
    let evidence = preserved_evidence(&run.output)?;
    eprintln!(
        "Freezing and validating a separate resume controller; workload binaries remain registered to the original snapshot"
    );
    let frozen = snapshot::prepare(edit, &output)?;
    let profiler_version =
        capture_text(command(&run.tools["profiler"].path).args(["flamegraph", "--version"]))?;
    let mut controller = Run {
        schema_version: 2,
        output,
        snapshot: frozen,
        target_root,
        seconds: run.seconds,
        artifacts: BTreeMap::new(),
        tools: run.tools.clone(),
        environment: host_environment(&profiler_version)?,
        branch,
        revision,
        power_policy: run.power_policy,
        publication_root: run.publication_root.clone(),
    };
    let checks = controller.target_root.join("checks");
    let mut make = command("make");
    configure(&controller, &mut make, &checks, false);
    make.arg("test");
    checked(&controller, &mut make, "make-test")?;
    let binaries = build(
        &controller,
        &controller.target_root.join("tools"),
        false,
        "flock-performance",
        &["--bin", "profile_preimages"],
        "build-resume-controller",
    )?;
    controller.artifacts.insert(
        "profile_preimages".into(),
        artifact(&binaries["profile_preimages"])?,
    );
    let resume = Resume {
        measurement_manifest,
        controller,
        preserved_evidence: evidence,
    };
    verify_preserved(&resume)?;
    read_measurement(&resume)?;
    verify_run(&resume.controller)?;
    let config = resume.controller.output.join("manifest.json");
    atomic_json(&config, &resume)?;
    let mut child = command(&resume.controller.artifacts["profile_preimages"].path);
    child
        .current_dir(&resume.controller.snapshot.root)
        .arg("--resume-frozen")
        .arg(config)
        .process_group(0);
    drop(ownership);
    logged(
        &mut child,
        &resume.controller.output.join("logs"),
        "resume-controller",
    )
}

fn bootstrap(
    edit: &Path,
    output: &Path,
    seconds: f64,
    power_policy: host::PowerPolicy,
) -> Result<()> {
    let branch = capture_text(
        command("git")
            .current_dir(edit)
            .args(["branch", "--show-current"]),
    )?
    .trim()
    .to_owned();
    if !branch.starts_with("chore/") {
        return Err("create the task's chore/ branch before running the plan".into());
    }
    let revision = capture_text(command("git").current_dir(edit).args(["rev-parse", "HEAD"]))?
        .trim()
        .to_owned();
    let metadata: Value = serde_json::from_str(&capture_text(
        command("cargo")
            .current_dir(edit)
            .env("RUSTUP_TOOLCHAIN", toolchain())
            .args(["metadata", "--locked", "--no-deps", "--format-version", "1"]),
    )?)?;
    let target_root = PathBuf::from(
        metadata["target_directory"]
            .as_str()
            .ok_or("Cargo target directory missing")?,
    )
    .join("preimage-flamegraphs")
    .join(output.file_name().ok_or("run ID missing")?);
    fs::create_dir_all(target_root.parent().ok_or("target root has no parent")?)?;
    fs::create_dir(&target_root)?;
    for role in [
        "checks",
        "tools",
        "performance-normal",
        "performance-symbols",
    ] {
        fs::create_dir(target_root.join(role))?;
    }
    eprintln!("Preparing private source snapshot for {}", output.display());
    let frozen = snapshot::prepare(edit, output)?;
    let profiler = edit.join("target/profiling-tools/flamegraph-0.6.13/bin/cargo-flamegraph");
    let profiler_version = capture_text(command(&profiler).args(["flamegraph", "--version"]))?;
    if !profiler_version.contains("0.6.13") {
        return Err(format!("expected flamegraph 0.6.13, got {profiler_version}").into());
    }
    let xctrace = PathBuf::from(capture_text(command("xcrun").args(["-f", "xctrace"]))?.trim());
    let cargo = PathBuf::from(
        capture_text(command("rustup").args(["which", "--toolchain", toolchain(), "cargo"]))?
            .trim(),
    );
    let rustc = PathBuf::from(
        capture_text(command("rustup").args(["which", "--toolchain", toolchain(), "rustc"]))?
            .trim(),
    );
    let dsymutil = PathBuf::from(capture_text(command("xcrun").args(["-f", "dsymutil"]))?.trim());
    let renderer = PathBuf::from(capture_text(command("which").arg("rsvg-convert"))?.trim());
    let tools = [
        ("profiler", profiler),
        ("xctrace", xctrace),
        ("cargo", cargo),
        ("rustc", rustc),
        ("dsymutil", dsymutil),
        ("svg-renderer", renderer),
    ]
    .into_iter()
    .map(|(k, p)| Ok((k.to_owned(), artifact(&p)?)))
    .collect::<Result<_>>()?;
    let environment = host_environment(&profiler_version)?;
    let mut run = Run {
        schema_version: 2,
        output: output.to_owned(),
        snapshot: frozen,
        target_root,
        seconds,
        artifacts: BTreeMap::new(),
        tools,
        environment,
        branch,
        revision,
        power_policy: Some(power_policy),
        publication_root: Some(output.with_file_name(format!(
                "{}-publication",
                output
                    .file_name()
                    .ok_or("run name missing")?
                    .to_string_lossy()
            ))),
    };
    atomic_json(
        &output.join("bootstrap.json"),
        &json!({"executable":artifact(&env::current_exe()?)?,"collects_measurements":false}),
    )?;
    atomic_json(&output.join("manifest.json"), &run)?;
    let checks = run.target_root.join("checks");
    let mut fmt = cargo_command(&run, &checks, false);
    fmt.args(["fmt", "--all", "--", "--check"]);
    checked(&run, &mut fmt, "format")?;
    let mut tests = cargo_command(&run, &checks, false);
    tests.args(["test", "--locked", "-p", "flock-performance"]);
    checked(&run, &mut tests, "performance-tests")?;
    let mut make = command("make");
    configure(&run, &mut make, &checks, false);
    make.arg("test");
    checked(&run, &mut make, "make-test")?;
    let preliminary = build(
        &run,
        &checks,
        false,
        "flock-prover",
        &[
            "--features",
            "veil",
            "--example",
            "preimage_profile",
            "--example",
            "preimage_scaling",
        ],
        "correctness-build",
    )?;
    for size in SIZES {
        for protocol in ["flock", "full-zk"] {
            for operation in ["prove", "verify"] {
                let id = format!("correctness-{protocol}-{operation}-{size:04}");
                let meta = run.output.join("logs").join(format!("{id}.json"));
                let mut c = command(&preliminary["preimage_profile"]);
                c.current_dir(&run.snapshot.root)
                    .args([
                        "--protocol",
                        protocol,
                        "--operation",
                        operation,
                        "--hashes",
                        &size.to_string(),
                        "--seconds",
                        "0.01",
                        "--attempt-id",
                        &id,
                        "--metadata",
                    ])
                    .arg(&meta);
                checked(&run, &mut c, &id)?;
                validate_harness(
                    &meta,
                    &id,
                    protocol,
                    operation,
                    size,
                    0.01,
                    &frozen_policy(&run)?,
                )?;
            }
        }
    }
    let mut compatibility = command(&preliminary["preimage_scaling"]);
    compatibility.current_dir(&run.snapshot.root).arg("1");
    checked(&run, &mut compatibility, "baseline-compatibility")?;
    report::read_baseline(&run.output.join("logs/baseline-compatibility.stdout"))?;
    let invalid_meta = run.output.join("logs/invalid-harness.json");
    for (flag, value) in [
        ("--seconds", "0"),
        ("--protocol", "invalid"),
        ("--hashes", "65"),
    ] {
        let mut args = vec![
            "--protocol",
            "flock",
            "--operation",
            "prove",
            "--hashes",
            "64",
            "--seconds",
            "0.01",
            "--attempt-id",
            "invalid-arguments",
        ];
        let index = args
            .iter()
            .position(|item| item == &flag)
            .expect("known argument");
        args[index + 1] = value;
        verify_run(&run)?;
        let result = command(&preliminary["preimage_profile"])
            .current_dir(&run.snapshot.root)
            .args(args)
            .arg("--metadata")
            .arg(&invalid_meta)
            .output()?;
        if result.status.success() {
            return Err("invalid harness arguments unexpectedly succeeded".into());
        }
        atomic_json(
            &run.output
                .join("logs")
                .join(format!("invalid-{}.json", flag.trim_start_matches('-'))),
            &json!({"successfully_rejected":true,"stderr":String::from_utf8_lossy(&result.stderr)}),
        )?;
        verify_run(&run)?;
    }
    // Simulate a recorder injecting a diagnostic after the runner has applied
    // its policy. The launched harness must reject it before constructing pools.
    let reintroduced = command(&preliminary["preimage_profile"])
        .current_dir(&run.snapshot.root)
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
            "environment-reintroduced",
            "--metadata",
        ])
        .arg(&invalid_meta)
        .output()?;
    if reintroduced.status.success() || invalid_meta.exists() {
        return Err(
            "harness accepted a reintroduced diagnostic or emitted success metadata".into(),
        );
    }
    atomic_json(
        &run.output.join("logs/reintroduced-environment.json"),
        &json!({"successfully_rejected":true,"stderr":String::from_utf8_lossy(&reintroduced.stderr)}),
    )?;
    verify_run(&run)?;
    let normal = build(
        &run,
        &run.target_root.join("performance-normal"),
        false,
        "flock-prover",
        &["--features", "veil", "--example", "preimage_scaling"],
        "build-normal",
    )?;
    run.artifacts.insert(
        "baseline-normal".into(),
        artifact(&normal["preimage_scaling"])?,
    );
    let symbols = build(
        &run,
        &run.target_root.join("performance-symbols"),
        true,
        "flock-prover",
        &[
            "--features",
            "veil",
            "--example",
            "preimage_scaling",
            "--example",
            "preimage_profile",
        ],
        "build-symbols",
    )?;
    run.artifacts.insert(
        "baseline-symbols".into(),
        artifact(&symbols["preimage_scaling"])?,
    );
    run.artifacts.insert(
        "preimage_profile".into(),
        artifact(&symbols["preimage_profile"])?,
    );
    let tools = build(
        &run,
        &run.target_root.join("tools"),
        false,
        "flock-performance",
        &["--bins"],
        "build-tools",
    )?;
    for name in ["profile_preimages", "xctrace_capture", "folded_capture"] {
        run.artifacts.insert(name.into(), artifact(&tools[name])?);
    }
    preserve_symbols(&run)?;
    atomic_json(&output.join("builds.json"), &run.artifacts)?;
    atomic_json(&output.join("manifest.json"), &run)?;
    verify_run(&run)?;
    let mut accepted = command(&run.artifacts["profile_preimages"].path);
    accepted
        .current_dir(&run.snapshot.root)
        .arg("--frozen-run")
        .arg(output.join("manifest.json"));
    accepted.process_group(0);
    logged(&mut accepted, &output.join("logs"), "frozen-runner")
}

fn preserve_symbols(run: &Run) -> Result<()> {
    let directory = run.output.join("build-artifacts");
    fs::create_dir(&directory)?;
    let executable = directory.join("preimage_profile");
    fs::copy(&run.artifacts["preimage_profile"].path, &executable)?;
    let mut dsym = command(&run.tools["dsymutil"].path);
    dsym.current_dir(&run.snapshot.root)
        .arg(&run.artifacts["preimage_profile"].path)
        .arg("-o")
        .arg(directory.join("preimage_profile.dSYM"));
    checked(run, &mut dsym, "archive-debug-symbols")?;
    if sha256(&executable)? != run.artifacts["preimage_profile"].sha256 {
        return Err("archived profiling executable differs from registered build".into());
    }
    Ok(())
}

fn configure(run: &Run, c: &mut Command, target: &Path, symbols: bool) {
    c.current_dir(&run.snapshot.root)
        .env(
            "RUSTUP_TOOLCHAIN",
            run.environment["toolchain"].as_str().unwrap_or(toolchain()),
        )
        .env("CARGO_TARGET_DIR", target);
    c.env_remove("CARGO_PROFILE_RELEASE_DEBUG")
        .env_remove("CARGO_PROFILE_RELEASE_STRIP");
    if symbols {
        c.env("CARGO_PROFILE_RELEASE_DEBUG", "2")
            .env("CARGO_PROFILE_RELEASE_STRIP", "none");
    }
    // cargo-flamegraph and Make invoke Cargo by name. Resolve that name to the
    // same recorded toolchain, regardless of the caller's PATH ordering.
    let mut paths = vec![
        run.tools["cargo"]
            .path
            .parent()
            .expect("Cargo has parent")
            .to_owned(),
    ];
    paths.extend(env::split_paths(&env::var_os("PATH").unwrap_or_default()));
    c.env(
        "PATH",
        env::join_paths(paths).expect("existing PATH and toolchain are valid"),
    );
}

fn cargo_command(run: &Run, target: &Path, symbols: bool) -> Command {
    let mut c = command(&run.tools["cargo"].path);
    configure(run, &mut c, target, symbols);
    c
}

fn build(
    run: &Run,
    target: &Path,
    symbols: bool,
    package: &str,
    extra: &[&str],
    label: &str,
) -> Result<BTreeMap<String, PathBuf>> {
    let mut c = cargo_command(run, target, symbols);
    c.args(["build", "--locked", "--release", "--manifest-path"])
        .arg(run.snapshot.root.join("Cargo.toml"))
        .args(["--message-format", "json-render-diagnostics", "-p", package])
        .args(extra);
    checked(run, &mut c, label)?;
    let mut paths = BTreeMap::new();
    for line in fs::read_to_string(run.output.join("logs").join(format!("{label}.stdout")))?.lines()
    {
        if let Ok(v) = serde_json::from_str::<Value>(line)
            && v["reason"] == "compiler-artifact"
            && let (Some(name), Some(path)) =
                (v["target"]["name"].as_str(), v["executable"].as_str())
        {
            let path = fs::canonicalize(path)?;
            if !path.starts_with(fs::canonicalize(target)?) {
                return Err("Cargo artifact escaped its registered target directory".into());
            }
            paths.insert(name.to_owned(), path);
        }
    }
    Ok(paths)
}

fn checked(run: &Run, c: &mut Command, label: &str) -> Result<()> {
    verify_run(run)?;
    eprintln!("Running {label}");
    let result = logged(c, &run.output.join("logs"), label);
    verify_run(run)?;
    result
}

fn logged(c: &mut Command, logs: &Path, label: &str) -> Result<()> {
    process::logged(c, logs, label, &INTERRUPTED, Duration::from_secs(10))?.ensure_success()
}

fn unique_id(prefix: &str) -> String {
    format!(
        "{prefix}-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
    )
}

fn preserve_failure(directory: &Path, stage: &str, error: &str) -> Result<()> {
    let relative = PathBuf::from("failures").join(format!("{}.json", unique_id(stage)));
    let failure = json!({"stage":stage,"error":error,"time":epoch(),"record":relative});
    atomic_json(&directory.join(&relative), &failure)?;
    if !directory.join("incomplete.json").exists() {
        atomic_json(&directory.join("incomplete.json"), &failure)?;
    }
    Ok(())
}

fn frozen_policy(run: &Run) -> Result<Vec<String>> {
    Ok(serde_json::from_slice(&fs::read(
        run.snapshot
            .root
            .join("tools/performance/measurement-env.json"),
    )?)?)
}

fn verify_run(run: &Run) -> Result<()> {
    snapshot::verify(&run.snapshot)?;
    for (name, a) in run.artifacts.iter().chain(run.tools.iter()) {
        if fs::canonicalize(&a.path)? != a.path || sha256(&a.path)? != a.sha256 {
            return Err(format!("registered {name} executable changed").into());
        }
    }
    Ok(())
}

fn settle(run: &Run, label: &str) -> Result<()> {
    let observations = host_load();
    eprintln!("Settling for 30 seconds before baseline-{label}");
    for _ in 0..30 {
        if INTERRUPTED.load(Ordering::SeqCst) {
            return Err("interrupted during settling".into());
        }
        thread::sleep(Duration::from_secs(1));
    }
    atomic_json(
        &run.output.join(format!("settling-{label}.json")),
        &json!({"seconds":30,"before":observations,"after":host_load()}),
    )
}

fn baseline(run: &Run, symbols: bool, directory: &Path, label: &str) -> Result<()> {
    if directory.join(format!("{label}.csv")).exists()
        || directory
            .join("logs")
            .join(format!("{label}.command.json"))
            .exists()
    {
        return Err(format!("refusing to overwrite baseline {label}").into());
    }
    let name = if symbols {
        "baseline-symbols"
    } else {
        "baseline-normal"
    };
    let mut c = command(&run.artifacts[name].path);
    configure(
        run,
        &mut c,
        &run.target_root.join(if symbols {
            "performance-symbols"
        } else {
            "performance-normal"
        }),
        symbols,
    );
    c.arg("5");
    verify_run(run)?;
    logged(&mut c, &directory.join("logs"), label)?;
    verify_run(run)?;
    let source = directory.join("logs").join(format!("{label}.stdout"));
    report::read_baseline(&source)?;
    fs::copy(source, directory.join(format!("{label}.csv")))?;
    Ok(())
}

#[derive(Serialize, PartialEq, Eq)]
struct CacheStamp {
    bytes: u64,
    modified_seconds: i64,
    modified_nanoseconds: i64,
    sha256: String,
}

// cargo-flamegraph always invokes Cargo's build/freshness resolution. Source
// hashes alone cannot detect recompilation that produces identical bytes.
fn cache_stamps(root: &Path) -> Result<BTreeMap<PathBuf, CacheStamp>> {
    fn walk(
        root: &Path,
        directory: &Path,
        files: &mut BTreeMap<PathBuf, CacheStamp>,
    ) -> Result<()> {
        for entry in fs::read_dir(directory)? {
            let entry = entry?;
            let path = entry.path();
            let metadata = fs::symlink_metadata(&path)?;
            if metadata.is_dir() {
                walk(root, &path, files)?;
            } else if metadata.is_file() {
                files.insert(
                    path.strip_prefix(root)?.into(),
                    CacheStamp {
                        bytes: metadata.len(),
                        modified_seconds: metadata.mtime(),
                        modified_nanoseconds: metadata.mtime_nsec(),
                        sha256: sha256(&path)?,
                    },
                );
            } else {
                return Err("unsupported file in frozen measurement build cache".into());
            }
        }
        Ok(())
    }
    let mut files = BTreeMap::new();
    walk(root, root, &mut files)?;
    if !files
        .keys()
        .any(|path| path.starts_with("release/.fingerprint"))
    {
        return Err("measurement build cache lacks Cargo fingerprints; start a new run".into());
    }
    Ok(files)
}

fn unchanged_build_cache(
    before: &BTreeMap<PathBuf, CacheStamp>,
    after: &BTreeMap<PathBuf, CacheStamp>,
) -> bool {
    before.len() == after.len()
        && before.iter().all(|(path, previous)| {
            let Some(current) = after.get(path) else {
                return false;
            };
            if path == Path::new("release/examples/preimage_profile.d") {
                // Cargo rewrites this aggregate dep-info file even for a fresh
                // build. Its contents remain checked. Compiler fingerprints,
                // hashed dep-info and executable timestamps remain strict.
                previous.bytes == current.bytes && previous.sha256 == current.sha256
            } else {
                previous == current
            }
        })
}

fn capture(
    run: &Run,
    episode: &str,
    kind: &str,
    capture_case: &records::Case,
    seconds: f64,
    number: usize,
    acceptance_guard: impl Fn() -> Result<()>,
) -> Result<report::CaptureStats> {
    verify_run(run)?;
    let protocol = capture_case.protocol.as_str();
    let operation = capture_case.operation.as_str();
    let size = capture_case.hashes;
    let case = format!("{protocol}-{operation}-{size:04}");
    let id = format!("{kind}-{number:03}");
    let attempt_id = format!("{case}-{id}");
    let parent = run.output.join("cases").join(&case);
    fs::create_dir_all(&parent)?;
    let dir = parent.join(&id);
    fs::create_dir(&dir)?;
    fs::create_dir(dir.join("raw"))?;
    let scratch = run
        .snapshot
        .root
        .join(".profile-scratch")
        .join(&case)
        .join(&id);
    fs::create_dir_all(scratch.parent().ok_or("scratch parent missing")?)?;
    fs::create_dir(&scratch)?;
    let power_before = host::PowerObservation::observe();
    let mut attempt = json!({"schema_version":2,"episode_id":episode,"attempt_id":attempt_id,"kind":kind,"protocol":protocol,"operation":operation,"hashes":size,"requested_seconds":seconds,"snapshot_id":run.snapshot.id,"executable":run.artifacts["preimage_profile"],"status":"incomplete","selected":false,"load_before":host_load(),"power_before":power_before});
    atomic_json(&dir.join("attempt.json"), &attempt)?;
    run.power_policy
        .unwrap_or(host::PowerPolicy::ObserveOnly)
        .validate(&power_before)?;
    let mut c = cargo_command(run, &run.target_root.join("performance-symbols"), true);
    c.current_dir(&scratch).env("CARGO_NET_OFFLINE", "true");
    let profiler_bin = run.tools["profiler"]
        .path
        .parent()
        .ok_or("profiler bin missing")?;
    let mut paths = vec![profiler_bin.to_owned()];
    paths.push(
        run.tools["cargo"]
            .path
            .parent()
            .ok_or("Cargo bin missing")?
            .to_owned(),
    );
    paths.extend(env::split_paths(&env::var_os("PATH").unwrap_or_default()));
    c.env("PATH", env::join_paths(paths)?);
    c.env("XCTRACE", &run.artifacts["xctrace_capture"].path)
        .env("FLOCK_PROFILE_XCTRACE_BIN", &run.tools["xctrace"].path)
        .env("FLOCK_PROFILE_ATTEMPT_ID", &attempt_id)
        .env("FLOCK_PROFILE_ATTEMPT_DIR", &dir)
        .env("FLOCK_PROFILE_FOLDED_PATH", dir.join("stacks.folded"));
    c.args(["flamegraph", "--manifest-path"])
        .arg(run.snapshot.root.join("Cargo.toml"))
        .args([
            "-p",
            "flock-prover",
            "--features",
            "veil",
            "--example",
            "preimage_profile",
            "--deterministic",
            "--title",
        ])
        .arg(format!("{protocol} {operation} / {size} hashes ({kind})"))
        .arg("--post-process")
        .arg(quote_command(&run.artifacts["folded_capture"].path)?)
        .arg("-o")
        .arg(dir.join("flamegraph.svg"))
        .args([
            "--",
            "--protocol",
            protocol,
            "--operation",
            operation,
            "--hashes",
            &size.to_string(),
            "--seconds",
            &seconds.to_string(),
            "--attempt-id",
            &attempt_id,
            "--metadata",
        ])
        .arg(dir.join("harness.json"));
    eprintln!("Capturing {attempt_id}: {seconds}s");
    let outcome = (|| -> Result<report::CaptureStats> {
        let cache = run.target_root.join("performance-symbols");
        let cache_before = cache_stamps(&cache)?;
        atomic_json(&dir.join("cargo-cache-before.json"), &cache_before)?;
        let recording = logged(&mut c, &dir.join("logs"), "flamegraph");
        let cache_after = cache_stamps(&cache)?;
        atomic_json(&dir.join("cargo-cache-after.json"), &cache_after)?;
        if !unchanged_build_cache(&cache_before, &cache_after) {
            return Err("Cargo changed measurement build/cache files during capture; retained recording cannot be accepted, start a fresh run if measurement identities changed".into());
        }
        recording?;
        verify_run(run)?;
        validate_harness(
            &dir.join("harness.json"),
            &attempt_id,
            protocol,
            operation,
            size,
            seconds,
            &frozen_policy(run)?,
        )?;
        for stage in ["record", "export"] {
            validate_stage(
                &dir.join(format!("{stage}-status.json")),
                &attempt_id,
                stage,
            )?;
        }
        if !dir.join("raw/recording.trace").is_dir() {
            return Err("missing archived trace".into());
        }
        let stats = report::analyze_capture(&dir)?;
        atomic_json(&dir.join("analysis.json"), &stats)?;
        let mut render = command(&run.tools["svg-renderer"].path);
        render
            .arg("--width")
            .arg("1200")
            .arg("--output")
            .arg(dir.join("preview.png"))
            .arg(dir.join("flamegraph.svg"));
        logged(&mut render, &dir.join("logs"), "render-svg")?;
        if fs::metadata(dir.join("preview.png"))?.len() == 0 {
            return Err("SVG renderer produced an empty preview".into());
        }
        if stats.usable_rows == 0 || stats.total_weight == 0 {
            return Err("capture has no usable stacks".into());
        }
        if !stats.has_workload_symbols {
            return Err("capture lacks symbolized workload frames".into());
        }
        if operation == "verify" && !stats.has_verifier_worker {
            return Err("capture lacks the verifier worker stacks".into());
        }
        if protocol == "full-zk" && operation == "prove" && !stats.has_rayon_worker {
            return Err("capture lacks Rayon worker stacks".into());
        }
        Ok(stats)
    })();
    match outcome {
        Ok(stats) => {
            attempt["stats"] = serde_json::to_value(&stats)?;
            attempt["load_after"] = host_load();
            let power_after = host::PowerObservation::observe();
            attempt["power_after"] = serde_json::to_value(&power_after)?;
            if let Err(error) = run
                .power_policy
                .unwrap_or(host::PowerPolicy::ObserveOnly)
                .validate(&power_after)
            {
                attempt["error"] = json!(error.to_string());
                atomic_json(&dir.join("attempt.json"), &attempt)?;
                return Err(error);
            }
            attempt["status"] = json!("validated");
            let selected = kind == "smoke" || stats.usable_rows >= 10_000;
            let promoted = kind == "primary" && selected;
            attempt["selected"] = json!(selected);
            attempt["promoted"] = json!(promoted);
            attempt["evidence_inventory"] =
                serde_json::to_value(evidence::inventory(&dir, &["attempt.json"])?)?;
            publish_attempt(&dir.join("attempt.json"), &mut attempt, acceptance_guard)?;
            eprintln!("Validated {attempt_id}: {} usable rows", stats.usable_rows);
            Ok(stats)
        }
        Err(error) => {
            attempt["error"] = json!(error.to_string());
            atomic_json(&dir.join("attempt.json"), &attempt)?;
            Err(error)
        }
    }
}

fn publish_attempt(
    path: &Path,
    attempt: &mut Value,
    acceptance_guard: impl Fn() -> Result<()>,
) -> Result<()> {
    if let Err(error) = acceptance_guard() {
        attempt["status"] = json!("incomplete");
        attempt["selected"] = json!(false);
        attempt["promoted"] = json!(false);
        attempt["error"] = json!(error.to_string());
        atomic_json(path, attempt)?;
        return Err(error);
    }
    atomic_json(path, attempt)
}

fn validate_stage(path: &Path, id: &str, stage: &str) -> Result<()> {
    records::validate_stage(path, id, stage).map(|_| ())
}

fn validate_harness(
    path: &Path,
    id: &str,
    protocol: &str,
    operation: &str,
    hashes: usize,
    seconds: f64,
    policy: &[String],
) -> Result<()> {
    records::read_harness(
        path,
        &records::Case::new(protocol, operation, hashes)?,
        id,
        seconds,
        policy,
    )
    .map(|_| ())
}

fn artifact(path: &Path) -> Result<Artifact> {
    Artifact::register(path)
}
fn epoch() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs_f64()
}
fn capture_text(c: &mut Command) -> Result<String> {
    let out = c.output()?;
    if !out.status.success() {
        return Err(format!(
            "{:?}: {}",
            c.get_program(),
            String::from_utf8_lossy(&out.stderr)
        )
        .into());
    }
    Ok(String::from_utf8(out.stdout)?)
}
fn quote_command(path: &Path) -> Result<String> {
    Ok(format!(
        "'{}'",
        path.to_str()
            .ok_or("post-process path must be Unicode")?
            .replace('\'', "'\\''")
    ))
}
fn observation(program: impl AsRef<OsStr>, args: &[&str]) -> Value {
    match command(program).args(args).output() {
        Ok(o) => {
            json!({"success":o.status.success(),"stdout":String::from_utf8_lossy(&o.stdout),"stderr":String::from_utf8_lossy(&o.stderr)})
        }
        Err(e) => json!({"error":e.to_string()}),
    }
}
fn host_load() -> Value {
    json!({"time":epoch(),"load":observation("sysctl", &["-n","vm.loadavg"]),"power":observation("pmset", &["-g","batt"]),"thermal":observation("pmset", &["-g","therm"])})
}
fn host_environment(profiler: &str) -> Result<Value> {
    Ok(
        json!({"cpu":observation("sysctl", &["-n","machdep.cpu.brand_string"]),"memory":observation("sysctl", &["-n","hw.memsize"]),"os":observation("sw_vers", &[]),"rustc":capture_text(command("rustup").args(["run",toolchain(),"rustc","-Vv"]))?,"cargo":capture_text(command("rustup").args(["run",toolchain(),"cargo","-V"]))?,"profiler":profiler,"xcode":observation("xcodebuild", &["-version"]),"power_settings":observation("pmset", &["-g","custom"]),"load":host_load(),"measurement_environment_removed":environment_keys(),"toolchain":toolchain()}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bootstrap_propagation_keeps_the_original_child_failure() -> Result<()> {
        let root = env::temp_dir().join(unique_id("flock-failure-test"));
        fs::create_dir(&root)?;
        preserve_failure(
            &root,
            "measurement-controller",
            "recorder interrupted during export",
        )?;
        let child = fs::read(root.join("incomplete.json"))?;
        preserve_failure(&root, "bootstrap", "child failed")?;
        assert_eq!(fs::read(root.join("incomplete.json"))?, child);
        let failures = fs::read_dir(root.join("failures"))?.collect::<std::io::Result<Vec<_>>>()?;
        assert_eq!(failures.len(), 2);
        assert!(failures.iter().any(|entry| {
            fs::read_to_string(entry.path())
                .unwrap()
                .contains("recorder interrupted during export")
        }));
        fs::remove_dir_all(root)?;
        Ok(())
    }

    #[test]
    fn cache_guard_detects_identical_rebuilds_and_missing_fingerprints() -> Result<()> {
        let root = env::temp_dir().join(unique_id("flock-cache-test"));
        let cache = root.join("release/.fingerprint/workload");
        fs::create_dir_all(&cache)?;
        let path = cache.join("invoked.timestamp");
        fs::write(&path, "same build output")?;
        let before = cache_stamps(&root)?;
        fs::File::options()
            .write(true)
            .open(&path)?
            .set_times(fs::FileTimes::new().set_modified(UNIX_EPOCH + Duration::from_secs(1)))?;
        let after = cache_stamps(&root)?;
        assert_eq!(
            before.values().next().unwrap().sha256,
            after.values().next().unwrap().sha256
        );
        assert!(
            !unchanged_build_cache(&before, &after),
            "identical bytes must not hide recompilation"
        );
        fs::remove_file(&path)?;
        assert!(cache_stamps(&root).is_err());
        fs::remove_dir_all(root)?;
        Ok(())
    }

    #[test]
    fn changed_controller_or_late_interruption_cannot_leave_a_selected_orphan() -> Result<()> {
        let root = env::temp_dir().join(unique_id("flock-acceptance-guard-test"));
        fs::create_dir(&root)?;
        for error in ["controller manifest changed", "interrupted during analysis"] {
            let mut attempt = json!({"status":"validated","selected":true,"promoted":true,"stats":{"usable_rows":10001}});
            let path = root.join("attempt.json");
            atomic_json(&path, &json!({"status":"incomplete"}))?;
            assert!(publish_attempt(&path, &mut attempt, || Err(error.into())).is_err());
            let saved: Value = serde_json::from_slice(&fs::read(&path)?)?;
            assert_eq!(saved["status"], "incomplete");
            assert_eq!(saved["selected"], false);
            assert_eq!(saved["promoted"], false);
            assert_eq!(saved["error"], error);
        }
        fs::remove_dir_all(root)?;
        Ok(())
    }

    #[test]
    fn cached_cargo_dep_info_touch_is_allowed_but_content_and_executable_changes_are_not()
    -> Result<()> {
        let root = env::temp_dir().join(unique_id("flock-cargo-dep-info-test"));
        fs::create_dir_all(root.join("release/.fingerprint/workload"))?;
        fs::write(
            root.join("release/.fingerprint/workload/invoked.timestamp"),
            "compiled",
        )?;
        fs::create_dir(root.join("release/examples"))?;
        let dep_info = root.join("release/examples/preimage_profile.d");
        let executable = root.join("release/examples/preimage_profile");
        fs::write(&dep_info, "recorded source dependencies")?;
        fs::write(&executable, "same executable")?;
        let before = cache_stamps(&root)?;
        let old_time = fs::FileTimes::new().set_modified(UNIX_EPOCH + Duration::from_secs(1));
        fs::File::options()
            .write(true)
            .open(&dep_info)?
            .set_times(old_time)?;
        let touched = cache_stamps(&root)?;
        assert!(unchanged_build_cache(&before, &touched));
        fs::File::options()
            .write(true)
            .open(&executable)?
            .set_times(old_time)?;
        assert!(!unchanged_build_cache(&touched, &cache_stamps(&root)?));
        fs::write(&dep_info, "different source dependencies")?;
        assert!(!unchanged_build_cache(&before, &cache_stamps(&root)?));
        fs::remove_dir_all(root)?;
        Ok(())
    }
    #[test]
    fn post_process_quote_preserves_spaces_and_single_quotes() {
        assert_eq!(
            quote_command(Path::new("/tmp/a b/helper")).unwrap(),
            "'/tmp/a b/helper'"
        );
        assert_eq!(
            quote_command(Path::new("/tmp/a'b/helper")).unwrap(),
            "'/tmp/a'\\''b/helper'"
        );
    }
}

//! Reproducible, local-only preimage profiling orchestration.
use std::{
    collections::BTreeMap,
    env,
    ffi::OsStr,
    fs::{self, File},
    os::unix::process::CommandExt,
    path::{Path, PathBuf},
    process::{Child, Command, ExitStatus, Stdio},
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use flock_performance::{
    Result, atomic_json, command, environment_keys, repair, report, sha256, snapshot,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

const SIZES: [usize; 7] = [64, 128, 256, 512, 1024, 2048, 4096];
const TOOLCHAIN: &str = "1.98.0";
static INTERRUPTED: AtomicBool = AtomicBool::new(false);

extern "C" fn interrupt(_: libc::c_int) {
    INTERRUPTED.store(true, Ordering::SeqCst);
}

#[derive(Clone, Serialize, Deserialize)]
struct Artifact {
    path: PathBuf,
    sha256: String,
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
}

#[derive(Serialize, Deserialize)]
struct Resume {
    measurement_manifest: Artifact,
    controller: Run,
    preserved_evidence: BTreeMap<PathBuf, Artifact>,
}

fn main() {
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
        let outcome = resume_measurements(&resume);
        if let Err(error) = &outcome {
            atomic_json(
                &resume.controller.output.join("incomplete.json"),
                &json!({"error":error.to_string(),"time":epoch()}),
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
        let outcome = measure(&run);
        if let Err(error) = &outcome {
            atomic_json(
                &run.output.join("incomplete.json"),
                &json!({"error":error.to_string(),"time":epoch(),"snapshot_id":run.snapshot.id}),
            )?;
        }
        return outcome;
    }
    if args.first().is_some_and(|a| a == "--report") && args.len() == 2 {
        let output = Path::new(&args[1]);
        report::write_report(output)?;
        return artifact_inventory(output);
    }
    let mut seconds: f64 = 30.0;
    let mut output = None;
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
    let prepared = bootstrap(&edit, &output, seconds);
    if let Err(error) = &prepared {
        atomic_json(
            &output.join("incomplete.json"),
            &json!({"stage":"bootstrap","error":error.to_string(),"time":epoch()}),
        )?;
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
    fn walk(root: &Path, path: &Path, files: &mut BTreeMap<PathBuf, Artifact>) -> Result<()> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() {
                walk(root, &entry.path(), files)?;
            } else if entry.file_type()?.is_file() {
                files.insert(
                    entry.path().strip_prefix(root)?.to_owned(),
                    artifact(&entry.path())?,
                );
            } else {
                return Err("resume evidence contains a symlink or unsupported file".into());
            }
        }
        Ok(())
    }
    let mut files = BTreeMap::new();
    walk(root, &root.join("cases"), &mut files)?;
    for name in [
        "baseline-before.csv",
        "baseline-symbols.csv",
        "incomplete.json",
    ] {
        files.insert(PathBuf::from(name), artifact(&root.join(name))?);
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

// This continuation deliberately supports the documented checkpoint only.
// Other interruptions need a new checkpoint description before measuring.
fn validated_attempt(
    run: &Run,
    kind: &str,
    protocol: &str,
    operation: &str,
    size: usize,
) -> Result<Option<Value>> {
    let case = format!("{protocol}-{operation}-{size:04}");
    let mut found = None;
    for entry in fs::read_dir(run.output.join("cases").join(&case))? {
        let entry = entry?;
        let name = entry.file_name();
        let name = name.to_str().ok_or("non-Unicode attempt name")?;
        if !name.starts_with(&format!("{kind}-")) {
            continue;
        }
        let dir = entry.path();
        let v: Value = serde_json::from_slice(&fs::read(dir.join("attempt.json"))?)?;
        if v["status"] != "validated" {
            continue;
        }
        let id = format!("{case}-{name}");
        let seconds = v["requested_seconds"]
            .as_f64()
            .ok_or("missing capture duration")?;
        if v["attempt_id"] != id
            || v["kind"] != kind
            || v["protocol"] != protocol
            || v["operation"] != operation
            || v["hashes"] != size
            || v["snapshot_id"] != run.snapshot.id
            || v["executable"] != serde_json::to_value(&run.artifacts["preimage_profile"])?
            || !seconds.is_finite()
            || seconds < if kind == "smoke" { 5.0 } else { run.seconds }
            || v["stats"]["usable_rows"].as_u64().unwrap_or(0)
                < if kind == "smoke" { 1 } else { 10_000 }
            || v["stats"]["has_workload_symbols"] != true
            || (operation == "verify" && v["stats"]["has_verifier_worker"] != true)
            || (protocol == "full-zk"
                && operation == "prove"
                && v["stats"]["has_rayon_worker"] != true)
            || (kind == "primary" && v["promoted"] != true)
        {
            return Err(format!("invalid saved attempt {id}").into());
        }
        validate_harness(
            &dir.join("harness.json"),
            &id,
            protocol,
            operation,
            size,
            seconds,
        )?;
        for stage in ["record", "export"] {
            validate_stage(&dir.join(format!("{stage}-status.json")), &id, stage)?;
        }
        if !dir.join("raw/recording.trace").is_dir() || !dir.join("raw/time-profile.xml").is_file()
        {
            return Err(format!("missing raw evidence for {id}").into());
        }
        if found.replace(v).is_some() {
            return Err(format!("ambiguous validated {kind} attempts for {case}").into());
        }
    }
    Ok(found)
}

fn validate_resume_checkpoint(run: &Run) -> Result<()> {
    if run.schema_version != 1 || !run.seconds.is_finite() || run.seconds < 30.0 {
        return Err("unsupported measurement manifest or duration".into());
    }
    let policy: Vec<String> = serde_json::from_slice(&fs::read(
        run.snapshot
            .root
            .join("tools/performance/measurement-env.json"),
    )?)?;
    if policy != environment_keys()
        || run.environment["measurement_environment_removed"] != json!(policy)
    {
        return Err(
            "resume controller differs from the original measurement environment policy".into(),
        );
    }
    let current = host_environment("flamegraph 0.6.13")?;
    for key in [
        "cpu",
        "memory",
        "os",
        "rustc",
        "cargo",
        "xcode",
        "toolchain",
    ] {
        if current[key] != run.environment[key] {
            return Err(format!("resume host or toolchain changed: {key}").into());
        }
    }
    for name in [
        "baseline-after.csv",
        "baseline-resume-before.csv",
        "complete.json",
        "measurements-complete.json",
        "report-processing.json",
        "resume.json",
    ] {
        if run.output.join(name).exists() {
            return Err(format!("resume would overwrite existing {name}").into());
        }
    }
    report::read_baseline(&run.output.join("baseline-before.csv"))?;
    report::read_baseline(&run.output.join("baseline-symbols.csv"))?;
    for size in SIZES {
        for protocol in ["flock", "full-zk"] {
            for operation in ["prove", "verify"] {
                if validated_attempt(run, "primary", protocol, operation, size)?.is_none() {
                    return Err("resume requires the complete validated primary matrix".into());
                }
                if [64, 4096].contains(&size) {
                    if validated_attempt(run, "smoke", protocol, operation, size)?.is_none() {
                        return Err("resume requires all eight validated smoke captures".into());
                    }
                    let repeat = validated_attempt(run, "repeat", protocol, operation, size)?;
                    if repeat.is_some() != (size == 64) {
                        return Err("resume checkpoint requires four 64-hash repeats and no accepted 4096-hash repeats".into());
                    }
                }
            }
        }
    }
    Ok(())
}

fn next_repeat(parent: &Path) -> Result<usize> {
    let mut highest = 1;
    for entry in fs::read_dir(parent)? {
        let entry = entry?;
        if let Some(number) = entry
            .file_name()
            .to_str()
            .and_then(|s| s.strip_prefix("repeat-"))
        {
            highest = highest.max(number.parse::<usize>()?);
        }
    }
    highest
        .checked_add(1)
        .ok_or_else(|| "repeat number overflow".into())
}

fn bootstrap_resume(manifest: &Path) -> Result<()> {
    let measurement_manifest = artifact(manifest)?;
    let run: Run = serde_json::from_slice(&fs::read(&measurement_manifest.path)?)?;
    if measurement_manifest.path != fs::canonicalize(run.output.join("manifest.json"))? {
        return Err("resume manifest must be the original output manifest".into());
    }
    verify_run(&run)?;
    validate_resume_checkpoint(&run)?;
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
    let output = run.output.join("resume-controller");
    fs::create_dir(&output)?;
    fs::create_dir(output.join("logs"))?;
    let target_root = run.target_root.join("resume-controller");
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
        schema_version: 1,
        output,
        snapshot: frozen,
        target_root,
        seconds: run.seconds,
        artifacts: BTreeMap::new(),
        tools: run.tools.clone(),
        environment: host_environment(&profiler_version)?,
        branch,
        revision,
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
    let status = wait_child(&mut child.spawn()?, "resumed frozen runner", 100)?;
    if !status.success() {
        return Err("resumed frozen runner failed; saved evidence retained".into());
    }
    Ok(())
}

fn resume_measurements(resume: &Resume) -> Result<()> {
    let run = read_measurement(resume)?;
    validate_resume_checkpoint(&run)?;
    verify_preserved(resume)?;
    let mut record = json!({"schema_version":1,"status":"in_progress","original_measurement_manifest":resume.measurement_manifest,
        "measurement_snapshot_id":run.snapshot.id,"controller_snapshot_id":resume.controller.snapshot.id,
        "controller":resume.controller.artifacts["profile_preimages"],"controller_manifest":"resume-controller/manifest.json",
        "started_unix_seconds":epoch(),"environment":host_environment("flamegraph 0.6.13")?,
        "pause_record":"incomplete.json","preserved_evidence_sha256":"resume-controller/manifest.json",
        "retained_primary_recordings":28,"retained_smokes":8,"retained_64_hash_repeats":4,
        "new_repeats":[],"limitation":"The primary episode has no immediate closing baseline; the new baselines bracket only the resumed 4096-hash repeats."});
    atomic_json(&run.output.join("resume.json"), &record)?;
    settle(&run, "resume-before")?;
    verify_run(&resume.controller)?;
    baseline(&run, false, "baseline-resume-before")?;
    verify_run(&resume.controller)?;
    for protocol in ["flock", "full-zk"] {
        for operation in ["prove", "verify"] {
            verify_run(&resume.controller)?;
            let case = format!("{protocol}-{operation}-4096");
            let number = next_repeat(&run.output.join("cases").join(&case))?.max(next_repeat(
                &run.snapshot.root.join(".profile-scratch").join(&case),
            )?);
            let stats = capture(
                &run,
                "repeat",
                protocol,
                operation,
                4096,
                run.seconds,
                number,
            )?;
            if stats.usable_rows < 10_000 {
                return Err("resumed endpoint repeat has insufficient samples".into());
            }
            verify_run(&resume.controller)?;
            record["new_repeats"].as_array_mut().ok_or("invalid resume record")?.push(json!({"case":case,"attempt":format!("repeat-{number:03}"),"usable_rows":stats.usable_rows}));
            atomic_json(&run.output.join("resume.json"), &record)?;
        }
    }
    settle(&run, "after")?;
    verify_run(&resume.controller)?;
    baseline(&run, false, "baseline-after")?;
    read_measurement(resume)?;
    verify_run(&resume.controller)?;
    verify_preserved(resume)?;
    record["status"] = json!("measurements_complete");
    record["completed_unix_seconds"] = json!(epoch());
    record["load_after"] = host_load();
    atomic_json(&run.output.join("resume.json"), &record)?;
    atomic_json(
        &run.output.join("measurements-complete.json"),
        &json!({"snapshot_id":run.snapshot.id,"resumed":true,"completed_unix_seconds":epoch(),"primary_recordings":28,"endpoint_repeats":8}),
    )?;
    repair::repair_report(&run.output)?;
    verify_run(&resume.controller)?;
    read_measurement(resume)?;
    atomic_json(
        &run.output.join("complete.json"),
        &json!({"snapshot_id":run.snapshot.id,"controller_snapshot_id":resume.controller.snapshot.id,"completed_unix_seconds":epoch(),"primary_svgs":28,"resumed":true}),
    )?;
    eprintln!("Complete: {}", run.output.join("report.md").display());
    Ok(())
}

fn bootstrap(edit: &Path, output: &Path, seconds: f64) -> Result<()> {
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
            .env("RUSTUP_TOOLCHAIN", TOOLCHAIN)
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
        capture_text(command("rustup").args(["which", "--toolchain", TOOLCHAIN, "cargo"]))?.trim(),
    );
    let rustc = PathBuf::from(
        capture_text(command("rustup").args(["which", "--toolchain", TOOLCHAIN, "rustc"]))?.trim(),
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
        schema_version: 1,
        output: output.to_owned(),
        snapshot: frozen,
        target_root,
        seconds,
        artifacts: BTreeMap::new(),
        tools,
        environment,
        branch,
        revision,
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
                validate_harness(&meta, &id, protocol, operation, size, 0.01)?;
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
    let status = wait_child(&mut accepted.spawn()?, "frozen runner", 100)?;
    if !status.success() {
        return Err(format!("frozen runner failed: {status}").into());
    }
    Ok(())
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
        .env("RUSTUP_TOOLCHAIN", TOOLCHAIN)
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
    fs::create_dir_all(logs)?;
    let begin = Instant::now();
    let spec = json!({"program":c.get_program().to_string_lossy(),"args":c.get_args().map(|a|a.to_string_lossy()).collect::<Vec<_>>(),"cwd":c.get_current_dir(),"environment_overrides":c.get_envs().map(|(k,v)|(k.to_string_lossy(),v.map(|v|v.to_string_lossy()))).collect::<BTreeMap<_,_>>(),"started_unix_seconds":epoch()});
    atomic_json(&logs.join(format!("{label}.command.json")), &spec)?;
    c.stdout(Stdio::from(File::create(
        logs.join(format!("{label}.stdout")),
    )?));
    c.stderr(Stdio::from(File::create(
        logs.join(format!("{label}.stderr")),
    )?));
    c.process_group(0);
    let status = wait_child(&mut c.spawn()?, label, 50)?;
    atomic_json(
        &logs.join(format!("{label}.result.json")),
        &json!({"success":status.success(),"exit_code":status.code(),"status":status.to_string(),"elapsed_seconds":begin.elapsed().as_secs_f64(),"interrupted":INTERRUPTED.load(Ordering::SeqCst)}),
    )?;
    if !status.success() || INTERRUPTED.load(Ordering::SeqCst) {
        return Err(format!(
            "{label} failed ({status}); see {}",
            logs.join(format!("{label}.stderr")).display()
        )
        .into());
    }
    Ok(())
}

fn wait_child(child: &mut Child, label: &str, grace_ticks: usize) -> Result<ExitStatus> {
    let begin = Instant::now();
    let mut last = begin;
    loop {
        if INTERRUPTED.load(Ordering::SeqCst) {
            // Each command owns a process group. Terminate its descendants too;
            // a frozen runner gets time to propagate the interruption to its group.
            let group = -(i32::try_from(child.id())?);
            unsafe {
                libc::kill(group, libc::SIGTERM);
            }
            for _ in 0..grace_ticks {
                if child.try_wait()?.is_some() {
                    break;
                }
                thread::sleep(Duration::from_millis(100));
            }
            unsafe {
                libc::kill(group, libc::SIGKILL);
            }
            let _ = child.wait();
            return Err(
                "runner interrupted; child process group stopped and evidence remains incomplete"
                    .into(),
            );
        }
        if let Some(status) = child.try_wait()? {
            return Ok(status);
        }
        if last.elapsed() >= Duration::from_secs(30) {
            eprintln!(
                "{label}: still running ({:.0}s)",
                begin.elapsed().as_secs_f64()
            );
            last = Instant::now();
        }
        thread::sleep(Duration::from_millis(100));
    }
}

fn verify_run(run: &Run) -> Result<()> {
    if INTERRUPTED.load(Ordering::SeqCst) {
        return Err("runner interrupted".into());
    }
    snapshot::verify(&run.snapshot)?;
    for (name, a) in run.artifacts.iter().chain(run.tools.iter()) {
        if sha256(&a.path)? != a.sha256 {
            return Err(format!("registered {name} executable changed").into());
        }
    }
    Ok(())
}

fn measure(run: &Run) -> Result<()> {
    for size in [64, 4096] {
        for protocol in ["flock", "full-zk"] {
            for operation in ["prove", "verify"] {
                capture(run, "smoke", protocol, operation, size, 5.0, 1)?;
            }
        }
    }
    settle(run, "before")?;
    baseline(run, false, "baseline-before")?;
    baseline(run, true, "baseline-symbols")?;
    for size in SIZES {
        for protocol in ["flock", "full-zk"] {
            for operation in ["prove", "verify"] {
                let mut duration = run.seconds;
                let mut accepted = false;
                for attempt in 1..=3 {
                    let stats =
                        capture(run, "primary", protocol, operation, size, duration, attempt)?;
                    if stats.usable_rows >= 10_000 {
                        accepted = true;
                        break;
                    }
                    eprintln!(
                        "Low sample count {}; extending {protocol}/{operation}/{size}",
                        stats.usable_rows
                    );
                    duration *= 2.0;
                }
                if !accepted {
                    return Err(format!(
                        "insufficient usable samples for {protocol}/{operation}/{size}"
                    )
                    .into());
                }
            }
        }
    }
    for size in [64, 4096] {
        for protocol in ["flock", "full-zk"] {
            for operation in ["prove", "verify"] {
                capture(run, "repeat", protocol, operation, size, run.seconds, 1)?;
            }
        }
    }
    settle(run, "after")?;
    baseline(run, false, "baseline-after")?;
    verify_run(run)?;
    atomic_json(
        &run.output.join("measurements-complete.json"),
        &json!({
            "snapshot_id": run.snapshot.id,
            "completed_unix_seconds": epoch(),
            "primary_recordings": 28,
            "endpoint_repeats": 8
        }),
    )?;
    // Preserve upstream output, then rebuild frame boundaries from raw XML.
    // Rust array-type semicolons otherwise become false folded-stack frames.
    repair::repair_report(&run.output)?;
    atomic_json(
        &run.output.join("complete.json"),
        &json!({"snapshot_id":run.snapshot.id,"completed_unix_seconds":epoch(),"primary_svgs":28}),
    )?;
    eprintln!("Complete: {}", run.output.join("report.md").display());
    Ok(())
}

fn artifact_inventory(root: &Path) -> Result<()> {
    fn walk(root: &Path, relative: &Path, files: &mut BTreeMap<PathBuf, Value>) -> Result<()> {
        for entry in fs::read_dir(root.join(relative))? {
            let entry = entry?;
            let path = relative.join(entry.file_name());
            if relative.as_os_str().is_empty()
                && matches!(
                    entry.file_name().to_str(),
                    Some("artifacts.json" | "complete.json")
                )
            {
                continue;
            }
            let metadata = entry.metadata()?;
            if metadata.is_dir() {
                walk(root, &path, files)?;
            } else if metadata.is_file() {
                files.insert(
                    path.clone(),
                    json!({"bytes":metadata.len(),"sha256":sha256(&root.join(path))?}),
                );
            } else {
                return Err(format!("unsupported report artifact {}", path.display()).into());
            }
        }
        Ok(())
    }
    let mut files = BTreeMap::new();
    walk(root, Path::new(""), &mut files)?;
    atomic_json(
        &root.join("artifacts.json"),
        &json!({"schema_version":1,"exclusions":["artifacts.json","complete.json"],"files":files}),
    )
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

fn baseline(run: &Run, symbols: bool, label: &str) -> Result<()> {
    if run.output.join(format!("{label}.csv")).exists()
        || run
            .output
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
    checked(run, &mut c, label)?;
    let source = run.output.join("logs").join(format!("{label}.stdout"));
    report::read_baseline(&source)?;
    fs::copy(source, run.output.join(format!("{label}.csv")))?;
    Ok(())
}

fn capture(
    run: &Run,
    kind: &str,
    protocol: &str,
    operation: &str,
    size: usize,
    seconds: f64,
    number: usize,
) -> Result<report::CaptureStats> {
    verify_run(run)?;
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
    let mut attempt = json!({"attempt_id":attempt_id,"kind":kind,"protocol":protocol,"operation":operation,"hashes":size,"requested_seconds":seconds,"snapshot_id":run.snapshot.id,"executable":run.artifacts["preimage_profile"],"status":"incomplete","load_before":host_load()});
    atomic_json(&dir.join("attempt.json"), &attempt)?;
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
        logged(&mut c, &dir.join("logs"), "flamegraph")?;
        verify_run(run)?;
        validate_harness(
            &dir.join("harness.json"),
            &attempt_id,
            protocol,
            operation,
            size,
            seconds,
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
            attempt["status"] = json!("validated");
            attempt["stats"] = serde_json::to_value(&stats)?;
            attempt["load_after"] = host_load();
            let promoted = kind == "primary" && stats.usable_rows >= 10_000;
            attempt["promoted"] = json!(promoted);
            atomic_json(&dir.join("attempt.json"), &attempt)?;
            if promoted {
                fs::create_dir_all(run.output.join("svg"))?;
                fs::copy(
                    dir.join("flamegraph.svg"),
                    run.output.join("svg").join(format!("{case}.svg")),
                )?;
            }
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

fn validate_stage(path: &Path, id: &str, stage: &str) -> Result<()> {
    let v: Value = serde_json::from_slice(&fs::read(path)?)?;
    if v["attempt_id"] != id
        || v["stage"] != stage
        || v["success"] != true
        || v["io_ok"] != true
        || v["exit_code"] != 0
        || !v["signal"].is_null()
    {
        return Err(format!("{stage} wrapper status missing, failed, or mismatched").into());
    }
    Ok(())
}

fn validate_harness(
    path: &Path,
    id: &str,
    protocol: &str,
    operation: &str,
    hashes: usize,
    seconds: f64,
) -> Result<()> {
    let v: Value = serde_json::from_slice(&fs::read(path)?)?;
    if v["attempt_id"] != id
        || v["protocol"] != protocol
        || v["operation"] != operation
        || v["hashes"] != hashes
        || v["requested_seconds"].as_f64() != Some(seconds)
        || v["completed_calls"].as_u64().unwrap_or(0) == 0
        || v["loop_seconds"]
            .as_f64()
            .is_none_or(|n| !n.is_finite() || n < seconds)
        || v["final_validation"] != true
        || v["environment_absent"] != true
        || v["environment_keys"] != json!(environment_keys())
    {
        return Err("harness metadata is missing, stale, failed, or mismatched".into());
    }
    Ok(())
}

fn artifact(path: &Path) -> Result<Artifact> {
    Ok(Artifact {
        path: fs::canonicalize(path)?,
        sha256: sha256(path)?,
    })
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
        json!({"cpu":observation("sysctl", &["-n","machdep.cpu.brand_string"]),"memory":observation("sysctl", &["-n","hw.memsize"]),"os":observation("sw_vers", &[]),"rustc":capture_text(command("rustup").args(["run",TOOLCHAIN,"rustc","-Vv"]))?,"cargo":capture_text(command("rustup").args(["run",TOOLCHAIN,"cargo","-V"]))?,"profiler":profiler,"xcode":observation("xcodebuild", &["-version"]),"power_settings":observation("pmset", &["-g","custom"]),"load":host_load(),"measurement_environment_removed":environment_keys(),"toolchain":TOOLCHAIN}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
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
    #[test]
    fn resume_allocates_after_every_existing_repeat_without_reusing_interrupted_evidence() {
        let root = env::temp_dir().join(format!("flock-resume-id-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        assert_eq!(next_repeat(&root).unwrap(), 2);
        fs::create_dir(root.join("repeat-001")).unwrap();
        assert_eq!(next_repeat(&root).unwrap(), 2);
        fs::create_dir(root.join("repeat-003")).unwrap();
        fs::create_dir(root.join("primary-009")).unwrap();
        assert_eq!(next_repeat(&root).unwrap(), 4);
        fs::create_dir(root.join("repeat-broken")).unwrap();
        assert!(next_repeat(&root).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn acceptance_rejects_stale_short_and_failed_metadata() {
        let root = env::temp_dir().join(format!("flock-acceptance-{}", std::process::id()));
        fs::create_dir_all(&root).unwrap();
        let path = root.join("harness.json");
        let good = json!({"attempt_id":"a","protocol":"flock","operation":"prove","hashes":64,"requested_seconds":30.0,"completed_calls":2,"loop_seconds":30.1,"final_validation":true,"environment_absent":true,"environment_keys":environment_keys()});
        fs::write(&path, serde_json::to_vec(&good).unwrap()).unwrap();
        assert!(validate_harness(&path, "a", "flock", "prove", 64, 30.0).is_ok());
        for (key, value) in [
            ("attempt_id", json!("old")),
            ("loop_seconds", json!(29.9)),
            ("completed_calls", json!(0)),
            ("final_validation", json!(false)),
            ("environment_absent", json!(false)),
        ] {
            let mut bad = good.clone();
            bad[key] = value;
            fs::write(&path, serde_json::to_vec(&bad).unwrap()).unwrap();
            assert!(validate_harness(&path, "a", "flock", "prove", 64, 30.0).is_err());
        }
        fs::remove_dir_all(root).unwrap();
    }
}

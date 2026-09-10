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

use flock_performance::{Result, atomic_json, command, environment_keys, report, sha256, snapshot};
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
    report::write_report(&run.output)?;
    artifact_inventory(&run.output)?;
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

//! Preserve xctrace evidence before cargo-flamegraph removes its working trace.

use flock_performance::{
    Result, StageStatus, archive_trace, atomic_json, command, process, reject_overlap, tee,
};
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::io;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

static INTERRUPTED: AtomicBool = AtomicBool::new(false);

extern "C" fn interrupt(_: libc::c_int) {
    INTERRUPTED.store(true, Ordering::SeqCst);
}

fn record_outcome(
    attempt: &Path,
    status: &mut StageStatus,
    outcome: &process::CommandOutcome,
) -> Result<()> {
    status.exit_code = outcome.exit_code;
    status.signal = outcome.signal;
    status.success = outcome.success;
    atomic_json(
        &attempt.join(format!("{}-process.json", status.stage)),
        outcome,
    )
}

fn spawn(command: &mut Command, attempt: &Path, status: &mut StageStatus) -> Result<Child> {
    let begin = Instant::now();
    match command.spawn() {
        Ok(child) => Ok(child),
        Err(error) => {
            record_outcome(
                attempt,
                status,
                &process::CommandOutcome::spawn_failure(&error, begin.elapsed()),
            )?;
            Err(error.into())
        }
    }
}

fn wait(
    child: &mut Child,
    attempt: &Path,
    status: &mut StageStatus,
) -> Result<process::CommandOutcome> {
    let outcome = process::wait(child, &status.stage, &INTERRUPTED, Duration::from_secs(3));
    record_outcome(attempt, status, &outcome)?;
    Ok(outcome)
}

fn required(name: &str) -> Result<OsString> {
    env::var_os(name).ok_or_else(|| format!("missing {name}").into())
}

fn argument(args: &[OsString], name: &str) -> Result<PathBuf> {
    let index = args
        .iter()
        .position(|arg| arg == OsStr::new(name))
        .ok_or_else(|| format!("missing recorder {name} argument"))?;
    args.get(index + 1)
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing value after {name}").into())
}

fn absolute(path: &Path) -> Result<PathBuf> {
    Ok(if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir()?.join(path)
    })
}

fn execute(args: &[OsString], attempt: &Path, status: &mut StageStatus) -> Result<()> {
    let executable = PathBuf::from(required("FLOCK_PROFILE_XCTRACE_BIN")?);
    if !executable.is_absolute()
        || executable.canonicalize()? == env::current_exe()?.canonicalize()?
    {
        return Err("real xctrace must be an absolute path distinct from the wrapper".into());
    }
    let raw = attempt.join("raw");
    reject_overlap(&env::current_dir()?, &raw)?;
    fs::create_dir_all(&raw)?;
    let mut child = command(executable);
    child
        .args(args)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .process_group(0);
    match status.stage.as_str() {
        "record" => {
            let trace = absolute(&argument(args, "--output")?)?;
            let archive = raw.join("recording.trace");
            reject_overlap(&trace, &archive)?;
            let mut child = spawn(child.stdout(Stdio::inherit()), attempt, status)?;
            let outcome = wait(&mut child, attempt, status)?;
            // Preserve partial traces too, while retaining the original failure.
            let copied = archive_trace(&trace, &archive);
            status.io_ok = copied.is_ok();
            status.success = status.success && status.io_ok;
            outcome.ensure_success()?;
            copied?;
        }
        "export" => {
            let mut output = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(raw.join("time-profile.xml"))?;
            let mut child = spawn(child.stdout(Stdio::piped()), attempt, status)?;
            let stdout = child.stdout.take().ok_or("recorder stdout was not piped")?;
            let copier = std::thread::spawn(move || -> Result<()> {
                let copied = tee(stdout, &mut output, io::stdout().lock());
                let synced = output.sync_all();
                copied?;
                synced?;
                Ok(())
            });
            let outcome = wait(&mut child, attempt, status)?;
            let copied = copier.join().map_err(|_| "XML copy thread panicked")?;
            status.io_ok = copied.is_ok();
            status.success = status.success && status.io_ok;
            outcome.ensure_success()?;
            copied?;
        }
        _ => return Err("wrapper supports only xctrace record and export".into()),
    }
    if !status.success {
        return Err(format!(
            "recorder {} failed: exit {:?}, signal {:?}",
            status.stage, status.exit_code, status.signal
        )
        .into());
    }
    Ok(())
}

fn run() -> Result<bool> {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let stage = args
        .first()
        .and_then(|arg| arg.to_str())
        .ok_or("missing recorder stage")?
        .to_owned();
    if stage != "record" && stage != "export" {
        return Err("wrapper supports only xctrace record and export".into());
    }
    let attempt = absolute(&PathBuf::from(required("FLOCK_PROFILE_ATTEMPT_DIR")?))?;
    let attempt_id = env::var("FLOCK_PROFILE_ATTEMPT_ID")?;
    let status_path = attempt.join(format!("{stage}-status.json"));
    if status_path.exists() {
        return Err(format!("refusing to reuse {}", status_path.display()).into());
    }
    let mut status = StageStatus::new(attempt_id, stage);
    if let Err(error) = execute(&args, &attempt, &mut status) {
        status.success = false;
        status.error = Some(error.to_string());
    }
    atomic_json(&status_path, &status)?;
    if let Some(error) = status.error {
        eprintln!("xctrace_capture: {error}");
    }
    Ok(status.success)
}

fn main() {
    unsafe {
        libc::signal(libc::SIGINT, interrupt as *const () as libc::sighandler_t);
        libc::signal(libc::SIGTERM, interrupt as *const () as libc::sighandler_t);
    }
    let success = match run() {
        Ok(success) => success,
        Err(error) => {
            eprintln!("xctrace_capture: {error}");
            false
        }
    };
    // Never forward 54, SIGINT, or SIGTERM: cargo-flamegraph accepts those.
    std::process::exit(if success { 0 } else { 1 });
}

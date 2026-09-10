mod common;

use common::Temporary;
use flock_performance::{Result, process};
use std::fs;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

#[test]
fn spawn_failure_is_recorded_before_error_propagation() -> Result<()> {
    let temp = Temporary::new("spawn-failure")?;
    let mut command = Command::new(temp.join("nonexistent"));
    let outcome = process::logged(
        &mut command,
        temp.path(),
        "missing",
        &AtomicBool::new(false),
        Duration::from_millis(50),
    )?;
    assert!(!outcome.success);
    assert!(outcome.spawn_error.is_some());
    assert!(outcome.ensure_success().is_err());
    let persisted: process::CommandOutcome =
        serde_json::from_slice(&fs::read(temp.join("missing.result.json"))?)?;
    assert_eq!(persisted.spawn_error, outcome.spawn_error);
    Ok(())
}

#[test]
fn interrupted_zero_exit_is_not_successful() -> Result<()> {
    let temp = Temporary::new("interrupted-zero")?;
    let ready = temp.join("ready");
    let flag = Arc::new(AtomicBool::new(false));
    let trigger = Arc::clone(&flag);
    let marker = ready.clone();
    let interrupter = thread::spawn(move || {
        let deadline = Instant::now() + Duration::from_secs(5);
        while !marker.exists() && Instant::now() < deadline {
            thread::sleep(Duration::from_millis(10));
        }
        trigger.store(true, Ordering::SeqCst);
    });
    let mut command = Command::new("/bin/sh");
    command
        .args([
            "-c",
            "trap 'exit 0' TERM; printf ready > \"$1\"; while :; do sleep 1; done",
            "fixture",
        ])
        .arg(ready);
    let outcome = process::logged(
        &mut command,
        temp.path(),
        "zero",
        &flag,
        Duration::from_secs(1),
    )?;
    interrupter.join().unwrap();
    assert!(outcome.interrupted);
    assert_eq!(outcome.exit_code, Some(0));
    assert!(!outcome.success);
    assert!(outcome.cleanup.child_reaped);
    assert!(temp.join("zero.result.json").is_file());
    Ok(())
}

#[test]
fn process_fixture() {
    let Ok(mode) = std::env::var("FLOCK_OUTCOME_FIXTURE") else {
        return;
    };
    let ready = std::env::var_os("FLOCK_OUTCOME_READY").unwrap();
    if mode == "profiler" {
        let mut child = Command::new(std::env::current_exe().unwrap());
        child
            .args(["--exact", "process_fixture", "--nocapture"])
            .env("FLOCK_OUTCOME_FIXTURE", "workload")
            .process_group(0);
        let mut child = child.spawn().unwrap();
        let _ = child.wait();
    } else {
        unsafe {
            libc::signal(libc::SIGTERM, libc::SIG_IGN);
        }
        fs::write(ready, std::process::id().to_string()).unwrap();
        loop {
            thread::sleep(Duration::from_secs(1));
        }
    }
}

#[test]
#[cfg(target_os = "macos")]
fn cancellation_tracks_workload_that_escaped_the_profiler_group() -> Result<()> {
    let temp = Temporary::new("escaped-profiler")?;
    let ready = temp.join("ready");
    let flag = Arc::new(AtomicBool::new(false));
    let trigger = Arc::clone(&flag);
    let marker = ready.clone();
    let interrupter = thread::spawn(move || {
        let deadline = Instant::now() + Duration::from_secs(5);
        while !marker.exists() && Instant::now() < deadline {
            thread::sleep(Duration::from_millis(10));
        }
        thread::sleep(Duration::from_millis(250));
        trigger.store(true, Ordering::SeqCst);
    });
    let mut command = Command::new(std::env::current_exe()?);
    command
        .args(["--exact", "process_fixture", "--nocapture"])
        .env("FLOCK_OUTCOME_FIXTURE", "profiler")
        .env("FLOCK_OUTCOME_READY", &ready);
    let outcome = process::logged(
        &mut command,
        temp.path(),
        "profiler",
        &flag,
        Duration::from_millis(150),
    )?;
    interrupter.join().unwrap();
    let pid: i32 = fs::read_to_string(ready)?.parse()?;
    assert!(!outcome.success);
    assert!(
        outcome
            .cleanup
            .observed_descendants
            .iter()
            .any(|process| process.process_id == pid)
    );
    assert!(
        outcome.cleanup.observed_descendants_terminated,
        "{outcome:?}"
    );
    assert!(outcome.cleanup.child_reaped);
    assert!(!outcome.cleanup.external_service_workloads_verified);
    Ok(())
}

//! Process execution that records failure and cancellation before propagation.

use crate::{Result, atomic_json};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::Path;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct CleanupOutcome {
    pub attempted: bool,
    pub term_sent: bool,
    pub kill_sent: bool,
    pub child_reaped: bool,
    pub process_group_gone: bool,
    pub observed_descendants: Vec<ObservedProcess>,
    pub observed_descendants_terminated: bool,
    pub descendant_observation_error: Option<String>,
    /// A profiler may ask a system service to launch a workload outside its
    /// ancestry. Process-tree observation alone cannot verify that boundary.
    pub external_service_workloads_verified: bool,
    pub error: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ObservedProcess {
    pub process_id: i32,
    pub start_seconds: u64,
    pub start_microseconds: u64,
}

#[cfg(target_os = "macos")]
fn identity(pid: i32) -> std::io::Result<Option<(ObservedProcess, bool)>> {
    let mut info = std::mem::MaybeUninit::<libc::proc_bsdinfo>::zeroed();
    let size = std::mem::size_of::<libc::proc_bsdinfo>() as i32;
    let bytes = unsafe {
        libc::proc_pidinfo(
            pid,
            libc::PROC_PIDTBSDINFO,
            0,
            info.as_mut_ptr().cast(),
            size,
        )
    };
    if bytes != size {
        if unsafe { libc::kill(pid, 0) } != 0
            && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH)
        {
            return Ok(None);
        }
        return Err(std::io::Error::other(
            "cannot observe process start identity",
        ));
    }
    let info = unsafe { info.assume_init() };
    Ok(Some((
        ObservedProcess {
            process_id: pid,
            start_seconds: info.pbi_start_tvsec,
            start_microseconds: info.pbi_start_tvusec,
        },
        info.pbi_status == libc::SZOMB,
    )))
}

#[cfg(not(target_os = "macos"))]
fn identity(_pid: i32) -> std::io::Result<Option<(ObservedProcess, bool)>> {
    Err(std::io::Error::other(
        "descendant identity observation is supported only on macOS",
    ))
}

#[cfg(target_os = "macos")]
fn observe_descendants(
    child: &Child,
    known: &mut BTreeMap<i32, ObservedProcess>,
) -> std::io::Result<()> {
    let mut parents = vec![i32::try_from(child.id()).map_err(std::io::Error::other)?];
    for process in known.values() {
        if identity(process.process_id)?
            .is_some_and(|(current, zombie)| current == *process && !zombie)
        {
            parents.push(process.process_id);
        }
    }
    let mut visited = std::collections::BTreeSet::new();
    while let Some(parent) = parents.pop() {
        if !visited.insert(parent) {
            continue;
        }
        let mut pids = vec![0_i32; 64];
        let count = loop {
            let count = unsafe {
                libc::proc_listchildpids(
                    parent,
                    pids.as_mut_ptr().cast(),
                    (pids.len() * std::mem::size_of::<i32>()) as i32,
                )
            };
            if count < 0 {
                return Err(std::io::Error::last_os_error());
            }
            let count = count as usize;
            if count < pids.len() {
                break count;
            }
            if pids.len() >= 4096 {
                return Err(std::io::Error::other(
                    "descendant observation capacity exceeded",
                ));
            }
            pids.resize(pids.len() * 2, 0);
        };
        for pid in pids.into_iter().take(count).filter(|pid| *pid > 0) {
            if let Some((process, zombie)) = identity(pid)? {
                if !zombie {
                    parents.push(pid);
                }
                known.insert(pid, process);
            }
        }
    }
    Ok(())
}

#[cfg(not(target_os = "macos"))]
fn observe_descendants(
    _child: &Child,
    _known: &mut BTreeMap<i32, ObservedProcess>,
) -> std::io::Result<()> {
    Ok(())
}

fn signal_descendants(known: &BTreeMap<i32, ObservedProcess>, signal: i32) -> std::io::Result<()> {
    for process in known.values().rev() {
        if identity(process.process_id)?
            .is_some_and(|(current, zombie)| current == *process && !zombie)
        {
            signal_group(process.process_id, signal)?;
        }
    }
    Ok(())
}

fn descendants_terminated(known: &BTreeMap<i32, ObservedProcess>) -> std::io::Result<bool> {
    for process in known.values() {
        if identity(process.process_id)?
            .is_some_and(|(current, zombie)| current == *process && !zombie)
        {
            return Ok(false);
        }
    }
    Ok(true)
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct CommandOutcome {
    pub success: bool,
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub status: String,
    pub elapsed_seconds: f64,
    pub interrupted: bool,
    pub spawn_error: Option<String>,
    pub wait_error: Option<String>,
    pub cleanup: CleanupOutcome,
}

impl CommandOutcome {
    pub fn spawn_failure(error: &std::io::Error, elapsed: Duration) -> Self {
        let mut outcome = Self::new();
        outcome.status = "spawn failed".into();
        outcome.spawn_error = Some(error.to_string());
        outcome.elapsed_seconds = elapsed.as_secs_f64();
        outcome
    }

    pub fn ensure_success(&self) -> Result<()> {
        if !self.success {
            return Err(format!(
                "command failed: {}{}",
                self.status,
                if self.interrupted {
                    "; interrupted"
                } else {
                    ""
                }
            )
            .into());
        }
        Ok(())
    }

    fn new() -> Self {
        Self {
            success: false,
            exit_code: None,
            signal: None,
            status: "not started".into(),
            elapsed_seconds: 0.0,
            interrupted: false,
            spawn_error: None,
            wait_error: None,
            cleanup: CleanupOutcome::default(),
        }
    }

    fn set_status(&mut self, status: ExitStatus) {
        self.exit_code = status.code();
        self.signal = status.signal();
        self.status = status.to_string();
        self.success = status.success()
            && !self.interrupted
            && self.wait_error.is_none()
            && self.spawn_error.is_none();
    }
}

fn group_gone(group: i32) -> std::io::Result<bool> {
    if unsafe { libc::kill(group, 0) } == 0 {
        return Ok(false);
    }
    let error = std::io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::ESRCH) {
        Ok(true)
    } else {
        Err(error)
    }
}

fn signal_group(group: i32, signal: i32) -> std::io::Result<bool> {
    if unsafe { libc::kill(group, signal) } == 0 {
        return Ok(true);
    }
    let error = std::io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::ESRCH) {
        Ok(false)
    } else {
        Err(error)
    }
}

fn cleanup(
    child: &mut Child,
    grace: Duration,
    known: &mut BTreeMap<i32, ObservedProcess>,
    outcome: &mut CommandOutcome,
) {
    outcome.cleanup.attempted = true;
    if let Err(error) = observe_descendants(child, known) {
        outcome.cleanup.descendant_observation_error = Some(error.to_string());
    }
    outcome.cleanup.observed_descendants = known.values().cloned().collect();
    let Ok(pid) = i32::try_from(child.id()) else {
        outcome.cleanup.error = Some("child PID cannot be represented".into());
        return;
    };
    let group = -pid;
    match signal_group(group, libc::SIGTERM) {
        Ok(sent) => outcome.cleanup.term_sent = sent,
        Err(error) => outcome.cleanup.error = Some(error.to_string()),
    }
    if let Err(error) = signal_descendants(known, libc::SIGTERM) {
        outcome.cleanup.error = Some(error.to_string());
    }
    let deadline = Instant::now() + grace;
    while Instant::now() < deadline {
        match child.try_wait() {
            Ok(Some(status)) => {
                outcome.set_status(status);
                outcome.cleanup.child_reaped = true;
            }
            Ok(None) => {}
            Err(error) => {
                outcome.cleanup.error = Some(error.to_string());
                break;
            }
        }
        match group_gone(group) {
            Ok(true) => {
                outcome.cleanup.process_group_gone = true;
                if descendants_terminated(known).unwrap_or(false) {
                    break;
                }
            }
            Ok(false) => {}
            Err(error) => {
                outcome.cleanup.error = Some(error.to_string());
                break;
            }
        }
        thread::sleep(Duration::from_millis(20));
    }
    if !outcome.cleanup.process_group_gone {
        match signal_group(group, libc::SIGKILL) {
            Ok(sent) => outcome.cleanup.kill_sent = sent,
            Err(error) => outcome.cleanup.error = Some(error.to_string()),
        }
    }
    if let Err(error) = signal_descendants(known, libc::SIGKILL) {
        outcome.cleanup.error = Some(error.to_string());
    }
    if !outcome.cleanup.child_reaped {
        // SIGKILL should make the owned child waitable. Bound observation rather
        // than claiming cleanup when a process cannot actually be reaped.
        let deadline = Instant::now() + Duration::from_secs(2);
        while Instant::now() < deadline {
            match child.try_wait() {
                Ok(Some(status)) => {
                    outcome.set_status(status);
                    outcome.cleanup.child_reaped = true;
                    break;
                }
                Ok(None) => thread::sleep(Duration::from_millis(20)),
                Err(error) => {
                    outcome.cleanup.error = Some(error.to_string());
                    break;
                }
            }
        }
    }
    for _ in 0..50 {
        match group_gone(group) {
            Ok(gone) => {
                outcome.cleanup.process_group_gone = gone;
                match descendants_terminated(known) {
                    Ok(terminated) => outcome.cleanup.observed_descendants_terminated = terminated,
                    Err(error) => {
                        outcome.cleanup.descendant_observation_error = Some(error.to_string())
                    }
                }
                if gone && outcome.cleanup.observed_descendants_terminated {
                    break;
                }
            }
            Err(error) => {
                outcome.cleanup.error = Some(error.to_string());
                break;
            }
        }
        thread::sleep(Duration::from_millis(20));
    }
    if !outcome.cleanup.child_reaped
        || !outcome.cleanup.process_group_gone
        || !outcome.cleanup.observed_descendants_terminated
    {
        outcome
            .cleanup
            .error
            .get_or_insert("process-group cleanup could not be confirmed".into());
    }
    outcome.success = false;
}

/// The caller must put the child in its own process group before spawning.
pub fn wait(
    child: &mut Child,
    label: &str,
    interrupted: &AtomicBool,
    grace: Duration,
) -> CommandOutcome {
    let begin = Instant::now();
    let mut update = begin;
    let mut outcome = CommandOutcome::new();
    let mut known = BTreeMap::new();
    loop {
        if let Err(error) = observe_descendants(child, &mut known) {
            outcome.cleanup.descendant_observation_error = Some(error.to_string());
        }
        if interrupted.load(Ordering::SeqCst) {
            outcome.interrupted = true;
            outcome.status = "interrupted".into();
            cleanup(child, grace, &mut known, &mut outcome);
            break;
        }
        match child.try_wait() {
            Ok(Some(status)) => {
                outcome.interrupted = interrupted.load(Ordering::SeqCst);
                outcome.set_status(status);
                if outcome.interrupted {
                    cleanup(child, grace, &mut known, &mut outcome);
                }
                break;
            }
            Ok(None) => {}
            Err(error) => {
                outcome.wait_error = Some(error.to_string());
                outcome.status = "waiting for child failed".into();
                cleanup(child, grace, &mut known, &mut outcome);
                break;
            }
        }
        if update.elapsed() >= Duration::from_secs(30) {
            eprintln!(
                "{label}: still running ({:.0}s)",
                begin.elapsed().as_secs_f64()
            );
            update = Instant::now();
        }
        thread::sleep(Duration::from_millis(100));
    }
    outcome.elapsed_seconds = begin.elapsed().as_secs_f64();
    outcome
}

pub fn logged(
    c: &mut Command,
    logs: &Path,
    label: &str,
    interrupted: &AtomicBool,
    grace: Duration,
) -> Result<CommandOutcome> {
    fs::create_dir_all(logs)?;
    let begin = Instant::now();
    let spec = json!({"program":c.get_program().to_string_lossy(),"args":c.get_args().map(|a|a.to_string_lossy()).collect::<Vec<_>>(),"cwd":c.get_current_dir(),"environment_overrides":c.get_envs().map(|(k,v)|(k.to_string_lossy(),v.map(|v|v.to_string_lossy()))).collect::<BTreeMap<_,_>>(),"started_unix_seconds":SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs_f64()});
    atomic_json(&logs.join(format!("{label}.command.json")), &spec)?;
    let mut outcome = CommandOutcome::new();
    let setup = (|| -> Result<()> {
        c.stdout(Stdio::from(File::create(
            logs.join(format!("{label}.stdout")),
        )?));
        c.stderr(Stdio::from(File::create(
            logs.join(format!("{label}.stderr")),
        )?));
        c.process_group(0);
        Ok(())
    })();
    if let Err(error) = setup {
        outcome.spawn_error = Some(error.to_string());
        outcome.status = "command output setup failed".into();
    } else if interrupted.load(Ordering::SeqCst) {
        outcome.interrupted = true;
        outcome.status = "interrupted before spawn".into();
    } else {
        match c.spawn() {
            Ok(mut child) => outcome = wait(&mut child, label, interrupted, grace),
            Err(error) => {
                outcome = CommandOutcome::spawn_failure(&error, begin.elapsed());
            }
        }
    }
    outcome.elapsed_seconds = begin.elapsed().as_secs_f64();
    atomic_json(&logs.join(format!("{label}.result.json")), &outcome)?;
    Ok(outcome)
}

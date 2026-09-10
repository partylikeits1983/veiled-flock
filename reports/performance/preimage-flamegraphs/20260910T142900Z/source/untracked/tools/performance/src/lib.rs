//! Shared policy and evidence IO for the preimage profiling workflow.

pub mod report;
pub mod snapshot;

use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::sync::atomic::{AtomicU64, Ordering};

pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;

static TEMP_ID: AtomicU64 = AtomicU64::new(0);

pub fn environment_keys() -> Vec<String> {
    serde_json::from_str(include_str!("../measurement-env.json"))
        .expect("measurement environment policy must be a JSON string array")
}

/// Construct all measurement and recorder children with the same policy.
/// Parent environment is never modified, including in multithreaded tests.
pub fn command(program: impl AsRef<OsStr>) -> Command {
    let mut cmd = Command::new(program);
    for key in environment_keys() {
        cmd.env_remove(key);
    }
    cmd
}

pub fn sha256(path: &Path) -> Result<String> {
    let mut input = File::open(path)?;
    let mut digest = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let count = input.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        digest.update(&buffer[..count]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn temporary_path(path: &Path) -> Result<PathBuf> {
    let name = path.file_name().ok_or("output path has no filename")?;
    let mut temporary = name.to_os_string();
    temporary.push(format!(
        ".tmp-{}-{}",
        std::process::id(),
        TEMP_ID.fetch_add(1, Ordering::Relaxed)
    ));
    Ok(path.with_file_name(temporary))
}

/// Publish complete JSON only after its contents have reached the filesystem.
pub fn atomic_json(path: &Path, value: &impl Serialize) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let temporary = temporary_path(path)?;
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)?;
    serde_json::to_writer_pretty(&mut output, value)?;
    output.write_all(b"\n")?;
    output.sync_all()?;
    fs::rename(temporary, path)?;
    Ok(())
}

/// Keep draining the reader after either writer fails so a child's full stdout
/// pipe cannot deadlock its exit. Return the first IO error after draining.
pub fn tee<R: Read, A: Write, B: Write>(
    mut input: R,
    mut first: A,
    mut second: B,
) -> io::Result<u64> {
    let mut first_ok = true;
    let mut second_ok = true;
    let mut failure = None;
    let mut total = 0;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let count = match input.read(&mut buffer) {
            Ok(0) => break,
            Ok(count) => count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => {
                failure.get_or_insert(error);
                break;
            }
        };
        total += count as u64;
        if first_ok && let Err(error) = first.write_all(&buffer[..count]) {
            first_ok = false;
            failure.get_or_insert(error);
        }
        if second_ok && let Err(error) = second.write_all(&buffer[..count]) {
            second_ok = false;
            failure.get_or_insert(error);
        }
    }
    if first_ok && let Err(error) = first.flush() {
        failure.get_or_insert(error);
    }
    if second_ok && let Err(error) = second.flush() {
        failure.get_or_insert(error);
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(total),
    }
}

#[derive(Debug, Serialize, serde::Deserialize)]
pub struct StageStatus {
    pub attempt_id: String,
    pub stage: String,
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub io_ok: bool,
    pub success: bool,
    pub error: Option<String>,
}

impl StageStatus {
    pub fn new(attempt_id: String, stage: String) -> Self {
        Self {
            attempt_id,
            stage,
            exit_code: None,
            signal: None,
            io_ok: false,
            success: false,
            error: None,
        }
    }

    pub fn child_status(&mut self, status: ExitStatus) {
        self.exit_code = status.code();
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            self.signal = status.signal();
        }
        self.success = status.success() && self.io_ok;
    }
}

/// Resolve an output that does not exist yet through its nearest existing
/// ancestor, detecting symlink aliases before recorder/archive overlap checks.
pub fn canonical_output(path: &Path) -> Result<PathBuf> {
    if path.exists() {
        return Ok(path.canonicalize()?);
    }
    let name = path.file_name().ok_or("cannot resolve output path")?;
    let parent = path.parent().ok_or("output path has no parent")?;
    Ok(canonical_output(parent)?.join(name))
}

pub fn reject_overlap(first: &Path, second: &Path) -> Result<()> {
    let first = canonical_output(first)?;
    let second = canonical_output(second)?;
    if first.starts_with(&second) || second.starts_with(&first) {
        return Err(format!(
            "recorder scratch and evidence archive overlap: {} and {}",
            first.display(),
            second.display()
        )
        .into());
    }
    Ok(())
}

fn copy_tree(source: &Path, destination: &Path) -> Result<()> {
    let metadata = fs::symlink_metadata(source)?;
    if !metadata.is_dir() {
        return Err(format!("trace is not a directory: {}", source.display()).into());
    }
    fs::create_dir(destination)?;
    let mut entries = fs::read_dir(source)?.collect::<io::Result<Vec<_>>>()?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let source = entry.path();
        let destination = destination.join(entry.file_name());
        let metadata = fs::symlink_metadata(&source)?;
        if metadata.is_dir() {
            copy_tree(&source, &destination)?;
        } else if metadata.is_file() {
            fs::copy(&source, &destination)?;
        } else {
            return Err(format!("unsupported trace entry: {}", source.display()).into());
        }
    }
    Ok(())
}

fn trace_inventory(root: &Path) -> Result<BTreeMap<PathBuf, Option<String>>> {
    fn visit(
        root: &Path,
        relative: &Path,
        inventory: &mut BTreeMap<PathBuf, Option<String>>,
    ) -> Result<()> {
        let full = root.join(relative);
        let metadata = fs::symlink_metadata(&full)?;
        if metadata.is_dir() {
            inventory.insert(relative.to_path_buf(), None);
            for entry in fs::read_dir(full)? {
                visit(root, &relative.join(entry?.file_name()), inventory)?;
            }
        } else if metadata.is_file() {
            inventory.insert(relative.to_path_buf(), Some(sha256(&full)?));
        } else {
            return Err(format!("unsupported trace entry: {}", full.display()).into());
        }
        Ok(())
    }
    let mut inventory = BTreeMap::new();
    visit(root, Path::new(""), &mut inventory)?;
    Ok(inventory)
}

/// Archive the trace outside the recorder's disposable directory and publish
/// it by rename only when every file was copied and its bytes verified.
pub fn archive_trace(source: &Path, destination: &Path) -> Result<()> {
    reject_overlap(source, destination)?;
    if destination.exists() {
        return Err("refusing to overwrite an existing trace archive".into());
    }
    let parent = destination.parent().ok_or("trace archive has no parent")?;
    fs::create_dir_all(parent)?;
    let temporary = temporary_path(destination)?;
    let inventory = trace_inventory(source)?;
    copy_tree(source, &temporary)?;
    if trace_inventory(source)? != inventory || trace_inventory(&temporary)? != inventory {
        return Err("trace changed while copying, or archive does not match its source".into());
    }
    fs::rename(temporary, destination)?;
    Ok(())
}

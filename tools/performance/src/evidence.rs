//! Shared artifact inventory and exclusive single-writer ownership.

use crate::{Result, atomic_json, sha256};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct InventoryFile {
    pub bytes: u64,
    pub sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Inventory {
    pub schema_version: u32,
    pub exclusions: Vec<String>,
    pub files: BTreeMap<PathBuf, InventoryFile>,
}

pub fn inventory(root: &Path, exclusions: &[&str]) -> Result<Inventory> {
    fn walk(
        root: &Path,
        relative: &Path,
        exclusions: &[&str],
        files: &mut BTreeMap<PathBuf, InventoryFile>,
    ) -> Result<()> {
        for entry in fs::read_dir(root.join(relative))? {
            let entry = entry?;
            let path = relative.join(entry.file_name());
            if exclusions
                .iter()
                .any(|exclude| path == Path::new(exclude) || path.starts_with(exclude))
            {
                continue;
            }
            let metadata = fs::symlink_metadata(entry.path())?;
            if metadata.is_dir() {
                walk(root, &path, exclusions, files)?;
            } else if metadata.is_file() {
                files.insert(
                    path.clone(),
                    InventoryFile {
                        bytes: metadata.len(),
                        sha256: sha256(&root.join(path))?,
                    },
                );
            } else {
                return Err(format!("unsupported evidence artifact: {}", path.display()).into());
            }
        }
        Ok(())
    }
    if exclusions.iter().any(|value| {
        value.is_empty()
            || Path::new(value).is_absolute()
            || Path::new(value)
                .components()
                .any(|part| !matches!(part, std::path::Component::Normal(_)))
    }) {
        return Err("inventory exclusions must be normalized relative paths".into());
    }
    let mut result = Inventory {
        schema_version: 1,
        exclusions: exclusions.iter().map(|s| s.to_string()).collect(),
        files: BTreeMap::new(),
    };
    walk(root, Path::new(""), exclusions, &mut result.files)?;
    Ok(result)
}

pub fn write_inventory(root: &Path, exclusions: &[&str]) -> Result<Inventory> {
    if !exclusions.contains(&"artifacts.json") {
        return Err("artifact inventory must exclude itself".into());
    }
    let result = inventory(root, exclusions)?;
    atomic_json(&root.join("artifacts.json"), &result)?;
    Ok(result)
}

pub fn verify_inventory(root: &Path, expected: &Inventory) -> Result<()> {
    if expected.schema_version != 1 {
        return Err("unsupported artifact inventory schema".into());
    }
    let exclusions: Vec<_> = expected.exclusions.iter().map(String::as_str).collect();
    if inventory(root, &exclusions)? != *expected {
        return Err("evidence inventory content or membership changed".into());
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct LockOwner {
    pub schema_version: u32,
    pub process_id: u32,
    pub process_start: String,
    pub nonce: String,
    pub released: bool,
}

fn process_start(pid: u32) -> Result<Option<String>> {
    let alive = unsafe { libc::kill(i32::try_from(pid)?, 0) };
    if alive != 0 {
        let error = std::io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::ESRCH) {
            return Ok(None);
        }
        return Err(error.into());
    }
    let output = Command::new("/bin/ps")
        .args(["-p", &pid.to_string(), "-o", "lstart="])
        .output()?;
    let start = String::from_utf8(output.stdout)?.trim().to_owned();
    if output.status.success() && !start.is_empty() {
        return Ok(Some(start));
    }
    if unsafe { libc::kill(i32::try_from(pid)?, 0) } != 0
        && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH)
    {
        return Ok(None);
    }
    Err("cannot verify writer process identity".into())
}

/// The OS lock prevents simultaneous writers. Persistent PID/start metadata
/// additionally prevents treating an unverified old owner as stale.
pub struct WriterLock {
    file: File,
    pub owner: LockOwner,
}

impl WriterLock {
    pub fn acquire(root: &Path) -> Result<Self> {
        fs::create_dir_all(root)?;
        let path = root.join(".writer-lock");
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .custom_flags(libc::O_NOFOLLOW)
            .open(path)?;
        if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err("another writer owns this output".into());
        }
        let mut contents = Vec::new();
        file.read_to_end(&mut contents)?;
        if !contents.is_empty() {
            let previous: LockOwner = serde_json::from_slice(&contents)
                .map_err(|_| "writer ownership is malformed; cannot establish stale ownership")?;
            if previous.schema_version != 1
                || previous.process_id == 0
                || previous.process_start.is_empty()
            {
                return Err("writer ownership is unsupported or incomplete".into());
            }
            if !previous.released
                && process_start(previous.process_id)?
                    .is_some_and(|start| start == previous.process_start)
            {
                return Err("previous writer is still alive; ownership cannot be reclaimed".into());
            }
            let history = root.join(".writer-lock-history");
            fs::create_dir_all(&history)?;
            let name = format!("{}-{}.json", previous.process_id, previous.nonce);
            if name.contains('/') || name.contains('\\') {
                return Err("invalid writer ownership nonce".into());
            }
            let history_path = history.join(name);
            match OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(history_path)
            {
                Ok(mut archive) => {
                    archive.write_all(&contents)?;
                    archive.sync_all()?;
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => return Err(error.into()),
            }
        }
        let owner = LockOwner {
            schema_version: 1,
            process_id: std::process::id(),
            process_start: process_start(std::process::id())?
                .ok_or("current process identity disappeared")?,
            nonce: SystemTime::now()
                .duration_since(UNIX_EPOCH)?
                .as_nanos()
                .to_string(),
            released: false,
        };
        let mut lock = Self { file, owner };
        lock.save()?;
        Ok(lock)
    }

    fn save(&mut self) -> Result<()> {
        self.file.seek(SeekFrom::Start(0))?;
        self.file.set_len(0)?;
        serde_json::to_writer_pretty(&mut self.file, &self.owner)?;
        self.file.write_all(b"\n")?;
        self.file.sync_all()?;
        Ok(())
    }
}

impl Drop for WriterLock {
    fn drop(&mut self) {
        self.owner.released = true;
        let _ = self.save();
        unsafe {
            libc::flock(self.file.as_raw_fd(), libc::LOCK_UN);
        }
    }
}

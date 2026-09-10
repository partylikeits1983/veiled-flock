#![allow(dead_code)] // Integration test binaries use different fixture helpers.

use flock_performance::Result;
use std::fs;
use std::ops::Deref;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static ID: AtomicU64 = AtomicU64::new(0);

/// Disposable fixture root. The spaces are deliberate path-handling coverage.
pub struct Temporary(PathBuf);

impl Temporary {
    pub fn new(prefix: &str) -> Result<Self> {
        Self::with_counter(prefix, &ID)
    }

    /// An isolated counter lets a fixture exercise stale names deterministically.
    pub fn with_counter(prefix: &str, counter: &AtomicU64) -> Result<Self> {
        loop {
            let path = std::env::temp_dir().join(format!(
                "{prefix} {} {}",
                std::process::id(),
                counter.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self(path)),
                // A reused PID can encounter leftovers from an interrupted
                // earlier test. Only the directory we created belongs to us.
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(format!("creating fixture {}: {error}", path.display()).into());
                }
            }
        }
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl Deref for Temporary {
    type Target = Path;

    fn deref(&self) -> &Path {
        self.path()
    }
}

impl Drop for Temporary {
    fn drop(&mut self) {
        remove_sealed(self.path());
    }
}

/// Remove sealed fixture directories without following symlinks or changing
/// permissions on linked files. This is only for roots owned by the test.
pub fn remove_sealed(path: &Path) {
    let Ok(metadata) = fs::symlink_metadata(path) else {
        return;
    };
    if metadata.is_dir() {
        let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o755));
        if let Ok(entries) = fs::read_dir(path) {
            for entry in entries.flatten() {
                remove_sealed(&entry.path());
            }
        }
        let _ = fs::remove_dir(path);
    } else {
        let _ = fs::remove_file(path);
    }
}

pub fn git(repo: &Path, args: &[&str]) -> Result<()> {
    let output = Command::new("git").current_dir(repo).args(args).output()?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned().into());
    }
    Ok(())
}

/// All history created here belongs to a disposable fixture repository.
pub fn init_git(repo: &Path) -> Result<()> {
    git(repo, &["init", "-q"])?;
    git(repo, &["add", "."])?;
    git(
        repo,
        &[
            "-c",
            "user.name=Performance Test",
            "-c",
            "user.email=performance@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "isolated test fixture",
        ],
    )
}

use flock_performance::snapshot::{prepare, verify};
use flock_performance::{Result, sha256};
use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Barrier};

static COUNTER: AtomicU64 = AtomicU64::new(0);

struct Fixture {
    base: PathBuf,
    repo: PathBuf,
}

impl Fixture {
    fn new() -> Result<Self> {
        let base = std::env::temp_dir().join(format!(
            "flock-snapshot-test-{}-{}",
            std::process::id(),
            COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&base)?;
        let repo = base.join("editing source");
        fs::create_dir_all(repo.join("crates"))?;
        fs::write(repo.join("Cargo.toml"), "[workspace]\nmembers = []\n")?;
        fs::write(repo.join("crates/input.bin"), [0, 255, 1, 128])?;
        fs::write(repo.join("crates/deleted.txt"), "old")?;
        fs::write(repo.join("crates/run.sh"), "#!/bin/sh\nexit 0\n")?;
        fs::set_permissions(
            repo.join("crates/run.sh"),
            fs::Permissions::from_mode(0o755),
        )?;
        fs::write(repo.join(".gitignore"), "crates/ignored.dat\n")?;
        let fixture = Self { base, repo };
        fixture.git(&["init", "-q"])?;
        fixture.git(&["add", "."])?;
        // This history belongs only to the isolated temporary fixture.
        fixture.git(&[
            "-c",
            "user.name=Snapshot Test",
            "-c",
            "user.email=snapshot@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "fixture",
        ])?;
        Ok(fixture)
    }

    fn git(&self, args: &[&str]) -> Result<()> {
        let result = Command::new("git")
            .current_dir(&self.repo)
            .args(args)
            .output()?;
        if !result.status.success() {
            return Err(String::from_utf8_lossy(&result.stderr).into_owned().into());
        }
        Ok(())
    }

    fn report(&self) -> PathBuf {
        self.base.join("report")
    }
}

fn remove_sealed(path: &Path) {
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

impl Drop for Fixture {
    fn drop(&mut self) {
        remove_sealed(&self.base);
    }
}

#[test]
fn reconstructs_final_bytes_modes_links_and_deletions_without_touching_index() -> Result<()> {
    let fixture = Fixture::new()?;
    fs::write(fixture.repo.join("crates/input.bin"), [7, 0, 255])?;
    fixture.git(&["add", "crates/input.bin"])?;
    fs::write(fixture.repo.join("crates/input.bin"), [11, 255, 0, 128])?;
    fs::remove_file(fixture.repo.join("crates/deleted.txt"))?;
    fs::write(fixture.repo.join("crates/new input.dat"), [254, 0, 129])?;
    fs::write(fixture.repo.join("crates/ignored.dat"), [255, 0, 255])?;
    symlink("input.bin", fixture.repo.join("crates/link.bin"))?;
    let index = sha256(&fixture.repo.join(".git/index"))?;
    let snapshot = prepare(&fixture.repo, &fixture.report())?;
    assert_eq!(index, sha256(&fixture.repo.join(".git/index"))?);
    assert_eq!(
        fs::read(snapshot.root.join("crates/input.bin"))?,
        [11, 255, 0, 128]
    );
    assert_eq!(
        fs::read(snapshot.root.join("crates/new input.dat"))?,
        [254, 0, 129]
    );
    assert_eq!(
        fs::read(snapshot.root.join("crates/ignored.dat"))?,
        [255, 0, 255]
    );
    assert_eq!(
        fs::read_link(snapshot.root.join("crates/link.bin"))?,
        PathBuf::from("input.bin")
    );
    assert!(!snapshot.root.join("crates/deleted.txt").exists());
    assert_eq!(
        fs::metadata(snapshot.root.join("crates/run.sh"))?
            .permissions()
            .mode()
            & 0o777,
        0o555
    );
    assert_eq!(
        fs::metadata(snapshot.root.join("crates/input.bin"))?
            .permissions()
            .mode()
            & 0o777,
        0o444
    );
    assert!(snapshot.root.join(".profile-scratch").is_dir());
    fs::write(snapshot.root.join(".profile-scratch/probe"), "scratch")?;
    verify(&snapshot)?;
    remove_sealed(&snapshot.root);
    Ok(())
}

#[test]
fn compiler_reads_private_bytes_during_live_edit_and_restore() -> Result<()> {
    let fixture = Fixture::new()?;
    let snapshot = prepare(&fixture.repo, &fixture.report())?;
    let ready = Arc::new(Barrier::new(2));
    let finished = Arc::new(Barrier::new(2));
    let compiler_ready = Arc::clone(&ready);
    let compiler_finished = Arc::clone(&finished);
    let compiler_path = snapshot.root.join("crates/input.bin");
    let compiler = std::thread::spawn(move || {
        compiler_ready.wait();
        let bytes = fs::read(compiler_path).unwrap();
        compiler_finished.wait();
        bytes
    });
    fs::write(
        fixture.repo.join("crates/input.bin"),
        b"transient edit seen only in checkout",
    )?;
    ready.wait();
    finished.wait();
    fs::write(fixture.repo.join("crates/input.bin"), [0, 255, 1, 128])?;
    assert_eq!(compiler.join().unwrap(), [0, 255, 1, 128]);
    verify(&snapshot)?;
    fs::write(
        fixture.repo.join("crates/input.bin"),
        b"persistent new edit",
    )?;
    verify(&snapshot)?;
    remove_sealed(&snapshot.root);
    Ok(())
}

#[test]
fn seal_prevents_writes_and_verifier_rejects_changed_private_input() -> Result<()> {
    let fixture = Fixture::new()?;
    let snapshot = prepare(&fixture.repo, &fixture.report())?;
    let input = snapshot.root.join("crates/input.bin");
    if unsafe { libc::geteuid() } != 0 {
        assert!(fs::write(&input, b"should fail").is_err());
    }
    fs::set_permissions(&input, fs::Permissions::from_mode(0o644))?;
    fs::write(&input, b"modified")?;
    assert!(verify(&snapshot).is_err());
    remove_sealed(&snapshot.root);
    Ok(())
}

#[test]
fn escaping_symlinks_and_hardlinks_are_rejected() -> Result<()> {
    let fixture = Fixture::new()?;
    fs::write(fixture.base.join("outside"), "mutable outside bytes")?;
    symlink(
        fixture.base.join("outside"),
        fixture.repo.join("crates/escape"),
    )?;
    assert!(
        prepare(&fixture.repo, &fixture.report())
            .unwrap_err()
            .to_string()
            .contains("symlink")
    );
    fs::remove_file(fixture.repo.join("crates/escape"))?;
    fs::hard_link(
        fixture.base.join("outside"),
        fixture.repo.join("crates/hardlink"),
    )?;
    assert!(
        prepare(&fixture.repo, &fixture.report())
            .unwrap_err()
            .to_string()
            .contains("hardlink")
    );
    Ok(())
}

#[test]
fn ancestor_cargo_configuration_is_not_silently_lost() -> Result<()> {
    let fixture = Fixture::new()?;
    fs::create_dir(fixture.base.join(".cargo"))?;
    fs::write(
        fixture.base.join(".cargo/config.toml"),
        "[build]\nrustflags = [\"-C\", \"opt-level=1\"]\n",
    )?;
    assert!(
        prepare(&fixture.repo, &fixture.report())
            .unwrap_err()
            .to_string()
            .contains("ancestor Cargo configuration")
    );
    Ok(())
}

#[test]
fn external_local_dependency_requires_explicit_freezing() -> Result<()> {
    let fixture = Fixture::new()?;
    fs::create_dir(fixture.base.join("external"))?;
    fs::write(
        fixture.repo.join("Cargo.toml"),
        "[workspace]\nmembers = []\n[workspace.dependencies]\nexternal = { path = \"../external\" }\n",
    )?;
    assert!(
        prepare(&fixture.repo, &fixture.report())
            .unwrap_err()
            .to_string()
            .contains("escapes source snapshot")
    );
    Ok(())
}

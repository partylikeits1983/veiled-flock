//! Immutable, independently materialized compiler inputs and their provenance.

use crate::{Result, atomic_json, sha256};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

const EXCLUDED: &[&str] = &[
    ".git",
    "target",
    ".lake",
    "reports",
    ".profile-scratch",
    "__pycache__",
    "node_modules",
    ".DS_Store",
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Input {
    pub path: PathBuf,
    pub kind: String,
    pub sha256: Option<String>,
    pub symlink_target: Option<PathBuf>,
    pub original_mode: u32,
    pub sealed_mode: u32,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ExternalConfig {
    pub path: PathBuf,
    pub sha256: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Snapshot {
    pub root: PathBuf,
    pub id: String,
    pub editing_root: PathBuf,
    pub base_revision: String,
    pub inventory: Vec<Input>,
    pub external_config: Vec<ExternalConfig>,
    pub build_environment: BTreeMap<String, String>,
}

fn output(mut cmd: Command) -> Result<Vec<u8>> {
    let result = cmd.output()?;
    if !result.status.success() {
        return Err(format!(
            "command failed ({:?}): {}",
            result.status,
            String::from_utf8_lossy(&result.stderr)
        )
        .into());
    }
    Ok(result.stdout)
}

fn git(root: &Path, args: &[&str]) -> Result<Vec<u8>> {
    let mut cmd = Command::new("git");
    cmd.current_dir(root).args(args);
    output(cmd)
}

fn paths(bytes: &[u8]) -> Result<BTreeSet<PathBuf>> {
    bytes
        .split(|b| *b == 0)
        .filter(|s| !s.is_empty())
        .map(|p| {
            // JSON paths must be reversible: reject unsupported names rather than
            // allowing lossy conversion to identify a different compiler input.
            let path = PathBuf::from(std::str::from_utf8(p)?);
            if path.is_absolute()
                || path
                    .components()
                    .any(|c| !matches!(c, Component::Normal(_)))
            {
                return Err(format!("unsafe source path: {}", path.display()).into());
            }
            Ok(path)
        })
        .collect()
}

fn excluded(path: &Path) -> bool {
    path.components()
        .any(|c| EXCLUDED.iter().any(|name| c.as_os_str() == *name))
}

fn build_relevant(path: &Path) -> bool {
    path.components().next().is_some_and(|c| {
        [
            ".cargo",
            "crates",
            "examples",
            "tools",
            "scripts",
            "lean",
            "Cargo.toml",
            "Cargo.lock",
            "Makefile",
            "rust-toolchain.toml",
            "rustfmt.toml",
            ".rustfmt.toml",
        ]
        .iter()
        .any(|name| c.as_os_str() == *name)
    })
}

fn walk(root: &Path, relative: &Path, files: &mut BTreeSet<PathBuf>) -> Result<()> {
    for entry in fs::read_dir(root.join(relative))? {
        let entry = entry?;
        let path = relative.join(entry.file_name());
        if excluded(&path) {
            continue;
        }
        let metadata = fs::symlink_metadata(entry.path())?;
        if metadata.is_dir() {
            walk(root, &path, files)?;
        } else {
            files.insert(path);
        }
    }
    Ok(())
}

fn live_paths(root: &Path) -> Result<BTreeSet<PathBuf>> {
    let mut files = paths(&git(root, &["ls-files", "--cached", "-z"])?)?;
    files.extend(paths(&git(
        root,
        &["ls-tree", "-rz", "--name-only", "HEAD"],
    )?)?);
    for path in paths(&git(
        root,
        &["ls-files", "--others", "--exclude-standard", "-z"],
    )?)? {
        if build_relevant(&path) && !excluded(&path) {
            files.insert(path);
        }
    }
    // Source-tree walking also preserves ignored include_bytes!/configuration
    // inputs. Generated toolchains, package caches and outputs are excluded.
    for prefix in [".cargo", "crates", "examples", "tools", "scripts", "lean"] {
        if root.join(prefix).is_dir() {
            walk(root, Path::new(prefix), &mut files)?;
        }
    }
    files.retain(|path| !excluded(path) && fs::symlink_metadata(root.join(path)).is_ok());
    Ok(files)
}

fn inventory(root: &Path, files: &BTreeSet<PathBuf>) -> Result<Vec<Input>> {
    let canonical_root = root.canonicalize()?;
    let mut out = Vec::with_capacity(files.len());
    for path in files {
        if path.to_str().is_none() {
            return Err("non-UTF-8 source path cannot be archived in JSON".into());
        }
        let full = root.join(path);
        let metadata = fs::symlink_metadata(&full)?;
        let mode = metadata.mode() & 0o777;
        if metadata.file_type().is_symlink() {
            let target = fs::read_link(&full)?;
            let resolved = full.canonicalize()?;
            let relative = resolved.strip_prefix(&canonical_root).map_err(|_| {
                format!("source symlink escapes snapshot inputs: {}", path.display())
            })?;
            if target.is_absolute() || !files.contains(relative) || !resolved.is_file() {
                return Err(format!(
                    "source symlink must refer to an inventoried internal file: {}",
                    path.display()
                )
                .into());
            }
            out.push(Input {
                path: path.clone(),
                kind: "symlink".into(),
                sha256: None,
                symlink_target: Some(target),
                original_mode: mode,
                sealed_mode: mode,
            });
        } else if metadata.is_file() {
            // A hard link could mutate the private tree via a second path. The
            // materializer copies bytes, and rejects pre-existing source links.
            if metadata.nlink() != 1 {
                return Err(
                    format!("hardlinked source input is unsupported: {}", path.display()).into(),
                );
            }
            out.push(Input {
                path: path.clone(),
                kind: "file".into(),
                sha256: Some(sha256(&full)?),
                symlink_target: None,
                original_mode: mode,
                sealed_mode: if mode & 0o111 != 0 { 0o555 } else { 0o444 },
            });
        } else {
            return Err(format!("unsupported source input type: {}", path.display()).into());
        }
    }
    Ok(out)
}

fn configs(root: &Path, private_root: &Path) -> Result<Vec<ExternalConfig>> {
    let private_ancestors: BTreeSet<_> = private_root
        .ancestors()
        .skip(1)
        .map(Path::to_path_buf)
        .collect();
    let cargo_home = env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|p| PathBuf::from(p).join(".cargo")))
        .ok_or("cannot locate Cargo home")?;
    let cargo_home = if cargo_home.is_absolute() {
        cargo_home
    } else {
        return Err("relative CARGO_HOME is not safe across snapshot working directories".into());
    };
    let mut candidates = BTreeSet::new();
    for ancestor in root.ancestors().skip(1) {
        for name in ["config", "config.toml"] {
            let candidate = ancestor.join(".cargo").join(name);
            if candidate.exists()
                && !private_ancestors.contains(ancestor)
                && candidate.parent() != Some(cargo_home.as_path())
            {
                return Err(format!(
                    "external ancestor Cargo configuration requires explicit freezing: {}",
                    candidate.display()
                )
                .into());
            }
            candidates.insert(candidate);
        }
    }
    for ancestor in private_ancestors {
        candidates.insert(ancestor.join(".cargo/config"));
        candidates.insert(ancestor.join(".cargo/config.toml"));
    }
    candidates.insert(cargo_home.join("config"));
    candidates.insert(cargo_home.join("config.toml"));
    candidates
        .into_iter()
        .map(|path| {
            let digest = if path.exists() {
                let text = fs::read_to_string(&path)?;
                // Cargo config can add relative paths, includes, credential hooks,
                // runners, linkers or wrappers. Fail closed until copied explicitly.
                if !text.trim().is_empty() {
                    return Err(format!(
                        "external Cargo configuration requires explicit freezing: {}",
                        path.display()
                    )
                    .into());
                }
                Some(sha256(&path)?)
            } else {
                None
            };
            Ok(ExternalConfig {
                path,
                sha256: digest,
            })
        })
        .collect()
}

fn build_environment() -> Result<BTreeMap<String, String>> {
    let mut map = BTreeMap::new();
    for (key, value) in env::vars_os() {
        let Some(key) = key.to_str() else { continue };
        let relevant = matches!(
            key,
            "RUSTFLAGS"
                | "CARGO_ENCODED_RUSTFLAGS"
                | "RUSTDOCFLAGS"
                | "RUSTC"
                | "RUSTC_WRAPPER"
                | "RUSTC_WORKSPACE_WRAPPER"
                | "RUSTDOC"
                | "CC"
                | "CXX"
                | "CFLAGS"
                | "CXXFLAGS"
                | "AR"
                | "CARGO_HOME"
                | "RUSTUP_HOME"
        ) || (key.starts_with("CARGO_")
            && (key.ends_with("_RUSTFLAGS")
                || key.ends_with("_LINKER")
                || key.ends_with("_RUNNER")
                || key.starts_with("CARGO_BUILD_")
                || key.starts_with("CARGO_PROFILE_")));
        if relevant
            && !matches!(
                key,
                "CARGO_BUILD_TARGET_DIR"
                    | "CARGO_PROFILE_RELEASE_DEBUG"
                    | "CARGO_PROFILE_RELEASE_STRIP"
            )
        {
            let value = value
                .to_str()
                .ok_or_else(|| format!("non-UTF-8 build setting {key}"))?;
            if matches!(
                key,
                "RUSTC_WRAPPER" | "RUSTC_WORKSPACE_WRAPPER" | "RUSTC" | "RUSTDOC"
            ) && !value.is_empty()
            {
                return Err(format!("build setting {key} requires explicit tool freezing").into());
            }
            map.insert(key.to_owned(), value.to_owned());
        }
    }
    Ok(map)
}

fn validate_manifest_paths(root: &Path, inputs: &[Input]) -> Result<()> {
    fn visit(value: &toml::Value, base: &Path, root: &Path) -> Result<()> {
        match value {
            toml::Value::Table(table) => {
                for (key, value) in table {
                    if key == "path"
                        && let Some(path) = value.as_str()
                    {
                        let candidate = base.join(path).canonicalize()?;
                        if !candidate.starts_with(root) {
                            return Err(format!(
                                "manifest path escapes source snapshot: {}",
                                candidate.display()
                            )
                            .into());
                        }
                    }
                    visit(value, base, root)?;
                }
            }
            toml::Value::Array(values) => {
                for value in values {
                    visit(value, base, root)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    for input in inputs {
        if input
            .path
            .file_name()
            .is_some_and(|name| name == "Cargo.toml")
        {
            let path = root.join(&input.path);
            let value = fs::read_to_string(&path)?.parse::<toml::Value>()?;
            visit(&value, path.parent().ok_or("manifest has no parent")?, root)?;
        }
        if input.path.starts_with(".cargo") && input.kind == "file" {
            let text = fs::read_to_string(root.join(&input.path))?;
            let value = text.parse::<toml::Value>()?;
            // The repository's native CPU flags are portable to the private
            // source root. Other config keys require an explicit implementation.
            let permitted = value.as_table().is_some_and(|table| {
                table.iter().all(|(key, value)| {
                    key == "build"
                        && value.as_table().is_some_and(|build| {
                            build.iter().all(|(key, value)| {
                                key == "rustflags"
                                    && value.as_array().is_some_and(|flags| {
                                        flags.iter().all(|flag| {
                                            flag.as_str().is_some_and(|flag| {
                                                !flag.contains('/') && !flag.contains('\\')
                                            })
                                        })
                                    })
                            })
                        })
                })
            });
            if !permitted {
                return Err(format!(
                    "Cargo configuration requires explicit freezing: {}",
                    input.path.display()
                )
                .into());
            }
        }
    }
    Ok(())
}

fn copy_input(from: &Path, to: &Path, input: &Input) -> Result<()> {
    let source = from.join(&input.path);
    let target = to.join(&input.path);
    fs::create_dir_all(target.parent().ok_or("input has no parent")?)?;
    if fs::symlink_metadata(&target).is_ok() {
        fs::remove_file(&target)?;
    }
    if let Some(link) = &input.symlink_target {
        symlink(link, target)?;
    } else {
        fs::copy(source, &target)?;
        fs::set_permissions(target, fs::Permissions::from_mode(input.original_mode))?;
    }
    Ok(())
}

fn seal(root: &Path, inputs: &[Input]) -> Result<()> {
    for input in inputs {
        if input.kind == "file" {
            fs::set_permissions(
                root.join(&input.path),
                fs::Permissions::from_mode(input.sealed_mode),
            )?;
        }
    }
    fn directories(path: &Path) -> Result<()> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            if entry.file_name() != ".profile-scratch" && entry.file_type()?.is_dir() {
                directories(&entry.path())?;
            }
        }
        fs::set_permissions(path, fs::Permissions::from_mode(0o555))?;
        Ok(())
    }
    fs::create_dir(root.join(".profile-scratch"))?;
    directories(root)
}

/// Prepare source evidence and a sealed, independent compiler-input tree.
pub fn prepare(edit_root: &Path, report_root: &Path) -> Result<Snapshot> {
    prepare_with(edit_root, report_root, || Ok(()))
}

fn prepare_with(
    edit_root: &Path,
    report_root: &Path,
    after_materialization: impl FnOnce() -> Result<()>,
) -> Result<Snapshot> {
    let edit_root = edit_root.canonicalize()?;
    let source = report_root.join("source");
    fs::create_dir_all(&source)?;
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
    let temp_base = if Path::new("/private/tmp").is_dir() {
        PathBuf::from("/private/tmp")
    } else {
        env::temp_dir()
    };
    let root = temp_base.join(format!(
        "flock-profile-source-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&root)?;
    let root = root.canonicalize()?;
    // Unaccepted candidates must never be reused by a later run.
    struct Candidate(PathBuf);
    impl Drop for Candidate {
        fn drop(&mut self) {
            fn unseal(path: &Path) {
                if let Ok(metadata) = fs::symlink_metadata(path)
                    && metadata.is_dir()
                {
                    let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o755));
                    if let Ok(entries) = fs::read_dir(path) {
                        for entry in entries.flatten() {
                            unseal(&entry.path());
                        }
                    }
                }
            }
            unseal(&self.0);
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let candidate = Candidate(root.clone());
    let external_config = configs(&edit_root, &root)?;
    let build_environment = build_environment()?;
    let before = inventory(&edit_root, &live_paths(&edit_root)?)?;
    validate_manifest_paths(&edit_root, &before)?;
    let base_revision = String::from_utf8(git(&edit_root, &["rev-parse", "HEAD"])?)?
        .trim()
        .to_owned();
    fs::write(
        source.join("base-revision.txt"),
        format!("{base_revision}\n"),
    )?;
    fs::write(
        source.join("git-status.txt"),
        git(
            &edit_root,
            &["status", "--porcelain=v1", "--untracked-files=all"],
        )?,
    )?;
    let patch = git(
        &edit_root,
        &[
            "diff",
            "--binary",
            "--full-index",
            "--no-ext-diff",
            "--no-textconv",
            "HEAD",
            "--",
        ],
    )?;
    fs::write(source.join("changes.patch"), &patch)?;
    let base_archive = source.join("base.tar");
    let file = fs::File::create(&base_archive)?;
    let mut archive = Command::new("git");
    archive
        .current_dir(&edit_root)
        .args(["archive", "--format=tar", &base_revision])
        .stdout(file);
    let status = archive.status()?;
    if !status.success() {
        return Err(format!("git archive failed: {status}").into());
    }
    let mut extract = Command::new("tar");
    extract
        .args(["-xf"])
        .arg(&base_archive)
        .arg("-C")
        .arg(&root);
    output(extract)?;
    if !patch.is_empty() {
        let mut apply = Command::new("git");
        apply
            .current_dir(&root)
            .args(["apply", "--binary", "--whitespace=nowarn"])
            .arg(source.join("changes.patch").canonicalize()?)
            .stdin(Stdio::null());
        output(apply)?;
    }
    let base_paths = paths(&git(
        &edit_root,
        &["ls-tree", "-rz", "--name-only", &base_revision],
    )?)?;
    let mut deleted = Vec::new();
    let present: BTreeSet<_> = before.iter().map(|i| i.path.clone()).collect();
    for path in &base_paths {
        if !present.contains(path) {
            deleted.push(path);
        }
    }
    for input in &before {
        if !base_paths.contains(&input.path) {
            copy_input(&edit_root, &root, input)?;
            copy_input(&edit_root, &source.join("untracked"), input)?;
        } else if input.kind == "file" {
            // Git records executable status, not the user's complete mode.
            fs::set_permissions(
                root.join(&input.path),
                fs::Permissions::from_mode(input.original_mode),
            )?;
        }
    }
    after_materialization()?;
    let after = inventory(&edit_root, &live_paths(&edit_root)?)?;
    let mut materialized_paths = BTreeSet::new();
    walk(&root, Path::new(""), &mut materialized_paths)?;
    let materialized = inventory(&root, &materialized_paths)?;
    if before != after || before != materialized {
        return Err(format!("source changed during snapshot preparation or reconstruction differs; discard candidate {}", root.display()).into());
    }
    if configs(&edit_root, &root)? != external_config
        || self::build_environment()? != build_environment
    {
        return Err("build configuration changed during snapshot preparation".into());
    }
    let identity = serde_json::to_vec(&(&before, &external_config, &build_environment))?;
    let id = format!("{:x}", Sha256::digest(identity));
    let plan = edit_root.join(".claude/plans/preimage-flamegraphs.md");
    if plan.exists() {
        fs::copy(plan, source.join("plan.md"))?;
    }
    atomic_json(
        &source.join("inputs.json"),
        &serde_json::json!({"inputs": before, "deleted": deleted, "exclusions": EXCLUDED}),
    )?;
    atomic_json(
        &source.join("build-config.json"),
        &serde_json::json!({"external_config": external_config, "environment": build_environment, "toolchain": "1.98.0"}),
    )?;
    seal(&root, &before)?;
    let snapshot = Snapshot {
        root,
        id,
        editing_root: edit_root,
        base_revision,
        inventory: before,
        external_config,
        build_environment,
    };
    // Preserve the exact sealed tree with the report so debug source locations
    // remain recoverable after the temporary compiler-input root is removed.
    let frozen_archive = source.canonicalize()?.join("frozen.tar");
    let mut archive = Command::new("tar");
    archive
        .arg("--exclude=./.profile-scratch")
        .arg("-cf")
        .arg(&frozen_archive)
        .arg("-C")
        .arg(&snapshot.root)
        .arg(".");
    output(archive)?;
    let archive_sha256 = sha256(&frozen_archive)?;
    let reconstruction = snapshot.root.with_file_name(format!(
        "flock-profile-archive-check-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&reconstruction)?;
    let reconstruction_guard = Candidate(reconstruction.clone());
    let mut extract = Command::new("tar");
    extract
        // Restore the sealed modes recorded by the archive, including its root
        // directory; default extraction applies the caller's writable umask.
        .arg("-xpf")
        .arg(&frozen_archive)
        .arg("-C")
        .arg(&reconstruction);
    output(extract)?;
    let reconstructed = Snapshot {
        root: reconstruction,
        ..snapshot.clone()
    };
    verify(&reconstructed)?;
    if sha256(&frozen_archive)? != archive_sha256 {
        return Err("frozen source archive changed during verification".into());
    }
    drop(reconstruction_guard);
    atomic_json(
        &source.join("frozen-archive.json"),
        &serde_json::json!({
            "path": "frozen.tar",
            "sha256": archive_sha256,
            "snapshot_id": snapshot.id,
            "input_count": snapshot.inventory.len(),
            "verified_by": "independent extraction and complete snapshot inventory verification",
            "excluded": [".profile-scratch"]
        }),
    )?;
    atomic_json(&source.join("snapshot.json"), &snapshot)?;
    atomic_json(
        &source.join("path-map.json"),
        &serde_json::json!({"editing_root": snapshot.editing_root, "compiler_source_root": snapshot.root, "snapshot_id": snapshot.id}),
    )?;
    verify(&snapshot)?;
    std::mem::forget(candidate);
    Ok(snapshot)
}

/// Refuse evidence when any frozen input, configuration or sealing mode changed.
pub fn verify(snapshot: &Snapshot) -> Result<()> {
    let mut files = BTreeSet::new();
    walk(&snapshot.root, Path::new(""), &mut files)?;
    let current = inventory(&snapshot.root, &files)?;
    if current.len() != snapshot.inventory.len() {
        return Err("snapshot input membership changed".into());
    }
    for (actual, expected) in current.iter().zip(&snapshot.inventory) {
        if actual.path != expected.path
            || actual.kind != expected.kind
            || actual.sha256 != expected.sha256
            || actual.symlink_target != expected.symlink_target
            || actual.original_mode != expected.sealed_mode
        {
            return Err(format!("frozen input changed: {}", expected.path.display()).into());
        }
    }
    fn check_directories(root: &Path) -> Result<()> {
        if fs::metadata(root)?.mode() & 0o222 != 0 {
            return Err(format!("frozen directory is writable: {}", root.display()).into());
        }
        for entry in fs::read_dir(root)? {
            let entry = entry?;
            if entry.file_name() != ".profile-scratch" && entry.file_type()?.is_dir() {
                check_directories(&entry.path())?;
            }
        }
        Ok(())
    }
    check_directories(&snapshot.root)?;
    for config in &snapshot.external_config {
        let current = if config.path.exists() {
            Some(sha256(&config.path)?)
        } else {
            None
        };
        if current != config.sha256 {
            return Err(format!(
                "external Cargo configuration changed: {}",
                config.path.display()
            )
            .into());
        }
    }
    if build_environment()? != snapshot.build_environment {
        return Err("build environment changed since snapshot preparation".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_changed_during_preparation_is_rejected() -> Result<()> {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let base = env::temp_dir().join(format!(
            "flock-snapshot-race-{}-{nonce}",
            std::process::id()
        ));
        let edit = base.join("edit");
        fs::create_dir_all(edit.join("crates"))?;
        fs::write(edit.join("Cargo.toml"), "[workspace]\nmembers = []\n")?;
        fs::write(edit.join("crates/input.rs"), "original")?;
        git(&edit, &["init", "-q"])?;
        git(&edit, &["add", "."])?;
        git(
            &edit,
            &[
                "-c",
                "user.name=Snapshot Test",
                "-c",
                "user.email=snapshot@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-qm",
                "fixture",
            ],
        )?;
        let result = prepare_with(&edit, &base.join("report"), || {
            fs::write(edit.join("crates/input.rs"), "changed while preparing")?;
            Ok(())
        });
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains("source changed during snapshot preparation")
        );
        fs::remove_dir_all(base)?;
        Ok(())
    }
}

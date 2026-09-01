use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const DIRECT_SHA256_NEEDLES: &[&str] = &[
    "use sha2::",
    "sha2::compress",
    "Sha256::digest",
    "Sha256::new",
];
const SUPERSEDED_ZK_SURFACE_NEEDLES: &[&str] =
    &["R1csProofZkA1", "prove_r1cs_zk_a1", "verify_r1cs_zk_a1"];

#[test]
fn direct_sha256_stays_inside_the_reviewed_random_oracle() {
    let root = workspace_root();
    let mut findings = Vec::new();

    for relative in ["crates/flock-core/src", "crates/flock-prover/src"] {
        scan_files(
            &root.join(relative),
            &mut |path| path.extension() == Some(OsStr::new("rs")),
            &mut |path, line_number, line| {
                let relative_path = relative_path(&root, path);
                if relative_path == Path::new("crates/flock-core/src/ro.rs")
                    || relative_path == Path::new("crates/flock-core/src/challenger.rs")
                {
                    return;
                }

                if DIRECT_SHA256_NEEDLES
                    .iter()
                    .any(|needle| line.contains(needle))
                {
                    findings.push(format!("{}:{line_number}:{line}", relative_path.display()));
                }
            },
        );
    }

    assert!(
        findings.is_empty(),
        "direct SHA-256 call outside ro.rs/challenger.rs:\n{}",
        findings.join("\n")
    );
}

#[test]
fn superseded_zk_surface_stays_removed() {
    let root = workspace_root();
    let this_test = Path::new("crates/flock-core/tests/repository_policy.rs");
    let mut findings = Vec::new();

    for relative in ["crates", "docs", "SPEC.md", "README.md"] {
        scan_files(
            &root.join(relative),
            &mut |_| true,
            &mut |path, line_number, line| {
                let relative_path = relative_path(&root, path);
                if relative_path != this_test && contains_superseded_zk_surface(line) {
                    findings.push(format!("{}:{line_number}:{line}", relative_path.display()));
                }
            },
        );
    }

    assert!(
        findings.is_empty(),
        "superseded or versioned ZK surface found:\n{}",
        findings.join("\n")
    );
}

#[test]
fn repository_has_no_python_or_shell_scripts() {
    let root = workspace_root();
    let output = Command::new("git")
        .args(["ls-files", "--", "*.py", "*.sh"])
        .current_dir(&root)
        .output()
        .expect("enumerate tracked scripts");

    assert!(
        output.status.success(),
        "git ls-files failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let scripts = String::from_utf8_lossy(&output.stdout);
    assert!(
        scripts.trim().is_empty(),
        "tracked Python or shell scripts found:\n{scripts}"
    );
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("flock-core lives two levels below the workspace root")
        .to_path_buf()
}

fn scan_files<F, G>(path: &Path, include: &mut F, visit: &mut G)
where
    F: FnMut(&Path) -> bool,
    G: FnMut(&Path, usize, &str),
{
    if path.is_dir() {
        let mut entries = fs::read_dir(path)
            .unwrap_or_else(|error| panic!("failed to read '{}': {error}", path.display()))
            .collect::<Result<Vec<_>, _>>()
            .unwrap_or_else(|error| {
                panic!("failed to read an entry in '{}': {error}", path.display())
            });
        entries.sort_by_key(|entry| entry.path());

        for entry in entries {
            scan_files(&entry.path(), include, visit);
        }
        return;
    }

    if !path.is_file() || !include(path) {
        return;
    }

    let Ok(contents) = fs::read_to_string(path) else {
        return;
    };
    for (index, line) in contents.lines().enumerate() {
        visit(path, index + 1, line);
    }
}

fn relative_path<'a>(root: &'a Path, path: &'a Path) -> &'a Path {
    path.strip_prefix(root).unwrap_or(path)
}

fn contains_superseded_zk_surface(line: &str) -> bool {
    SUPERSEDED_ZK_SURFACE_NEEDLES
        .iter()
        .any(|needle| line.contains(needle))
        || contains_versioned_veil_flock_domain(line)
}

fn contains_versioned_veil_flock_domain(line: &str) -> bool {
    let needle = "veil-flock";
    let mut search_from = 0;
    while let Some(relative) = line[search_from..].find(needle) {
        let tail_start = search_from + relative + needle.len();
        let tail = &line[tail_start..];
        let tail_end = tail.find(['"', ' ']).unwrap_or(tail.len());
        if tail.as_bytes()[..tail_end]
            .windows(3)
            .any(|window| window[0] == b'-' && window[1] == b'v' && window[2].is_ascii_digit())
        {
            return true;
        }
        search_from = tail_start;
    }
    false
}

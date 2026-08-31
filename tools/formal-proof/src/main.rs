//! Reproducible Lean build and axiom audit for the repository's formal proofs.

use std::{
    collections::BTreeSet,
    env,
    error::Error,
    ffi::OsStr,
    fs,
    io::{self, BufRead, BufReader, IsTerminal, Write},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
    sync::mpsc,
    thread,
    time::{SystemTime, UNIX_EPOCH},
};

const ALLOWED_AXIOMS: &[&str] = &["propext", "Classical.choice", "Quot.sound"];
const PRODUCTION_AUDIT_FILE: &str = "VeiledFlock/Production/Security/FormalZKAxiomAudit.lean";
const MAIN_THEOREM: &str = "VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126";
const DEFAULT_BAR_WIDTH: usize = 36;

type AnyError = Box<dyn Error + Send + Sync>;
type Result<T> = std::result::Result<T, AnyError>;

fn main() -> ExitCode {
    if let Err(error) = run() {
        eprintln!("formal-proof: {error}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

fn run() -> Result<()> {
    let command = env::args().nth(1).unwrap_or_else(|| "verify".to_owned());
    let root = repository_root()?;
    match command.as_str() {
        "verify" => verify(&root),
        "build" => build(&root),
        "audit" => audit(&root),
        "help" | "--help" | "-h" => {
            println!("Usage: formal-proof [verify|build|audit]");
            Ok(())
        }
        _ => Err(invalid_input(format!(
            "unknown command '{command}'; expected verify, build, or audit"
        ))),
    }
}

fn verify(root: &Path) -> Result<()> {
    let lean_dir = root.join("lean");
    eprintln!("formal-proof: preparing the pinned Mathlib cache");
    run_lake(&lean_dir, ["exe", "cache", "get"])?;
    build(root)?;
    eprintln!("formal-proof: auditing theorem axioms");
    audit(root)?;
    eprintln!("formal-proof: verified");
    Ok(())
}

fn build(root: &Path) -> Result<()> {
    let lean_dir = root.join("lean");
    let bar_width = progress_bar_width()?;
    let interactive = io::stderr().is_terminal();
    eprintln!("formal-proof: building all Lean proof libraries");
    if interactive {
        draw_progress(0, 1, bar_width)?;
    } else {
        eprintln!("Lean build [  0%] 0/? targets");
    }

    let lake = env::var_os("LAKE").unwrap_or_else(|| "lake".into());
    let mut child = Command::new(lake)
        .arg("build")
        .current_dir(&lean_dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| invalid_input(format!("could not start lake build: {error}")))?;

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| invalid_input("could not capture lake stdout"))?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| invalid_input("could not capture lake stderr"))?;
    let (sender, receiver) = mpsc::channel();
    let stdout_reader = forward_lines(stdout, sender.clone());
    let stderr_reader = forward_lines(stderr, sender);

    let mut completed = 0;
    let mut total = 1;
    let mut saw_progress = false;
    let mut next_report = 0;
    for message in receiver {
        let line = message?;
        if let Some((new_completed, new_total)) = parse_lake_progress(&line) {
            completed = new_completed;
            total = new_total;
            saw_progress = true;
            let percent = completed.saturating_mul(100) / total;
            if interactive {
                draw_progress(completed, total, bar_width)?;
            } else if percent >= next_report {
                eprintln!("Lean build [{percent:3}%] {completed}/{total} targets");
                next_report = (percent / 5 + 1) * 5;
            }
        } else {
            if interactive && saw_progress {
                clear_progress()?;
            }
            eprintln!("{line}");
            if interactive && saw_progress {
                draw_progress(completed, total, bar_width)?;
            }
        }
    }

    join_reader(stdout_reader)?;
    join_reader(stderr_reader)?;
    let status = child.wait()?;
    if !status.success() {
        if interactive {
            clear_progress()?;
        }
        return Err(invalid_input(format!(
            "Lean build failed with status {status}"
        )));
    }

    if interactive {
        draw_progress(1, 1, bar_width)?;
        eprintln!();
    } else {
        eprintln!("Lean build [100%] complete");
    }
    Ok(())
}

fn audit(root: &Path) -> Result<()> {
    let lean_dir = root.join("lean");
    let names = audited_theorems(&lean_dir)?;
    if names.is_empty() {
        return Err(invalid_input("axiom audit found no theorems"));
    }

    let audit_dir = TemporaryDirectory::create()?;
    let audit_file = audit_dir.path.join("AxiomAudit.lean");
    let mut source = String::from("import Flockzk\nimport VeiledFlock\n");
    for name in &names {
        source.push_str("#print axioms ");
        source.push_str(name);
        source.push('\n');
    }
    fs::write(&audit_file, source)?;

    let lake = env::var_os("LAKE").unwrap_or_else(|| "lake".into());
    let output = Command::new(lake)
        .args([OsStr::new("env"), OsStr::new("lean")])
        .arg(&audit_file)
        .current_dir(&lean_dir)
        .output()
        .map_err(|error| invalid_input(format!("could not start Lean axiom audit: {error}")))?;

    io::stdout().write_all(&output.stdout)?;
    io::stderr().write_all(&output.stderr)?;
    if !output.status.success() {
        return Err(invalid_input(format!(
            "axiom audit elaboration failed with status {}",
            output.status
        )));
    }

    let mut rendered = String::from_utf8_lossy(&output.stdout).into_owned();
    rendered.push_str(&String::from_utf8_lossy(&output.stderr));
    let report = parse_axiom_report(&rendered)?;
    let missing = names.difference(&report.theorems).collect::<Vec<_>>();
    let unexpected = report.theorems.difference(&names).collect::<Vec<_>>();
    if !missing.is_empty() || !unexpected.is_empty() {
        return Err(invalid_input(format!(
            "axiom report mismatch; missing: {missing:?}; unexpected: {unexpected:?}"
        )));
    }

    let allowed = ALLOWED_AXIOMS.iter().copied().collect::<BTreeSet<_>>();
    let bad_axioms = report
        .axioms
        .iter()
        .filter(|axiom| !allowed.contains(axiom.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if !bad_axioms.is_empty() {
        return Err(invalid_input(format!(
            "non-standard axioms found: {}",
            bad_axioms.join(", ")
        )));
    }

    println!(
        "lean-axioms: OK — {} theorems depend only on propext / Classical.choice / Quot.sound",
        names.len()
    );
    Ok(())
}

fn repository_root() -> Result<PathBuf> {
    let current = env::current_dir()?;
    if let Some(root) = find_repository_root(&current) {
        return Ok(root);
    }
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    find_repository_root(manifest_dir).ok_or_else(|| {
        invalid_input(
            "could not locate repository root containing Cargo.toml and lean/lakefile.toml",
        )
    })
}

fn find_repository_root(start: &Path) -> Option<PathBuf> {
    start.ancestors().find_map(|candidate| {
        (candidate.join("Cargo.toml").is_file() && candidate.join("lean/lakefile.toml").is_file())
            .then(|| candidate.to_path_buf())
    })
}

fn progress_bar_width() -> Result<usize> {
    let Some(value) = env::var_os("FORMAL_PROOF_BAR_WIDTH") else {
        return Ok(DEFAULT_BAR_WIDTH);
    };
    let value = value
        .into_string()
        .map_err(|_| invalid_input("FORMAL_PROOF_BAR_WIDTH must be valid UTF-8"))?;
    let width = value
        .parse::<usize>()
        .map_err(|_| invalid_input("FORMAL_PROOF_BAR_WIDTH must be a positive integer"))?;
    if width == 0 {
        return Err(invalid_input(
            "FORMAL_PROOF_BAR_WIDTH must be a positive integer",
        ));
    }
    Ok(width)
}

fn run_lake<I, S>(lean_dir: &Path, args: I) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let lake = env::var_os("LAKE").unwrap_or_else(|| "lake".into());
    let status = Command::new(lake)
        .args(args)
        .current_dir(lean_dir)
        .status()?;
    if status.success() {
        Ok(())
    } else {
        Err(invalid_input(format!("lake failed with status {status}")))
    }
}

fn forward_lines<R>(reader: R, sender: mpsc::Sender<io::Result<String>>) -> thread::JoinHandle<()>
where
    R: io::Read + Send + 'static,
{
    thread::spawn(move || {
        for line in BufReader::new(reader).lines() {
            if sender.send(line).is_err() {
                break;
            }
        }
    })
}

fn join_reader(reader: thread::JoinHandle<()>) -> Result<()> {
    reader
        .join()
        .map_err(|_| invalid_input("lake output reader thread panicked"))
}

fn parse_lake_progress(line: &str) -> Option<(usize, usize)> {
    let open = line.find('[')?;
    let close = line[open + 1..].find(']')? + open + 1;
    if !line[close + 1..].contains("Built") {
        return None;
    }
    let (completed, total) = line[open + 1..close].split_once('/')?;
    let completed = completed.parse().ok()?;
    let total = total.parse().ok()?;
    (total > 0 && completed <= total).then_some((completed, total))
}

fn draw_progress(completed: usize, total: usize, width: usize) -> Result<()> {
    let percent = completed.saturating_mul(100) / total;
    let filled = completed.saturating_mul(width) / total;
    let empty = width - filled;
    eprint!(
        "\r\x1b[2KLean build [{}{}] {percent:3}% ({completed}/{total})",
        "#".repeat(filled),
        "-".repeat(empty)
    );
    io::stderr().flush()?;
    Ok(())
}

fn clear_progress() -> Result<()> {
    eprint!("\r\x1b[2K");
    io::stderr().flush()?;
    Ok(())
}

fn audited_theorems(lean_dir: &Path) -> Result<BTreeSet<String>> {
    let mut files = fs::read_dir(lean_dir.join("Flockzk"))?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    files.sort();

    let mut names = BTreeSet::new();
    for path in files.into_iter().filter(|path| {
        path.extension()
            .is_some_and(|extension| extension == OsStr::new("lean"))
    }) {
        for line in fs::read_to_string(path)?.lines() {
            let Some(declaration) = line.strip_prefix("theorem ") else {
                continue;
            };
            if let Some(name) = declaration.split_whitespace().next() {
                names.insert(format!("FlockZk.{name}"));
            }
        }
    }
    let mut production_count = 0;
    for line in fs::read_to_string(lean_dir.join(PRODUCTION_AUDIT_FILE))?.lines() {
        if let Some(declaration) = line.trim().strip_prefix("#print axioms ")
            && let Some(name) = declaration.split_whitespace().next()
        {
            names.insert(name.to_owned());
            production_count += 1;
        }
    }
    if production_count == 0 || !names.contains(MAIN_THEOREM) {
        return Err(invalid_input(format!(
            "{PRODUCTION_AUDIT_FILE} must audit the main FormalZK theorem"
        )));
    }
    Ok(names)
}

#[derive(Default)]
struct AxiomReport {
    theorems: BTreeSet<String>,
    axioms: BTreeSet<String>,
}

fn parse_axiom_report(output: &str) -> Result<AxiomReport> {
    let mut report = AxiomReport::default();
    let mut pending_axioms = None::<String>;

    for line in output.lines() {
        if let Some(name) = reported_theorem(line) {
            report.theorems.insert(name.to_owned());
        }

        if let Some((_, start)) = line.split_once("depends on axioms: [") {
            let mut record = start.to_owned();
            if let Some((complete, _)) = record.split_once(']') {
                add_axioms(&mut report.axioms, complete);
            } else {
                record.push(' ');
                pending_axioms = Some(record);
            }
        } else if let Some(record) = pending_axioms.as_mut() {
            if let Some((complete, _)) = line.split_once(']') {
                record.push_str(complete);
                add_axioms(&mut report.axioms, record);
                pending_axioms = None;
            } else {
                record.push_str(line);
                record.push(' ');
            }
        }
    }

    if pending_axioms.is_some() {
        return Err(invalid_input("unterminated axiom report"));
    }
    Ok(report)
}

fn reported_theorem(line: &str) -> Option<&str> {
    if !(line.contains("does not depend on any axioms") || line.contains("depends on axioms:")) {
        return None;
    }
    let rest = line.strip_prefix('\'')?;
    rest.split_once('\'').map(|(name, _)| name)
}

fn add_axioms(axioms: &mut BTreeSet<String>, record: &str) {
    axioms.extend(
        record
            .split(',')
            .map(str::trim)
            .filter(|axiom| !axiom.is_empty())
            .map(str::to_owned),
    );
}

struct TemporaryDirectory {
    path: PathBuf,
}

impl TemporaryDirectory {
    fn create() -> Result<Self> {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let path = env::temp_dir().join(format!(
            "veiled-flock-axioms-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path)?;
        Ok(Self { path })
    }
}

impl Drop for TemporaryDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn invalid_input(message: impl Into<String>) -> AnyError {
    io::Error::new(io::ErrorKind::InvalidInput, message.into()).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_lake_progress() {
        assert_eq!(parse_lake_progress("[12/80] Built Foo"), Some((12, 80)));
        assert_eq!(parse_lake_progress("[12/80] Building Foo"), None);
        assert_eq!(parse_lake_progress("Build completed"), None);
    }

    #[test]
    fn parses_wrapped_axiom_reports() {
        let output = "'A' does not depend on any axioms\n\
'B' depends on axioms: [propext,\n\
 Classical.choice,\n\
 Quot.sound]\n";
        let report = parse_axiom_report(output).unwrap();
        assert_eq!(report.theorems, BTreeSet::from(["A".into(), "B".into()]));
        assert_eq!(
            report.axioms,
            BTreeSet::from([
                "Classical.choice".into(),
                "Quot.sound".into(),
                "propext".into()
            ])
        );
    }
}

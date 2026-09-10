//! Immutable report generations over read-only measurement evidence.
//!
//! Payload -> inventory -> generation manifest -> external current pointer is
//! an acyclic checksum chain. Publication is one pointer replacement, never a
//! sequence of replacements of visible reports or flamegraphs.

use crate::{
    Result, atomic_json, canonical_output, evidence, records, report, sha256, snapshot, xctrace,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{BufReader, BufWriter, Write},
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

const EXCLUSIONS: &[&str] = &["artifacts.json", "generation.json"];
static NEXT: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Serialize, Deserialize)]
struct Generation {
    schema_version: u32,
    id: String,
    state: String,
    inventory_sha256: String,
    evidence_root: PathBuf,
    input_sha256: BTreeMap<PathBuf, String>,
    processor: snapshot::ProcessorIdentity,
    authored_findings: Option<records::ArtifactIdentity>,
}

#[derive(Debug, Serialize, Deserialize)]
struct Pointer {
    schema_version: u32,
    generation: String,
    manifest_sha256: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Boundary {
    Ready,
    Renamed,
    Published,
}

fn json(path: &Path) -> Result<Value> {
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}

fn safe_relative(path: &Path) -> Result<()> {
    if path.as_os_str().is_empty()
        || path
            .components()
            .any(|p| !matches!(p, Component::Normal(_)))
    {
        return Err(format!("expected a contained relative path: {}", path.display()).into());
    }
    Ok(())
}

fn remember(inputs: &mut BTreeMap<PathBuf, String>, path: &Path) -> Result<()> {
    let path = path.canonicalize()?;
    if !fs::symlink_metadata(&path)?.is_file() {
        return Err("input is not a regular file".into());
    }
    let hash = sha256(&path)?;
    if inputs.get(&path).is_some_and(|old| old != &hash) {
        return Err("input changed while preparing publication".into());
    }
    inputs.insert(path, hash);
    Ok(())
}

fn verify_inputs(inputs: &BTreeMap<PathBuf, String>) -> Result<()> {
    for (path, hash) in inputs {
        if sha256(path)? != *hash {
            return Err(format!("publication input changed: {}", path.display()).into());
        }
    }
    Ok(())
}

fn copy_input(from: &Path, to: &Path, inputs: &mut BTreeMap<PathBuf, String>) -> Result<()> {
    remember(inputs, from)?;
    fs::create_dir_all(to.parent().ok_or("copy destination has no parent")?)?;
    if to.exists() {
        return Err(format!("refusing to replace staged input {}", to.display()).into());
    }
    fs::copy(from, to)?;
    if sha256(from)? != sha256(to)? {
        return Err("copied input changed".into());
    }
    Ok(())
}

fn verify_generation(path: &Path) -> Result<Generation> {
    let generation: Generation = serde_json::from_slice(&fs::read(path.join("generation.json"))?)?;
    if generation.schema_version != 2 || generation.state != "ready" {
        return Err("generation is not ready for publication".into());
    }
    safe_relative(Path::new(&generation.id))?;
    if Path::new(&generation.id).components().count() != 1 {
        return Err("invalid generation identity".into());
    }
    if sha256(&path.join("artifacts.json"))? != generation.inventory_sha256 {
        return Err("generation inventory checksum differs".into());
    }
    let inventory: evidence::Inventory =
        serde_json::from_slice(&fs::read(path.join("artifacts.json"))?)?;
    if inventory
        .exclusions
        .iter()
        .map(String::as_str)
        .ne(EXCLUSIONS.iter().copied())
    {
        return Err("generation inventory exclusions differ from publication policy".into());
    }
    evidence::verify_inventory(path, &inventory)?;
    check_links(path)?;
    Ok(generation)
}

fn finish(
    staging: &Path,
    output: &Path,
    mut generation: Generation,
    mut boundary: impl FnMut(Boundary) -> Result<()>,
) -> Result<PathBuf> {
    verify_inputs(&generation.input_sha256)?;
    check_links(staging)?;
    evidence::write_inventory(staging, EXCLUSIONS)?;
    generation.inventory_sha256 = sha256(&staging.join("artifacts.json"))?;
    generation.state = "ready".into();
    atomic_json(&staging.join("generation.json"), &generation)?;
    boundary(Boundary::Ready)?;
    let destination = output.join("generations").join(&generation.id);
    if destination.exists() {
        return Err("generation destination already exists".into());
    }
    fs::rename(staging, &destination)?;
    // Relative links into companion evidence must still resolve after rename.
    verify_generation(&destination)?;
    boundary(Boundary::Renamed)?;
    verify_inputs(&generation.input_sha256)?;
    let pointer = Pointer {
        schema_version: 2,
        generation: generation.id,
        manifest_sha256: sha256(&destination.join("generation.json"))?,
    };
    atomic_json(&output.join("current.json"), &pointer)?;
    boundary(Boundary::Published)?;
    Ok(destination.join("index.html").canonicalize()?)
}

/// Validate a published pointer exactly once and return its immutable gallery.
pub fn current(output: &Path) -> Result<PathBuf> {
    let output = output.canonicalize()?;
    ordinary_directory(&output.join("generations"))?;
    let pointer: Pointer = serde_json::from_slice(&fs::read(output.join("current.json"))?)?;
    safe_relative(Path::new(&pointer.generation))?;
    if pointer.schema_version != 2 || Path::new(&pointer.generation).components().count() != 1 {
        return Err("invalid publication pointer".into());
    }
    let path = output.join("generations").join(&pointer.generation);
    if sha256(&path.join("generation.json"))? != pointer.manifest_sha256 {
        return Err("current generation manifest checksum differs".into());
    }
    let generation = verify_generation(&path)?;
    if generation.id != pointer.generation {
        return Err("current generation identity differs".into());
    }
    Ok(path.join("index.html"))
}

/// Select a ready orphan after a process stopped between rename and pointer swap.
/// Partial staging directories are retained; retries allocate a fresh one.
pub fn recover_ready(output: &Path, id: &str) -> Result<PathBuf> {
    let output = output.canonicalize()?;
    safe_relative(Path::new(id))?;
    if Path::new(id).components().count() != 1 {
        return Err("invalid generation id".into());
    }
    let _lock = evidence::WriterLock::acquire(&output)?;
    ordinary_directory(&output.join("generations"))?;
    let path = output.join("generations").join(id);
    let generation = verify_generation(&path)?;
    if generation.id != id {
        return Err("orphan generation identity differs".into());
    }
    verify_inputs(&generation.input_sha256)?;
    generation.processor.verify()?;
    let measured_manifest = json(&generation.evidence_root.join("manifest.json"))?;
    let policy: Vec<String> = serde_json::from_value(
        measured_manifest["environment"]["measurement_environment_removed"].clone(),
    )?;
    for attempt in selected_evidence(&generation.evidence_root, &measured_manifest, &policy)? {
        records::verify_attempt_evidence(&attempt)?;
    }
    if measured_manifest["schema_version"].as_u64().unwrap_or(1) == 1
        && generation.evidence_root.join("artifacts.json").is_file()
    {
        let inventory =
            serde_json::from_slice(&fs::read(generation.evidence_root.join("artifacts.json"))?)?;
        evidence::verify_inventory(&generation.evidence_root, &inventory)?;
    }
    atomic_json(
        &output.join("current.json"),
        &Pointer {
            schema_version: 2,
            generation: id.into(),
            manifest_sha256: sha256(&path.join("generation.json"))?,
        },
    )?;
    Ok(path.join("index.html"))
}

/// Reconstruct display artifacts in a fresh generation. Neither a legacy root
/// nor its authored findings, input metadata or previously corrected files are
/// ever modified. The processor must have been built from a registered snapshot.
pub fn publish(
    evidence_root: &Path,
    output: &Path,
    authored_findings: Option<&Path>,
    processor: &snapshot::ProcessorIdentity,
) -> Result<PathBuf> {
    let root = evidence_root.canonicalize()?;
    let output = canonical_output(output)?;
    crate::reject_overlap(&root, &output)?;
    processor.verify_running()?;
    if !root.join("complete.json").is_file() && !root.join("measurements-complete.json").is_file() {
        return Err("publication requires completed measurement evidence".into());
    }
    let mut inputs = BTreeMap::new();
    remember(&mut inputs, &root.join("manifest.json"))?;
    if root.join("selection.json").is_file() {
        remember(&mut inputs, &root.join("selection.json"))?;
    }
    if root.join("report-processing.json").is_file() {
        remember(&mut inputs, &root.join("report-processing.json"))?;
        if json(&root.join("report-processing.json"))?["status"] != "complete" {
            return Err("legacy report processing is incomplete".into());
        }
    }
    let manifest = json(&root.join("manifest.json"))?;
    let measured: snapshot::Snapshot = serde_json::from_value(manifest["snapshot"].clone())?;
    let policy: Vec<String> =
        serde_json::from_value(manifest["environment"]["measurement_environment_removed"].clone())?;
    verify_frozen_policy(&root, &measured, &policy, &mut inputs)?;
    let v2 = manifest["schema_version"].as_u64().unwrap_or(1) == 2;
    if !v2 && root.join("artifacts.json").is_file() {
        remember(&mut inputs, &root.join("artifacts.json"))?;
        let inventory = serde_json::from_slice(&fs::read(root.join("artifacts.json"))?)?;
        evidence::verify_inventory(&root, &inventory)?;
    }
    let power_policy = if v2 {
        Some(serde_json::from_value::<crate::host::PowerPolicy>(
            manifest["power_policy"].clone(),
        )?)
    } else {
        None
    };
    let selected = selected_evidence(&root, &manifest, &policy)?;
    fs::create_dir_all(&output)?;
    let _lock = evidence::WriterLock::acquire(&output)?;
    let generations = output.join("generations");
    if !generations.exists() {
        fs::create_dir(&generations)?;
    }
    ordinary_directory(&generations)?;
    let id = format!(
        "{}-{}-{}",
        SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos(),
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    );
    // Same depth as the final generations/<id> directory for companion links.
    let staging = output.join("generations").join(format!(".staging-{id}"));
    fs::create_dir(&staging)?;
    let result = (|| -> Result<PathBuf> {
        copy_input(
            &root.join("manifest.json"),
            &staging.join("manifest.json"),
            &mut inputs,
        )?;
        for name in [
            "selection.json",
            "complete.json",
            "measurements-complete.json",
            "resume.json",
        ] {
            if root.join(name).is_file() {
                copy_input(&root.join(name), &staging.join(name), &mut inputs)?;
            }
        }
        let episode_caveats = prepare_baselines(&root, &staging, power_policy, &mut inputs)?;
        let legacy_episodes = if v2 {
            BTreeMap::new()
        } else {
            legacy_episodes(&root, &staging, &mut inputs)?
        };
        fs::create_dir(staging.join("source"))?;
        fs::create_dir(staging.join("logs"))?;
        if root.join("logs").is_dir() {
            for entry in fs::read_dir(root.join("logs"))? {
                let entry = entry?;
                if entry.file_type()?.is_file() {
                    copy_input(
                        &entry.path(),
                        &staging.join("logs").join(entry.file_name()),
                        &mut inputs,
                    )?;
                }
            }
        }
        fs::create_dir(staging.join("svg"))?;
        fs::create_dir(staging.join("processing"))?;
        copy_input(
            &processor.source_archive.path,
            &staging.join("processing/frozen.tar"),
            &mut inputs,
        )?;
        atomic_json(&staging.join("processing/identity.json"), processor)?;
        let lock = processor.snapshot.root.join("Cargo.lock");
        let lock_data: toml::Value = toml::from_str(&fs::read_to_string(&lock)?)?;
        let versions = lock_data["package"]
            .as_array()
            .ok_or("frozen lockfile package list missing")?
            .iter()
            .filter(|package| package["name"].as_str() == Some("inferno"))
            .map(|package| {
                package["version"]
                    .as_str()
                    .ok_or("renderer version missing")
            })
            .collect::<std::result::Result<Vec<_>, _>>()?;
        if versions.len() != 1 {
            return Err("frozen renderer dependency identity is ambiguous".into());
        }
        copy_input(&lock, &staging.join("processing/Cargo.lock"), &mut inputs)?;
        atomic_json(
            &staging.join("processing/dependencies.json"),
            &json!({"inferno":versions[0],"source":"Cargo.lock"}),
        )?;
        let source = prepare_source(&measured, &staging, &mut inputs)?;
        let mut captures = Vec::new();
        for saved in &selected {
            records::verify_attempt_evidence(saved)?;
            let relative = saved.dir.strip_prefix(&root)?;
            safe_relative(relative)?;
            let destination = staging.join(relative);
            fs::create_dir_all(&destination)?;
            for name in [
                "attempt.json",
                "harness.json",
                "record-status.json",
                "export-status.json",
            ] {
                copy_input(&saved.dir.join(name), &destination.join(name), &mut inputs)?;
            }
            let xml = saved.dir.join("raw/time-profile.xml");
            remember(&mut inputs, &xml)?;
            let trace = xctrace::collapse(BufReader::new(File::open(&xml)?))?;
            let stats = report::analyze_resolved(&trace)?;
            let original = json(&saved.dir.join("attempt.json"))?;
            if original["schema_version"] == 2 {
                validate_power(
                    &original,
                    power_policy.unwrap_or(crate::host::PowerPolicy::ObserveOnly),
                )?;
            }
            if original["stats"]["usable_rows"].as_u64() != Some(stats.usable_rows)
                || original["stats"]["xml_rows"].as_u64() != Some(stats.xml_rows)
            {
                return Err("reconstructed sample totals differ from accepted evidence".into());
            }
            let mut folded = BufWriter::new(File::create(destination.join("stacks.folded"))?);
            for (stack, count) in &trace.stacks {
                writeln!(folded, "{stack} {count}")?;
            }
            folded.flush()?;
            atomic_json(&destination.join("analysis.json"), &stats)?;
            atomic_json(&destination.join("symbol-names.json"), &trace.symbols)?;
            atomic_json(&destination.join("collapse.json"), &trace.summary)?;
            let mut options = inferno::flamegraph::Options::default();
            options.deterministic = true;
            options.title = format!(
                "{} — usable backtrace rows",
                original["attempt_id"]
                    .as_str()
                    .ok_or("missing attempt identity")?
            );
            inferno::flamegraph::from_reader(
                &mut options,
                BufReader::new(File::open(destination.join("stacks.folded"))?),
                File::create(destination.join("flamegraph.svg"))?,
            )?;
            report::validate_svg(&destination.join("flamegraph.svg"))?;
            let case = saved
                .dir
                .parent()
                .and_then(Path::file_name)
                .and_then(|s| s.to_str())
                .ok_or("case directory missing")?
                .to_owned();
            if original["kind"] == "primary" {
                fs::copy(
                    destination.join("flamegraph.svg"),
                    staging.join("svg").join(format!("{case}.svg")),
                )?;
            }
            // Every raw link is explicit and tied to the companion evidence root.
            let companion = relative_path(&destination, &saved.dir)?;
            fs::write(
                destination.join("evidence.md"),
                format!(
                    "[Original XML]({companion}/raw/time-profile.xml) · [Original trace]({companion}/raw/recording.trace/)\n"
                ),
            )?;
            let mut display_attempt = original;
            if let Some(episode) = legacy_episodes.get(
                display_attempt["attempt_id"]
                    .as_str()
                    .ok_or("attempt ID missing")?,
            ) {
                display_attempt["episode_id"] = json!(episode);
            }
            captures.push(report::Capture {
                dir: destination,
                case,
                attempt: display_attempt,
                harness: serde_json::to_value(&saved.harness)?,
                stats,
            });
        }
        let findings_path = authored_findings.map(Path::to_path_buf).or_else(|| {
            root.join("findings.md")
                .is_file()
                .then(|| root.join("findings.md"))
        });
        let findings_identity = if let Some(path) = findings_path {
            let artifact = records::ArtifactIdentity::register(&path)?;
            copy_input(&path, &staging.join("findings-source.md"), &mut inputs)?;
            let content = fs::read_to_string(&path)?;
            // Keep authored bytes exact; the rendered copy resolves links from
            // the author's declared source directory into companion evidence.
            fs::write(
                staging.join("findings.md"),
                relocate_markdown(
                    &content,
                    path.parent().ok_or("findings have no parent")?,
                    &staging,
                )?,
            )?;
            Some(artifact)
        } else {
            None
        };
        let caveats = format!(
            "{}\n{}\n[Original measurement evidence]({}) remains in its recorded companion directory; raw trace/XML links depend on that directory. The immutable generation records hashes of its consumed inputs.\n\n",
            episode_caveats,
            power_caveats(&captures),
            relative_path(&staging, &root)?
        );
        report::render(&staging, source.as_deref(), captures, &caveats)?;
        // Temporary lookup copies are not needed after verified excerpts have
        // been emitted; retain them as provenance rather than delete evidence.
        processor.verify_running()?;
        finish(
            &staging,
            &output,
            Generation {
                schema_version: 2,
                id: id.clone(),
                state: "rendered".into(),
                inventory_sha256: String::new(),
                evidence_root: root.clone(),
                input_sha256: inputs.clone(),
                processor: processor.clone(),
                authored_findings: findings_identity,
            },
            |step| {
                if step == Boundary::Renamed {
                    processor.verify_running()?;
                    for saved in &selected {
                        records::verify_attempt_evidence(saved)?;
                    }
                }
                Ok(())
            },
        )
    })();
    if let Err(error) = &result
        && staging.exists()
    {
        atomic_json(
            &staging.join("failure.json"),
            &json!({"state":"partial_failure","error":error.to_string()}),
        )?;
    }
    result
}

fn ordinary_directory(path: &Path) -> Result<()> {
    if !fs::symlink_metadata(path)?.is_dir() {
        return Err("publication directory must not be a symlink".into());
    }
    Ok(())
}

fn selected_evidence(
    root: &Path,
    manifest: &Value,
    policy: &[String],
) -> Result<Vec<records::SelectedAttempt>> {
    let workload: records::ArtifactIdentity =
        serde_json::from_value(manifest["artifacts"]["preimage_profile"].clone())?;
    let snapshot_id = manifest["snapshot"]["id"]
        .as_str()
        .ok_or("measurement snapshot identity missing")?;
    let acceptance = match manifest["schema_version"].as_u64().unwrap_or(1) {
        1 => records::AcceptancePolicy::LegacyV1,
        2 => records::AcceptancePolicy::NewRun,
        _ => return Err("unsupported measurement schema".into()),
    };
    let mut selected = Vec::new();
    for kind in [
        records::AttemptKind::Smoke,
        records::AttemptKind::Primary,
        records::AttemptKind::Repeat,
    ] {
        let attempts =
            records::selected_attempts(root, kind, snapshot_id, &workload, policy, acceptance)?;
        records::require_matrix(
            &attempts,
            &if kind == records::AttemptKind::Primary {
                records::all_cases()
            } else {
                records::endpoints()
            },
        )?;
        selected.extend(attempts.into_values());
    }
    Ok(selected)
}

fn prepare_source(
    snapshot: &snapshot::Snapshot,
    staging: &Path,
    inputs: &mut BTreeMap<PathBuf, String>,
) -> Result<Option<PathBuf>> {
    if !snapshot.root.is_dir() {
        return Ok(None);
    }
    let destination = staging.join("source/verified-inputs");
    fs::create_dir(&destination)?;
    for input in &snapshot.inventory {
        if input.kind != "file" || input.path.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        safe_relative(&input.path)?;
        let from = snapshot.root.join(&input.path);
        if Some(sha256(&from)?) != input.sha256 {
            return Err("measured source differs from frozen inventory".into());
        }
        copy_input(&from, &destination.join(&input.path), inputs)?;
    }
    Ok(Some(destination))
}

fn verify_frozen_policy(
    root: &Path,
    measured: &snapshot::Snapshot,
    expected: &[String],
    inputs: &mut BTreeMap<PathBuf, String>,
) -> Result<()> {
    use sha2::Digest;
    let relative = Path::new("tools/performance/measurement-env.json");
    let identity = measured
        .inventory
        .iter()
        .find(|entry| entry.path == relative && entry.kind == "file")
        .ok_or("frozen environment policy is not inventoried")?;
    let path = measured.root.join(relative);
    let bytes = if path.is_file() {
        remember(inputs, &path)?;
        fs::read(&path)?
    } else {
        let archive = root.join("source/frozen.tar");
        let record = root.join("source/frozen-archive.json");
        remember(inputs, &record)?;
        remember(inputs, &archive)?;
        let metadata = json(&record)?;
        if metadata["snapshot_id"] != measured.id || metadata["sha256"] != sha256(&archive)? {
            return Err("measurement source archive identity differs".into());
        }
        let output = crate::command("tar")
            .arg("-xOf")
            .arg(&archive)
            .arg("./tools/performance/measurement-env.json")
            .output()?;
        if !output.status.success() {
            return Err("cannot read frozen environment policy from archive".into());
        }
        output.stdout
    };
    if identity.sha256.as_deref() != Some(format!("{:x}", sha2::Sha256::digest(&bytes)).as_str())
        || serde_json::from_slice::<Vec<String>>(&bytes)? != expected
    {
        return Err("manifest environment policy differs from its measured frozen source".into());
    }
    Ok(())
}

fn validate_power(record: &Value, policy: crate::host::PowerPolicy) -> Result<()> {
    for key in ["power_before", "power_after"] {
        let observation: crate::host::PowerObservation =
            serde_json::from_value(record[key].clone())?;
        if !observation.observed_unix_seconds.is_finite() || observation.observed_unix_seconds < 0.0
        {
            return Err("invalid power observation timestamp".into());
        }
        if observation.error.is_none()
            && crate::host::PowerObservation::parse(&observation.raw).source != observation.source
        {
            return Err("power observation differs from its raw evidence".into());
        }
        policy.validate(&observation)?;
    }
    Ok(())
}

fn legacy_episodes(
    root: &Path,
    staging: &Path,
    inputs: &mut BTreeMap<PathBuf, String>,
) -> Result<BTreeMap<String, String>> {
    let mut episodes = BTreeMap::new();
    if !root.join("resume.json").is_file() {
        return Ok(episodes);
    }
    remember(inputs, &root.join("resume.json"))?;
    let resume = json(&root.join("resume.json"))?;
    if let Some(path) = resume["controller_manifest"].as_str() {
        safe_relative(Path::new(path))?;
        let path = root.join(path);
        if path.is_file() {
            remember(inputs, &path)?;
            let controller = json(&path)?;
            copy_input(
                &path,
                &staging.join("legacy-controller-manifest.json"),
                inputs,
            )?;
            if let Some(preserved) = controller["preserved_evidence"].as_object() {
                for (name, artifact) in preserved {
                    let relative = Path::new(name);
                    if !relative.starts_with("cases")
                        || relative
                            .file_name()
                            .is_none_or(|name| name != "attempt.json")
                    {
                        continue;
                    }
                    safe_relative(relative)?;
                    let current = root.join(relative);
                    let original = current
                        .parent()
                        .ok_or("attempt parent missing")?
                        .join("original/attempt.json");
                    let expected = artifact["sha256"]
                        .as_str()
                        .ok_or("preserved attempt hash missing")?;
                    let source = if current.is_file() && sha256(&current)? == expected {
                        current
                    } else if original.is_file() && sha256(&original)? == expected {
                        original
                    } else {
                        return Err("preserved legacy attempt identity differs".into());
                    };
                    remember(inputs, &source)?;
                    let record = json(&source)?;
                    if record["status"] == "validated" {
                        episodes.insert(
                            record["attempt_id"]
                                .as_str()
                                .ok_or("preserved attempt id missing")?
                                .to_owned(),
                            "legacy-original".into(),
                        );
                    }
                }
            }
        }
    }
    if let Some(repeats) = resume["new_repeats"].as_array() {
        for repeat in repeats {
            let case = repeat["case"]
                .as_str()
                .ok_or("resumed repeat case missing")?;
            let attempt = repeat["attempt"]
                .as_str()
                .ok_or("resumed repeat attempt missing")?;
            safe_relative(Path::new(case))?;
            safe_relative(Path::new(attempt))?;
            let path = root
                .join("cases")
                .join(case)
                .join(attempt)
                .join("attempt.json");
            remember(inputs, &path)?;
            let record = json(&path)?;
            let id = format!("{case}-{attempt}");
            if record["attempt_id"] != id
                || record["kind"] != "repeat"
                || record["status"] != "validated"
                || episodes.contains_key(&id)
            {
                return Err("conflicting resumed attempt identity".into());
            }
            episodes.insert(id, "legacy-resumed".into());
        }
    }
    atomic_json(&staging.join("legacy-episode-membership.json"), &episodes)?;
    Ok(episodes)
}

fn prepare_baselines(
    root: &Path,
    staging: &Path,
    power_policy: Option<crate::host::PowerPolicy>,
    inputs: &mut BTreeMap<PathBuf, String>,
) -> Result<String> {
    if !root.join("episodes").is_dir() {
        if power_policy.is_some() {
            return Err("new measurements require recorded episode controls".into());
        }
        for name in [
            "baseline-before.csv",
            "baseline-after.csv",
            "baseline-symbols.csv",
            "baseline-resume-before.csv",
        ] {
            if root.join(name).is_file() {
                copy_input(&root.join(name), &staging.join(name), inputs)?;
            }
        }
        return Ok("**Legacy measurement episodes.** Episode membership is recovered from recorded preservation and resumed-attempt identities when available; other memberships remain unknown. Before/after observations do not establish uninterrupted conditions across a recorded pause, and a later control cannot retrospectively close an earlier episode. Historical acceptance is retained; it is not upgraded to the new require-AC policy.\n\n".into());
    }
    // An unchanged v1 measurement manifest may have been continued by a new
    // controller. Keep original controls distinct from the new episode's CSVs.
    let mut legacy_controls = Vec::new();
    for name in [
        "baseline-before.csv",
        "baseline-after.csv",
        "baseline-symbols.csv",
        "baseline-resume-before.csv",
    ] {
        if root.join(name).is_file() {
            copy_input(
                &root.join(name),
                &staging.join("legacy-controls").join(name),
                inputs,
            )?;
            legacy_controls.push(name);
            if name == "baseline-resume-before.csv" {
                copy_input(&root.join(name), &staging.join(name), inputs)?;
            }
        }
    }
    let effective_power_policy = power_policy.unwrap_or(crate::host::PowerPolicy::ObserveOnly);
    let mut episodes = Vec::new();
    for entry in fs::read_dir(root.join("episodes"))? {
        let entry = entry?;
        if !entry.file_type()?.is_dir() {
            continue;
        }
        let from = entry.path().join("episode.json");
        let data = json(&from)?;
        if data["schema_version"] != 2
            || !data["started_unix_seconds"]
                .as_f64()
                .is_some_and(f64::is_finite)
            || data["id"].as_str() != entry.file_name().to_str()
        {
            return Err("invalid episode identity or start time".into());
        }
        let relative = from.strip_prefix(root)?;
        copy_input(&from, &staging.join(relative), inputs)?;
        for key in ["before_baseline", "symbols_baseline", "after_baseline"] {
            if let Some(path) = data[key].as_str() {
                safe_relative(Path::new(path))?;
                copy_input(&root.join(path), &staging.join(path), inputs)?;
                let stage_path = Path::new(path).with_extension("stage.json");
                let stage = json(&root.join(&stage_path))?;
                if stage["status"] != "accepted" || stage["episode_id"] != data["id"] {
                    return Err("baseline stage is not accepted for its episode".into());
                }
                let csv: records::ArtifactIdentity = serde_json::from_value(stage["csv"].clone())?;
                if csv.path.canonicalize()? != root.join(path).canonicalize()? {
                    return Err("baseline CSV role differs from its accepted stage".into());
                }
                csv.verify()?;
                validate_power(&stage, effective_power_policy)?;
                copy_input(&root.join(&stage_path), &staging.join(&stage_path), inputs)?;
            }
        }
        episodes.push(data);
    }
    episodes.sort_by(|a, b| {
        a["started_unix_seconds"]
            .as_f64()
            .unwrap()
            .total_cmp(&b["started_unix_seconds"].as_f64().unwrap())
    });
    let first = episodes
        .iter()
        .find(|e| e["before_baseline"].is_string())
        .ok_or("no episode before baseline")?;
    let symbols = episodes
        .iter()
        .find(|e| e["symbols_baseline"].is_string())
        .ok_or("no symbol baseline")?;
    let last = episodes
        .iter()
        .rev()
        .find(|e| e["status"] == "complete" && e["after_baseline"].is_string())
        .ok_or("no completed episode after baseline")?;
    for (episode, key, output) in [
        (first, "before_baseline", "baseline-before.csv"),
        (symbols, "symbols_baseline", "baseline-symbols.csv"),
        (last, "after_baseline", "baseline-after.csv"),
    ] {
        copy_input(
            &root.join(episode[key].as_str().unwrap()),
            &staging.join(output),
            inputs,
        )?;
    }
    let mut text = format!(
        "**Recorded measurement episodes.** Displayed before control: `{}`; symbol control: `{}`; after control: `{}`. Only controls belonging to the same completed episode can bracket its captures. Interrupted episodes remain unclosed.\n\n",
        first["id"].as_str().unwrap_or("unknown"),
        symbols["id"].as_str().unwrap_or("unknown"),
        last["id"].as_str().unwrap_or("unknown")
    );
    if !legacy_controls.is_empty() {
        text.push_str("\nOriginal controls are preserved separately: ");
        for name in legacy_controls {
            text.push_str(&format!("[{name}](legacy-controls/{name}) "));
        }
        text.push_str(". New episode controls do not close the earlier legacy capture interval. Legacy captures retain their historical acceptance policy.\n\n");
    }
    text.push_str("| Episode | Recorded status |\n| --- | --- |\n");
    for episode in episodes {
        text.push_str(&format!(
            "| `{}` | {} |\n",
            episode["id"].as_str().unwrap_or("unknown"),
            episode["status"].as_str().unwrap_or("unknown")
        ));
    }
    text.push('\n');
    Ok(text)
}

fn power_caveats(captures: &[report::Capture]) -> String {
    let mut counts = BTreeMap::from([("AC", 0), ("battery", 0), ("unknown", 0)]);
    for capture in captures {
        for side in ["before", "after"] {
            let typed = &capture.attempt[format!("power_{side}")];
            let raw = &capture.attempt[format!("load_{side}")]["power"];
            let observation = if !typed.is_null() {
                serde_json::from_value::<crate::host::PowerObservation>(typed.clone()).ok()
            } else if raw["success"] == true {
                Some(crate::host::PowerObservation::parse(
                    raw["stdout"].as_str().unwrap_or(""),
                ))
            } else {
                None
            };
            let state = match observation.filter(|p| p.error.is_none()).map(|p| p.source) {
                Some(crate::host::PowerSource::Ac) => "AC",
                Some(crate::host::PowerSource::Battery) => "battery",
                _ => "unknown",
            };
            *counts.get_mut(state).unwrap() += 1;
        }
    }
    format!(
        "**Power observations.** Selected capture boundaries contain {} AC, {} battery and {} unknown observations. Battery and AC captures can have different power conditions; these profiles do not establish constant clocks or continuous AC between observations. Missing thermal warnings do not prove stable frequency. Hotspot shares are usable sampled backtrace rows, not wall-clock percentages.\n\n",
        counts["AC"], counts["battery"], counts["unknown"]
    )
}

fn relative_path(from: &Path, target: &Path) -> Result<String> {
    let from = canonical_output(from)?;
    let target = canonical_output(target)?;
    let a = from.components().collect::<Vec<_>>();
    let b = target.components().collect::<Vec<_>>();
    let common = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let mut result = PathBuf::new();
    for _ in common..a.len() {
        result.push("..");
    }
    for component in &b[common..] {
        result.push(component.as_os_str());
    }
    Ok(result
        .to_str()
        .ok_or("link path is not Unicode")?
        .replace('%', "%25")
        .replace(' ', "%20"))
}

fn local_target(link: &str) -> Option<&str> {
    if link.is_empty()
        || link.starts_with('#')
        || link.contains("://")
        || link.starts_with("mailto:")
    {
        return None;
    }
    Some(link.split('#').next().unwrap().split('?').next().unwrap())
}

fn relocate_markdown(text: &str, source: &Path, destination: &Path) -> Result<String> {
    let mut result = String::new();
    let mut tail = text;
    while let Some(start) = tail.find("](") {
        result.push_str(&tail[..start + 2]);
        tail = &tail[start + 2..];
        let end = tail.find(')').ok_or("unterminated findings link")?;
        let link = &tail[..end];
        if let Some(local) = local_target(link) {
            let target = source.join(local.replace("%20", " ").replace("%25", "%"));
            if !target.exists() {
                return Err(
                    format!("authored findings link is missing: {}", target.display()).into(),
                );
            }
            result.push_str(&relative_path(destination, &target)?);
            if let Some((_, anchor)) = link.split_once('#') {
                result.push('#');
                result.push_str(anchor);
            }
        } else {
            result.push_str(link);
        }
        result.push(')');
        tail = &tail[end + 1..];
    }
    result.push_str(tail);
    Ok(result)
}

fn check_links(root: &Path) -> Result<()> {
    fn visit(root: &Path, path: &Path) -> Result<()> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() {
                visit(root, &entry.path())?;
                continue;
            }
            let p = entry.path();
            // Copied source and exact authored bytes are inputs, not rendered documents.
            if p.starts_with(root.join("source"))
                || p.file_name().is_some_and(|s| s == "findings-source.md")
            {
                continue;
            }
            if !matches!(p.extension().and_then(|s| s.to_str()), Some("md" | "html")) {
                continue;
            }
            let text = fs::read_to_string(&p)?;
            for (start, end) in [(" ](", ')'), ("](", ')'), ("href=\"", '"'), ("src=\"", '"')] {
                for suffix in text.split(start).skip(1) {
                    let link = suffix
                        .split(end)
                        .next()
                        .ok_or("unterminated document link")?;
                    if let Some(local) = local_target(link) {
                        let target = p
                            .parent()
                            .unwrap()
                            .join(local.replace("%20", " ").replace("%25", "%"));
                        if !target.exists() {
                            return Err(
                                format!("missing local link in {}: {link}", p.display()).into()
                            );
                        }
                    }
                }
            }
        }
        Ok(())
    }
    visit(root, root)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Temp(PathBuf);
    impl Temp {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "flock publication {} {}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Temp {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn draft(base: &Path, id: &str) -> Result<(PathBuf, PathBuf, Generation)> {
        let output = base.join("publication");
        let staging = output.join("generations").join(format!(".staging-{id}"));
        fs::create_dir_all(&staging)?;
        fs::write(
            staging.join("report.md"),
            format!("{id}: reviewed content\n"),
        )?;
        fs::write(
            staging.join("index.html"),
            format!("<a href=\"report.md\">{id}</a>"),
        )?;
        let identity = records::ArtifactIdentity {
            path: base.join("processor"),
            sha256: "unused-test-identity".into(),
        };
        let processor = snapshot::ProcessorIdentity {
            snapshot: snapshot::Snapshot {
                root: base.join("frozen"),
                id: "test-source".into(),
                editing_root: base.join("edit"),
                base_revision: "test-revision".into(),
                inventory: Vec::new(),
                external_config: Vec::new(),
                build_environment: BTreeMap::new(),
            },
            source_archive: identity.clone(),
            executable: identity,
        };
        let generation = Generation {
            schema_version: 2,
            id: id.into(),
            state: "rendered".into(),
            inventory_sha256: String::new(),
            evidence_root: base.join("evidence"),
            input_sha256: BTreeMap::new(),
            processor,
            authored_findings: None,
        };
        Ok((staging, output, generation))
    }

    #[test]
    fn checksum_chain_is_acyclic_and_published_payload_is_verified() -> Result<()> {
        let base = Temp::new();
        let (staging, output, generation) = draft(&base.0, "one")?;
        let gallery = finish(&staging, &output, generation, |_| Ok(()))?;
        assert_eq!(current(&output)?, gallery);
        let inventory = json(&gallery.parent().unwrap().join("artifacts.json"))?;
        assert!(inventory["files"].get("generation.json").is_none());
        assert!(inventory["files"].get("artifacts.json").is_none());
        fs::write(gallery.parent().unwrap().join("report.md"), "modified")?;
        assert!(current(&output).is_err());
        // Even a self-consistent checksum chain cannot weaken the fixed payload
        // coverage policy by excluding a modified report from the inventory.
        let directory = gallery.parent().unwrap();
        let inventory = evidence::inventory(
            directory,
            &["artifacts.json", "generation.json", "report.md"],
        )?;
        atomic_json(&directory.join("artifacts.json"), &inventory)?;
        let mut generation: Generation =
            serde_json::from_slice(&fs::read(directory.join("generation.json"))?)?;
        generation.inventory_sha256 = sha256(&directory.join("artifacts.json"))?;
        atomic_json(&directory.join("generation.json"), &generation)?;
        atomic_json(
            &output.join("current.json"),
            &Pointer {
                schema_version: 2,
                generation: generation.id,
                manifest_sha256: sha256(&directory.join("generation.json"))?,
            },
        )?;
        assert!(
            verify_generation(directory)
                .unwrap_err()
                .to_string()
                .contains("exclusions")
        );
        assert!(current(&output).is_err());
        Ok(())
    }

    #[test]
    fn process_exit_at_publication_boundaries_exposes_only_complete_generations() -> Result<()> {
        for boundary in [Boundary::Ready, Boundary::Renamed, Boundary::Published] {
            let base = Temp::new();
            let (staging, output, old) = draft(&base.0, "old")?;
            finish(&staging, &output, old, |_| Ok(()))?;
            let (_, _, next) = draft(&base.0, "new")?;
            atomic_json(&base.0.join("next.json"), &next)?;
            let status = std::process::Command::new(std::env::current_exe()?)
                .args([
                    "--exact",
                    "publication::tests::crash_child",
                    "--ignored",
                    "--nocapture",
                ])
                .env("FLOCK_PUBLICATION_TEST_ROOT", &base.0)
                .env("FLOCK_PUBLICATION_TEST_BOUNDARY", format!("{boundary:?}"))
                .output()?
                .status;
            assert_eq!(status.code(), Some(77), "child must stop without unwinding");
            let gallery = current(&output)?;
            let expected = if boundary == Boundary::Published {
                "new"
            } else {
                "old"
            };
            assert!(gallery.ends_with(format!("{expected}/index.html")));
            if boundary == Boundary::Renamed {
                assert_eq!(
                    verify_generation(&output.join("generations/new"))?.state,
                    "ready"
                );
            }
        }
        Ok(())
    }

    #[test]
    #[ignore = "subprocess fixture invoked by publication boundary test"]
    fn crash_child() -> Result<()> {
        let base = PathBuf::from(
            std::env::var_os("FLOCK_PUBLICATION_TEST_ROOT").ok_or("child root missing")?,
        );
        let stop = std::env::var("FLOCK_PUBLICATION_TEST_BOUNDARY")?;
        let generation = serde_json::from_slice(&fs::read(base.join("next.json"))?)?;
        let output = base.join("publication");
        finish(
            &output.join("generations/.staging-new"),
            &output,
            generation,
            |point| {
                if format!("{point:?}") == stop {
                    std::process::exit(77);
                }
                Ok(())
            },
        )?;
        Err("child did not reach expected boundary".into())
    }

    #[test]
    fn authored_bytes_and_links_remain_valid_after_directory_rename() -> Result<()> {
        let base = Temp::new();
        let evidence = base.0.join("original evidence");
        fs::create_dir(&evidence)?;
        fs::write(evidence.join("data.json"), "{}")?;
        let authored = "Human findings: [supporting observation](data.json#measurement)\n";
        fs::write(evidence.join("findings.md"), authored)?;
        let (staging, output, generation) = draft(&base.0, "review")?;
        fs::write(staging.join("findings-source.md"), authored)?;
        fs::write(
            staging.join("findings.md"),
            relocate_markdown(authored, &evidence, &staging)?,
        )?;
        let gallery = finish(&staging, &output, generation, |_| Ok(()))?;
        assert_eq!(fs::read_to_string(evidence.join("findings.md"))?, authored);
        assert_eq!(
            fs::read_to_string(gallery.parent().unwrap().join("findings-source.md"))?,
            authored
        );
        check_links(gallery.parent().unwrap())?;
        Ok(())
    }

    #[test]
    fn changed_inputs_and_broken_links_cannot_replace_current() -> Result<()> {
        let base = Temp::new();
        let (staging, output, old) = draft(&base.0, "old")?;
        finish(&staging, &output, old, |_| Ok(()))?;
        let original_pointer = fs::read(output.join("current.json"))?;
        let input = base.0.join("input.json");
        fs::write(&input, "before")?;
        let (staging, _, mut next) = draft(&base.0, "changed")?;
        remember(&mut next.input_sha256, &input)?;
        fs::write(&input, "after")?;
        assert!(finish(&staging, &output, next, |_| Ok(())).is_err());
        let (staging, _, next) = draft(&base.0, "broken-link")?;
        fs::write(staging.join("report.md"), "[missing](absent.json)")?;
        assert!(finish(&staging, &output, next, |_| Ok(())).is_err());
        assert_eq!(fs::read(output.join("current.json"))?, original_pointer);
        assert!(recover_ready(&output, "../outside").is_err());
        Ok(())
    }

    #[test]
    fn episode_controls_follow_timestamps_and_enforce_recorded_power() -> Result<()> {
        let base = Temp::new();
        let root = base.0.join("evidence");
        let staging = base.0.join("staging");
        fs::create_dir_all(&staging)?;
        let ac = crate::host::PowerObservation::parse(
            "Now drawing from 'AC Power'\n -InternalBattery 50%; charging",
        );
        for (id, start, status, value) in [
            ("episode-z", 10.0, "interrupted", "first"),
            ("episode-a", 20.0, "complete", "last"),
        ] {
            let directory = root.join("episodes").join(id);
            fs::create_dir_all(&directory)?;
            let mut episode =
                json!({"schema_version":2,"id":id,"started_unix_seconds":start,"status":status});
            for (key, label) in [
                ("before_baseline", "baseline-before"),
                ("symbols_baseline", "baseline-symbols"),
                ("after_baseline", "baseline-after"),
            ] {
                if status == "interrupted" && key == "after_baseline" {
                    continue;
                }
                fs::write(directory.join(format!("{label}.csv")), value)?;
                atomic_json(
                    &directory.join(format!("{label}.stage.json")),
                    &json!({"schema_version":2,"episode_id":id,"status":"accepted","power_before":ac,"power_after":ac,"csv":records::ArtifactIdentity::register(&directory.join(format!("{label}.csv")))?}),
                )?;
                episode[key] = json!(format!("episodes/{id}/{label}.csv"));
            }
            atomic_json(&directory.join("episode.json"), &episode)?;
        }
        let mut inputs = BTreeMap::new();
        let description = prepare_baselines(
            &root,
            &staging,
            Some(crate::host::PowerPolicy::RequireAc),
            &mut inputs,
        )?;
        assert!(description.contains("before control: `episode-z`"));
        assert!(description.contains("after control: `episode-a`"));
        assert_eq!(
            fs::read_to_string(staging.join("baseline-before.csv"))?,
            "first"
        );
        assert_eq!(
            fs::read_to_string(staging.join("baseline-after.csv"))?,
            "last"
        );
        let path = root.join("episodes/episode-a/baseline-after.stage.json");
        let mut stage = json(&path)?;
        stage["power_after"] = serde_json::to_value(crate::host::PowerObservation::parse(
            "Now drawing from 'Battery Power'",
        ))?;
        atomic_json(&path, &stage)?;
        let retry = base.0.join("retry");
        fs::create_dir(&retry)?;
        assert!(
            prepare_baselines(
                &root,
                &retry,
                Some(crate::host::PowerPolicy::RequireAc),
                &mut BTreeMap::new()
            )
            .is_err()
        );
        assert!(validate_power(&stage, crate::host::PowerPolicy::ObserveOnly).is_ok());
        stage["power_after"]["source"] = json!("ac");
        assert!(validate_power(&stage, crate::host::PowerPolicy::RequireAc).is_err());
        Ok(())
    }
}

//! Correct an upstream folded-stack delimiter collision using original XML.
//!
//! The measurement source and raw evidence are untouched. All original derived
//! artifacts are retained before any replacements. Compilation finishes before
//! timing begins; offline processing starts only after the final baseline.

use crate::{Result, atomic_json, command, report, sha256};
use quick_xml::Reader;
use quick_xml::events::{BytesStart, Event};
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

const DERIVED: &[&str] = &[
    "stacks.folded",
    "flamegraph.svg",
    "preview.png",
    "analysis.json",
    "stats.json",
    "attempt.json",
];
const PROTECTED: &[&str] = &[
    "raw/time-profile.xml",
    "harness.json",
    "record-status.json",
    "export-status.json",
];
const PROCESSING_SOURCES: &[(&str, &str)] = &[
    ("tools/performance/src/repair.rs", include_str!("repair.rs")),
    ("tools/performance/src/report.rs", include_str!("report.rs")),
    ("tools/performance/src/lib.rs", include_str!("lib.rs")),
    (
        "tools/performance/src/snapshot.rs",
        include_str!("snapshot.rs"),
    ),
    (
        "tools/performance/src/bin/repair_preimage_report.rs",
        include_str!("bin/repair_preimage_report.rs"),
    ),
    (
        "tools/performance/src/bin/profile_preimages.rs",
        include_str!("bin/profile_preimages.rs"),
    ),
    (
        "tools/performance/measurement-env.json",
        include_str!("../measurement-env.json"),
    ),
    (
        "tools/performance/Cargo.toml",
        include_str!("../Cargo.toml"),
    ),
    ("Cargo.toml", include_str!("../../../Cargo.toml")),
    ("Cargo.lock", include_str!("../../../Cargo.lock")),
    (
        "rust-toolchain.toml",
        include_str!("../../../rust-toolchain.toml"),
    ),
    (
        ".cargo/config.toml",
        include_str!("../../../.cargo/config.toml"),
    ),
];

#[derive(Debug, Serialize)]
struct Symbol {
    frame_id: String,
    raw_name: String,
    demangled_name: String,
    display_name: String,
    address: Option<String>,
}

#[derive(Debug, Serialize)]
struct CollapseSummary {
    xml_rows: u64,
    usable_rows: u64,
    unique_backtraces: usize,
    unique_frames: usize,
    transformed_frames: usize,
    samples_with_transformed_frames: u64,
    spurious_separator_occurrences_removed: u64,
    maximum_real_stack_depth: usize,
}

struct Collapsed {
    stacks: BTreeMap<String, u64>,
    symbols: BTreeMap<String, Symbol>,
    summary: CollapseSummary,
}

fn attrs(element: &BytesStart<'_>) -> Result<BTreeMap<String, String>> {
    element
        .attributes()
        .map(|attribute| {
            let attribute = attribute?;
            Ok((
                std::str::from_utf8(attribute.key.as_ref())?.to_owned(),
                quick_xml::escape::unescape(std::str::from_utf8(&attribute.value)?)?.into_owned(),
            ))
        })
        .collect()
}

fn symbol(id: String, raw_name: String, address: Option<String>) -> Result<Symbol> {
    let demangled_name = rustc_demangle::try_demangle(&raw_name)
        .map(|name| format!("{name:#}"))
        .unwrap_or_else(|_| raw_name.clone());
    let display_name = demangled_name.replace(';', "；").replace(['\r', '\n'], " ");
    if display_name.trim().is_empty() {
        return Err("empty symbol cannot be represented in folded stacks".into());
    }
    Ok(Symbol {
        frame_id: id,
        raw_name,
        demangled_name,
        display_name,
        address,
    })
}

fn collapse(input: impl BufRead) -> Result<Collapsed> {
    let mut reader = Reader::from_reader(input);
    let mut buffer = Vec::new();
    let mut symbols = BTreeMap::<String, Symbol>::new();
    let mut backtraces = BTreeMap::<String, Vec<String>>::new();
    let mut occurrences = BTreeMap::<String, u64>::new();
    let mut display_sources = BTreeMap::<String, String>::new();
    let mut row: Option<Option<String>> = None;
    let mut active_backtrace: Option<(String, Vec<String>)> = None;
    let mut rows = 0_u64;
    let mut depth = 0_u64;
    let mut root_seen = false;
    loop {
        let event = reader.read_event_into(&mut buffer)?;
        let empty = matches!(event, Event::Empty(_));
        match event {
            Event::Start(element) | Event::Empty(element) => {
                let name = element.name();
                let name = name.as_ref();
                if depth == 0 {
                    if root_seen || name != b"trace-query-result" || empty {
                        return Err("XML requires one nonempty trace-query-result root".into());
                    }
                    root_seen = true;
                }
                match name {
                    b"row" => {
                        if row.is_some() || empty {
                            return Err("nested or empty sample row".into());
                        }
                        row = Some(None);
                        rows = rows.checked_add(1).ok_or("XML row count overflow")?;
                    }
                    b"backtrace" if row.is_some() => {
                        if active_backtrace.is_some() || row.as_ref().unwrap().is_some() {
                            return Err("multiple backtraces in sample row".into());
                        }
                        let attrs = attrs(&element)?;
                        if let Some(id) = attrs.get("ref") {
                            if !empty || !backtraces.contains_key(id) {
                                return Err("invalid backtrace reference".into());
                            }
                            row = Some(Some(id.clone()));
                        } else {
                            let id = attrs.get("id").ok_or("backtrace lacks id or ref")?.clone();
                            if backtraces.contains_key(&id) {
                                return Err("duplicate backtrace id".into());
                            }
                            if empty {
                                backtraces.insert(id.clone(), Vec::new());
                                row = Some(Some(id));
                            } else {
                                active_backtrace = Some((id, Vec::new()));
                            }
                        }
                    }
                    b"frame" if active_backtrace.is_some() => {
                        let attrs = attrs(&element)?;
                        let id = if let Some(id) = attrs.get("ref") {
                            if !empty || !symbols.contains_key(id) {
                                return Err("invalid frame reference".into());
                            }
                            id.clone()
                        } else {
                            let id = attrs.get("id").ok_or("frame lacks id or ref")?.clone();
                            if symbols.contains_key(&id) {
                                return Err("duplicate frame id".into());
                            }
                            let raw = attrs.get("name").ok_or("frame has no name")?.clone();
                            let frame = symbol(id.clone(), raw, attrs.get("addr").cloned())?;
                            if let Some(previous) = display_sources.get(&frame.display_name) {
                                if previous != &frame.demangled_name {
                                    return Err(
                                        "display normalization would merge distinct symbols".into(),
                                    );
                                }
                            } else {
                                display_sources.insert(
                                    frame.display_name.clone(),
                                    frame.demangled_name.clone(),
                                );
                            }
                            symbols.insert(id.clone(), frame);
                            id
                        };
                        active_backtrace.as_mut().unwrap().1.push(id);
                    }
                    _ => {}
                }
                if !empty {
                    depth += 1;
                }
            }
            Event::End(element) => {
                match element.name().as_ref() {
                    b"backtrace" => {
                        let (id, frames) =
                            active_backtrace.take().ok_or("backtrace was not opened")?;
                        backtraces.insert(id.clone(), frames);
                        row = Some(Some(id));
                    }
                    b"row" => {
                        if let Some(id) = row.take().ok_or("row was not opened")? {
                            let count = occurrences.entry(id).or_default();
                            *count = count.checked_add(1).ok_or("backtrace count overflow")?;
                        }
                    }
                    _ => {}
                }
                depth = depth.checked_sub(1).ok_or("unmatched XML end tag")?;
            }
            Event::Eof => break,
            Event::Text(text) if depth == 0 && !text.iter().all(u8::is_ascii_whitespace) => {
                return Err("text outside XML root".into());
            }
            _ => {}
        }
        buffer.clear();
    }
    if !root_seen || depth != 0 || row.is_some() || active_backtrace.is_some() {
        return Err("truncated XML".into());
    }
    let mut summary = CollapseSummary {
        xml_rows: rows,
        usable_rows: 0,
        unique_backtraces: backtraces.len(),
        unique_frames: symbols.len(),
        transformed_frames: symbols
            .values()
            .filter(|s| s.demangled_name != s.display_name)
            .count(),
        samples_with_transformed_frames: 0,
        spurious_separator_occurrences_removed: 0,
        maximum_real_stack_depth: 0,
    };
    let mut stacks = BTreeMap::<String, u64>::new();
    for (id, count) in occurrences {
        let frames = backtraces.get(&id).ok_or("unresolved backtrace id")?;
        if frames.is_empty() {
            continue;
        }
        let resolved = frames
            .iter()
            .rev()
            .map(|id| symbols.get(id).ok_or_else(|| "unresolved frame id".into()))
            .collect::<Result<Vec<_>>>()?;
        let stack = resolved
            .iter()
            .map(|s| s.display_name.as_str())
            .collect::<Vec<_>>()
            .join(";");
        if stack.split(';').count() != frames.len() {
            return Err("a display symbol retained a folded delimiter".into());
        }
        if resolved.iter().any(|s| s.demangled_name != s.display_name) {
            summary.samples_with_transformed_frames += count;
        }
        let separators = resolved
            .iter()
            .map(|s| s.demangled_name.matches(';').count() as u64)
            .sum::<u64>();
        summary.spurious_separator_occurrences_removed += separators
            .checked_mul(count)
            .ok_or("separator count overflow")?;
        summary.maximum_real_stack_depth = summary.maximum_real_stack_depth.max(frames.len());
        summary.usable_rows = summary
            .usable_rows
            .checked_add(count)
            .ok_or("usable row count overflow")?;
        let total = stacks.entry(stack).or_default();
        *total = total.checked_add(count).ok_or("folded count overflow")?;
    }
    if summary.usable_rows == 0 {
        return Err("XML contains no usable backtraces".into());
    }
    Ok(Collapsed {
        stacks,
        symbols,
        summary,
    })
}

/// Parse and reconstruct a retained XML file without writing any artifacts.
pub fn validate_xml(path: &Path) -> Result<Value> {
    let parsed = collapse(BufReader::new(File::open(path)?))?;
    Ok(serde_json::to_value(&parsed.summary)?)
}

fn exclusive_file(path: &Path) -> Result<File> {
    Ok(OpenOptions::new().create_new(true).write(true).open(path)?)
}

fn copy_verified(from: &Path, to: &Path) -> Result<String> {
    if to.exists() {
        return Err(format!("refusing to overwrite preserved file {}", to.display()).into());
    }
    let before = sha256(from)?;
    fs::copy(from, to)?;
    if sha256(from)? != before || sha256(to)? != before {
        return Err("original changed while preserving report evidence".into());
    }
    Ok(before)
}

fn checksums(dir: &Path, names: &[&str]) -> Result<BTreeMap<String, String>> {
    names
        .iter()
        .filter(|name| dir.join(name).is_file())
        .map(|name| Ok(((*name).to_owned(), sha256(&dir.join(name))?)))
        .collect()
}

fn completed_attempts(root: &Path) -> Result<Vec<PathBuf>> {
    let mut attempts = Vec::new();
    let mut kinds = BTreeMap::<String, usize>::new();
    for case in fs::read_dir(root.join("cases"))? {
        let case = case?;
        if !case.file_type()?.is_dir() {
            continue;
        }
        for entry in fs::read_dir(case.path())? {
            let entry = entry?;
            let path = entry.path();
            if !entry.file_type()?.is_dir() || !path.join("attempt.json").is_file() {
                continue;
            }
            let value: Value = serde_json::from_slice(&fs::read(path.join("attempt.json"))?)?;
            if value["status"] != "validated" {
                continue;
            }
            let kind = value["kind"].as_str().ok_or("attempt kind missing")?;
            if !matches!(kind, "smoke" | "primary" | "repeat") {
                return Err("unexpected completed attempt kind".into());
            }
            *kinds.entry(kind.to_owned()).or_default() += 1;
            for required in [
                "stacks.folded",
                "flamegraph.svg",
                "preview.png",
                "analysis.json",
            ] {
                if !path.join(required).is_file() {
                    return Err(format!("completed attempt lacks {required}").into());
                }
            }
            for required in PROTECTED {
                if !path.join(required).is_file() {
                    return Err(format!("completed attempt lacks {required}").into());
                }
            }
            if path.join("original").exists()
                || path.join("repair.json").exists()
                || path.join("repair-work").exists()
            {
                return Err(format!(
                    "refusing to repeat or overwrite a prior repair: {}",
                    path.display()
                )
                .into());
            }
            attempts.push(path);
        }
    }
    if kinds.get("smoke") != Some(&8)
        || kinds.get("repeat") != Some(&8)
        || kinds.get("primary").copied().unwrap_or(0) < 28
    {
        return Err(format!("completed smoke/primary/repeat matrix is missing: {kinds:?}").into());
    }
    attempts.sort();
    Ok(attempts)
}

fn registered_tool(manifest: &Value, category: &str, name: &str) -> Result<PathBuf> {
    let entry = &manifest[category][name];
    let path = PathBuf::from(
        entry["path"]
            .as_str()
            .ok_or("registered tool path missing")?,
    );
    if sha256(&path)?
        != entry["sha256"]
            .as_str()
            .ok_or("registered tool hash missing")?
    {
        return Err(format!("registered {name} tool changed").into());
    }
    Ok(path)
}

fn refresh_inventory(root: &Path) -> Result<()> {
    fn walk(root: &Path, relative: &Path, files: &mut BTreeMap<PathBuf, Value>) -> Result<()> {
        for entry in fs::read_dir(root.join(relative))? {
            let entry = entry?;
            if relative.as_os_str().is_empty()
                && matches!(
                    entry.file_name().to_str(),
                    Some("artifacts.json" | "complete.json")
                )
            {
                continue;
            }
            let path = relative.join(entry.file_name());
            let metadata = fs::symlink_metadata(entry.path())?;
            if metadata.is_dir() {
                walk(root, &path, files)?;
            } else if metadata.is_file() {
                files.insert(
                    path.clone(),
                    json!({"bytes":metadata.len(), "sha256":sha256(&root.join(path))?}),
                );
            } else {
                return Err(format!("unsupported report artifact {}", path.display()).into());
            }
        }
        Ok(())
    }
    let mut files = BTreeMap::new();
    walk(root, Path::new(""), &mut files)?;
    atomic_json(
        &root.join("artifacts.json"),
        &json!({"schema_version":1,"exclusions":["artifacts.json","complete.json"],"files":files}),
    )
}

fn repair_attempt(
    dir: &Path,
    renderer: &Path,
    tool_hash: &str,
    expected_inputs: &BTreeMap<String, String>,
) -> Result<Value> {
    let original: Value = serde_json::from_slice(&fs::read(dir.join("original/attempt.json"))?)?;
    let protected = checksums(dir, PROTECTED)?;
    if &protected != expected_inputs || protected.len() != PROTECTED.len() {
        return Err("raw inputs changed since report-processing preflight".into());
    }
    let before = checksums(&dir.join("original"), DERIVED)?;
    let mut record = json!({
        "schema_version": 1, "status": "in_progress", "attempt_id": original["attempt_id"],
        "processing_tool_sha256": tool_hash, "input_sha256": protected, "before_sha256": before,
        "originals": "original/", "raw_recording_unchanged": true,
        "display_transformation": "In each demangled frame replace ASCII semicolon with fullwidth ；, and CR/LF with spaces; only then join frames with ASCII semicolon."
    });
    atomic_json(&dir.join("repair.json"), &record)?;
    let result = (|| -> Result<()> {
        let corrected = collapse(BufReader::new(File::open(
            dir.join("raw/time-profile.xml"),
        )?))?;
        if original["stats"]["usable_rows"].as_u64() != Some(corrected.summary.usable_rows) {
            return Err("repair changed the accepted usable sample count".into());
        }
        let work = dir.join("repair-work");
        fs::create_dir(&work)?;
        let mut folded = BufWriter::new(exclusive_file(&work.join("stacks.folded"))?);
        for (stack, count) in &corrected.stacks {
            writeln!(folded, "{stack} {count}")?;
        }
        folded.flush()?;
        folded.get_ref().sync_all()?;
        drop(folded);
        atomic_json(&work.join("symbol-names.json"), &corrected.symbols)?;
        let mut options = inferno::flamegraph::Options::default();
        options.deterministic = true;
        options.title = format!(
            "{} {} / {} hashes ({})",
            original["protocol"].as_str().ok_or("protocol missing")?,
            original["operation"].as_str().ok_or("operation missing")?,
            original["hashes"].as_u64().ok_or("hash count missing")?,
            original["kind"].as_str().ok_or("capture kind missing")?
        );
        let mut svg = BufWriter::new(exclusive_file(&work.join("flamegraph.svg"))?);
        inferno::flamegraph::from_reader(
            &mut options,
            File::open(work.join("stacks.folded"))?,
            &mut svg,
        )?;
        svg.flush()?;
        svg.get_ref().sync_all()?;
        drop(svg);
        let render = command(renderer)
            .args(["--width", "1200", "--output"])
            .arg(work.join("preview.png"))
            .arg(work.join("flamegraph.svg"))
            .output()?;
        fs::write(work.join("render.stderr"), &render.stderr)?;
        if !render.status.success() || fs::metadata(work.join("preview.png"))?.len() == 0 {
            return Err("corrected SVG preview rendering failed".into());
        }
        if checksums(dir, PROTECTED)? != protected {
            return Err("raw inputs changed during offline report processing".into());
        }
        for name in [
            "stacks.folded",
            "flamegraph.svg",
            "preview.png",
            "symbol-names.json",
        ] {
            fs::rename(work.join(name), dir.join(name))?;
        }
        let stats = report::analyze_capture(dir)?;
        if stats.usable_rows != corrected.summary.usable_rows
            || stats.total_weight != corrected.summary.usable_rows
        {
            return Err("corrected analysis changed sample denominator".into());
        }
        let mut attempt = original.clone();
        attempt["stats"] = serde_json::to_value(&stats)?;
        attempt["report_processing"] = json!({"repaired":true,"record":"repair.json","originals":"original/","processing_tool_sha256":tool_hash});
        atomic_json(&dir.join("attempt.json"), &attempt)?;
        record["collapse"] = serde_json::to_value(&corrected.summary)?;
        record["after_sha256"] = serde_json::to_value(checksums(
            dir,
            &[
                "stacks.folded",
                "flamegraph.svg",
                "preview.png",
                "analysis.json",
                "attempt.json",
                "symbol-names.json",
            ],
        )?)?;
        record["input_sha256_after"] = serde_json::to_value(checksums(dir, PROTECTED)?)?;
        record["status"] = json!("complete");
        Ok(())
    })();
    if let Err(error) = &result {
        record["status"] = json!("partial_failure");
        record["error"] = json!(error.to_string());
    }
    atomic_json(&dir.join("repair.json"), &record)?;
    result?;
    Ok(record)
}

/// Rebuild derived artifacts from recorded XML after every measurement finishes.
/// Refuse repeated or partial previous repairs to preserve original evidence.
pub fn repair_report(root: &Path) -> Result<()> {
    let root = root.canonicalize()?;
    if !(root.join("complete.json").is_file() || root.join("measurements-complete.json").is_file())
        || !root.join("baseline-after.csv").is_file()
    {
        return Err("offline repair requires the completed run and final baseline".into());
    }
    if root.join("report-processing.json").exists()
        || root.join("report-original").exists()
        || root.join("report-processing-source").exists()
    {
        return Err("refusing to overwrite previous report processing or original evidence".into());
    }
    let manifest: Value = serde_json::from_slice(&fs::read(root.join("manifest.json"))?)?;
    let attempts = completed_attempts(&root)?;
    let renderer = registered_tool(&manifest, "tools", "svg-renderer")?;
    // Prove that every real XML document can be reconstructed before creating
    // backup directories or changing any output. Unsupported input remains a
    // completely read-only failure that can be fixed and retried safely.
    let mut input_identities = BTreeMap::new();
    let mut preflight = Vec::new();
    for (index, dir) in attempts.iter().enumerate() {
        eprintln!(
            "Validating raw XML {}/{}: {}",
            index + 1,
            attempts.len(),
            dir.strip_prefix(&root)?.display()
        );
        let inputs = checksums(dir, PROTECTED)?;
        if inputs.len() != PROTECTED.len() {
            return Err("raw input missing during report-processing preflight".into());
        }
        let original: Value = serde_json::from_slice(&fs::read(dir.join("attempt.json"))?)?;
        let parsed = collapse(BufReader::new(File::open(
            dir.join("raw/time-profile.xml"),
        )?))?;
        if original["stats"]["usable_rows"].as_u64() != Some(parsed.summary.usable_rows)
            || original["stats"]["xml_rows"].as_u64() != Some(parsed.summary.xml_rows)
            || checksums(dir, PROTECTED)? != inputs
        {
            return Err("raw XML preflight differs from accepted evidence or sample counts".into());
        }
        preflight.push(json!({"attempt":dir.strip_prefix(&root)?,"input_sha256":inputs,"collapse":parsed.summary}));
        input_identities.insert(dir.clone(), inputs);
    }
    let tool = std::env::current_exe()?.canonicalize()?;
    let tool_hash = sha256(&tool)?;
    let mut processing = json!({
        "schema_version":1, "status":"in_progress", "original_snapshot_id":manifest["snapshot"]["id"],
        "tool":{"path":tool,"sha256":tool_hash},
        "dependencies":{"rustc-demangle":"0.1.27","inferno":"0.12.6","quick-xml":"0.39.4"},
        "transformation":"Original XML frame boundaries and row occurrences are authoritative. Rust names are demangled, in-frame ASCII ; becomes fullwidth ；, CR/LF becomes space, and frames are joined root-to-leaf by ASCII ;. Exact raw/demangled/display names and addresses are retained per frame. No sample weighting, time slicing, or recapture is applied.",
        "measurements_unchanged":true, "expected_attempts":attempts.len(), "raw_xml_preflight":preflight,
        "source_archive":"report-processing-source/", "source_archive_kind":"compile-time embedded processing sources",
        "original_aggregate_reports":"report-original/", "started_unix_seconds":SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs_f64()
    });
    atomic_json(&root.join("report-processing.json"), &processing)?;
    let result = (|| -> Result<()> {
        let source = root.join("report-processing-source");
        fs::create_dir(&source)?;
        let mut source_hashes = BTreeMap::new();
        for (name, contents) in PROCESSING_SOURCES {
            let path = source.join(name);
            fs::create_dir_all(path.parent().ok_or("processing source has no parent")?)?;
            let mut file = exclusive_file(&path)?;
            file.write_all(contents.as_bytes())?;
            file.sync_all()?;
            source_hashes.insert(*name, sha256(&path)?);
        }
        processing["source_sha256"] = serde_json::to_value(source_hashes)?;
        let aggregate = root.join("report-original");
        fs::create_dir(&aggregate)?;
        let mut original_hashes = BTreeMap::new();
        for name in [
            "report.md",
            "index.html",
            "hotspots.csv",
            "reference.csv",
            "artifacts.json",
            "complete.json",
        ] {
            if root.join(name).is_file() {
                original_hashes.insert(
                    name.to_owned(),
                    copy_verified(&root.join(name), &aggregate.join(name))?,
                );
            }
        }
        fs::create_dir(aggregate.join("svg"))?;
        for entry in fs::read_dir(root.join("svg"))? {
            let entry = entry?;
            if !entry.file_type()?.is_file() {
                return Err("unexpected non-file in primary SVG directory".into());
            }
            let name = format!(
                "svg/{}",
                entry
                    .file_name()
                    .to_str()
                    .ok_or("SVG filename is not Unicode")?
            );
            original_hashes.insert(
                name.clone(),
                copy_verified(&entry.path(), &aggregate.join(name))?,
            );
        }
        processing["original_aggregate_sha256"] = serde_json::to_value(original_hashes)?;
        // Preserve every attempt's original derived files before changing any.
        for dir in &attempts {
            let original = dir.join("original");
            fs::create_dir(&original)?;
            for name in DERIVED {
                if dir.join(name).is_file() {
                    copy_verified(&dir.join(name), &original.join(name))?;
                }
            }
        }
        processing["originals_preserved"] = json!(true);
        atomic_json(&root.join("report-processing.json"), &processing)?;
        let mut repaired = Vec::new();
        for (index, dir) in attempts.iter().enumerate() {
            eprintln!(
                "Repairing {}/{}: {}",
                index + 1,
                attempts.len(),
                dir.strip_prefix(&root)?.display()
            );
            let record = repair_attempt(dir, &renderer, &tool_hash, &input_identities[dir])?;
            repaired
                .push(json!({"attempt":dir.strip_prefix(&root)?,"collapse":record["collapse"]}));
        }
        for dir in &attempts {
            let attempt: Value = serde_json::from_slice(&fs::read(dir.join("attempt.json"))?)?;
            if attempt["kind"] == "primary" && attempt["promoted"] == true {
                let case = dir
                    .parent()
                    .and_then(Path::file_name)
                    .ok_or("case name missing")?;
                let mut name = case.to_os_string();
                name.push(".svg");
                fs::copy(dir.join("flamegraph.svg"), root.join("svg").join(name))?;
            }
        }
        processing["attempts"] = json!(repaired);
        processing["status"] = json!("derived_outputs_complete");
        atomic_json(&root.join("report-processing.json"), &processing)?;
        report::write_report(&root)?;
        if sha256(&tool)? != tool_hash {
            return Err("processing executable changed during repair".into());
        }
        registered_tool(&manifest, "tools", "svg-renderer")?;
        processing["status"] = json!("complete");
        processing["completed_unix_seconds"] =
            json!(SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs_f64());
        processing["artifact_inventory"] = json!(
            "Regenerated by this processing tool after corrected artifacts and report are complete."
        );
        atomic_json(&root.join("report-processing.json"), &processing)?;
        refresh_inventory(&root)?;
        Ok(())
    })();
    if let Err(error) = &result {
        processing["status"] = json!("partial_failure");
        processing["error"] = json!(error.to_string());
        atomic_json(&root.join("report-processing.json"), &processing)?;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn arrays_and_frame_references_preserve_real_depth_leaves_and_counts() -> Result<()> {
        let xml = r#"<trace-query-result><node>
          <row><weight>999</weight><backtrace id="10">
            <frame id="1" name="flock_core::consume&lt;[u8; 64]&gt;" addr="0x1"/>
            <frame id="2" name="_ZN4test4main17h0123456789abcdefE" addr="0x2"/>
          </backtrace></row>
          <row><backtrace ref="10"/></row>
          <row><backtrace id="11"><frame ref="1"/><frame ref="2"/></backtrace></row>
          <row><sentinel/></row><row><backtrace id="12"/></row>
        </node></trace-query-result>"#;
        let corrected = collapse(Cursor::new(xml))?;
        assert_eq!(corrected.summary.xml_rows, 5);
        assert_eq!(corrected.summary.usable_rows, 3);
        assert_eq!(corrected.summary.maximum_real_stack_depth, 2);
        assert_eq!(corrected.summary.samples_with_transformed_frames, 3);
        assert_eq!(corrected.summary.spurious_separator_occurrences_removed, 3);
        let frame = &corrected.symbols["1"];
        assert_eq!(frame.raw_name, "flock_core::consume<[u8; 64]>");
        assert_eq!(frame.display_name, "flock_core::consume<[u8； 64]>");
        assert_eq!(
            corrected.stacks["test::main;flock_core::consume<[u8； 64]>"],
            3
        );
        let (stack, count) = corrected.stacks.first_key_value().unwrap();
        let frames = stack.split(';').collect::<Vec<_>>();
        assert_eq!(frames, ["test::main", "flock_core::consume<[u8； 64]>"]);
        assert_eq!(*count, 3);
        let broken = "test::main;flock_core::consume<[u8; 64]>";
        assert_eq!(broken.split(';').next_back(), Some(" 64]>"));
        assert!(!frames.iter().any(|name| name.starts_with(" 64]")));
        let mut options = inferno::flamegraph::Options::default();
        options.deterministic = true;
        let mut svg = Vec::new();
        inferno::flamegraph::from_reader(
            &mut options,
            Cursor::new(format!("{stack} {count}\n")),
            &mut svg,
        )?;
        let svg = String::from_utf8(svg)?;
        assert!(svg.contains("flock_core::consume&lt;[u8； 64]&gt; (3 samples"));
        assert!(!svg.contains("<title> 64]"));
        Ok(())
    }

    #[test]
    fn normalization_keeps_exact_names_and_removes_embedded_line_breaks() -> Result<()> {
        let frame = symbol("1".into(), "array<[u8; 64]>\r\nleaf".into(), None)?;
        assert_eq!(frame.raw_name, "array<[u8; 64]>\r\nleaf");
        assert_eq!(frame.display_name, "array<[u8； 64]>  leaf");
        assert!(!frame.display_name.contains([';', '\r', '\n']));
        Ok(())
    }

    #[test]
    fn invalid_references_and_truncated_xml_cannot_yield_repaired_stacks() {
        for xml in [
            "<trace-query-result><row><backtrace ref=\"missing\"/></row></trace-query-result>",
            "<trace-query-result><row><backtrace id=\"1\"><frame ref=\"missing\"/></backtrace></row></trace-query-result>",
            "<trace-query-result><row><backtrace id=\"1\"><frame id=\"2\" name=\"leaf\"/>",
        ] {
            assert!(collapse(Cursor::new(xml)).is_err());
        }
    }

    #[test]
    fn normalization_collision_is_rejected_instead_of_merging_symbols() {
        let xml = "<trace-query-result><row><backtrace id=\"1\"><frame id=\"2\" name=\"a;b\"/><frame id=\"3\" name=\"a；b\"/></backtrace></row></trace-query-result>";
        assert!(collapse(Cursor::new(xml)).is_err());
    }
}

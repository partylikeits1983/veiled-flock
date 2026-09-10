//! Validation and reporting for captured benchmark evidence.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};

use quick_xml::Reader;
use quick_xml::events::{BytesStart, Event};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{Result, atomic_json, sha256};

const SIZES: [usize; 7] = [64, 128, 256, 512, 1024, 2048, 4096];
const CSV_HEADER: &str = "hashes,protocol,prove_ms_median,verify_ms_median,proof_bytes_median,proof_bytes_min,proof_bytes_max";
const REFERENCE: &str = "hashes,flock_prove_ms,flock_verify_ms,flock_bytes,full_zk_prove_ms,full_zk_verify_ms,full_zk_bytes,size_overhead_percent\n64,4.944,13.123,274609,19.350,11.454,801705,191.9\n128,5.140,13.544,283537,18.987,11.338,801865,182.8\n256,6.447,13.467,377697,19.485,11.534,802185,112.4\n512,7.961,14.042,385081,24.723,12.499,811281,110.7\n1024,10.381,14.460,398657,32.597,11.974,847489,112.6\n2048,15.925,15.033,433425,49.119,13.442,863857,99.3\n4096,23.917,16.476,451937,81.780,15.662,885585,96.0\n";

#[derive(Debug, Serialize, Deserialize)]
pub struct Baseline {
    pub hashes: usize,
    pub protocol: String,
    pub prove_ms_median: f64,
    pub verify_ms_median: f64,
    pub proof_bytes_median: u64,
    pub proof_bytes_min: u64,
    pub proof_bytes_max: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CaptureStats {
    pub usable_rows: u64,
    pub total_weight: u64,
    pub has_workload_symbols: bool,
    pub has_verifier_worker: bool,
    pub has_rayon_worker: bool,
    pub xml_rows: u64,
    pub missing_or_empty_backtrace_rows: u64,
    pub unknown_frame_rows: u64,
    pub unknown_leaf_rows: u64,
    pub marked_truncated_rows: u64,
    pub inclusive: Vec<Hotspot>,
    pub self_samples: Vec<Hotspot>,
    pub self_categories: Vec<Hotspot>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Hotspot {
    pub symbol: String,
    pub samples: u64,
    pub percent: f64,
}

pub fn read_baseline(path: &Path) -> Result<Vec<Baseline>> {
    parse_baseline(&fs::read_to_string(path)?)
}

fn parse_baseline(text: &str) -> Result<Vec<Baseline>> {
    let mut lines = text.lines();
    if lines.next() != Some(CSV_HEADER) {
        return Err("baseline CSV header does not match preimage_scaling".into());
    }
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    for line in lines {
        let fields: Vec<_> = line.split(',').collect();
        if fields.len() != 7 {
            return Err("baseline CSV row must have seven columns".into());
        }
        let row = Baseline {
            hashes: fields[0].parse()?,
            protocol: fields[1].to_owned(),
            prove_ms_median: fields[2].parse()?,
            verify_ms_median: fields[3].parse()?,
            proof_bytes_median: fields[4].parse()?,
            proof_bytes_min: fields[5].parse()?,
            proof_bytes_max: fields[6].parse()?,
        };
        if !SIZES.contains(&row.hashes)
            || !matches!(
                row.protocol.as_str(),
                "FLOCK-non-ZK-Secure" | "VEIL-FLOCK-full-ZK"
            )
            || !row.prove_ms_median.is_finite()
            || row.prove_ms_median <= 0.0
            || !row.verify_ms_median.is_finite()
            || row.verify_ms_median <= 0.0
            || row.proof_bytes_min == 0
            || row.proof_bytes_min > row.proof_bytes_median
            || row.proof_bytes_median > row.proof_bytes_max
            || !seen.insert((row.hashes, row.protocol.clone()))
        {
            return Err(format!("invalid or duplicate baseline CSV row: {line}").into());
        }
        result.push(row);
    }
    if result.len() != 14 {
        return Err("baseline must contain exactly both protocols at all seven sizes".into());
    }
    Ok(result)
}

#[derive(Default)]
struct XmlStats {
    rows: u64,
    usable_rows: u64,
    verifier_thread: bool,
}

fn attributes(element: &BytesStart<'_>) -> Result<BTreeMap<String, String>> {
    element
        .attributes()
        .map(|attr| {
            let attr = attr?;
            Ok((
                std::str::from_utf8(attr.key.as_ref())?.to_owned(),
                quick_xml::escape::unescape(std::str::from_utf8(&attr.value)?)?.into_owned(),
            ))
        })
        .collect()
}

fn analyze_xml(path: &Path) -> Result<XmlStats> {
    let mut reader = Reader::from_reader(BufReader::new(File::open(path)?));
    let mut buffer = Vec::new();
    let mut stats = XmlStats::default();
    let mut depth = 0_u64;
    let mut root_seen = false;
    let mut row: Option<Option<String>> = None;
    let mut active_backtrace: Option<(String, usize)> = None;
    let mut backtraces: BTreeMap<String, usize> = BTreeMap::new();
    let mut frames = BTreeSet::new();
    loop {
        let event = reader.read_event_into(&mut buffer)?;
        let empty = matches!(event, Event::Empty(_));
        match event {
            Event::Start(element) | Event::Empty(element) => {
                let name = element.name();
                let name = name.as_ref();
                let attrs = attributes(&element)?;
                if depth == 0 {
                    if root_seen || name != b"trace-query-result" || empty {
                        return Err(
                            "xctrace XML requires one nonempty trace-query-result root".into()
                        );
                    }
                    root_seen = true;
                }
                if attrs.values().any(|text| text.contains("flock-verify")) {
                    stats.verifier_thread = true;
                }
                match name {
                    b"row" => {
                        if row.is_some() || empty {
                            return Err("nested or empty sample row".into());
                        }
                        row = Some(None);
                        stats.rows += 1;
                    }
                    b"backtrace" if row.is_some() => {
                        if active_backtrace.is_some() || row.as_ref().unwrap().is_some() {
                            return Err("multiple backtraces in one sample row".into());
                        }
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
                                backtraces.insert(id.clone(), 0);
                                row = Some(Some(id));
                            } else {
                                active_backtrace = Some((id, 0));
                            }
                        }
                    }
                    b"frame" if active_backtrace.is_some() => {
                        if let Some(id) = attrs.get("ref") {
                            if !frames.contains(id) {
                                return Err("invalid frame reference".into());
                            }
                        } else {
                            let id = attrs.get("id").ok_or("frame lacks id or ref")?;
                            if !attrs.contains_key("name") || !frames.insert(id.clone()) {
                                return Err("frame is unnamed or duplicated".into());
                            }
                        }
                        active_backtrace.as_mut().unwrap().1 += 1;
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
                        if let Some((id, count)) = active_backtrace.take() {
                            backtraces.insert(id.clone(), count);
                            row = Some(Some(id));
                        }
                    }
                    b"row" => {
                        if let Some(id) = row.take().ok_or("sample row was not opened")?
                            && backtraces.get(&id).copied().unwrap_or(0) > 0
                        {
                            stats.usable_rows += 1;
                        }
                    }
                    _ => {}
                }
                depth = depth.checked_sub(1).ok_or("unmatched XML closing tag")?;
            }
            Event::Eof => break,
            Event::Text(text) if depth == 0 && !text.iter().all(u8::is_ascii_whitespace) => {
                return Err("text outside XML document root".into());
            }
            _ => {}
        }
        buffer.clear();
    }
    if !root_seen || depth != 0 || row.is_some() || active_backtrace.is_some() {
        return Err("truncated xctrace XML".into());
    }
    Ok(stats)
}

fn validate_svg(path: &Path) -> Result<()> {
    let mut reader = Reader::from_reader(BufReader::new(File::open(path)?));
    let mut buffer = Vec::new();
    let mut depth = 0_u64;
    let mut root_seen = false;
    let mut rectangles = 0;
    loop {
        let event = reader.read_event_into(&mut buffer)?;
        let empty = matches!(event, Event::Empty(_));
        match event {
            Event::Start(element) | Event::Empty(element) => {
                if depth == 0 {
                    if root_seen || element.name().as_ref() != b"svg" || empty {
                        return Err("flamegraph must have one nonempty SVG root".into());
                    }
                    root_seen = true;
                }
                attributes(&element)?;
                if element.name().as_ref() == b"rect" {
                    rectangles += 1;
                }
                if !empty {
                    depth += 1;
                }
            }
            Event::End(_) => depth = depth.checked_sub(1).ok_or("unmatched SVG closing tag")?,
            Event::Eof => break,
            _ => {}
        }
        buffer.clear();
    }
    if !root_seen || depth != 0 || rectangles < 2 {
        return Err("SVG is incomplete or has no flamegraph rectangles".into());
    }
    Ok(())
}

fn category(symbol: &str) -> &'static str {
    let lower = symbol.to_ascii_lowercase();
    if ["malloc", "free", "alloc::", "dealloc", "memcpy", "memmove"]
        .iter()
        .any(|s| lower.contains(s))
    {
        "allocation and copying"
    } else if [
        "rayon_core",
        "pthread",
        "semaphore",
        "__psynch",
        "sched",
        "thread::park",
        "swtch",
        "thread_yield",
    ]
    .iter()
    .any(|s| lower.contains(s))
    {
        "scheduling and synchronization"
    } else if [
        "challenger",
        "sha256",
        "sha2::",
        "blake3::",
        "zkrng",
        "random",
        "getentropy",
    ]
    .iter()
    .any(|s| lower.contains(s))
    {
        "transcript, hashing, and randomness"
    } else if [
        "field::",
        "field128",
        "f128::",
        "::fft",
        "::ntt",
        "butterfly",
        "binius_field",
        // These polynomial NEON intrinsics implement carryless multiplication;
        // do not classify unrelated integer/floating-point vmul intrinsics here.
        "vmull_p64",
        "vmull_high_p64",
        "vmull_p8",
        "vmull_high_p8",
        "vmul_p8",
        "vmulq_p8",
    ]
    .iter()
    .any(|s| lower.contains(s))
    {
        "field arithmetic and transforms"
    } else if ["sumcheck", "zerocheck", "lincheck"]
        .iter()
        .any(|s| lower.contains(s))
    {
        "sumchecks and constraint checks"
    } else if ["::pcs::", "::merkle", "ligerito"]
        .iter()
        .any(|s| lower.contains(s))
    {
        "PCS and Merkle work"
    } else if lower.contains("veil") || lower.contains("hadamard") {
        "VEIL protocol work"
    } else {
        "other or unresolved"
    }
}

fn ranked(values: BTreeMap<String, u64>, total: u64) -> Vec<Hotspot> {
    let mut result: Vec<_> = values
        .into_iter()
        .map(|(symbol, samples)| Hotspot {
            symbol,
            samples,
            percent: samples as f64 / total.max(1) as f64 * 100.0,
        })
        .collect();
    result.sort_by(|a, b| b.samples.cmp(&a.samples).then(a.symbol.cmp(&b.symbol)));
    result
}

fn unknown(symbol: &str) -> bool {
    let symbol = symbol.trim();
    symbol.starts_with("0x") || symbol == "???" || symbol.to_ascii_lowercase().contains("unknown")
}

pub fn analyze_capture(dir: &Path) -> Result<CaptureStats> {
    let xml = analyze_xml(&dir.join("raw/time-profile.xml"))?;
    validate_svg(&dir.join("flamegraph.svg"))?;
    let mut total = 0_u64;
    let mut inclusive = BTreeMap::new();
    let mut leaves = BTreeMap::new();
    let mut categories = BTreeMap::new();
    let mut unknown_rows = 0;
    let mut unknown_leaves = 0;
    let mut truncated = 0;
    let mut has_workload = false;
    let mut has_verifier = xml.verifier_thread;
    let mut has_rayon = false;
    for line in BufReader::new(File::open(dir.join("stacks.folded"))?).lines() {
        let line = line?;
        if line.is_empty() {
            continue;
        }
        let (stack, count) = line.rsplit_once(' ').ok_or("invalid folded-stack count")?;
        let count: u64 = count.parse()?;
        if stack.is_empty() || count == 0 {
            continue;
        }
        let frames: Vec<_> = stack.split(';').collect();
        if frames.iter().any(|f| f.is_empty()) {
            return Err("empty frame inside folded stack".into());
        }
        total = total
            .checked_add(count)
            .ok_or("folded sample count overflow")?;
        let unique: BTreeSet<_> = frames.iter().copied().collect();
        for frame in unique {
            *inclusive.entry(frame.to_owned()).or_insert(0_u64) += count;
        }
        let leaf = frames.last().unwrap();
        *leaves.entry((*leaf).to_owned()).or_insert(0_u64) += count;
        *categories.entry(category(leaf).to_owned()).or_insert(0_u64) += count;
        if frames.iter().any(|f| unknown(f)) {
            unknown_rows += count;
        }
        if unknown(leaf) {
            unknown_leaves += count;
        }
        if stack.to_ascii_lowercase().contains("truncated") || stack.contains("[...]") {
            truncated += count;
        }
        has_workload |= stack.contains("flock_core::")
            || stack.contains("flock_prover::")
            || stack.contains("veil_f128::");
        has_verifier |= stack.contains("flock_core::verifier::verify_core_inner")
            || stack.contains("flock_core::verifier::verify_claims_ligerito_inner")
            || stack.contains("flock-verify");
        has_rayon |= stack.contains("rayon_core::") || stack.contains("rayon::");
    }
    if total == 0 || total != xml.usable_rows {
        return Err(format!(
            "folded total {total} does not equal usable xctrace rows {}",
            xml.usable_rows
        )
        .into());
    }
    let stats = CaptureStats {
        usable_rows: xml.usable_rows,
        total_weight: total,
        has_workload_symbols: has_workload,
        has_verifier_worker: has_verifier,
        has_rayon_worker: has_rayon,
        xml_rows: xml.rows,
        missing_or_empty_backtrace_rows: xml.rows - xml.usable_rows,
        unknown_frame_rows: unknown_rows,
        unknown_leaf_rows: unknown_leaves,
        marked_truncated_rows: truncated,
        inclusive: ranked(inclusive, total),
        self_samples: ranked(leaves, total),
        self_categories: ranked(categories, total),
    };
    atomic_json(&dir.join("analysis.json"), &stats)?;
    Ok(stats)
}

struct Capture {
    dir: PathBuf,
    case: String,
    attempt: Value,
    harness: Value,
    stats: CaptureStats,
}

fn captures(root: &Path) -> Result<Vec<Capture>> {
    let mut result = Vec::new();
    for case in fs::read_dir(root.join("cases"))? {
        let case = case?;
        if !case.file_type()?.is_dir() {
            continue;
        }
        for attempt_dir in fs::read_dir(case.path())? {
            let dir = attempt_dir?.path();
            let path = dir.join("attempt.json");
            if !path.is_file() {
                continue;
            }
            let attempt: Value = serde_json::from_slice(&fs::read(path)?)?;
            if attempt["status"] != "validated" {
                continue;
            }
            let harness: Value = serde_json::from_slice(&fs::read(dir.join("harness.json"))?)?;
            if harness["attempt_id"] != attempt["attempt_id"] || harness["final_validation"] != true
            {
                return Err("validated attempt has mismatching or failed harness metadata".into());
            }
            let stats = analyze_capture(&dir)?;
            result.push(Capture {
                dir,
                case: case.file_name().to_string_lossy().into_owned(),
                attempt,
                harness,
                stats,
            });
        }
    }
    result.sort_by(|a, b| a.dir.cmp(&b.dir));
    Ok(result)
}

fn row<'a>(rows: &'a [Baseline], size: usize, protocol: &str) -> &'a Baseline {
    rows.iter()
        .find(|r| r.hashes == size && r.protocol == protocol)
        .expect("validated baseline matrix")
}

fn delta(after: f64, before: f64) -> f64 {
    (after / before - 1.0) * 100.0
}
fn markdown(value: &str) -> String {
    value
        .replace('|', "\\|")
        .replace(['\n', '\r'], " ")
        .replace('`', "'")
}
fn csv(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}
fn html(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}
fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace(' ', "%20")
}
fn text<'a>(value: &'a Value, key: &str) -> &'a str {
    value[key].as_str().unwrap_or("unavailable")
}

fn stripping_warning_logs(root: &Path) -> Result<Vec<PathBuf>> {
    let mut matches = Vec::new();
    for entry in fs::read_dir(root.join("logs"))? {
        let entry = entry?;
        if !entry.file_type()?.is_file() {
            continue;
        }
        let bytes = fs::read(entry.path())?;
        let log = String::from_utf8_lossy(&bytes);
        if log.contains("rust-objcopy") && log.contains("libLLVM.dylib") {
            matches.push(entry.path());
        }
    }
    matches.sort();
    Ok(matches)
}

/// Copy a source module from the recorded snapshot for portable symbol lookup.
/// This is name-based lookup, not a claim of address-to-line symbolication.
fn source_lookup(root: &Path, snapshot: &Path, symbol: &str) -> Result<Option<String>> {
    let packages = [
        ("flock_core::", "flock-core"),
        ("flock_prover::", "flock-prover"),
        ("veil_f128::", "veil-f128"),
    ];
    let Some((prefix, package)) = packages
        .iter()
        .find(|(prefix, _)| symbol.starts_with(prefix))
    else {
        return Ok(None);
    };
    let parts: Vec<_> = symbol[prefix.len()..].split("::").collect();
    let base = PathBuf::from("crates").join(package).join("src");
    let mut matched = None;
    let mut module = base.clone();
    for (index, part) in parts.iter().enumerate() {
        if !part.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            break;
        }
        module.push(part);
        for path in [module.with_extension("rs"), module.join("mod.rs")] {
            if snapshot.join(&path).is_file() {
                matched = Some((path, index + 1));
            }
        }
    }
    let Some((path, offset)) = matched else {
        return Ok(None);
    };
    let contents = fs::read_to_string(snapshot.join(&path))?;
    let mut line = 1;
    for part in parts.iter().skip(offset) {
        let name = part.split('<').next().unwrap_or(part);
        if name.is_empty() {
            continue;
        }
        if let Some(index) = contents.lines().position(|line| {
            line.contains(&format!("fn {name}(")) || line.contains(&format!("fn {name}<"))
        }) {
            line = index + 1;
            break;
        }
    }
    let output = root.join("source/locations").join(&path);
    fs::create_dir_all(output.parent().ok_or("source lookup path has no parent")?)?;
    if !output.exists() {
        fs::write(&output, contents)?;
    }
    Ok(Some(format!(
        "[{}:{line}]({}#L{line})",
        path.display(),
        relative(root, &output)
    )))
}

pub fn write_report(root: &Path) -> Result<()> {
    let manifest: Value = serde_json::from_slice(&fs::read(root.join("manifest.json"))?)?;
    let snapshot = PathBuf::from(
        manifest["snapshot"]["root"]
            .as_str()
            .ok_or("manifest snapshot root missing")?,
    );
    let before = read_baseline(&root.join("baseline-before.csv"))?;
    let after = read_baseline(&root.join("baseline-after.csv"))?;
    let symbols = read_baseline(&root.join("baseline-symbols.csv"))?;
    let resumed = root.join("resume.json").is_file();
    let resume_before = if resumed {
        Some(read_baseline(&root.join("baseline-resume-before.csv"))?)
    } else {
        None
    };
    let all = captures(root)?;
    let primaries: Vec<_> = all
        .iter()
        .filter(|capture| {
            capture.attempt["kind"] == "primary" && capture.attempt["promoted"] == true
        })
        .collect();
    let repeats: Vec<_> = all
        .iter()
        .filter(|capture| capture.attempt["kind"] == "repeat")
        .collect();
    let mut seen = BTreeSet::new();
    for capture in &primaries {
        let expected = format!(
            "{}-{}-{:04}",
            text(&capture.attempt, "protocol"),
            text(&capture.attempt, "operation"),
            capture.attempt["hashes"]
                .as_u64()
                .ok_or("capture hashes missing")?
        );
        if expected != capture.case || capture.stats.usable_rows < 10_000 || !seen.insert(expected)
        {
            return Err("primary capture has invalid identity, insufficient samples, or duplicate promotion".into());
        }
        let svg = root.join("svg").join(format!("{}.svg", capture.case));
        validate_svg(&svg)?;
        if sha256(&svg)? != sha256(&capture.dir.join("flamegraph.svg"))? {
            return Err("promoted SVG does not match its accepted attempt".into());
        }
    }
    for size in SIZES {
        for protocol in ["flock", "full-zk"] {
            for operation in ["prove", "verify"] {
                if !seen.contains(&format!("{protocol}-{operation}-{size:04}")) {
                    return Err("primary SVG matrix is incomplete".into());
                }
            }
        }
    }
    if primaries.len() != 28 || repeats.len() != 8 {
        return Err("report requires 28 primary captures and eight endpoint repeats".into());
    }
    fs::write(root.join("reference.csv"), REFERENCE)?;
    let environment = &manifest["environment"];
    let mut md = String::from("# BLAKE3 preimage flamegraph report\n\n");
    writeln!(
        md,
        "Completed 28 primary captures and eight endpoint repeats. [Open the flamegraph gallery](index.html). Fresh unprofiled timing medians and proof sizes are below; the [historical reference](reference.csv) is a separate series.\n"
    )?;
    if root.join("report-processing.json").is_file() {
        md.push_str("**Report processing correction.** The displayed stacks and SVGs were regenerated from the archived raw XML after capture to correct semicolons embedded in Rust array type names. An embedded semicolon within one frame is displayed as `；` (fullwidth semicolon); ASCII `;` remains the separator between frames. The original XML, original collapsed stacks, and original SVGs are preserved. [Report processing provenance](report-processing.json) records the inputs, preserved originals, and revised reporting tools separately from the measured source snapshot.\n\n");
    }
    if resumed {
        md.push_str("**Two measurement episodes.** All 28 primary captures, the four 64-hash repeats, and the original normal/symbol baselines belong to the first episode. After a pause, the four 4,096-hash repeats were captured in a second episode, bracketed by a new [resume baseline](baseline-resume-before.csv) and the [final baseline](baseline-after.csv). The primary episode has no immediate closing baseline. Original-before versus final-after differences are cross-session changes, not drift measured across an uninterrupted primary series. [Resume provenance](resume.json) records the resumed controller separately and verifies that the registered workload, helper, Cargo, and profiler binaries retain their original identities.\n\n");
    }
    writeln!(
        md,
        "## Environment and measurement\n\nCPU: {}. Memory: {} bytes. Branch: `{}`. Base revision: `{}`. Frozen source identity: `{}`. Toolchain: `{}`. Profiler: {}. [Run manifest](manifest.json) records OS/Xcode versions, build settings, tool paths and checksums, power settings, and load observations.\n",
        markdown(text(&environment["cpu"], "stdout").trim()),
        markdown(text(&environment["memory"], "stdout").trim()),
        markdown(text(&manifest, "branch")),
        text(&manifest, "revision"),
        text(&manifest["snapshot"], "id"),
        text(environment, "toolchain"),
        markdown(text(environment, "profiler").trim())
    )?;
    md.push_str("The reference used an Apple M2 Pro with 16 GiB and revision `9a369670ba5ad3d9a450b859572760b179085666`; machine/revision differences prevent interpreting a timing difference as a code regression. The current series uses release optimization and `target-cpu=native`, with separately prebuilt normal and debug-symbol binaries. Each baseline uses one warm-up and five samples, verifies every proof, and reports medians. Setup, message/digest generation, and serialization are outside its timers; public API checks remain inside. [Exact benchmark source](source/locations/crates/flock-prover/examples/preimage_scaling.rs).\n\n");
    let benchmark = PathBuf::from("crates/flock-prover/examples/preimage_scaling.rs");
    let benchmark_out = root.join("source/locations").join(&benchmark);
    fs::create_dir_all(
        benchmark_out
            .parent()
            .ok_or("benchmark source parent missing")?,
    )?;
    fs::copy(snapshot.join(&benchmark), benchmark_out)?;
    let warning_logs = stripping_warning_logs(root)?;
    if !warning_logs.is_empty() {
        md.push_str("The validation/build logs record a local Rust toolchain warning: `rust-objcopy` aborted because `libLLVM.dylib` could not be loaded. On macOS, Rust invokes this utility for requested debug-info stripping and reports a started utility's unsuccessful exit as a warning; this can leave debug information unstripped. The profiling build explicitly uses `strip=none`, and accepted captures separately require symbolized workload stacks. See the [pinned Rust compiler implementation](https://github.com/rust-lang/rust/blob/88d9e12ae178fab0fb5cc050a94da85685d449ea/compiler/rustc_codegen_ssa/src/back/link.rs#L1168-L1248) and the recorded logs: ");
        for (index, path) in warning_logs.iter().enumerate() {
            if index > 0 {
                md.push_str(", ");
            }
            write!(
                md,
                "[{}]({})",
                markdown(&path.file_name().unwrap_or_default().to_string_lossy()),
                relative(root, path)
            )?;
        }
        md.push_str(".\n\n");
    }
    md.push_str("Captures sample the whole process across all threads. Proving checks warm-up and final outputs, retaining only the latest proof; verification rotates through eight prepared and validated proofs. The shared verifier pool keeps its one-worker policy. Full-ZK verification also performs outer circuit work on the calling thread and dispatches parallel Rayon work outside that pool, so its profile must retain both caller and worker stacks. Preparation, warm-up, challenger construction, proof destruction, final validation, and cleanup remain visible. The harness records phase durations and the absence of all 12 prohibited environment variables before creating pools. No temporal slice was applied.\n\nFlamegraph width and all percentages below use **usable backtrace row occurrences**, matching inferno 0.12.6's xctrace collapse algorithm: one row contributes one count, irrespective of the XML `weight` column. This is sampled CPU activity across threads, not wall-clock latency, and it is not a nanosecond-weighted time sum. Scheduler frames such as `swtch_pri` and `thread_yield` in sampled Running stacks represent observed scheduling activity; their share is not blocked wall-clock time. Inclusive counts deduplicate repeated occurrences of the same symbol within each stack; inclusive symbols overlap and must not be summed. Self counts use the leaf frame and do form a partition. [Collapsed stacks and original XML](cases/) preserve the denominator evidence.\n\n");
    md.push_str("## Fresh timing and size results\n\nValues are from the normal baseline before profiling. Full-ZK/FLOCK ratios compare paired medians. Size overhead is `(full_zk_bytes / flock_bytes - 1) × 100`.\n\n| Hashes | FLOCK prove ms | FLOCK verify ms | FLOCK bytes | Full-ZK prove ms | Full-ZK verify ms | Full-ZK bytes | Prove ratio | Verify ratio | Size overhead |\n| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n");
    for size in SIZES {
        let f = row(&before, size, "FLOCK-non-ZK-Secure");
        let z = row(&before, size, "VEIL-FLOCK-full-ZK");
        writeln!(
            md,
            "| {size} | {:.3} | {:.3} | {} | {:.3} | {:.3} | {} | {:.2}× | {:.2}× | {:.1}% |",
            f.prove_ms_median,
            f.verify_ms_median,
            f.proof_bytes_median,
            z.prove_ms_median,
            z.verify_ms_median,
            z.proof_bytes_median,
            z.prove_ms_median / f.prove_ms_median,
            z.verify_ms_median / f.verify_ms_median,
            delta(z.proof_bytes_median as f64, f.proof_bytes_median as f64)
        )?;
    }
    md.push_str("\nFull-ZK batches of 64 and 128 pad to 256 slots. Non-ZK uses smaller circuits and ad hoc PCS schedules below the registry floor. Serialized proof sizes exclude returned witness commitments, public digests, and bundle framing. CPU profiles do not establish proof size overhead.\n\n");
    if resumed {
        md.push_str("### Cross-session timing changes and debug-symbol comparison\n\nDeltas below are relative to the original normal baseline before primary profiling. The final normal baseline follows the resumed episode; it does not immediately close the primary episode. These before/after values describe cross-session changes and cannot bound within-episode drift for the primary matrix. The symbol baseline belongs to the first episode.\n\n");
    } else {
        md.push_str("### Baseline drift and debug-symbol comparison\n\nDeltas are relative to the normal baseline before profiling. The two normal baselines bracket the capture series; the symbol baseline runs before the series.\n\n");
    }
    md.push_str("These are five-sample medians, without confidence intervals. A large delta warrants checking load/thermal observations and repeating baselines before attributing smaller differences to code.\n\n| Hashes | Protocol | Normal after prove / verify ms | After change prove / verify | Symbols prove / verify ms | Symbol delta prove / verify | Bytes before min–max | Bytes after min–max | Bytes symbols min–max |\n| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n");
    let mut max_drift = 0_f64;
    let mut max_symbol = 0_f64;
    for b in &before {
        let a = row(&after, b.hashes, &b.protocol);
        let s = row(&symbols, b.hashes, &b.protocol);
        let dp = delta(a.prove_ms_median, b.prove_ms_median);
        let dv = delta(a.verify_ms_median, b.verify_ms_median);
        let sp = delta(s.prove_ms_median, b.prove_ms_median);
        let sv = delta(s.verify_ms_median, b.verify_ms_median);
        max_drift = max_drift.max(dp.abs()).max(dv.abs());
        max_symbol = max_symbol.max(sp.abs()).max(sv.abs());
        writeln!(
            md,
            "| {} | {} | {:.3} / {:.3} | {dp:+.1}% / {dv:+.1}% | {:.3} / {:.3} | {sp:+.1}% / {sv:+.1}% | {}–{} | {}–{} | {}–{} |",
            b.hashes,
            b.protocol,
            a.prove_ms_median,
            a.verify_ms_median,
            s.prove_ms_median,
            s.verify_ms_median,
            b.proof_bytes_min,
            b.proof_bytes_max,
            a.proof_bytes_min,
            a.proof_bytes_max,
            s.proof_bytes_min,
            s.proof_bytes_max
        )?;
    }
    let comparison_label = if resumed {
        "cross-session"
    } else {
        "within-series"
    };
    writeln!(
        md,
        "\nLargest absolute {comparison_label} before/after timing change: **{max_drift:.1}%**. Largest absolute symbol-build delta: **{max_symbol:.1}%**. These comparisons combine build effects and measurement variability; they do not isolate a causal debug-symbol effect. Exact data: [before](baseline-before.csv), [after](baseline-after.csv), [symbols](baseline-symbols.csv).\n"
    )?;
    if let Some(resume_before) = &resume_before {
        md.push_str("### Resumed-episode baseline controls\n\nThese normal-binary baselines bracket only the four resumed 4,096-hash repeats. They use the same prebuilt executable as the first episode. All seven sizes were sampled in each control run; they are additional timing observations, not replacement primary captures. Exact timing and proof-size ranges: [resume before](baseline-resume-before.csv), [final after](baseline-after.csv).\n\n| Hashes | Protocol | Resume before prove / verify ms | Final after prove / verify ms | Resumed-interval change prove / verify |\n| ---: | --- | ---: | ---: | ---: |\n");
        let mut max_resumed_change = 0_f64;
        let mut max_reopening_change = 0_f64;
        for b in resume_before {
            let a = row(&after, b.hashes, &b.protocol);
            let original = row(&before, b.hashes, &b.protocol);
            let dp = delta(a.prove_ms_median, b.prove_ms_median);
            let dv = delta(a.verify_ms_median, b.verify_ms_median);
            max_resumed_change = max_resumed_change.max(dp.abs()).max(dv.abs());
            max_reopening_change = max_reopening_change
                .max(delta(b.prove_ms_median, original.prove_ms_median).abs())
                .max(delta(b.verify_ms_median, original.verify_ms_median).abs());
            writeln!(
                md,
                "| {} | {} | {:.3} / {:.3} | {:.3} / {:.3} | {dp:+.1}% / {dv:+.1}% |",
                b.hashes,
                b.protocol,
                b.prove_ms_median,
                b.verify_ms_median,
                a.prove_ms_median,
                a.verify_ms_median
            )?;
        }
        writeln!(
            md,
            "\nLargest absolute timing change across the resumed interval: **{max_resumed_change:.1}%**. Largest absolute change from the original-before baseline to the resume-before baseline: **{max_reopening_change:.1}%**. The latter is a cross-session comparison. These controls cannot recover the missing immediate closing baseline for the first episode.\n"
        )?;
    }
    md.push_str("### Scaling observations\n\n");
    for protocol in ["FLOCK-non-ZK-Secure", "VEIL-FLOCK-full-ZK"] {
        let small = row(&before, 64, protocol);
        let large = row(&before, 4096, protocol);
        writeln!(
            md,
            "- {protocol}: a 64× increase in hashes changes prove latency by {:.2}×, verify latency by {:.2}×, and median proof bytes by {:.2}× in the before baseline.",
            large.prove_ms_median / small.prove_ms_median,
            large.verify_ms_median / small.verify_ms_median,
            large.proof_bytes_median as f64 / small.proof_bytes_median as f64
        )?;
    }
    md.push_str("\n## Flamegraph matrix\n\nOpen an SVG to use its search and zoom controls.\n\n| Hashes | FLOCK prove | FLOCK verify | Full-ZK prove | Full-ZK verify |\n| ---: | --- | --- | --- | --- |\n");
    let mut gallery = String::from(
        "<!doctype html><html lang=\"en\"><meta charset=\"utf-8\"><title>Preimage flamegraph gallery</title><style>body{font:16px system-ui;margin:2rem;background:#fafafa;color:#222}table{border-collapse:collapse;width:100%;table-layout:fixed}th,td{border:1px solid #ccc;padding:.6rem;vertical-align:top}th:first-child{width:4rem}img{width:100%;height:130px;object-fit:contain;background:white}a{color:#164ca0}</style><h1>Preimage flamegraphs</h1><p>28 primary captures. Open an SVG for search and zoom. Width represents sampled backtrace-row share across threads.</p><p><a href=\"report.md\">Full report and methodology</a></p><table><tr><th>Hashes</th><th>FLOCK prove</th><th>FLOCK verify</th><th>Full-ZK prove</th><th>Full-ZK verify</th></tr>",
    );
    for size in SIZES {
        write!(md, "| {size} ")?;
        write!(gallery, "<tr><th>{size}</th>")?;
        for (protocol, operation) in [
            ("flock", "prove"),
            ("flock", "verify"),
            ("full-zk", "prove"),
            ("full-zk", "verify"),
        ] {
            let file = format!("svg/{protocol}-{operation}-{size:04}.svg");
            write!(md, "| [SVG]({file}) ")?;
            write!(
                gallery,
                "<td><a href=\"{file}\"><img src=\"{file}\" alt=\"{}\"><br>Open SVG</a></td>",
                html(&format!("{protocol} {operation}, {size} hashes"))
            )?;
        }
        md.push_str("|\n");
        gallery.push_str("</tr>");
    }
    gallery.push_str("</table></html>\n");
    fs::write(root.join("index.html"), gallery)?;
    md.push_str("\nRepresentative small and large proving cases:\n\n![FLOCK prove, 64 hashes](svg/flock-prove-0064.svg)\n\n![FLOCK prove, 4096 hashes](svg/flock-prove-4096.svg)\n\n![Full-ZK prove, 64 hashes](svg/full-zk-prove-0064.svg)\n\n![Full-ZK prove, 4096 hashes](svg/full-zk-prove-4096.svg)\n\n## Capture quality and phase durations\n\nLoop call rates are profiled throughput and must not replace the unprofiled baseline timings. Phase durations are wall-clock observations; they do not measure phase CPU shares. Missing/unknown/truncated counts refer to XML rows or recognized frame markers, as labeled. Zero marked truncation does not establish complete stacks.\n\n| Case | Usable / all XML rows | Loop seconds / calls | Preparation / validation / cleanup seconds | Rows with unknown frame / unknown leaf | Marked truncated rows | Global / verifier workers |\n| --- | ---: | ---: | ---: | ---: | ---: | ---: |\n");
    for c in &primaries {
        writeln!(
            md,
            "| [{}]({}/attempt.json) | {} / {} | {:.3} / {} | {:.3} / {:.3} / {:.3} | {} / {} | {} | {} / {} |",
            c.case,
            relative(root, &c.dir),
            c.stats.usable_rows,
            c.stats.xml_rows,
            c.harness["loop_seconds"].as_f64().unwrap_or(0.0),
            c.harness["completed_calls"],
            c.harness["preparation_seconds"].as_f64().unwrap_or(0.0),
            c.harness["validation_seconds"].as_f64().unwrap_or(0.0),
            c.harness["cleanup_seconds"].as_f64().unwrap_or(0.0),
            c.stats.unknown_frame_rows,
            c.stats.unknown_leaf_rows,
            c.stats.marked_truncated_rows,
            c.harness["thread_count"],
            c.harness["verifier_thread_count"]
        )?;
    }
    md.push_str("\n## Hotspots\n\nEach case lists its top five inclusive and top five self symbols. Full counts and explicit denominators are in [hotspots.csv](hotspots.csv). Source links are **symbol-name lookups** in copied frozen modules; they are not address-derived line attribution. A module link at line 1 means no function declaration was resolved. External-library symbols remain labeled without a repository source link. Self categories use a single leaf-symbol rule and form disjoint buckets, but inlining and missing symbols can shift attribution. Category names are clues for investigation, not exact API phase boundaries.\n\n");
    let mut hotspots =
        String::from("case,aggregation,symbol,samples,denominator_rows,percent,source_lookup\n");
    let mut category_scores: BTreeMap<String, (f64, String, f64)> = BTreeMap::new();
    for c in &primaries {
        writeln!(
            md,
            "### {}\n\n[SVG](svg/{}.svg) · [attempt evidence]({}/attempt.json)\n\n| Attribution | Symbol | Rows | Share | Source lookup |\n| --- | --- | ---: | ---: | --- |",
            c.case,
            c.case,
            relative(root, &c.dir)
        )?;
        for (kind, list) in [
            ("inclusive", &c.stats.inclusive),
            ("self", &c.stats.self_samples),
        ] {
            for (index, h) in list.iter().enumerate() {
                let source = if index < 5 {
                    source_lookup(root, &snapshot, &h.symbol)?
                        .unwrap_or_else(|| "external or unresolved".into())
                } else {
                    String::new()
                };
                writeln!(
                    hotspots,
                    "{},{},{},{},{},{:.6},{}",
                    c.case,
                    kind,
                    csv(&h.symbol),
                    h.samples,
                    c.stats.total_weight,
                    h.percent,
                    csv(&source)
                )?;
                if index < 5 {
                    writeln!(
                        md,
                        "| {kind} | `{}` | {} | {:.2}% | {source} |",
                        markdown(&h.symbol),
                        h.samples,
                        h.percent
                    )?;
                }
            }
        }
        md.push_str("\nSelf categories: ");
        for (i, h) in c.stats.self_categories.iter().enumerate() {
            if i > 0 {
                md.push_str("; ");
            }
            write!(md, "{} {:.2}%", h.symbol, h.percent)?;
            let entry =
                category_scores
                    .entry(h.symbol.clone())
                    .or_insert((0.0, String::new(), 0.0));
            entry.0 += h.percent / 28.0;
            if h.percent > entry.2 {
                entry.1 = c.case.clone();
                entry.2 = h.percent;
            }
            writeln!(
                hotspots,
                "{},self-category,{},{},{},{:.6},\"\"",
                c.case,
                csv(&h.symbol),
                h.samples,
                c.stats.total_weight,
                h.percent
            )?;
        }
        md.push_str(".\n\n");
    }
    fs::write(root.join("hotspots.csv"), hotspots)?;
    md.push_str("## Endpoint repeat variability\n\nThe repeated endpoints use fresh attempts at full duration. Profiled call-rate delta is repeat relative to primary. Top self-share comparisons use the primary's leading self symbol; changing share does not itself establish a speed change.\n\n");
    if resumed {
        md.push_str("The 64-hash repeats share the first measurement episode with their primaries. The 4,096-hash repeats belong to the resumed second episode, so their primary/repeat differences combine repeat variability with cross-session conditions. Use the resumed-episode baseline controls above when interpreting them.\n\n");
    }
    md.push_str("| Case | Repeat episode | Usable rows primary / repeat | Profiled call-rate delta | Primary top self symbol | Self share primary / repeat |\n| --- | --- | ---: | ---: | --- | ---: |\n");
    let mut repeated = BTreeSet::new();
    for repeat in &repeats {
        if !repeated.insert(repeat.case.clone()) {
            return Err("duplicate endpoint repeat".into());
        }
        let primary = primaries
            .iter()
            .find(|p| p.case == repeat.case)
            .ok_or("repeat has no primary")?;
        let size = repeat.attempt["hashes"]
            .as_u64()
            .ok_or("repeat hashes missing")?;
        if size != 64 && size != 4096 {
            return Err("repeat is not an endpoint".into());
        }
        let episode = if resumed && size == 4096 {
            "second; cross-session comparison"
        } else {
            "same episode as primary"
        };
        let rate = |c: &Capture| {
            c.harness["completed_calls"].as_f64().unwrap_or(0.0)
                / c.harness["loop_seconds"].as_f64().unwrap_or(1.0)
        };
        let top = primary
            .stats
            .self_samples
            .first()
            .ok_or("primary has no self hotspot")?;
        let share = repeat
            .stats
            .self_samples
            .iter()
            .find(|h| h.symbol == top.symbol)
            .map(|h| h.percent)
            .unwrap_or(0.0);
        writeln!(
            md,
            "| [{}]({}/attempt.json) | {episode} | {} / {} | {:+.1}% | `{}` | {:.2}% / {:.2}% |",
            repeat.case,
            relative(root, &repeat.dir),
            primary.stats.usable_rows,
            repeat.stats.usable_rows,
            delta(rate(repeat), rate(primary)),
            markdown(&top.symbol),
            top.percent,
            share
        )?;
    }
    md.push_str("\n## Ranked follow-up experiments\n\nThese are hypotheses ranked by mean per-case self share across the 28 primary captures, giving every workload equal weight. They are not predicted speedups or a combined application CPU budget. Confirm the relevant symbols and repeat stability in the individual case before changing code.\n\n");
    let mut scores: Vec<_> = category_scores
        .into_iter()
        .filter(|(name, _)| name != "other or unresolved")
        .collect();
    scores.sort_by(|a, b| b.1.0.total_cmp(&a.1.0));
    for (index, (name, (mean, case, peak))) in scores.into_iter().take(5).enumerate() {
        let experiment = match name.as_str() {
            "allocation and copying" => {
                "Measure allocation counts and bytes on the leading call paths. If framed Merkle verification is implicated, test two reusable node buffers in verify_merkle_multi_proof_framed (merkle.rs:535), whose current level loop allocates a new vector. Preserve rejection checks, sibling ordering, and exact proof consumption; compare unprofiled medians and endpoint captures."
            }
            "scheduling and synchronization" => {
                "Inspect task granularity in the observed Rayon call paths. FsChallenger::grind_pow (challenger.rs:311) uses ordered parallel search above 8,192 expected hashes; lincheck's parallel threshold is 4,096 elements (lincheck.rs:944). Change one relevant threshold or chunk size at a time while preserving the shared verifier pool and canonical proof output. Compare latency with sampled scheduling activity; the latter is not blocked wall time."
            }
            "transcript, hashing, and randomness" => {
                "Use caller stacks to separate Merkle hashing, transcript hashing, proof-of-work, and entropy acquisition. If proof-of-work dominates, test fixed-block hashing or nonce-batch sizing around sha256_has_leading_zero_bits (challenger.rs:400). Its encoded input is already a 41-byte stack array (ro.rs:189). Preserve difficulty, transcript bytes, the smallest successful nonce, and fresh full-ZK randomness."
            }
            "field arithmetic and transforms" => {
                "Benchmark the leading carryless-arithmetic or transform kernel at the recorded dimensions. The interleaved NTT already fuses layers and uses a 2 MiB subgroup target (ntt/additive_ntt_f128.rs:280); test subgroup size or task granularity before proposing more fusion. Require scalar-equivalent outputs and full protocol tests, then measure endpoint latency."
            }
            "sumchecks and constraint checks" => {
                "Measure the leading packed reduction or fold at representative sizes. Zerocheck already fuses its fold with the first multilinear message (zerocheck.rs:467), and lincheck already fuses two binds with the next evaluation (lincheck.rs:1104). Test chunk sizing or reusable temporary storage while preserving bit-exact round messages and every public API witness and soundness check."
            }
            "PCS and Merkle work" => {
                "Separate NTT encoding and framed Merkle construction beneath finalize_commit (pcs/commit.rs:473) from Ligerito opening verification. For a measured verification bottleneck, test node-buffer reuse or batching independent parent hashes in merkle.rs:535. Preserve PCS parameters, domain framing, query schedules, sibling ordering, and proof verification."
            }
            _ => {
                "Measure circuit construction, temporary storage, and the two proof branches separately. prove_constraints_from_commitment (veil-f128/src/constraints.rs:716) validates original and padded circuits and clones constraints; succinct_veil.rs:1511 joins the independent PCS and VEIL branches. Test bounded storage reuse or a measured branch's task partitioning while preserving blinding, fresh randomness, transcript forks, and all validation."
            }
        };
        writeln!(
            md,
            "{}. **{}** — mean self share {:.2}%; largest observed case [{}](svg/{}.svg), {:.2}%. {}\n",
            index + 1,
            name,
            mean,
            case,
            case,
            peak,
            experiment
        )?;
    }
    md.push_str("## Evidence and limitations\n\n[Manifest](manifest.json), [source archive and patch](source/), [validation/build logs](logs/), [all attempts](cases/), and per-attempt recorder/export status, harness JSON, folded stacks, original XML, and archived `.trace` directories preserve the evidence. Low-sample attempts remain archived; only accepted primary SVGs enter the matrix. The source archive includes uncommitted implementation files and the plan, so the base Git revision alone does not describe the measured code. No commit or push is part of this run.\n\nUnknown addresses and explicitly marked truncation are counted above, but sampling cannot establish complete stacks or expose every short-lived function. Full-ZK randomness and warm-cache corpus reuse differ from independent one-shot verification. Compare small timing differences against the available baseline controls, symbol-build variability, and endpoint repeats; the sample totals are adequacy checks, not confidence intervals. One-time phases remain included in every SVG. Frame-based source lookup and self-category grouping are heuristic and must be verified before making optimization claims.\n");
    if resumed {
        md.push_str("\nThe first episode lacks an immediate closing baseline. The resumed interval's before/after controls describe only its four large endpoint repeats; they do not establish continuous thermal/load stability across the pause or retrospectively bracket the primary matrix.\n");
    }
    fs::write(root.join("report.md"), md)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static ID: AtomicU64 = AtomicU64::new(0);
    fn temporary() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "flock-report-{}-{}",
            std::process::id(),
            ID.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&p).unwrap();
        p
    }
    fn baseline() -> String {
        let mut s = format!("{CSV_HEADER}\n");
        for n in SIZES {
            for protocol in ["FLOCK-non-ZK-Secure", "VEIL-FLOCK-full-ZK"] {
                writeln!(s, "{n},{protocol},1.0,2.0,100,90,110").unwrap();
            }
        }
        s
    }
    #[test]
    fn baseline_requires_complete_unique_finite_matrix() {
        let good = baseline();
        assert_eq!(parse_baseline(&good).unwrap().len(), 14);
        assert!(parse_baseline(&good.replace("1.0", "NaN")).is_err());
        assert!(parse_baseline(&good.replace("100,90,110", "80,90,110")).is_err());
        assert!(parse_baseline(&good.replacen("128,", "64,", 1)).is_err());
        assert!(parse_baseline(&good.lines().take(14).collect::<Vec<_>>().join("\n")).is_err());
    }
    #[test]
    fn capture_counts_rows_deduplicates_recursion_and_reconciles_folded() {
        let p = temporary();
        fs::create_dir(p.join("raw")).unwrap();
        fs::write(p.join("raw/time-profile.xml"),r#"<trace-query-result><node><row><weight>999999</weight><thread fmt="flock-verify"/><backtrace id="1"><frame id="1" name="flock_core::verifier::verify_core_inner&lt;[u8; 32]&gt;"/><frame id="2" name="rayon_core::worker"/></backtrace></row><row><backtrace ref="1"/></row><row><backtrace ref="1"/></row><row><sentinel/></row></node></trace-query-result>"#).unwrap();
        fs::write(p.join("stacks.folded"),"rayon_core::worker;flock_core::verifier::verify_core_inner<[u8； 32]>;flock_core::verifier::verify_core_inner<[u8； 32]> 2\nrayon_core::worker;0x1234 1\n").unwrap();
        fs::write(p.join("flamegraph.svg"), "<svg><rect/><g><rect/></g></svg>").unwrap();
        let s = analyze_capture(&p).unwrap();
        assert_eq!(s.usable_rows, 3);
        assert_eq!(s.total_weight, 3);
        assert_eq!(s.xml_rows, 4);
        assert_eq!(
            s.inclusive
                .iter()
                .find(|h| h.symbol.contains("verify_core_inner"))
                .unwrap()
                .samples,
            2
        );
        assert_eq!(s.self_samples.iter().map(|h| h.samples).sum::<u64>(), 3);
        assert_eq!(s.unknown_frame_rows, 1);
        assert_eq!(s.inclusive.len(), 3);
        assert!(
            s.inclusive
                .iter()
                .any(|h| h.symbol.ends_with("<[u8； 32]>"))
        );
        assert!(s.has_workload_symbols && s.has_verifier_worker && s.has_rayon_worker);
        fs::write(p.join("stacks.folded"), "rayon_core::worker 4\n").unwrap();
        assert!(analyze_capture(&p).is_err());
        fs::write(p.join("flamegraph.svg"), "<svg><rect/><g><rect/></svg>").unwrap();
        assert!(validate_svg(&p.join("flamegraph.svg")).is_err());
        fs::write(p.join("raw/time-profile.xml"), "<trace-query-result><node>").unwrap();
        assert!(analyze_xml(&p.join("raw/time-profile.xml")).is_err());
        fs::remove_dir_all(p).unwrap();
    }

    #[test]
    fn categories_recognize_scheduler_and_polynomial_intrinsics() {
        for name in ["swtch", "swtch_pri", "thread_yield", "pthread_cond_wait"] {
            assert_eq!(category(name), "scheduling and synchronization");
        }
        for name in [
            "core::core_arch::aarch64::neon::generated::vmull_p64",
            "core::core_arch::arm_shared::neon::generated::vmull_p8",
            "core::core_arch::aarch64::neon::generated::vmull_high_p64",
        ] {
            assert_eq!(category(name), "field arithmetic and transforms");
        }
        assert_eq!(
            category("core::core_arch::aarch64::neon::vmulq_f32"),
            "other or unresolved"
        );
    }
}

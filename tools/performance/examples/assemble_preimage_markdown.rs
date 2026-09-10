//! Assemble the existing reviewed legacy report without processing measurements.
//! Usage: assemble_preimage_markdown RUN OVERVIEW OUTPUT.md
use flock_performance::{Result, canonical_output, evidence, records, sha256};
use pulldown_cmark::{Event, LinkType, Options, Parser, Tag, TagEnd};
use records::{AcceptancePolicy, ArtifactIdentity, AttemptKind, Case, SelectedAttempt};
use serde::Serialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

fn main() {
    if let Err(error) = run() {
        eprintln!("Markdown assembly failed: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 3 {
        return Err("usage: assemble_preimage_markdown RUN OVERVIEW OUTPUT.md".into());
    }
    assemble(
        Path::new(&args[0]),
        Path::new(&args[1]),
        Path::new(&args[2]),
    )
}

fn parser(text: &str) -> Parser<'_> {
    Parser::new_ext(text, Options::ENABLE_TABLES | Options::ENABLE_STRIKETHROUGH)
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn read_json(path: &Path) -> Result<Value> {
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}

fn required<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value[key]
        .as_str()
        .ok_or_else(|| format!("missing string field {key}").into())
}

fn relative(from: &Path, to: &Path) -> Result<String> {
    let from: Vec<_> = from.components().collect();
    let to: Vec<_> = to.components().collect();
    let common = from.iter().zip(&to).take_while(|(a, b)| a == b).count();
    if common == 0 {
        return Err("relative links require a common filesystem root".into());
    }
    let mut result = PathBuf::new();
    for _ in common..from.len() {
        result.push("..");
    }
    for part in &to[common..] {
        result.push(part.as_os_str());
    }
    Ok(result.to_str().ok_or("non-Unicode report path")?.into())
}

fn encode_destination(value: &str) -> String {
    value
        .replace('%', "%25")
        .replace(' ', "%20")
        .replace('(', "%28")
        .replace(')', "%29")
        .replace('<', "%3C")
        .replace('>', "%3E")
}

fn decode_destination(value: &str) -> Result<String> {
    let mut bytes = Vec::new();
    let mut input = value.bytes();
    while let Some(byte) = input.next() {
        if byte == b'%' {
            let a = input.next().ok_or("truncated URL escape")?;
            let b = input.next().ok_or("truncated URL escape")?;
            let hex = |c: u8| (c as char).to_digit(16).ok_or("invalid URL escape");
            bytes.push((hex(a)? * 16 + hex(b)?) as u8);
        } else {
            bytes.push(byte);
        }
    }
    Ok(String::from_utf8(bytes)?)
}

fn external(value: &str) -> bool {
    value.starts_with("//")
        || value.split_once(':').is_some_and(|(scheme, _)| {
            !scheme.is_empty()
                && scheme
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.'))
        })
}

fn destination(value: &str, source: &Path, output_parent: &Path) -> Result<String> {
    if external(value) {
        return Ok(value.into());
    }
    let (path, fragment) = value.split_once('#').unwrap_or((value, ""));
    let decoded = decode_destination(path)?;
    let target = if path.is_empty() {
        source.to_path_buf()
    } else {
        source.parent().ok_or("source has no parent")?.join(decoded)
    };
    let target = target.canonicalize()?;
    let mut result = encode_destination(&relative(output_parent, &target)?);
    if !fragment.is_empty() {
        result.push('#');
        result.push_str(fragment);
    }
    Ok(result)
}

#[derive(Clone, Debug, Serialize)]
struct Edit {
    source_bytes: Range<usize>,
    before: String,
    after: String,
    reason: &'static str,
}

fn edit(source: &str, range: Range<usize>, after: String, reason: &'static str) -> Edit {
    Edit {
        before: source[range.clone()].into(),
        source_bytes: range,
        after,
        reason,
    }
}

/// Apply disjoint parser-directed edits and prove they can be reversed exactly.
fn apply_edits(source: &str, edits: &mut [Edit]) -> Result<String> {
    edits.sort_by_key(|edit| (edit.source_bytes.start, edit.source_bytes.end));
    let mut result = String::new();
    let mut cursor = 0;
    let mut reverse = Vec::new();
    for edit in edits.iter() {
        let range = &edit.source_bytes;
        if range.start < cursor || source.get(range.clone()) != Some(edit.before.as_str()) {
            return Err("overlapping or invalid Markdown edits".into());
        }
        result.push_str(&source[cursor..range.start]);
        let start = result.len();
        result.push_str(&edit.after);
        reverse.push((start..result.len(), edit.before.as_str()));
        cursor = range.end;
    }
    result.push_str(&source[cursor..]);
    let mut recovered = result.clone();
    for (range, before) in reverse.into_iter().rev() {
        recovered.replace_range(range, before);
    }
    if recovered != source {
        return Err("source content did not survive reversible presentation changes".into());
    }
    Ok(result)
}

/// Locate the destination only after the parser has identified an inline link.
/// Balanced labels, escaped punctuation, code spans, and parenthesized paths
/// must not turn text that merely resembles a link into an edit.
fn inline_destination(source: &str, range: Range<usize>) -> Result<Range<usize>> {
    let bytes = source.as_bytes();
    let mut at = range.start;
    if bytes.get(at) == Some(&b'!') {
        at += 1;
    }
    if bytes.get(at) != Some(&b'[') {
        return Err("inline link lacks its opening label".into());
    }
    let mut depth = 0;
    while at < range.end {
        match bytes[at] {
            b'\\' => at += 2,
            b'`' => {
                let start = at;
                while bytes.get(at) == Some(&b'`') {
                    at += 1;
                }
                let delimiter = &source[start..at];
                if let Some(end) = source[at..range.end].find(delimiter) {
                    at += end + delimiter.len();
                }
            }
            b'[' => {
                depth += 1;
                at += 1;
            }
            b']' => {
                depth -= 1;
                at += 1;
                if depth == 0 {
                    break;
                }
            }
            _ => at += 1,
        }
    }
    while bytes.get(at).is_some_and(u8::is_ascii_whitespace) {
        at += 1;
    }
    if bytes.get(at) != Some(&b'(') {
        return Err("unsupported inline-link layout".into());
    }
    at += 1;
    while bytes.get(at).is_some_and(u8::is_ascii_whitespace) {
        at += 1;
    }
    let start = at;
    if bytes.get(at) == Some(&b'<') {
        at += 1;
        while at < range.end {
            if bytes[at] == b'\\' {
                at += 2;
            } else if bytes[at] == b'>' {
                return Ok(start..at + 1);
            } else {
                at += 1;
            }
        }
    } else {
        let mut depth = 0;
        while at < range.end {
            match bytes[at] {
                b'\\' => at += 2,
                b'(' => {
                    depth += 1;
                    at += 1;
                }
                b')' if depth == 0 => return Ok(start..at),
                b')' => {
                    depth -= 1;
                    at += 1;
                }
                b if b.is_ascii_whitespace() && depth == 0 => return Ok(start..at),
                _ => at += 1,
            }
        }
    }
    Err("cannot locate parsed inline-link destination".into())
}

#[derive(Clone, Debug, Serialize)]
struct Heading {
    text: String,
    range: Range<usize>,
    level: usize,
}

fn headings(source: &str) -> Vec<Heading> {
    let mut result = Vec::new();
    let mut current: Option<Heading> = None;
    for (event, range) in parser(source).into_offset_iter() {
        match event {
            Event::Start(Tag::Heading { level, .. }) => {
                current = Some(Heading {
                    text: String::new(),
                    range,
                    level: level as usize,
                });
            }
            Event::Text(text) | Event::Code(text) => {
                if let Some(heading) = &mut current {
                    heading.text.push_str(&text);
                }
            }
            Event::End(TagEnd::Heading(_)) => {
                if let Some(heading) = current.take() {
                    result.push(heading);
                }
            }
            _ => {}
        }
    }
    result
}

fn slug(text: &str) -> String {
    text.to_lowercase()
        .chars()
        .filter_map(|c| {
            if c.is_alphanumeric() || matches!(c, '_' | '-') {
                Some(c)
            } else if c.is_whitespace() {
                Some('-')
            } else {
                None
            }
        })
        .collect()
}

#[derive(Clone, Debug, Serialize)]
struct Figure {
    case: Case,
    role: AttemptKind,
    attempt_id: String,
    attempt_path: String,
    attempt_sha256: String,
    episode: String,
    svg: String,
    svg_sha256: String,
    png_fallback: String,
    png_sha256: String,
    anchor: String,
}

impl Figure {
    fn label(&self) -> String {
        let protocol = if self.case.protocol == records::Protocol::Flock {
            "FLOCK"
        } else {
            "Full-ZK"
        };
        format!(
            "{protocol} {} — {} hashes ({})",
            self.case.operation.as_str(),
            self.case.hashes,
            self.role.as_str()
        )
    }

    fn caption(&self) -> String {
        format!(
            "{}; {}. Width represents usable sampled backtrace rows across all threads, not elapsed latency. Attempt: `{}`.",
            self.label(),
            self.episode,
            self.attempt_id
        )
    }

    fn links_and_caption(&self) -> String {
        format!(
            "[Open/download SVG]({}) · [Optional PNG fallback]({})\n\n{}\n",
            self.svg,
            self.png_fallback,
            self.caption()
        )
    }

    fn block(&self) -> String {
        format!(
            "\n\n<a id=\"{}\"></a>\n\n[![{}; {}]({})]({})\n\n{}\n",
            self.anchor,
            self.label(),
            self.episode,
            self.svg,
            self.svg,
            self.links_and_caption()
        )
    }
}

#[derive(Debug, Serialize)]
struct Coverage {
    source: String,
    source_sha256: String,
    appendix_anchor: String,
    source_headings: Vec<Heading>,
    tables: usize,
    table_body_rows: Vec<usize>,
    source_image_count: usize,
    source_bytes_reconstructed_exactly: bool,
    edits: Vec<Edit>,
}

fn table_rows(source: &str) -> Vec<usize> {
    let mut counts = Vec::new();
    for event in parser(source) {
        match event {
            Event::Start(Tag::Table(_)) => counts.push(0),
            Event::Start(Tag::TableRow) => {
                if let Some(rows) = counts.last_mut() {
                    *rows += 1;
                }
            }
            _ => {}
        }
    }
    counts
}

fn import_document(
    path: &Path,
    output_parent: &Path,
    namespace: &str,
    appendix_anchor: &str,
    figures: &[Figure],
) -> Result<(String, Coverage)> {
    let source = fs::read_to_string(path)?;
    let mut edits = Vec::new();
    let source_headings = headings(&source);
    let mut seen = BTreeSet::new();
    let mut primary_cases = BTreeSet::new();
    for heading in &source_headings {
        let line = &source[heading.range.clone()];
        let prefix = "#".repeat(heading.level);
        if !line.starts_with(&format!("{prefix} ")) || heading.level >= 6 {
            return Err("reviewed appendices require ordinary ATX headings below level six".into());
        }
        let anchor = format!("{namespace}-{}", slug(&heading.text));
        if !seen.insert(anchor.clone()) {
            return Err("duplicate imported heading needs an explicit disambiguation".into());
        }
        edits.push(edit(
            &source,
            heading.range.start..heading.range.start,
            format!("<a id=\"{anchor}\"></a>\n\n#"),
            "heading demotion and unique anchor",
        ));
        if let Some(figure) = figures.iter().find(|figure| {
            namespace == "report"
                && figure.role == AttemptKind::Primary
                && heading.text == figure.case.id()
        }) {
            primary_cases.insert(figure.case);
            edits.push(edit(
                &source,
                heading.range.end..heading.range.end,
                figure.block(),
                "insert accepted primary SVG with caption",
            ));
        }
    }
    if namespace == "report" && primary_cases.len() != 28 {
        return Err("reviewed report does not contain all 28 exact case headings".into());
    }
    let mut images = 0;
    for (event, range) in parser(&source).into_offset_iter() {
        let (link_type, url, image) = match event {
            Event::Start(Tag::Link {
                link_type,
                dest_url,
                ..
            }) => (link_type, dest_url, false),
            Event::Start(Tag::Image {
                link_type,
                dest_url,
                ..
            }) => (link_type, dest_url, true),
            _ => continue,
        };
        match link_type {
            LinkType::Autolink | LinkType::Email if external(&url) => continue,
            LinkType::Inline => {}
            _ => return Err("reviewed source uses reference-style links; explicit migration is required before assembly".into()),
        }
        let rebased = destination(&url, path, output_parent)?;
        let target = inline_destination(&source, range.clone())?;
        // External destinations retain their original spelling, escapes and titles.
        if !external(&url) {
            edits.push(edit(
                &source,
                target,
                rebased.clone(),
                "rebase parsed Markdown destination",
            ));
        }
        if image {
            images += 1;
            let figure = figures
                .iter()
                .find(|figure| figure.svg == rebased)
                .ok_or("source image does not identify an accepted corrected primary")?;
            edits.push(edit(
                &source,
                range.start..range.start,
                "[".into(),
                "link preserved source image to SVG",
            ));
            edits.push(edit(
                &source,
                range.end..range.end,
                format!("]({rebased})\n\n{}", figure.links_and_caption()),
                "caption preserved source image",
            ));
        }
    }
    let mut contents = String::new();
    for heading in source_headings.iter().filter(|heading| heading.level == 2) {
        contents.push_str(&format!(
            "- [{}](#{namespace}-{})\n",
            heading.text,
            slug(&heading.text)
        ));
    }
    let first = source_headings
        .first()
        .filter(|heading| heading.level == 1)
        .ok_or("reviewed document lacks a top-level title")?;
    edits.push(edit(
        &source,
        first.range.end..first.range.end,
        format!("\n\n{contents}\n"),
        "insert appendix navigation after its title",
    ));
    let body = apply_edits(&source, &mut edits)?;
    let rows = table_rows(&source);
    if table_rows(&body) != rows {
        return Err("presentation changes altered source table structure".into());
    }
    let result = format!("<a id=\"{appendix_anchor}\"></a>\n\n{body}\n");
    Ok((
        result,
        Coverage {
            source: relative(output_parent, path)?,
            source_sha256: digest(source.as_bytes()),
            appendix_anchor: appendix_anchor.into(),
            source_headings,
            tables: rows.len(),
            table_body_rows: rows,
            source_image_count: images,
            source_bytes_reconstructed_exactly: true,
            edits,
        },
    ))
}

fn select_figures(root: &Path, parent: &Path, manifest: &Value) -> Result<Vec<Figure>> {
    let snapshot = required(&manifest["snapshot"], "id")?;
    let executable: ArtifactIdentity =
        serde_json::from_value(manifest["artifacts"]["preimage_profile"].clone())?;
    let policy: Vec<String> =
        serde_json::from_value(manifest["environment"]["measurement_environment_removed"].clone())?;
    let frozen_policy: Vec<String> = serde_json::from_slice(&fs::read(
        root.join("source/untracked/tools/performance/measurement-env.json"),
    )?)?;
    if policy != frozen_policy {
        return Err("measurement policy differs from its preserved source".into());
    }
    let resume = read_json(&root.join("resume.json"))?;
    let controller = read_json(&root.join("resume-controller/manifest.json"))?;
    if resume["status"] != "measurements_complete" || resume["measurement_snapshot_id"] != snapshot
    {
        return Err("resume provenance is not complete for this measurement snapshot".into());
    }
    let new: BTreeSet<String> = resume["new_repeats"]
        .as_array()
        .ok_or("resume repeat mapping missing")?
        .iter()
        .map(|value| {
            Ok(format!(
                "cases/{}/{}/attempt.json",
                required(value, "case")?,
                required(value, "attempt")?
            ))
        })
        .collect::<Result<_>>()?;
    let preserved = controller["preserved_evidence"]
        .as_object()
        .ok_or("preserved episode mapping missing")?;
    let mut result = Vec::new();
    for role in [
        AttemptKind::Primary,
        AttemptKind::Repeat,
        AttemptKind::Smoke,
    ] {
        let selected = records::selected_attempts(
            root,
            role,
            snapshot,
            &executable,
            &policy,
            AcceptancePolicy::LegacyV1,
        )?;
        records::require_matrix(
            &selected,
            &if role == AttemptKind::Primary {
                records::all_cases()
            } else {
                records::endpoints()
            },
        )?;
        for (case, selected) in selected {
            result.push(figure(root, parent, case, role, selected, &new, preserved)?);
        }
    }
    Ok(result)
}

fn figure(
    root: &Path,
    parent: &Path,
    case: Case,
    role: AttemptKind,
    selected: SelectedAttempt,
    new: &BTreeSet<String>,
    preserved: &serde_json::Map<String, Value>,
) -> Result<Figure> {
    records::verify_attempt_evidence(&selected)?;
    let attempt_path = selected.dir.join("attempt.json");
    let relative_attempt = relative(root, &attempt_path)?;
    let episode = if new.contains(&relative_attempt) {
        if role != AttemptKind::Repeat {
            return Err("resumed attempt is not an endpoint repeat".into());
        }
        "Episode 2: resumed"
    } else if preserved.contains_key(&relative_attempt) {
        let original = selected.dir.join("original/attempt.json");
        if sha256(&original)? != required(&preserved[&relative_attempt], "sha256")? {
            return Err("original episode attempt disagrees with resume provenance".into());
        }
        "Episode 1: original"
    } else {
        return Err("accepted attempt has no recorded episode membership".into());
    };
    let repair = read_json(&selected.dir.join("repair.json"))?;
    if repair["status"] != "complete"
        || repair["attempt_id"] != selected.attempt.attempt_id
        || repair["raw_recording_unchanged"] != true
    {
        return Err("selected SVG lacks complete correction provenance".into());
    }
    let svg = if role == AttemptKind::Primary {
        root.join("svg").join(format!("{case}.svg"))
    } else {
        selected.dir.join("flamegraph.svg")
    };
    let svg_hash = sha256(&svg)?;
    if svg_hash != required(&repair["after_sha256"], "flamegraph.svg")?
        || svg_hash != sha256(&selected.dir.join("flamegraph.svg"))?
    {
        return Err("canonical SVG is not the accepted corrected attempt asset".into());
    }
    let png = selected.dir.join("preview.png");
    let png_hash = sha256(&png)?;
    if png_hash != required(&repair["after_sha256"], "preview.png")? {
        return Err("PNG fallback differs from corrected evidence".into());
    }
    Ok(Figure {
        case,
        role,
        attempt_id: selected.attempt.attempt_id,
        attempt_path: encode_destination(&relative(parent, &attempt_path)?),
        attempt_sha256: sha256(&attempt_path)?,
        episode: episode.into(),
        svg: encode_destination(&relative(parent, &svg)?),
        svg_sha256: svg_hash,
        png_fallback: encode_destination(&relative(parent, &png)?),
        png_sha256: png_hash,
        anchor: format!("figure-{}-{case}", role.as_str()),
    })
}

fn matrix(figures: &[Figure]) -> Result<String> {
    let mut result = "| Hashes | FLOCK prove | FLOCK verify | Full-ZK prove | Full-ZK verify |\n| ---: | --- | --- | --- | --- |\n".to_owned();
    for hashes in records::SIZES {
        result.push_str(&format!("| {hashes} "));
        for protocol in ["flock", "full-zk"] {
            for operation in ["prove", "verify"] {
                let case = Case::new(protocol, operation, hashes)?;
                let figure = figures
                    .iter()
                    .find(|figure| figure.case == case && figure.role == AttemptKind::Primary)
                    .ok_or("primary matrix has a missing slot")?;
                result.push_str(&format!(
                    "| [Figure](#{}) · [SVG]({}) ",
                    figure.anchor, figure.svg
                ));
            }
        }
        result.push_str("|\n");
    }
    Ok(result)
}

fn role_appendix(figures: &[Figure], role: AttemptKind) -> String {
    let title = if role == AttemptKind::Repeat {
        "Endpoint repeat flamegraphs"
    } else {
        "Smoke recordings"
    };
    let intro = if role == AttemptKind::Repeat {
        "These eight full-duration repeats supplement the primary captures. Episode labels preserve the distinction between same-episode and resumed comparisons."
    } else {
        "These eight short smokes check recording quality and worker capture. They are not additional performance measurements."
    };
    let mut result = format!(
        "\n<a id=\"{}-flamegraphs\"></a>\n\n## {title}\n\n{intro}\n\n",
        role.as_str()
    );
    for figure in figures.iter().filter(|figure| figure.role == role) {
        result.push_str(&format!("- [{}](#{})\n", figure.label(), figure.anchor));
    }
    for figure in figures.iter().filter(|figure| figure.role == role) {
        result.push_str(&format!("\n### {}\n{}", figure.label(), figure.block()));
    }
    result
}

fn evidence_index(root: &Path, parent: &Path, figures: &[Figure]) -> Result<String> {
    let mut result = "\n<a id=\"evidence-and-run-history\"></a>\n\n## Recording evidence and run history\n\nThe tables below index 44 accepted recording identities. Repeated images inherited from the reviewed report do not add recordings.\n".to_owned();
    for role in [
        AttemptKind::Primary,
        AttemptKind::Repeat,
        AttemptKind::Smoke,
    ] {
        result.push_str(&format!("\n### Accepted {} recordings\n\n| Recording | Episode | Attempt | Corrected SVG | Optional PNG fallback |\n| --- | --- | --- | --- | --- |\n", role.as_str()));
        for figure in figures.iter().filter(|figure| figure.role == role) {
            result.push_str(&format!(
                "| [{}](#{}) | {} | [{}]({}) | [SVG]({}) | [PNG]({}) |\n",
                figure.label(),
                figure.anchor,
                figure.episode,
                figure.attempt_id,
                figure.attempt_path,
                figure.svg,
                figure.png_fallback
            ));
        }
    }
    result.push_str("\n### Retained unsuccessful attempts\n\nThese files document unsuccessful work and are excluded from accepted results.\n\n");
    for case in fs::read_dir(root.join("cases"))? {
        for attempt in fs::read_dir(case?.path())? {
            let path = attempt?.path().join("attempt.json");
            if !path.is_file() {
                continue;
            }
            let value = read_json(&path)?;
            if value["status"] != "validated" {
                result.push_str(&format!(
                    "- [{}]({}): `{}`.\n",
                    required(&value, "attempt_id")?,
                    encode_destination(&relative(parent, &path)?),
                    required(&value, "status")?
                ));
            }
        }
    }
    let failed = root
        .parent()
        .ok_or("run has no parent")?
        .join("20260910T142700Z/incomplete.json");
    if !failed.is_file() || read_json(&failed)?["stage"] != "bootstrap" {
        return Err("expected earlier bootstrap-failure evidence is missing".into());
    }
    result.push_str(&format!("- [Earlier bootstrap failure]({}): the profiler version probe was rejected before measurements.\n", encode_destination(&relative(parent,&failed)?)));
    result.push_str("\n### Supporting files and archived versions\n\n");
    for (file, description) in [
        ("complete.json", "Completion record"),
        ("measurements-complete.json", "Measurement completion"),
        ("manifest.json", "Measurement manifest"),
        ("resume.json", "Resume and episode provenance"),
        (
            "incomplete.json",
            "Preserved interruption record; superseded by successful continuation",
        ),
        ("report.md", "Original reviewed report"),
        ("findings.md", "Original authored findings"),
        ("index.html", "Interactive primary gallery"),
        ("reference.csv", "Historical reference data"),
        ("baseline-before.csv", "Original normal baseline"),
        ("baseline-symbols.csv", "Original symbol baseline"),
        (
            "baseline-resume-before.csv",
            "Resumed-episode opening baseline",
        ),
        ("baseline-after.csv", "Resumed-episode closing baseline"),
        ("hotspots.csv", "Complete hotspot counts and denominators"),
        ("cases/", "All attempt evidence and preserved originals"),
        ("source/", "Measured source archive"),
        ("logs/", "Build and validation logs"),
        ("artifacts.json", "Historical artifact inventory"),
        (
            "report-processing.json",
            "Corrected frame-label processing provenance",
        ),
        (
            "report-processing-source/",
            "Preserved correction-tool source",
        ),
        ("editorial-review.json", "Editorial review provenance"),
        (
            "report-generated.md",
            "Generated report before final editorial additions",
        ),
        (
            "report-original/",
            "Original derived artifacts before the frame-label correction",
        ),
        (
            "execution-plan-completed.md",
            "Completed execution plan and amendments",
        ),
    ] {
        let path = root.join(file).canonicalize()?;
        result.push_str(&format!(
            "- [{description}]({})\n",
            encode_destination(&relative(parent, &path)?)
        ));
    }
    Ok(result)
}

fn anchors(source: &str) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    let mut duplicates = BTreeMap::<String, usize>::new();
    for heading in headings(source) {
        let slug = slug(&heading.text);
        let count = duplicates.entry(slug.clone()).or_default();
        result.insert(if *count == 0 {
            slug
        } else {
            format!("{slug}-{count}")
        });
        *count += 1;
    }
    for event in parser(source) {
        if let Event::Html(html) | Event::InlineHtml(html) = event {
            for part in html.split("id=\"").skip(1) {
                if let Some((id, _)) = part.split_once('"') {
                    result.insert(id.into());
                }
            }
        }
    }
    result
}

fn validate_links(markdown: &str, output: &Path, figures: &[Figure]) -> Result<Value> {
    let parent = output.parent().ok_or("output has no parent")?;
    let own_anchors = anchors(markdown);
    let mut local = BTreeSet::new();
    let mut external_links = BTreeSet::new();
    let mut image_counts = BTreeMap::<String, usize>::new();
    let mut image_alt = None;
    for event in parser(markdown) {
        match event {
            Event::Start(Tag::Link { ref dest_url, .. })
            | Event::Start(Tag::Image { ref dest_url, .. }) => {
                let is_image = matches!(event, Event::Start(Tag::Image { .. }));
                if is_image {
                    image_alt = Some(String::new());
                    *image_counts.entry(dest_url.to_string()).or_default() += 1;
                }
                if external(dest_url) {
                    external_links.insert(dest_url.to_string());
                    continue;
                }
                let (path, fragment) = dest_url.split_once('#').unwrap_or((dest_url, ""));
                let path = decode_destination(path)?;
                let target = if path.is_empty() {
                    output.to_path_buf()
                } else {
                    parent.join(path).canonicalize()?
                };
                if !fragment.is_empty() {
                    if target == output {
                        if !own_anchors.contains(fragment) {
                            return Err(format!("missing output anchor: {fragment}").into());
                        }
                    } else if target
                        .extension()
                        .is_some_and(|extension| extension == "md")
                    {
                        if !anchors(&fs::read_to_string(&target)?).contains(fragment) {
                            return Err(format!("missing Markdown fragment: {dest_url}").into());
                        }
                    } else if let Some(line) = fragment.strip_prefix('L') {
                        let mut ends = line.split("-L");
                        let start = ends.next().ok_or("empty line fragment")?.parse::<usize>()?;
                        let end = ends
                            .next()
                            .map(str::parse::<usize>)
                            .transpose()?
                            .unwrap_or(start);
                        let count = fs::read_to_string(&target)?.lines().count();
                        if start == 0 || end < start || end > count || ends.next().is_some() {
                            return Err(
                                format!("source-line fragment out of bounds: {dest_url}").into()
                            );
                        }
                    } else {
                        return Err(format!(
                            "unsupported local fragment needs manual resolution: {dest_url}"
                        )
                        .into());
                    }
                }
                local.insert(dest_url.to_string());
            }
            Event::Text(text) | Event::Code(text) => {
                if let Some(alt) = &mut image_alt {
                    alt.push_str(&text);
                }
            }
            Event::End(TagEnd::Image)
                if image_alt.take().is_none_or(|alt| alt.trim().is_empty()) =>
            {
                return Err("image lacks descriptive alt text".into());
            }
            _ => {}
        }
    }
    for figure in figures {
        if !image_counts.contains_key(&figure.svg)
            || !markdown.contains(&figure.caption())
            || !markdown.contains(&format!("[Open/download SVG]({})", figure.svg))
        {
            return Err(format!(
                "accepted figure missing its image/caption/open link: {}",
                figure.attempt_id
            )
            .into());
        }
        if sha256(&parent.join(decode_destination(&figure.svg)?))? != figure.svg_sha256 {
            return Err("embedded SVG identity changed".into());
        }
    }
    let accepted_paths: BTreeSet<_> = figures.iter().map(|figure| figure.svg.as_str()).collect();
    if image_counts
        .keys()
        .any(|path| !accepted_paths.contains(path.as_str()))
    {
        return Err("image destination is not an accepted corrected SVG".into());
    }
    Ok(
        json!({"status":"passed","local_destinations_checked":local.len(),"external_links_preserved_not_fetched":external_links,"accepted_recording_images":figures.len(),"svg_image_occurrences":image_counts.values().sum::<usize>(),"image_occurrences_by_path":image_counts,"anchors_checked":own_anchors.len(),"source_line_fragments_checked":true}),
    )
}

fn assemble(root: &Path, overview: &Path, output: &Path) -> Result<()> {
    let root = root.canonicalize()?;
    let overview = overview.canonicalize()?;
    let output = canonical_output(&std::path::absolute(output)?)?;
    let parent = output
        .parent()
        .ok_or("output has no parent")?
        .canonicalize()?;
    if output.starts_with(&root) || output.extension().is_none_or(|extension| extension != "md") {
        return Err("output must be a new Markdown file outside the historical run".into());
    }
    for sibling in fs::read_dir(root.parent().ok_or("run has no parent")?)? {
        let path = sibling?.path();
        if path.is_dir()
            && (path.join("manifest.json").is_file() || path.join("incomplete.json").is_file())
            && output.starts_with(path.canonicalize()?)
        {
            return Err("assembly output would modify a historical run directory".into());
        }
    }
    let stem = output
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or("invalid output stem")?;
    let sources_path = parent.join(format!("{stem}.sources.json"));
    let validation_path = parent.join(format!("{stem}.validation.json"));
    for path in [&output, &sources_path, &validation_path] {
        if fs::symlink_metadata(path).is_ok() {
            return Err(format!(
                "destination already exists; preserve/review it before assembly: {}",
                path.display()
            )
            .into());
        }
    }
    let inventory_path = root.join("artifacts.json");
    let inventory: evidence::Inventory = serde_json::from_slice(&fs::read(&inventory_path)?)?;
    if inventory.schema_version != 1 || inventory.exclusions != ["artifacts.json", "complete.json"]
    {
        return Err("unsupported legacy inventory contract".into());
    }
    eprintln!("Verifying unchanged historical evidence before assembly...");
    evidence::verify_inventory(&root, &inventory)?;
    let initial_inventory_sha = sha256(&inventory_path)?;
    let initial_complete_sha = sha256(&root.join("complete.json"))?;
    let earlier_failure = root
        .parent()
        .ok_or("run has no parent")?
        .join("20260910T142700Z/incomplete.json");
    let earlier_failure_sha = sha256(&earlier_failure)?;
    let overview_sha = sha256(&overview)?;
    let manifest = read_json(&root.join("manifest.json"))?;
    let snapshot = required(&manifest["snapshot"], "id")?;
    let complete = read_json(&root.join("complete.json"))?;
    let measurements = read_json(&root.join("measurements-complete.json"))?;
    let processing = read_json(&root.join("report-processing.json"))?;
    let editorial = read_json(&root.join("editorial-review.json"))?;
    if complete["snapshot_id"] != snapshot
        || complete["primary_svgs"] != 28
        || measurements["snapshot_id"] != snapshot
        || measurements["primary_recordings"] != 28
        || measurements["endpoint_repeats"] != 8
        || processing["status"] != "complete"
        || processing["expected_attempts"] != 44
        || processing["measurements_unchanged"] != true
        || processing["original_snapshot_id"] != snapshot
        || editorial["status"] != "complete"
        || editorial["measurement_snapshot_id"] != snapshot
        || editorial["recordings_and_generated_metrics_changed"] != false
    {
        return Err("completion/processing/editorial records do not reconcile".into());
    }
    for key in ["reviewed_report", "generated_report", "findings"] {
        let path = root.join(required(&editorial[key], "path")?);
        if sha256(&path)? != required(&editorial[key], "sha256")? {
            return Err(format!("editorial source changed: {key}").into());
        }
    }
    let figures = select_figures(&root, &parent, &manifest)?;
    let processed: BTreeSet<_> = processing["attempts"]
        .as_array()
        .ok_or("processing attempt list missing")?
        .iter()
        .map(|a| required(a, "attempt").map(str::to_owned))
        .collect::<Result<_>>()?;
    let selected: BTreeSet<_> = figures
        .iter()
        .map(|figure| {
            let path = parent
                .join(decode_destination(&figure.attempt_path)?)
                .canonicalize()?;
            relative(&root, path.parent().ok_or("attempt has no parent")?)
        })
        .collect::<Result<_>>()?;
    if selected != processed || selected.len() != 44 {
        return Err("corrected and accepted recording sets differ".into());
    }
    let authored = fs::read_to_string(&overview)?;
    if authored.matches("<!-- PRIMARY_MATRIX -->").count() != 1 {
        return Err("overview must contain exactly one PRIMARY_MATRIX marker".into());
    }
    let mut markdown = authored.replace("<!-- PRIMARY_MATRIX -->", &matrix(&figures)?);
    let (report, report_coverage) = import_document(
        &root.join("report.md"),
        &parent,
        "report",
        "complete-reviewed-report",
        &figures,
    )?;
    let (findings, findings_coverage) = import_document(
        &root.join("findings.md"),
        &parent,
        "findings",
        "complete-findings",
        &figures,
    )?;
    markdown.push_str(&format!("\n\n{report}\n{findings}"));
    markdown.push_str(&role_appendix(&figures, AttemptKind::Repeat));
    markdown.push_str(&role_appendix(&figures, AttemptKind::Smoke));
    markdown.push_str(&evidence_index(&root, &parent, &figures)?);
    let mut validation = validate_links(&markdown, &output, &figures)?;
    validation["source_content_reversible"] = json!(true);
    validation["source_tables_unchanged"] = json!(true);
    validation["counts_by_role"] = json!({"primary":28,"repeat":8,"smoke":8});
    eprintln!("Rechecking historical evidence after content/link validation...");
    evidence::verify_inventory(&root, &inventory)?;
    if sha256(&inventory_path)? != initial_inventory_sha
        || sha256(&root.join("complete.json"))? != initial_complete_sha
        || sha256(&overview)? != overview_sha
        || sha256(&earlier_failure)? != earlier_failure_sha
    {
        return Err("source changed during assembly".into());
    }
    let mut consumed: BTreeSet<PathBuf> = [
        "manifest.json",
        "report.md",
        "findings.md",
        "report-generated.md",
        "reference.csv",
        "baseline-before.csv",
        "baseline-symbols.csv",
        "baseline-resume-before.csv",
        "baseline-after.csv",
        "measurements-complete.json",
        "report-processing.json",
        "editorial-review.json",
        "resume.json",
        "resume-controller/manifest.json",
        "source/untracked/tools/performance/measurement-env.json",
    ]
    .into_iter()
    .map(PathBuf::from)
    .collect();
    for figure in &figures {
        for link in [&figure.svg, &figure.png_fallback, &figure.attempt_path] {
            consumed.insert(
                parent
                    .join(decode_destination(link)?)
                    .canonicalize()?
                    .strip_prefix(&root)?
                    .to_path_buf(),
            );
        }
        let dir = parent
            .join(decode_destination(&figure.attempt_path)?)
            .canonicalize()?
            .parent()
            .ok_or("attempt lacks parent")?
            .to_path_buf();
        for file in [
            "harness.json",
            "record-status.json",
            "export-status.json",
            "repair.json",
            "original/attempt.json",
            "flamegraph.svg",
        ] {
            consumed.insert(dir.join(file).strip_prefix(&root)?.to_path_buf());
        }
    }
    let source_hashes: BTreeMap<_, _> = consumed
        .into_iter()
        .map(|path| {
            let file = inventory
                .files
                .get(&path)
                .ok_or("consumed file absent from historical inventory")?;
            Ok((path, file.sha256.clone()))
        })
        .collect::<Result<_>>()?;
    let source_record = json!({
        "schema_version": 1,
        "kind": "editorial-markdown-assembly",
        "run": relative(&parent, &root)?,
        "measurement_snapshot_id": snapshot,
        "controller_snapshot_id": complete["controller_snapshot_id"],
        "historical_inventory_sha256": initial_inventory_sha,
        "completion_sha256": initial_complete_sha,
        "earlier_bootstrap_failure": {
            "path": relative(&parent, &earlier_failure)?,
            "sha256": earlier_failure_sha
        },
        "overview": {
            "path": relative(&parent, &overview)?,
            "sha256": overview_sha,
            "interpretation": "newly authored overview; PRIMARY_MATRIX replaced"
        },
        "assembler": {
            "source_sha256": digest(include_bytes!("assemble_preimage_markdown.rs")),
            "cargo_lock_sha256": digest(include_bytes!("../../../Cargo.lock"))
        },
        "source_hashes": source_hashes,
        "source_to_section_coverage": [report_coverage, findings_coverage],
        "accepted_attempts_and_embedded_svgs": figures,
        "output": {"path": format!("{stem}.md"), "sha256": digest(markdown.as_bytes())},
        "transformations": [
            "demote imported headings and add unique explicit anchors",
            "rebase parser-confirmed inline link/image destinations",
            "preserve original images and add caption/open links",
            "insert 44 corrected SVG figures without modifying assets",
            "append role-specific figures and accepted-evidence index"
        ],
        "historical_evidence_unchanged": true,
        "xml_reanalysis": false,
        "svg_regeneration": false,
        "measurements_run": false,
        "validation": format!("{stem}.validation.json")
    });
    validation["output_sha256"] = json!(digest(markdown.as_bytes()));
    validation["source_record_sha256"] = json!(digest(&serde_json::to_vec_pretty(&source_record)?));
    validation["historical_inventory_files_verified_before_and_after"] =
        json!(inventory.files.len());
    validation["historical_evidence_unchanged"] = json!(true);
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
    let staging = parent.join(format!(".{stem}.assembly-{}-{nonce}", std::process::id()));
    fs::create_dir(&staging)?;
    for (name, bytes) in [
        ("document.md", markdown.into_bytes()),
        ("sources.json", serde_json::to_vec_pretty(&source_record)?),
        ("validation.json", serde_json::to_vec_pretty(&validation)?),
    ] {
        fs::write(staging.join(name), bytes)?;
    }
    // Exclusive hard links never replace a destination introduced concurrently.
    // Install the reading document last, after both companion records exist.
    fs::hard_link(staging.join("sources.json"), &sources_path)?;
    fs::hard_link(staging.join("validation.json"), &validation_path)?;
    fs::hard_link(staging.join("document.md"), &output)?;
    for file in ["document.md", "sources.json", "validation.json"] {
        fs::remove_file(staging.join(file))?;
    }
    fs::remove_dir(staging)?;
    println!(
        "Created {} with 44 accepted corrected SVGs; validation passed.",
        output.display()
    );
    Ok(())
}

#[cfg(test)]
#[path = "../tests/common/mod.rs"]
mod common;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_edits_only_real_links_and_preserves_code_and_tables() {
        let source = "# Header\n\n`[fake](keep.md)`\n\n```md\n![fake](keep.svg)\n```\n\n| A | B |\n| - | - |\n| [real](old.md) | `](not-a-link)` |\n";
        let mut edits = Vec::new();
        for (event, range) in parser(source).into_offset_iter() {
            if let Event::Start(Tag::Link { .. }) = event {
                edits.push(edit(
                    source,
                    inline_destination(source, range).unwrap(),
                    "new.md".into(),
                    "test",
                ));
            }
        }
        assert_eq!(edits.len(), 1);
        let output = apply_edits(source, &mut edits).unwrap();
        assert!(output.contains("[real](new.md)"));
        assert!(output.contains("`[fake](keep.md)`"));
        assert!(output.contains("![fake](keep.svg)"));
        assert_eq!(table_rows(source), table_rows(&output));
    }

    #[test]
    fn destination_ranges_handle_nested_images_code_and_escaped_parentheses() {
        let source = "[![alt](a.svg)](a.svg) [a `](` b](<path with spaces.md> \"title\") [x](a(b).md) [y](a\\(b\\).md)";
        let mut destinations = Vec::new();
        for (event, range) in parser(source).into_offset_iter() {
            if matches!(
                event,
                Event::Start(Tag::Link { .. }) | Event::Start(Tag::Image { .. })
            ) {
                destinations.push(source[inline_destination(source, range).unwrap()].to_owned());
            }
        }
        assert_eq!(
            destinations,
            [
                "a.svg",
                "a.svg",
                "<path with spaces.md>",
                "a(b).md",
                "a\\(b\\).md"
            ]
        );
    }

    #[test]
    fn reversible_insertions_preserve_every_source_byte() {
        let source = "# Exact\n\nSentence with 75.89%.\n";
        let mut edits = vec![
            edit(source, 0..0, "<a id=\"x\"></a>\n\n#".into(), "heading"),
            edit(source, 8..8, "\n![graph](x.svg)\n".into(), "image"),
        ];
        let result = apply_edits(source, &mut edits).unwrap();
        assert!(result.contains("## Exact"));
        assert!(result.contains("Sentence with 75.89%."));
        let mut bad = vec![
            edit(source, 0..3, "x".into(), "bad"),
            edit(source, 2..5, "y".into(), "bad"),
        ];
        assert!(apply_edits(source, &mut bad).is_err());
    }

    #[test]
    fn figure_roles_and_episode_labels_do_not_guess_attempt_suffixes() {
        let figure = Figure {
            case: Case::new("flock", "prove", 4096).unwrap(),
            role: AttemptKind::Repeat,
            attempt_id: "flock-prove-4096-repeat-002".into(),
            attempt_path: "case/attempt.json".into(),
            attempt_sha256: "hash".into(),
            episode: "Episode 2: resumed".into(),
            svg: "case/flamegraph.svg".into(),
            svg_sha256: "hash".into(),
            png_fallback: "case/preview.png".into(),
            png_sha256: "hash".into(),
            anchor: "figure-repeat-flock-prove-4096".into(),
        };
        let block = figure.block();
        assert!(block.contains("repeat-002"));
        assert!(block.contains("Episode 2: resumed"));
        assert!(block.contains("[![FLOCK prove"));
        assert!(block.contains("[Open/download SVG](case/flamegraph.svg)"));
    }

    #[test]
    fn explicit_anchors_and_gfm_duplicates_are_resolved() {
        let result =
            anchors("# Same\n\n# Same\n\n<a id=\"specific\"></a>\n\n`<a id=\"fake\"></a>`\n");
        assert!(
            result.contains("same") && result.contains("same-1") && result.contains("specific")
        );
        assert!(!result.contains("fake"));
    }

    #[test]
    fn url_paths_preserve_spaces_and_percent_characters() {
        let value = "a folder/percent%/(thing).svg";
        assert_eq!(
            decode_destination(&encode_destination(value)).unwrap(),
            value
        );
        assert!(decode_destination("bad%2").is_err());
        assert!(external("https://example.com/a(b)#L4"));
        assert!(!external("../source.rs#L4"));
        assert_eq!(
            relative(Path::new("/a/b"), Path::new("/a/c/file.md")).unwrap(),
            "../c/file.md"
        );
    }

    #[test]
    fn complete_case_import_keeps_tables_original_images_and_title_before_navigation() {
        let temp = common::Temporary::new("Markdown import").unwrap();
        let parent = temp.path().canonicalize().unwrap();
        let root = parent.join("run with spaces");
        fs::create_dir(&root).unwrap();
        fs::create_dir(root.join("svg")).unwrap();
        let mut source = "# Reviewed report\n\n## Details\n\nPreserve **every word** and `symbol<[u8; 64]>`.\n\n| Exact | Table |\n| --- | --- |\n| 75.89% | 4.944 ms |\n\n".to_owned();
        let mut figures = Vec::new();
        for case in records::all_cases() {
            let svg = root.join("svg").join(format!("{case}.svg"));
            fs::write(&svg, "<svg/>").unwrap();
            source.push_str(&format!("### {case}\n\nExact {case} analysis.\n\n"));
            figures.push(Figure {
                case,
                role: AttemptKind::Primary,
                attempt_id: format!("{case}-primary-001"),
                attempt_path: "unused".into(),
                attempt_sha256: "unused".into(),
                episode: "Episode 1: original".into(),
                svg: encode_destination(&relative(&parent, &svg).unwrap()),
                svg_sha256: sha256(&svg).unwrap(),
                png_fallback: "unused".into(),
                png_sha256: "unused".into(),
                anchor: format!("figure-primary-{case}"),
            });
        }
        for figure in figures.iter().take(4) {
            source.push_str(&format!(
                "![Original {}](svg/{}.svg)\n\n",
                figure.case, figure.case
            ));
        }
        let path = root.join("report.md");
        fs::write(&path, &source).unwrap();
        let (output, coverage) = import_document(
            &path,
            &parent,
            "report",
            "complete-reviewed-report",
            &figures,
        )
        .unwrap();
        assert!(output.find("## Reviewed report").unwrap() < output.find("- [Details]").unwrap());
        assert_eq!(coverage.source_headings.len(), 30);
        assert_eq!(coverage.table_body_rows, vec![1]);
        assert_eq!(coverage.source_image_count, 4);
        assert_eq!(
            parser(&output)
                .filter(|event| matches!(event, Event::Start(Tag::Image { .. })))
                .count(),
            32
        );
        assert!(output.contains("Preserve **every word** and `symbol<[u8; 64]>`."));
        assert!(output.contains("| 75.89% | 4.944 ms |"));
        assert!(output.contains("run%20with%20spaces/svg/"));
        assert_eq!(fs::read_to_string(&path).unwrap(), source);
    }

    #[test]
    fn reference_style_input_fails_closed_instead_of_rewriting_a_code_lookalike() {
        let temp = common::Temporary::new("Markdown references").unwrap();
        let path = temp.join("findings.md");
        fs::write(
            &path,
            "# Findings\n\n[external][ref]\n\n[ref]: https://example.invalid\n",
        )
        .unwrap();
        let error = import_document(&path, temp.path(), "findings", "complete-findings", &[])
            .unwrap_err()
            .to_string();
        assert!(error.contains("reference-style"));
    }

    #[test]
    fn svg_link_alone_does_not_satisfy_embed_coverage_and_changed_svg_is_rejected() {
        let temp = common::Temporary::new("Markdown image validation").unwrap();
        let parent = temp.path().canonicalize().unwrap();
        fs::write(parent.join("graph.svg"), "<svg/>").unwrap();
        fs::write(parent.join("preview.png"), "fixture").unwrap();
        let figure = Figure {
            case: Case::new("flock", "verify", 64).unwrap(),
            role: AttemptKind::Smoke,
            attempt_id: "flock-verify-0064-smoke-001".into(),
            attempt_path: "unused".into(),
            attempt_sha256: "unused".into(),
            episode: "Episode 1: original".into(),
            svg: "graph.svg".into(),
            svg_sha256: sha256(&parent.join("graph.svg")).unwrap(),
            png_fallback: "preview.png".into(),
            png_sha256: "unused".into(),
            anchor: "figure-smoke-flock-verify-0064".into(),
        };
        let path = parent.join("README.md");
        assert!(
            validate_links(
                &figure.links_and_caption(),
                &path,
                std::slice::from_ref(&figure)
            )
            .is_err()
        );
        assert!(validate_links(&figure.block(), &path, std::slice::from_ref(&figure)).is_ok());
        fs::write(parent.join("graph.svg"), "changed").unwrap();
        assert!(validate_links(&figure.block(), &path, &[figure]).is_err());
    }
}

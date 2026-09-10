//! Authoritative frame boundaries and sample occurrences from xctrace time-profile XML.

use crate::Result;
use quick_xml::{
    Reader,
    events::{BytesStart, Event},
};
use serde::Serialize;
use serde_json::Value;
use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

#[derive(Debug, Clone, Serialize, serde::Deserialize)]
pub struct Symbol {
    pub frame_id: String,
    pub raw_name: String,
    pub demangled_name: String,
    pub display_name: String,
    pub address: Option<String>,
}

#[derive(Debug, Clone, Serialize, serde::Deserialize)]
pub struct CollapseSummary {
    pub xml_rows: u64,
    pub verifier_thread: bool,
    pub usable_rows: u64,
    pub unique_backtraces: usize,
    pub unique_frames: usize,
    pub transformed_frames: usize,
    pub samples_with_transformed_frames: u64,
    pub spurious_separator_occurrences_removed: u64,
    pub maximum_real_stack_depth: usize,
}

pub struct Collapsed {
    pub stacks: BTreeMap<String, u64>,
    pub symbols: BTreeMap<String, Symbol>,
    pub summary: CollapseSummary,
}

pub(crate) fn attrs(element: &BytesStart<'_>) -> Result<BTreeMap<String, String>> {
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

pub fn collapse(input: impl BufRead) -> Result<Collapsed> {
    let mut reader = Reader::from_reader(input);
    let mut buffer = Vec::new();
    let mut symbols = BTreeMap::<String, Symbol>::new();
    let mut backtraces = BTreeMap::<String, Vec<String>>::new();
    let mut occurrences = BTreeMap::<String, u64>::new();
    let mut display_sources = BTreeMap::<String, String>::new();
    let mut row: Option<Option<String>> = None;
    let mut active_backtrace: Option<(String, Vec<String>)> = None;
    let mut rows = 0_u64;
    let mut verifier_thread = false;
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
                let attributes = attrs(&element)?;
                verifier_thread |= attributes
                    .values()
                    .any(|value| value.contains("flock-verify"));
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
        verifier_thread,
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

    #[test]
    fn unrelated_columns_retain_worker_evidence_but_nonempty_refs_are_invalid() -> Result<()> {
        let xml = r#"<trace-query-result><node><row><thread id="7" fmt="flock-verify"/><future-column value="anything"/><backtrace id="1"><frame id="2" name="leaf"/></backtrace></row><row><thread ref="7"/><backtrace id="3"><frame ref="2"/></backtrace></row></node></trace-query-result>"#;
        let parsed = collapse(Cursor::new(xml))?;
        assert!(parsed.summary.verifier_thread);
        assert_eq!(parsed.summary.usable_rows, 2);
        assert_eq!(parsed.stacks["leaf"], 2);
        assert!(
            collapse(Cursor::new(
                xml.replace("<frame ref=\"2\"/>", "<frame ref=\"2\"></frame>")
            ))
            .is_err()
        );
        Ok(())
    }
}

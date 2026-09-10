//! One-time editorial finalization; never launches a measured workload.
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, error::Error, fs, io::Read, path::Path};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn digest(path: &Path) -> Result<String> {
    let mut file = fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut bytes = [0_u8; 65536];
    loop {
        let count = file.read(&mut bytes)?;
        if count == 0 {
            break;
        }
        hasher.update(&bytes[..count]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn json_file(path: &Path) -> Result<Value> {
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}

fn write_json(path: &Path, value: &Value) -> Result<()> {
    let temp = path.with_extension("json.finalizing");
    fs::write(&temp, serde_json::to_vec_pretty(value)?)?;
    fs::rename(temp, path)?;
    Ok(())
}

fn walk(root: &Path, path: &Path, entries: &mut BTreeMap<String, Value>) -> Result<()> {
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let relative = entry
            .path()
            .strip_prefix(root)?
            .to_str()
            .ok_or("non-Unicode path")?
            .to_owned();
        if matches!(relative.as_str(), "artifacts.json" | "complete.json") {
            continue;
        }
        let kind = entry.file_type()?;
        if kind.is_dir() {
            walk(root, &entry.path(), entries)?;
        } else if kind.is_file() {
            entries.insert(
                relative,
                json!({"bytes":entry.metadata()?.len(),"sha256":digest(&entry.path())?}),
            );
        } else {
            return Err("unsupported report file type".into());
        }
    }
    Ok(())
}

fn links(root: &Path) -> Result<usize> {
    let mut count = 0;
    for (file, markers, closing) in [
        ("report.md", vec!["]("], ')'),
        ("findings.md", vec!["]("], ')'),
        ("index.html", vec!["href=\"", "src=\""], '"'),
    ] {
        let contents = fs::read_to_string(root.join(file))?;
        for marker in markers {
            for rest in contents.split(marker).skip(1) {
                let target = rest.split(closing).next().ok_or("unterminated link")?;
                if target.starts_with("https://") || target.starts_with("http://") {
                    continue;
                }
                let path = target.split('#').next().ok_or("invalid link")?;
                if path.is_empty() {
                    continue;
                }
                if !root.join(path).exists() {
                    return Err(format!("broken link in {file}: {target}").into());
                }
                count += 1;
            }
        }
    }
    Ok(count)
}

fn main() -> Result<()> {
    let root = std::env::args_os()
        .nth(1)
        .ok_or("expected report directory")?;
    let root = Path::new(&root).canonicalize()?;
    if root.join("editorial-review.json").exists() || root.join("artifacts-generated.json").exists()
    {
        return Err("editorial finalization already exists".into());
    }
    let complete = json_file(&root.join("complete.json"))?;
    let processing = json_file(&root.join("report-processing.json"))?;
    if complete["primary_svgs"] != 28
        || processing["status"] != "complete"
        || processing["attempts"]
            .as_array()
            .ok_or("missing attempts")?
            .len()
            != 44
    {
        return Err("report processing is not complete".into());
    }
    let old = json_file(&root.join("artifacts.json"))?;
    if old["files"]["report.md"]["sha256"] != digest(&root.join("report-generated.md"))? {
        return Err("preserved generated report does not match original inventory".into());
    }
    let manifest = json_file(&root.join("manifest.json"))?;
    let module = "crates/flock-core/src/lincheck.rs";
    let original_module = Path::new(
        manifest["snapshot"]["root"]
            .as_str()
            .ok_or("snapshot root missing")?,
    )
    .join(module);
    let copied_module = root.join("source/locations").join(module);
    if digest(&original_module)? != digest(&copied_module)? {
        return Err("source mapping differs from measured source".into());
    }
    fs::copy(
        root.join("artifacts.json"),
        root.join("artifacts-generated.json"),
    )?;
    let own = std::env::current_exe()?.canonicalize()?;
    let mut record = json!({
        "schema_version":1,"status":"in_progress","kind":"post-generation editorial review",
        "measurement_snapshot_id":manifest["snapshot"]["id"],
        "generated_report":{"path":"report-generated.md","sha256":digest(&root.join("report-generated.md"))?},
        "reviewed_report":{"path":"report.md","sha256":digest(&root.join("report.md"))?},
        "findings":{"path":"findings.md","sha256":digest(&root.join("findings.md"))?},
        "changes":["Disclose battery primary/small repeats and AC resumed large repeats prominently.","Clarify that the backtrace-row denominator applies to hotspot percentages.","Add reviewed hotspot findings, CSC source mapping and concrete follow-up experiments."],
        "additional_source":{"path":"source/locations/crates/flock-core/src/lincheck.rs","sha256":digest(&copied_module)?},
        "recordings_and_generated_metrics_changed":false,
        "pre_editorial_inventory":"artifacts-generated.json",
        "finalizer":{"path":own,"sha256":digest(&own)?,"source":"editorial-finalize.rs","source_sha256":digest(&root.join("editorial-finalize.rs"))?},
        "verification":"Every previously inventoried file except reviewed report.md must retain its exact checksum. The preserved generated report must equal that file's original checksum. The final inventory covers all report files except its own index and the completion marker."
    });
    write_json(&root.join("editorial-review.json"), &record)?;
    let linked_targets = links(&root)?;
    let mut current = BTreeMap::new();
    walk(&root, &root, &mut current)?;
    for (name, before) in old["files"].as_object().ok_or("invalid inventory")? {
        if name != "report.md" && current.get(name) != Some(before) {
            return Err(
                format!("unexpected evidence change during editorial review: {name}").into(),
            );
        }
    }
    record["status"] = json!("complete");
    record["local_link_targets_checked"] = json!(linked_targets);
    write_json(&root.join("editorial-review.json"), &record)?;
    current.insert(
        "editorial-review.json".into(),
        json!({
            "bytes":fs::metadata(root.join("editorial-review.json"))?.len(),
            "sha256":digest(&root.join("editorial-review.json"))?
        }),
    );
    write_json(
        &root.join("artifacts.json"),
        &json!({"schema_version":1,"exclusions":["artifacts.json","complete.json"],"files":current}),
    )?;
    println!(
        "Validated {linked_targets} local links; {} files inventoried; all original evidence unchanged.",
        current.len()
    );
    Ok(())
}

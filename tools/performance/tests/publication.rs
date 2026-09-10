mod common;

use common::{Temporary, init_git, remove_sealed};
use flock_performance::{
    Result, atomic_json, environment_keys, evidence, publication, records, report, snapshot,
    xctrace,
};
use serde_json::json;
use std::{fs, io::Cursor, path::PathBuf};

struct Fixture {
    base: Temporary,
    evidence: PathBuf,
    processor: snapshot::ProcessorIdentity,
}
impl Fixture {
    fn new() -> Result<Self> {
        let base = Temporary::new("publication complete fixture")?;
        let edit = base.join("editing source");
        fs::create_dir_all(edit.join("tools/performance"))?;
        fs::create_dir_all(edit.join("crates/flock-prover/examples"))?;
        fs::write(edit.join("Cargo.toml"), "[workspace]\nmembers=[]\n")?;
        fs::write(
            edit.join("Cargo.lock"),
            "version = 4\n[[package]]\nname = \"inferno\"\nversion = \"0.12.6\"\n",
        )?;
        fs::write(
            edit.join("crates/flock-prover/examples/preimage_scaling.rs"),
            "// independent fixture source\n",
        )?;
        atomic_json(
            &edit.join("tools/performance/measurement-env.json"),
            &environment_keys(),
        )?;
        init_git(&edit).map_err(|error| {
            format!(
                "initializing publication fixture {}: {error}",
                edit.display()
            )
        })?;
        let evidence = base.join("legacy evidence");
        let source = snapshot::prepare(&edit, &evidence).map_err(|error| {
            format!(
                "preparing publication fixture snapshot for {}: {error}",
                evidence.display()
            )
        })?;
        let processor = snapshot::ProcessorIdentity::register(
            &source,
            &evidence.join("source"),
            &std::env::current_exe()?,
        )
        .map_err(|error| {
            format!(
                "registering publication fixture processor {}: {error}",
                source.root.display()
            )
        })?;
        let fixture = Self {
            base,
            evidence,
            processor,
        };
        fixture.populate().map_err(|error| {
            format!(
                "populating publication fixture {}: {error}",
                fixture.evidence.display()
            )
        })?;
        Ok(fixture)
    }

    fn populate(&self) -> Result<()> {
        let manifest = json!({"schema_version":1,"snapshot":self.processor.snapshot,"artifacts":{"preimage_profile":self.processor.executable},"environment":{"measurement_environment_removed":environment_keys(),"cpu":{"stdout":"fixture CPU"},"memory":{"stdout":"1000"},"toolchain":"fixture","profiler":"fixture"},"branch":"fixture","revision":"fixture"});
        atomic_json(&self.evidence.join("manifest.json"), &manifest)?;
        atomic_json(
            &self.evidence.join("complete.json"),
            &json!({"primary_svgs":28}),
        )?;
        fs::write(
            self.evidence.join("report.md"),
            "Original reviewed report must stay unchanged.\n",
        )?;
        fs::write(
            self.evidence.join("findings.md"),
            "Reviewed findings: [baseline](baseline-before.csv).\n",
        )?;
        let mut baseline = String::from(
            "hashes,protocol,prove_ms_median,verify_ms_median,proof_bytes_median,proof_bytes_min,proof_bytes_max\n",
        );
        for n in records::SIZES {
            for protocol in ["FLOCK-non-ZK-Secure", "VEIL-FLOCK-full-ZK"] {
                baseline.push_str(&format!("{n},{protocol},1,2,100,100,100\n"));
            }
        }
        for name in [
            "baseline-before.csv",
            "baseline-after.csv",
            "baseline-symbols.csv",
        ] {
            fs::write(self.evidence.join(name), &baseline)?;
        }
        for kind in [
            records::AttemptKind::Smoke,
            records::AttemptKind::Primary,
            records::AttemptKind::Repeat,
        ] {
            for case in if kind == records::AttemptKind::Primary {
                records::all_cases()
            } else {
                records::endpoints()
            } {
                let path = self
                    .evidence
                    .join("cases")
                    .join(case.id())
                    .join(format!("{}-001", kind.as_str()));
                fs::create_dir_all(path.join("raw/recording.trace"))?;
                let count = if kind == records::AttemptKind::Primary {
                    10_000
                } else {
                    1
                };
                let mut xml = String::from(
                    "<trace-query-result><node><row><thread fmt=\"flock-verify\"/><backtrace id=\"1\"><frame id=\"1\" name=\"flock_core::verifier::verify_core_inner&lt;[u8; 64]&gt;\"/><frame id=\"2\" name=\"rayon_core::worker\"/></backtrace></row>",
                );
                for _ in 1..count {
                    xml.push_str("<row><backtrace ref=\"1\"/></row>");
                }
                xml.push_str("</node></trace-query-result>");
                fs::write(path.join("raw/time-profile.xml"), &xml)?;
                let stats = report::analyze_resolved(&xctrace::collapse(Cursor::new(xml))?)?;
                fs::write(
                    path.join("stacks.folded"),
                    format!(
                        "rayon_core::worker;flock_core::verifier::verify_core_inner<[u8; 64]> {count}\n"
                    ),
                )?;
                fs::write(path.join("flamegraph.svg"), "<svg><rect/><rect/></svg>")?;
                fs::write(path.join("preview.png"), "fixture placeholder")?;
                atomic_json(&path.join("analysis.json"), &stats)?;
                let id = format!("{}-{}-001", case.id(), kind.as_str());
                let seconds = if kind == records::AttemptKind::Smoke {
                    5.0
                } else {
                    30.0
                };
                let scope = if case.operation == records::Operation::Prove {
                    "warm-up and final proof"
                } else {
                    "entire corpus, every loop call, and final verification"
                };
                let harness = json!({"schema_version":1,"process_id":1,"attempt_id":id,"protocol":case.protocol,"operation":case.operation,"hashes":case.hashes,"requested_seconds":seconds,"loop_seconds":seconds,"completed_calls":1,"final_validation":true,"environment_absent":true,"environment_keys":environment_keys(),"thread_count":4,"verifier_thread_count":1,"corpus_size":if case.operation==records::Operation::Prove {1}else{8},"preparation_seconds":0.0,"validation_seconds":0.0,"cleanup_seconds":0.0,"validation_scope":scope});
                atomic_json(&path.join("harness.json"), &harness)?;
                let power = json!({"power":{"success":true,"stdout":"Now drawing from 'Battery Power'\n -InternalBattery 50%; discharging"}});
                let attempt = json!({"attempt_id":id,"kind":kind,"protocol":case.protocol,"operation":case.operation,"hashes":case.hashes,"requested_seconds":seconds,"snapshot_id":self.processor.snapshot.id,"executable":self.processor.executable,"status":"validated","promoted":kind==records::AttemptKind::Primary,"stats":stats,"load_before":power,"load_after":power});
                atomic_json(&path.join("attempt.json"), &attempt)?;
                for stage in ["record", "export"] {
                    atomic_json(
                        &path.join(format!("{stage}-status.json")),
                        &json!({"attempt_id":id,"stage":stage,"exit_code":0,"signal":null,"io_ok":true,"success":true,"error":null}),
                    )?;
                }
            }
        }
        Ok(())
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        remove_sealed(&self.processor.snapshot.root);
    }
}

#[test]
fn full_legacy_publication_corrects_frames_without_mutating_inputs_or_reviewed_content()
-> Result<()> {
    let fixture = Fixture::new()?;
    // Use a small resumed case so membership cannot be inferred from case size.
    let original = "cases/flock-prove-0064/primary-001/attempt.json";
    atomic_json(
        &fixture.evidence.join("resume-controller/manifest.json"),
        &json!({"preserved_evidence":{original:{"sha256":flock_performance::sha256(&fixture.evidence.join(original))?}}}),
    )?;
    atomic_json(
        &fixture.evidence.join("resume.json"),
        &json!({"schema_version":1,"status":"measurements_complete","controller_manifest":"resume-controller/manifest.json","new_repeats":[{"case":"flock-prove-0064","attempt":"repeat-001"}]}),
    )?;
    fs::copy(
        fixture.evidence.join("baseline-before.csv"),
        fixture.evidence.join("baseline-resume-before.csv"),
    )?;
    evidence::write_inventory(&fixture.evidence, &["artifacts.json", "complete.json"])?;
    let before = evidence::inventory(&fixture.evidence, &[])?;
    let output = fixture.base.join("new publication");
    assert!(
        publication::publish(
            &fixture.evidence,
            &fixture.evidence.join("nested"),
            None,
            &fixture.processor
        )
        .is_err()
    );
    let gallery = publication::publish(&fixture.evidence, &output, None, &fixture.processor)
        .map_err(|error| format!("publishing first legacy generation: {error}"))?;
    let generation = gallery.parent().unwrap();
    assert_eq!(fs::read_dir(generation.join("svg"))?.count(), 28);
    let folded =
        fs::read_to_string(generation.join("cases/flock-prove-0064/primary-001/stacks.folded"))?;
    assert!(folded.contains("<[u8； 64]>"));
    assert!(!folded.contains("[u8; 64]"));
    assert_eq!(
        fs::read_to_string(generation.join("findings-source.md"))?,
        fs::read_to_string(fixture.evidence.join("findings.md"))?
    );
    assert!(fs::read_to_string(generation.join("report.md"))?.contains("88 battery"));
    assert!(
        fs::read_to_string(generation.join("report.md"))?.contains("different recorded episodes")
    );
    let episodes: serde_json::Value = serde_json::from_slice(&fs::read(
        generation.join("legacy-episode-membership.json"),
    )?)?;
    assert_eq!(episodes["flock-prove-0064-primary-001"], "legacy-original");
    assert_eq!(episodes["flock-prove-0064-repeat-001"], "legacy-resumed");
    evidence::verify_inventory(&fixture.evidence, &before)?;
    assert_eq!(publication::current(&output)?, gallery);
    // Authored input edits create a new generation, while the original
    // generation remains usable and retains its immutable authored bytes.
    let changed = fixture.base.join("updated findings.md");
    fs::write(&changed, "A separate reviewed interpretation.\n")?;
    let next = publication::publish(
        &fixture.evidence,
        &output,
        Some(&changed),
        &fixture.processor,
    )
    .map_err(|error| format!("publishing revised legacy generation: {error}"))?;
    assert_ne!(next, gallery);
    assert_eq!(
        fs::read_to_string(generation.join("findings-source.md"))?,
        fs::read_to_string(fixture.evidence.join("findings.md"))?
    );
    evidence::verify_inventory(&fixture.evidence, &before)?;
    Ok(())
}

#[test]
fn unchanged_v1_manifest_with_v2_continuation_uses_episode_controls() -> Result<()> {
    let fixture = Fixture::new()?;
    let manifest_before = fs::read(fixture.evidence.join("manifest.json"))?;
    let original_before = fs::read(fixture.evidence.join("baseline-before.csv"))?;
    // Model an interrupted legacy run with no closing baseline and a retained
    // resume marker which never produced a legacy resume-before CSV.
    fs::remove_file(fixture.evidence.join("baseline-after.csv"))?;
    fs::remove_file(fixture.evidence.join("complete.json"))?;
    atomic_json(
        &fixture.evidence.join("resume.json"),
        &json!({"schema_version":1,"status":"interrupted"}),
    )?;
    let id = "episode-new-controller";
    let relative = PathBuf::from("episodes").join(id);
    let directory = fixture.evidence.join(&relative);
    fs::create_dir_all(&directory)?;
    let observation =
        flock_performance::host::PowerObservation::parse("Now drawing from 'Battery Power'\n");
    let mut episode = json!({"schema_version":2,"id":id,"status":"complete","started_unix_seconds":100.0,"power_policy":null});
    for (key, label) in [
        ("before_baseline", "baseline-before"),
        ("symbols_baseline", "baseline-symbols"),
        ("after_baseline", "baseline-after"),
    ] {
        let path = directory.join(format!("{label}.csv"));
        fs::write(&path, &original_before)?;
        atomic_json(
            &directory.join(format!("{label}.stage.json")),
            &json!({"schema_version":2,"episode_id":id,"status":"accepted","power_before":observation,"power_after":observation,"csv":records::ArtifactIdentity::register(&path)?}),
        )?;
        episode[key] = json!(relative.join(format!("{label}.csv")));
    }
    atomic_json(&directory.join("episode.json"), &episode)?;
    atomic_json(
        &fixture.evidence.join("measurements-complete.json"),
        &json!({"schema_version":2,"primary_svgs":28,"episode_id":id}),
    )?;
    let attempt_dir = fixture.evidence.join("cases/flock-prove-0064/primary-001");
    let mut attempt: serde_json::Value =
        serde_json::from_slice(&fs::read(attempt_dir.join("attempt.json"))?)?;
    attempt["schema_version"] = json!(2);
    attempt["selected"] = json!(true);
    attempt["episode_id"] = json!(id);
    attempt["power_before"] = json!(observation);
    attempt["power_after"] = json!(observation);
    attempt["evidence_inventory"] =
        serde_json::to_value(evidence::inventory(&attempt_dir, &["attempt.json"])?)?;
    atomic_json(&attempt_dir.join("attempt.json"), &attempt)?;
    let before = evidence::inventory(&fixture.evidence, &[])?;
    let gallery = publication::publish(
        &fixture.evidence,
        &fixture.base.join("mixed publication"),
        None,
        &fixture.processor,
    )
    .map_err(|error| format!("publishing mixed legacy/v2 generation: {error}"))?;
    let generation = gallery.parent().unwrap();
    let report = fs::read_to_string(generation.join("report.md"))?;
    assert!(report.contains("before control: `episode-new-controller`"));
    assert!(report.contains("do not close the earlier legacy capture interval"));
    assert!(!generation.join("baseline-resume-before.csv").exists());
    assert_eq!(
        fs::read(generation.join("legacy-controls/baseline-before.csv"))?,
        original_before
    );
    assert_eq!(
        fs::read(fixture.evidence.join("manifest.json"))?,
        manifest_before
    );
    evidence::verify_inventory(&fixture.evidence, &before)?;
    assert_eq!(
        publication::current(&fixture.base.join("mixed publication"))?,
        gallery
    );
    Ok(())
}

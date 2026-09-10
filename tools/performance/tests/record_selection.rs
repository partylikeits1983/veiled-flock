mod common;

use common::Temporary;
use flock_performance::records::{
    self, AcceptancePolicy, ArtifactIdentity, AttemptKind, Case, SelectionEntry, SelectionIndex,
};
use flock_performance::{Result, environment_keys, sha256};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

fn attempt(
    root: &Path,
    executable: &ArtifactIdentity,
    number: usize,
    rows: u64,
    version_two: bool,
) -> Result<PathBuf> {
    let dir = root.join(format!("cases/flock-prove-0064/primary-{number:03}"));
    fs::create_dir_all(dir.join("raw/recording.trace"))?;
    let id = format!("flock-prove-0064-primary-{number:03}");
    let mut harness: Value = serde_json::from_str(include_str!("fixtures/harness-v1.json"))?;
    harness["attempt_id"] = json!(id);
    harness["requested_seconds"] = json!(30.0);
    harness["loop_seconds"] = json!(30.1);
    fs::write(dir.join("harness.json"), serde_json::to_vec(&harness)?)?;
    for stage in ["record", "export"] {
        fs::write(
            dir.join(format!("{stage}-status.json")),
            serde_json::to_vec(
                &json!({"attempt_id":id,"stage":stage,"success":true,"io_ok":true,"exit_code":0,"signal":null,"error":null}),
            )?,
        )?;
    }
    for name in [
        "raw/time-profile.xml",
        "stacks.folded",
        "flamegraph.svg",
        "preview.png",
        "analysis.json",
    ] {
        fs::write(dir.join(name), "fixture bytes")?;
    }
    let mut record = json!({"attempt_id":id,"kind":"primary","protocol":"flock","operation":"prove","hashes":64,"requested_seconds":30.0,"snapshot_id":"snapshot-a","executable":executable,"status":"validated","promoted":rows>=10_000,"stats":{"usable_rows":rows,"total_weight":rows,"has_workload_symbols":true,"has_verifier_worker":false,"has_rayon_worker":false}});
    if version_two {
        record["schema_version"] = json!(2);
        record["selected"] = json!(rows >= 10_000);
    }
    fs::write(dir.join("attempt.json"), serde_json::to_vec(&record)?)?;
    Ok(dir)
}

fn executable(root: &Path) -> Result<ArtifactIdentity> {
    let path = root.join("harness");
    fs::write(&path, "registered fixture executable")?;
    ArtifactIdentity::register(&path)
}

#[test]
fn legacy_low_sample_primary_is_retained_before_unique_promoted_retry() -> Result<()> {
    let temp = Temporary::new("legacy-selection")?;
    let executable = executable(temp.path())?;
    let low = attempt(temp.path(), &executable, 1, 20, false)?;
    let before = sha256(&low.join("attempt.json"))?;
    let high = attempt(temp.path(), &executable, 2, 12_000, false)?;
    let selected = records::selected_attempts(
        temp.path(),
        AttemptKind::Primary,
        "snapshot-a",
        &executable,
        &environment_keys(),
        AcceptancePolicy::LegacyV1,
    )?;
    assert_eq!(selected.len(), 1);
    assert_eq!(selected.values().next().unwrap().dir, high);
    assert_eq!(before, sha256(&low.join("attempt.json"))?);
    assert!(records::require_matrix(&selected, &records::all_cases()).is_err());
    attempt(temp.path(), &executable, 3, 12_000, false)?;
    assert!(
        records::selected_attempts(
            temp.path(),
            AttemptKind::Primary,
            "snapshot-a",
            &executable,
            &environment_keys(),
            AcceptancePolicy::LegacyV1
        )
        .is_err()
    );
    Ok(())
}

#[test]
fn selection_index_is_authoritative_and_scheduler_recovers_missing_publication() -> Result<()> {
    let temp = Temporary::new("selection-recovery")?;
    let executable = executable(temp.path())?;
    let failed = temp.join("cases/flock-prove-0064/primary-001");
    fs::create_dir_all(&failed)?;
    fs::write(
        failed.join("attempt.json"),
        "{\"status\":\"incomplete\",\"error\":\"interrupted\"}",
    )?;
    let failed_hash = sha256(&failed.join("attempt.json"))?;
    let high = attempt(temp.path(), &executable, 2, 12_000, true)?;
    assert!(
        records::selected_attempts(
            temp.path(),
            AttemptKind::Primary,
            "snapshot-a",
            &executable,
            &environment_keys(),
            AcceptancePolicy::NewRun
        )?
        .is_empty()
    );
    let recovered = records::recover_selected_attempts(
        temp.path(),
        AttemptKind::Primary,
        "snapshot-a",
        &executable,
        &environment_keys(),
        AcceptancePolicy::NewRun,
    )?;
    assert_eq!(recovered.len(), 1);
    let case = Case::new("flock", "prove", 64)?;
    let entry = SelectionEntry {
        attempt_id: recovered[&case].attempt.attempt_id.clone(),
        path: high.strip_prefix(temp.path())?.to_owned(),
        sha256: sha256(&high.join("attempt.json"))?,
    };
    let mut index = SelectionIndex {
        schema_version: 2,
        selected: BTreeMap::from([(format!("primary/{case}"), entry)]),
    };
    fs::write(temp.join("selection.json"), serde_json::to_vec(&index)?)?;
    assert_eq!(
        records::selected_attempts(
            temp.path(),
            AttemptKind::Primary,
            "snapshot-a",
            &executable,
            &environment_keys(),
            AcceptancePolicy::NewRun
        )?
        .len(),
        1
    );

    // A second episode completes another distinct slot before updating its
    // selection index. Recovery must preserve the earlier selection exactly.
    let second = attempt(temp.path(), &executable, 3, 13_000, true)?;
    let second_case = Case::new("flock", "prove", 128)?;
    let second_parent = temp.join(format!("cases/{second_case}"));
    fs::create_dir_all(&second_parent)?;
    let second_target = second_parent.join("primary-003");
    fs::rename(&second, &second_target)?;
    for name in [
        "attempt.json",
        "harness.json",
        "record-status.json",
        "export-status.json",
    ] {
        let path = second_target.join(name);
        let mut value: Value = serde_json::from_slice(&fs::read(&path)?)?;
        value["attempt_id"] = json!("flock-prove-0128-primary-003");
        if value.get("hashes").is_some() {
            value["hashes"] = json!(128);
        }
        fs::write(path, serde_json::to_vec(&value)?)?;
    }
    let recovered = records::recover_selected_attempts(
        temp.path(),
        AttemptKind::Primary,
        "snapshot-a",
        &executable,
        &environment_keys(),
        AcceptancePolicy::NewRun,
    )?;
    assert_eq!(recovered.len(), 2);
    assert_eq!(
        records::selected_attempts(
            temp.path(),
            AttemptKind::Primary,
            "snapshot-a",
            &executable,
            &environment_keys(),
            AcceptancePolicy::NewRun
        )?
        .len(),
        1
    );
    index.selected.insert(
        format!("primary/{second_case}"),
        SelectionEntry {
            attempt_id: recovered[&second_case].attempt.attempt_id.clone(),
            path: second_target.strip_prefix(temp.path())?.to_owned(),
            sha256: sha256(&second_target.join("attempt.json"))?,
        },
    );
    fs::write(temp.join("selection.json"), serde_json::to_vec(&index)?)?;
    assert_eq!(
        records::selected_attempts(
            temp.path(),
            AttemptKind::Primary,
            "snapshot-a",
            &executable,
            &environment_keys(),
            AcceptancePolicy::NewRun
        )?
        .len(),
        2
    );
    assert_eq!(failed_hash, sha256(&failed.join("attempt.json"))?);
    fs::write(
        high.join("attempt.json"),
        fs::read_to_string(high.join("attempt.json"))? + " ",
    )?;
    assert!(
        records::recover_selected_attempts(
            temp.path(),
            AttemptKind::Primary,
            "snapshot-a",
            &executable,
            &environment_keys(),
            AcceptancePolicy::NewRun
        )
        .is_err()
    );
    Ok(())
}

#[test]
fn accepted_v2_inventory_rejects_raw_tampering_and_legacy_absence_is_readable() -> Result<()> {
    let temp = Temporary::new("selection-evidence")?;
    let executable = executable(temp.path())?;
    let dir = attempt(temp.path(), &executable, 1, 12_000, false)?;
    let mut selected = records::selected_attempts(
        temp.path(),
        AttemptKind::Primary,
        "snapshot-a",
        &executable,
        &environment_keys(),
        AcceptancePolicy::LegacyV1,
    )?
    .into_values()
    .next()
    .unwrap();
    records::verify_attempt_evidence(&selected)?;
    selected.attempt.schema_version = Some(2);
    assert!(records::verify_attempt_evidence(&selected).is_err());
    let inventory = flock_performance::evidence::inventory(&dir, &["attempt.json"])?;
    selected.attempt.extra.insert(
        "evidence_inventory".into(),
        serde_json::to_value(&inventory)?,
    );
    records::verify_attempt_evidence(&selected)?;
    fs::write(
        dir.join("raw/time-profile.xml"),
        "tampered raw trace export",
    )?;
    assert!(records::verify_attempt_evidence(&selected).is_err());
    let mut permissive = inventory;
    permissive.exclusions.push("raw".into());
    selected.attempt.extra.insert(
        "evidence_inventory".into(),
        serde_json::to_value(permissive)?,
    );
    assert!(records::verify_attempt_evidence(&selected).is_err());
    Ok(())
}

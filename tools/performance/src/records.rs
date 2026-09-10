//! Versioned measurement records, semantic validation and exact case selection.

use crate::{Result, StageStatus, sha256};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

pub const SIZES: [usize; 7] = [64, 128, 256, 512, 1024, 2048, 4096];

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Protocol {
    Flock,
    FullZk,
}

impl Protocol {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Flock => "flock",
            Self::FullZk => "full-zk",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Operation {
    Prove,
    Verify,
}

impl Operation {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Prove => "prove",
            Self::Verify => "verify",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum AttemptKind {
    Smoke,
    Primary,
    Repeat,
}

impl AttemptKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Smoke => "smoke",
            Self::Primary => "primary",
            Self::Repeat => "repeat",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Case {
    pub protocol: Protocol,
    pub operation: Operation,
    pub hashes: usize,
}

impl Case {
    pub fn new(protocol: &str, operation: &str, hashes: usize) -> Result<Self> {
        let protocol = match protocol {
            "flock" => Protocol::Flock,
            "full-zk" => Protocol::FullZk,
            _ => return Err("unsupported protocol".into()),
        };
        let operation = match operation {
            "prove" => Operation::Prove,
            "verify" => Operation::Verify,
            _ => return Err("unsupported operation".into()),
        };
        if !SIZES.contains(&hashes) {
            return Err("unsupported hash count".into());
        }
        Ok(Self {
            protocol,
            operation,
            hashes,
        })
    }

    pub fn id(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for Case {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}-{}-{:04}",
            self.protocol.as_str(),
            self.operation.as_str(),
            self.hashes
        )
    }
}

pub fn all_cases() -> Vec<Case> {
    SIZES
        .into_iter()
        .flat_map(|hashes| {
            [Protocol::Flock, Protocol::FullZk]
                .into_iter()
                .flat_map(move |protocol| {
                    [Operation::Prove, Operation::Verify]
                        .into_iter()
                        .map(move |operation| Case {
                            protocol,
                            operation,
                            hashes,
                        })
                })
        })
        .collect()
}

pub fn endpoints() -> Vec<Case> {
    all_cases()
        .into_iter()
        .filter(|case| [64, 4096].contains(&case.hashes))
        .collect()
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ArtifactIdentity {
    pub path: PathBuf,
    pub sha256: String,
}

impl ArtifactIdentity {
    pub fn register(path: &Path) -> Result<Self> {
        Ok(Self {
            path: path.canonicalize()?,
            sha256: sha256(path)?,
        })
    }

    pub fn verify(&self) -> Result<()> {
        if !self.path.is_absolute()
            || self.path.canonicalize()? != self.path
            || sha256(&self.path)? != self.sha256
        {
            return Err(format!("registered artifact changed: {}", self.path.display()).into());
        }
        Ok(())
    }
}

/// Deliberately independent of the example's producer type. Required v1 fields
/// have no defaults; future optional episode facts belong to attempt records.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct HarnessMetadata {
    pub schema_version: u32,
    pub process_id: u32,
    pub attempt_id: String,
    pub protocol: Protocol,
    pub operation: Operation,
    pub hashes: usize,
    pub requested_seconds: f64,
    pub loop_seconds: f64,
    pub completed_calls: u64,
    pub final_validation: bool,
    pub environment_absent: bool,
    pub environment_keys: Vec<String>,
    pub thread_count: usize,
    pub verifier_thread_count: usize,
    pub corpus_size: usize,
    pub preparation_seconds: f64,
    pub validation_seconds: f64,
    pub cleanup_seconds: f64,
    pub validation_scope: String,
}

impl HarnessMetadata {
    pub fn validate(
        &self,
        case: &Case,
        attempt_id: &str,
        seconds: f64,
        policy: &[String],
    ) -> Result<()> {
        let scope = match case.operation {
            Operation::Prove => "warm-up and final proof",
            Operation::Verify => "entire corpus, every loop call, and final verification",
        };
        let phases = [
            self.preparation_seconds,
            self.validation_seconds,
            self.cleanup_seconds,
        ];
        let unique_policy: BTreeSet<_> = policy.iter().collect();
        if self.schema_version != 1
            || self.process_id == 0
            || attempt_id.is_empty()
            || self.attempt_id != attempt_id
            || self.protocol != case.protocol
            || self.operation != case.operation
            || self.hashes != case.hashes
            || !SIZES.contains(&case.hashes)
            || !seconds.is_finite()
            || seconds <= 0.0
            || self.requested_seconds != seconds
            || !self.loop_seconds.is_finite()
            || self.loop_seconds < seconds
            || self.completed_calls == 0
            || !self.final_validation
            || !self.environment_absent
            || self.environment_keys != policy
            || policy.is_empty()
            || policy.iter().any(String::is_empty)
            || unique_policy.len() != policy.len()
            || self.thread_count == 0
            || self.verifier_thread_count != 1
            || self.corpus_size
                != if case.operation == Operation::Prove {
                    1
                } else {
                    8
                }
            || phases
                .iter()
                .any(|phase| !phase.is_finite() || *phase < 0.0)
            || self.validation_scope != scope
        {
            return Err("harness metadata violates the v1 measurement contract".into());
        }
        Ok(())
    }
}

pub fn read_harness(
    path: &Path,
    case: &Case,
    attempt_id: &str,
    seconds: f64,
    policy: &[String],
) -> Result<HarnessMetadata> {
    let metadata: HarnessMetadata = serde_json::from_slice(&fs::read(path)?)?;
    metadata.validate(case, attempt_id, seconds, policy)?;
    Ok(metadata)
}

pub fn validate_stage(path: &Path, id: &str, stage: &str) -> Result<StageStatus> {
    let status: StageStatus = serde_json::from_slice(&fs::read(path)?)?;
    if status.attempt_id != id
        || status.stage != stage
        || !status.success
        || !status.io_ok
        || status.exit_code != Some(0)
        || status.signal.is_some()
        || status.error.is_some()
    {
        return Err(format!("{stage} wrapper status missing, failed, or mismatched").into());
    }
    Ok(status)
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SampleEvidence {
    pub usable_rows: u64,
    pub total_weight: u64,
    pub has_workload_symbols: bool,
    pub has_verifier_worker: bool,
    pub has_rayon_worker: bool,
    #[serde(flatten)]
    pub extra: BTreeMap<String, Value>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct AttemptRecord {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema_version: Option<u32>,
    pub attempt_id: String,
    pub kind: AttemptKind,
    pub protocol: Protocol,
    pub operation: Operation,
    pub hashes: usize,
    pub requested_seconds: f64,
    pub snapshot_id: String,
    pub executable: ArtifactIdentity,
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub promoted: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stats: Option<SampleEvidence>,
    #[serde(flatten)]
    pub extra: BTreeMap<String, Value>,
}

impl AttemptRecord {
    pub fn case(&self) -> Case {
        Case {
            protocol: self.protocol,
            operation: self.operation,
            hashes: self.hashes,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AcceptancePolicy {
    LegacyV1,
    NewRun,
}

#[derive(Clone, Debug, Serialize)]
pub struct SelectedAttempt {
    pub dir: PathBuf,
    pub attempt: AttemptRecord,
    pub harness: HarnessMetadata,
}

/// Verify the artifact anchor written when a v2 capture was accepted. This is
/// deliberately separate from selection: schedulers can scan slot metadata
/// without repeatedly hashing every retained trace during a long run.
pub fn verify_attempt_evidence(selected: &SelectedAttempt) -> Result<()> {
    verify_recorded_evidence(&selected.dir, &selected.attempt)
}

/// The same immutable artifact anchor applies to retained validated attempts
/// that did not meet the role's sample threshold and were not selected.
pub fn verify_recorded_evidence(dir: &Path, attempt: &AttemptRecord) -> Result<()> {
    if attempt
        .schema_version
        .is_some_and(|version| ![1, 2].contains(&version))
    {
        return Err("unsupported accepted attempt schema".into());
    }
    let Some(value) = attempt.extra.get("evidence_inventory") else {
        if attempt.schema_version == Some(2) {
            return Err("v2 accepted attempt has no evidence inventory".into());
        }
        return Ok(());
    };
    let inventory: crate::evidence::Inventory = serde_json::from_value(value.clone())?;
    if inventory.schema_version != 1 || inventory.exclusions != ["attempt.json"] {
        return Err("accepted attempt inventory has unsupported schema or exclusions".into());
    }
    crate::evidence::verify_inventory(dir, &inventory)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SelectionEntry {
    pub attempt_id: String,
    pub path: PathBuf,
    pub sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SelectionIndex {
    pub schema_version: u32,
    pub selected: BTreeMap<String, SelectionEntry>,
}

/// Validate retained recordings before selecting one candidate per exact slot.
/// Failed/missing records remain evidence and are never inferred successful.
pub fn selected_attempts(
    root: &Path,
    kind: AttemptKind,
    snapshot_id: &str,
    executable: &ArtifactIdentity,
    frozen_policy: &[String],
    acceptance: AcceptancePolicy,
) -> Result<BTreeMap<Case, SelectedAttempt>> {
    select(
        root,
        kind,
        snapshot_id,
        executable,
        frozen_policy,
        acceptance,
        false,
    )
}

/// Scheduler-only recovery of explicit completion declarations written before
/// a crash prevented publishing selection.json. The caller persists the result
/// before invoking publication; the publisher uses selected_attempts instead.
pub fn recover_selected_attempts(
    root: &Path,
    kind: AttemptKind,
    snapshot_id: &str,
    executable: &ArtifactIdentity,
    frozen_policy: &[String],
    acceptance: AcceptancePolicy,
) -> Result<BTreeMap<Case, SelectedAttempt>> {
    select(
        root,
        kind,
        snapshot_id,
        executable,
        frozen_policy,
        acceptance,
        true,
    )
}

fn select(
    root: &Path,
    kind: AttemptKind,
    snapshot_id: &str,
    executable: &ArtifactIdentity,
    frozen_policy: &[String],
    acceptance: AcceptancePolicy,
    recover: bool,
) -> Result<BTreeMap<Case, SelectedAttempt>> {
    let mut selected = BTreeMap::new();
    let index_path = root.join("selection.json");
    let index = if index_path.exists() {
        let index: SelectionIndex = serde_json::from_slice(&fs::read(index_path)?)?;
        if index.schema_version != 2 {
            return Err("unsupported selection index schema".into());
        }
        for (slot, entry) in &index.selected {
            if !["smoke/", "primary/", "repeat/"]
                .iter()
                .any(|prefix| slot.starts_with(prefix))
                || entry.path.is_absolute()
                || entry
                    .path
                    .components()
                    .any(|c| !matches!(c, std::path::Component::Normal(_)))
                || !entry.path.starts_with("cases")
            {
                return Err("invalid selection index slot or relative path".into());
            }
        }
        Some(index)
    } else {
        None
    };
    let cases = root.join("cases");
    if !cases.exists() {
        if index
            .as_ref()
            .is_some_and(|index| !index.selected.is_empty())
        {
            return Err("selected evidence is missing".into());
        }
        return Ok(selected);
    }
    for case_dir in fs::read_dir(cases)? {
        let case_dir = case_dir?;
        if !case_dir.file_type()?.is_dir() {
            return Err("case evidence must be an ordinary directory".into());
        }
        for entry in fs::read_dir(case_dir.path())? {
            let entry = entry?;
            if !entry.file_type()?.is_dir() {
                return Err("attempt evidence must be an ordinary directory".into());
            }
            let dir = entry.path();
            let path = dir.join("attempt.json");
            if !path.exists() {
                continue;
            }
            let value: Value = serde_json::from_slice(&fs::read(&path)?)?;
            if value["status"] != "validated" {
                continue;
            }
            let attempt: AttemptRecord = serde_json::from_value(value)?;
            if attempt.kind != kind {
                continue;
            }
            let case = attempt.case();
            let case_name = case_dir.file_name();
            let attempt_name = entry.file_name();
            let attempt_name = attempt_name.to_str().ok_or("non-Unicode attempt name")?;
            let number = attempt_name
                .strip_prefix(&format!("{}-", kind.as_str()))
                .and_then(|number| number.parse::<u64>().ok())
                .filter(|number| *number > 0)
                .ok_or("attempt directory lacks a positive numeric ID")?;
            if case_name != case.id().as_str()
                || attempt_name != format!("{}-{number:03}", kind.as_str())
                || attempt.attempt_id != format!("{case}-{attempt_name}")
                || !SIZES.contains(&case.hashes)
                || (kind != AttemptKind::Primary && ![64, 4096].contains(&case.hashes))
                || attempt.snapshot_id != snapshot_id
                || attempt.executable != *executable
                || attempt
                    .schema_version
                    .is_some_and(|version| ![1, 2].contains(&version))
                || (attempt.schema_version == Some(2) && attempt.selected.is_none())
                || (acceptance == AcceptancePolicy::NewRun
                    && (attempt.schema_version != Some(2) || attempt.selected.is_none()))
            {
                return Err(format!("invalid attempt identity: {}", path.display()).into());
            }
            let harness = read_harness(
                &dir.join("harness.json"),
                &case,
                &attempt.attempt_id,
                attempt.requested_seconds,
                frozen_policy,
            )?;
            for stage in ["record", "export"] {
                validate_stage(
                    &dir.join(format!("{stage}-status.json")),
                    &attempt.attempt_id,
                    stage,
                )?;
            }
            for file in [
                "raw/time-profile.xml",
                "stacks.folded",
                "flamegraph.svg",
                "preview.png",
                "analysis.json",
            ] {
                let metadata = fs::symlink_metadata(dir.join(file))?;
                if !metadata.is_file() || metadata.len() == 0 {
                    return Err(format!("missing or empty capture evidence: {file}").into());
                }
            }
            if !fs::symlink_metadata(dir.join("raw/recording.trace"))?.is_dir() {
                return Err("missing archived trace".into());
            }
            let stats = attempt
                .stats
                .as_ref()
                .ok_or("validated attempt lacks sample evidence")?;
            if stats.usable_rows == 0
                || stats.total_weight == 0
                || !stats.has_workload_symbols
                || (case.operation == Operation::Verify && !stats.has_verifier_worker)
                || (case.protocol == Protocol::FullZk
                    && case.operation == Operation::Prove
                    && !stats.has_rayon_worker)
            {
                return Err("validated recording lacks required sample or worker evidence".into());
            }
            let is_selected = attempt
                .selected
                .unwrap_or_else(|| kind != AttemptKind::Primary || attempt.promoted == Some(true));
            if kind == AttemptKind::Primary && is_selected != (attempt.promoted == Some(true)) {
                return Err("primary selection disagrees with promotion".into());
            }
            if let Some(index) = &index {
                let slot = format!("{}/{case}", kind.as_str());
                if let Some(entry) = index.selected.get(&slot) {
                    if entry.attempt_id != attempt.attempt_id {
                        if recover && is_selected {
                            return Err(
                                "ambiguous completion declaration conflicts with selected slot"
                                    .into(),
                            );
                        }
                        continue;
                    }
                    if entry.path != dir.strip_prefix(root)?
                        || sha256(&path)? != entry.sha256
                        || !is_selected
                    {
                        return Err("selected attempt path, hash or selection state changed".into());
                    }
                } else if !recover {
                    continue;
                }
            } else if acceptance == AcceptancePolicy::NewRun && !recover {
                // A crash between recording and index publication leaves an
                // unselected recording; directory order never promotes it.
                continue;
            }
            if !is_selected {
                continue;
            }
            let minimum_rows = if kind == AttemptKind::Primary
                || (acceptance == AcceptancePolicy::NewRun && kind == AttemptKind::Repeat)
            {
                10_000
            } else {
                1
            };
            let minimum_seconds = if acceptance == AcceptancePolicy::NewRun {
                if kind == AttemptKind::Smoke {
                    5.0
                } else {
                    30.0
                }
            } else {
                0.0
            };
            if stats.usable_rows < minimum_rows || attempt.requested_seconds < minimum_seconds {
                return Err(
                    "selected attempt does not satisfy its recorded acceptance policy".into(),
                );
            }
            if selected
                .insert(
                    case,
                    SelectedAttempt {
                        dir,
                        attempt,
                        harness,
                    },
                )
                .is_some()
            {
                return Err(
                    format!("ambiguous selected {} attempt for {case}", kind.as_str()).into(),
                );
            }
        }
    }
    if let Some(index) = &index {
        for (slot, entry) in &index.selected {
            if slot.starts_with(&format!("{}/", kind.as_str()))
                && !selected.values().any(|candidate| {
                    candidate.attempt.attempt_id == entry.attempt_id
                        && slot == &format!("{}/{}", kind.as_str(), candidate.attempt.case())
                })
            {
                return Err(format!(
                    "selection index refers to missing or invalid evidence: {slot}"
                )
                .into());
            }
        }
    }
    Ok(selected)
}

pub fn require_matrix(selected: &BTreeMap<Case, SelectedAttempt>, expected: &[Case]) -> Result<()> {
    let expected: BTreeSet<_> = expected.iter().copied().collect();
    let actual: BTreeSet<_> = selected.keys().copied().collect();
    if actual != expected {
        return Err(format!(
            "incomplete or unexpected case coverage: missing {:?}, unexpected {:?}",
            expected.difference(&actual).collect::<Vec<_>>(),
            actual.difference(&expected).collect::<Vec<_>>()
        )
        .into());
    }
    Ok(())
}

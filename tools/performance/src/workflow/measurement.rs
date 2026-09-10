//! Sequential, same-host measurement episodes. Existing evidence is never rewritten.
use super::*;
use records::{
    AcceptancePolicy, ArtifactIdentity, AttemptKind, Case, SelectedAttempt,
    SelectionEntry as Selection, SelectionIndex as State,
};

struct Bindings {
    measurement: Artifact,
    controller: Artifact,
}

impl Bindings {
    fn verify(&self) -> Result<()> {
        for (role, identity) in [
            ("measurement", &self.measurement),
            ("controller", &self.controller),
        ] {
            if sha256(&identity.path)? != identity.sha256 {
                return Err(format!("{role} manifest changed during the episode").into());
            }
        }
        Ok(())
    }
}

fn verify_manifest_role(path: &Path, expected: &Run, controller: bool) -> Result<()> {
    let mut value: Value = serde_json::from_slice(&fs::read(path)?)?;
    if controller && value.get("controller").is_some() {
        value = value["controller"].take();
    }
    let recorded: Run = serde_json::from_value(value)?;
    if serde_json::to_value(recorded)? != serde_json::to_value(expected)? {
        return Err(
            "measurement and controller manifest roles do not match the registered runs".into(),
        );
    }
    Ok(())
}

fn selection_key(kind: AttemptKind, case: &Case) -> String {
    format!("{}/{}", kind.as_str(), case.id())
}

fn selections(run: &Run, kind: AttemptKind) -> Result<BTreeMap<Case, SelectedAttempt>> {
    let executable = &run.artifacts["preimage_profile"];
    records::recover_selected_attempts(
        &run.output,
        kind,
        &run.snapshot.id,
        &ArtifactIdentity {
            path: executable.path.clone(),
            sha256: executable.sha256.clone(),
        },
        &frozen_policy(run)?,
        if run.schema_version == 1 {
            AcceptancePolicy::LegacyV1
        } else {
            AcceptancePolicy::NewRun
        },
    )
}

fn read_state(run: &Run) -> Result<State> {
    let path = run.output.join("selection.json");
    let mut state = if path.exists() {
        let state: State = serde_json::from_slice(&fs::read(&path)?)?;
        if state.schema_version != 2 {
            return Err("unsupported selection state".into());
        }
        state
    } else {
        State {
            schema_version: 2,
            selected: BTreeMap::new(),
        }
    };
    let mut observed = BTreeMap::new();
    for kind in [
        AttemptKind::Smoke,
        AttemptKind::Primary,
        AttemptKind::Repeat,
    ] {
        for (case, selected) in selections(run, kind)? {
            let attempt_path = selected.dir.join("attempt.json");
            let value: Value = serde_json::from_slice(&fs::read(&attempt_path)?)?;
            observed.insert(
                selection_key(kind, &case),
                Selection {
                    attempt_id: value["attempt_id"]
                        .as_str()
                        .ok_or("missing selected ID")?
                        .into(),
                    path: selected.dir.strip_prefix(&run.output)?.into(),
                    sha256: sha256(&attempt_path)?,
                },
            );
        }
    }
    for (slot, old) in &state.selected {
        if observed.get(slot) != Some(old) {
            return Err(format!("selected evidence changed or disappeared: {slot}").into());
        }
    }
    // A completed attempt carries an explicit selection declaration. Recover it
    // after a crash between exclusive attempt completion and state replacement.
    state.selected = observed;
    Ok(state)
}

fn save_state(run: &Run) -> Result<State> {
    let state = read_state(run)?;
    atomic_json(&run.output.join("selection.json"), &state)?;
    Ok(state)
}

pub(super) fn validate_resume(run: &Run) -> Result<()> {
    if ![1, 2].contains(&run.schema_version) || !run.seconds.is_finite() || run.seconds < 30.0 {
        return Err("unsupported measurement manifest or duration".into());
    }
    if run.schema_version == 2 && run.power_policy.is_none() {
        return Err("new measurement manifest is missing its fixed power policy".into());
    }
    if frozen_policy(run)? != environment_keys()
        || run.environment["measurement_environment_removed"] != json!(frozen_policy(run)?)
    {
        return Err(
            "resume controller differs from the original measurement environment policy".into(),
        );
    }
    let current = host_environment(run.environment["profiler"].as_str().unwrap_or("unknown"))?;
    for key in [
        "cpu",
        "memory",
        "os",
        "rustc",
        "cargo",
        "xcode",
        "toolchain",
    ] {
        if current[key] != run.environment[key] {
            return Err(format!("resume host or toolchain changed: {key}").into());
        }
    }
    if run.output.join("complete.json").exists()
        || run.output.join("measurements-complete.json").exists()
    {
        return Err(
            "measurements are complete; use --report with a separate --output to publish".into(),
        );
    }
    if run.output.join("report-processing.json").exists() {
        return Err(
            "legacy processing has begun; capture recovery cannot change its inputs".into(),
        );
    }
    read_state(run)?;
    for kind in [
        AttemptKind::Smoke,
        AttemptKind::Primary,
        AttemptKind::Repeat,
    ] {
        for selected in selections(run, kind)?.values() {
            records::verify_attempt_evidence(selected)?;
        }
    }
    Ok(())
}

pub(super) fn resume(resume: &Resume) -> Result<()> {
    let run = read_measurement(resume)?;
    validate_resume(&run)?;
    verify_preserved(resume)?;
    let result = execute(
        &run,
        &resume.controller,
        &resume.controller.output.join("manifest.json"),
    );
    // This check runs on failure as well; old incomplete attempts and episodes
    // remain byte-identical across any number of continuations.
    verify_preserved(resume)?;
    result
}

fn verify_pair(run: &Run, controller: &Run, bindings: &Bindings) -> Result<()> {
    bindings.verify()?;
    verify_run(run)?;
    verify_run(controller)?;
    if run.power_policy != controller.power_policy {
        return Err("controller changed the immutable measurement power policy".into());
    }
    let own = fs::canonicalize(env::current_exe()?)?;
    if own != controller.artifacts["profile_preimages"].path {
        return Err("measurement/controller executable roles were swapped".into());
    }
    if INTERRUPTED.load(Ordering::SeqCst) {
        return Err("runner interrupted before measurement acceptance".into());
    }
    Ok(())
}

fn next_attempt(run: &Run, case: &str, kind: &str) -> Result<usize> {
    let mut highest = 0;
    for parent in [
        run.output.join("cases").join(case),
        run.snapshot.root.join(".profile-scratch").join(case),
    ] {
        if !parent.exists() {
            continue;
        }
        for entry in fs::read_dir(parent)? {
            let entry = entry?;
            if let Some(number) = entry
                .file_name()
                .to_str()
                .and_then(|name| name.strip_prefix(&format!("{kind}-")))
            {
                highest = highest.max(number.parse::<usize>()?);
            }
        }
    }
    highest
        .checked_add(1)
        .ok_or_else(|| "attempt number overflow".into())
}

fn baseline_stage(
    run: &Run,
    controller: &Run,
    bindings: &Bindings,
    directory: &Path,
    label: &str,
    symbols: bool,
) -> Result<()> {
    verify_pair(run, controller, bindings)?;
    let before = host::PowerObservation::observe();
    let path = directory.join(format!("{label}.stage.json"));
    let mut stage = json!({"schema_version":2,"episode_id":directory.file_name(),"status":"incomplete","power_before":before});
    atomic_json(&path, &stage)?;
    let policy = run.power_policy.unwrap_or(host::PowerPolicy::ObserveOnly);
    let result = (|| {
        policy.validate(&before)?;
        baseline(run, symbols, directory, label)?;
        let after = host::PowerObservation::observe();
        stage["power_after"] = serde_json::to_value(&after)?;
        policy.validate(&after)
    })();
    let identity = verify_pair(run, controller, bindings);
    match &result {
        Ok(()) if identity.is_ok() => {
            stage["status"] = json!("accepted");
            stage["csv"] =
                serde_json::to_value(artifact(&directory.join(format!("{label}.csv")))?)?;
        }
        Err(error) => stage["error"] = json!(error.to_string()),
        _ => stage["error"] = json!("measurement or controller identity changed"),
    }
    atomic_json(&path, &stage)?;
    identity?;
    result
}

fn fill_slots(
    run: &Run,
    controller: &Run,
    bindings: &Bindings,
    episode: &str,
    kind: AttemptKind,
    cases: &[Case],
) -> Result<()> {
    for case in cases {
        if read_state(run)?
            .selected
            .contains_key(&selection_key(kind, case))
        {
            continue;
        }
        let mut seconds = if kind == AttemptKind::Smoke {
            5.0
        } else {
            run.seconds
        };
        let mut accepted = false;
        for _ in 0..3 {
            verify_pair(run, controller, bindings)?;
            let number = next_attempt(run, &case.id(), kind.as_str())?;
            let result = capture(run, episode, kind.as_str(), case, seconds, number, || {
                verify_pair(run, controller, bindings)
            });
            verify_pair(run, controller, bindings)?;
            result?;
            let state = save_state(run)?;
            if state.selected.contains_key(&selection_key(kind, case)) {
                accepted = true;
                break;
            }
            seconds *= 2.0;
        }
        if !accepted {
            return Err(format!("insufficient samples for {} {}", kind.as_str(), case.id()).into());
        }
    }
    Ok(())
}

pub(super) fn execute(run: &Run, controller: &Run, controller_manifest: &Path) -> Result<()> {
    let _ownership = evidence::WriterLock::acquire(&run.output)?;
    let bindings = Bindings {
        measurement: artifact(&run.output.join("manifest.json"))?,
        controller: artifact(controller_manifest)?,
    };
    verify_manifest_role(&bindings.measurement.path, run, false)?;
    verify_manifest_role(&bindings.controller.path, controller, true)?;
    verify_pair(run, controller, &bindings)?;
    if run.output.join("measurements-complete.json").exists() {
        return Err("measurements already complete".into());
    }
    save_state(run)?;
    let id = unique_id("episode");
    let relative = PathBuf::from("episodes").join(&id);
    let directory = run.output.join(&relative);
    fs::create_dir_all(&directory)?;
    let path = directory.join("episode.json");
    let mut episode = json!({"schema_version":2,"id":id,"status":"in_progress","started_unix_seconds":epoch(),
        "measurement_manifest":artifact(&run.output.join("manifest.json"))?,"controller_manifest":artifact(controller_manifest)?,
        "power_policy":run.power_policy,"before_baseline":null,"after_baseline":null,"symbols_baseline":null});
    atomic_json(&path, &episode)?;
    let result = (|| -> Result<()> {
        fill_slots(
            run,
            controller,
            &bindings,
            &id,
            AttemptKind::Smoke,
            &records::endpoints(),
        )?;
        settle(run, &id)?;
        baseline_stage(
            run,
            controller,
            &bindings,
            &directory,
            "baseline-before",
            false,
        )?;
        episode["before_baseline"] = json!(relative.join("baseline-before.csv"));
        atomic_json(&path, &episode)?;
        baseline_stage(
            run,
            controller,
            &bindings,
            &directory,
            "baseline-symbols",
            true,
        )?;
        episode["symbols_baseline"] = json!(relative.join("baseline-symbols.csv"));
        atomic_json(&path, &episode)?;
        fill_slots(
            run,
            controller,
            &bindings,
            &id,
            AttemptKind::Primary,
            &records::all_cases(),
        )?;
        fill_slots(
            run,
            controller,
            &bindings,
            &id,
            AttemptKind::Repeat,
            &records::endpoints(),
        )?;
        settle(run, &format!("{id}-after"))?;
        baseline_stage(
            run,
            controller,
            &bindings,
            &directory,
            "baseline-after",
            false,
        )?;
        episode["after_baseline"] = json!(relative.join("baseline-after.csv"));
        for (kind, expected) in [
            (AttemptKind::Primary, records::all_cases()),
            (AttemptKind::Smoke, records::endpoints()),
            (AttemptKind::Repeat, records::endpoints()),
        ] {
            records::require_matrix(&selections(run, kind)?, &expected)?;
        }
        verify_pair(run, controller, &bindings)?;
        Ok(())
    })();
    episode["ended_unix_seconds"] = json!(epoch());
    if let Err(error) = result {
        episode["status"] = json!(if INTERRUPTED.load(Ordering::SeqCst) {
            "interrupted"
        } else {
            "failed"
        });
        episode["error"] = json!(error.to_string());
        atomic_json(&path, &episode)?;
        return Err(error);
    }
    episode["status"] = json!("complete");
    atomic_json(&path, &episode)?;
    atomic_json(
        &run.output.join("measurements-complete.json"),
        &json!({"schema_version":2,"snapshot_id":run.snapshot.id,"completed_unix_seconds":epoch(),"closing_episode":id,"selected_attempts":44}),
    )?;
    // The accepted controller's complete source closure is the processor input.
    let processor = snapshot::ProcessorIdentity::register(
        &controller.snapshot,
        &controller.output.join("source"),
        &controller.artifacts["profile_preimages"].path,
    )?;
    let destination = run.publication_root.clone().unwrap_or_else(|| {
        run.output.with_file_name(format!(
            "{}-publication",
            run.output.file_name().unwrap_or_default().to_string_lossy()
        ))
    });
    let gallery = crate::publication::publish(&run.output, &destination, None, &processor)?;
    verify_pair(run, controller, &bindings)?;
    atomic_json(
        &run.output.join("complete.json"),
        &json!({"schema_version":2,"snapshot_id":run.snapshot.id,"completed_unix_seconds":epoch(),"gallery":gallery}),
    )?;
    eprintln!("Complete: {}", gallery.display());
    Ok(())
}

/// Short integration coverage uses the production recorder path and a separately
/// registered frozen run. It never produces timing baselines or a completed run.
pub(super) fn integration_smoke(manifest: &Path) -> Result<()> {
    let run: Run = serde_json::from_slice(&fs::read(manifest)?)?;
    verify_run(&run)?;
    verify_manifest_role(manifest, &run, false)?;
    if run.output.join("cases").exists() || run.output.join("integration-smokes.json").exists() {
        return Err("integration smokes require unused evidence and scratch paths".into());
    }
    let _lock = evidence::WriterLock::acquire(&run.output)?;
    let bindings = Bindings {
        measurement: artifact(manifest)?,
        controller: artifact(manifest)?,
    };
    verify_pair(&run, &run, &bindings)?;
    let id = unique_id("integration-smoke");
    let cases: Vec<_> = records::endpoints()
        .into_iter()
        .filter(|case| case.hashes == 64)
        .collect();
    fill_slots(&run, &run, &bindings, &id, AttemptKind::Smoke, &cases)?;
    verify_pair(&run, &run, &bindings)?;
    atomic_json(
        &run.output.join("integration-smokes.json"),
        &json!({"schema_version":2,"episode_id":id,"measurement_manifest":bindings.measurement,"completed_unix_seconds":epoch(),"cases":cases,"purpose":"recorder and worker integration only; no performance conclusions"}),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_fixture(root: &Path, name: &str) -> Run {
        serde_json::from_value(json!({
            "schema_version":2,"output":root.join(name),"snapshot":{
                "root":root.join(format!("{name}-source")),"id":name,"editing_root":root,
                "base_revision":"fixture","inventory":[],"external_config":[],"build_environment":{}
            },"target_root":root.join(format!("{name}-target")),"seconds":30.0,
            "artifacts":{"profile_preimages":{"path":root.join(name),"sha256":name}},
            "tools":{},"environment":{},"branch":"chore/fixture","revision":"fixture"
        }))
        .unwrap()
    }

    #[test]
    fn measurement_and_controller_manifests_keep_distinct_roles_and_hashes() -> Result<()> {
        let root = env::temp_dir().join(unique_id("flock-bindings-test"));
        fs::create_dir(&root)?;
        let measurement = run_fixture(&root, "measurement");
        let controller = run_fixture(&root, "controller");
        let a = root.join("a.json");
        let b = root.join("b.json");
        atomic_json(&a, &measurement)?;
        atomic_json(&b, &json!({"controller":controller}))?;
        verify_manifest_role(&a, &measurement, false)?;
        verify_manifest_role(&b, &controller, true)?;
        assert!(verify_manifest_role(&a, &controller, true).is_err());
        assert!(verify_manifest_role(&b, &measurement, false).is_err());
        let bindings = Bindings {
            measurement: artifact(&a)?,
            controller: artifact(&b)?,
        };
        bindings.verify()?;
        fs::write(&b, "{}")?;
        assert!(
            bindings
                .verify()
                .unwrap_err()
                .to_string()
                .contains("controller manifest changed")
        );
        atomic_json(&b, &json!({"controller":controller}))?;
        fs::write(&a, "{}")?;
        assert!(
            bindings
                .verify()
                .unwrap_err()
                .to_string()
                .contains("measurement manifest changed")
        );
        fs::remove_dir_all(root)?;
        Ok(())
    }

    #[test]
    fn repeated_continuations_allocate_after_incomplete_evidence_and_scratch() -> Result<()> {
        let root = env::temp_dir().join(unique_id("flock-continuation-test"));
        let run = run_fixture(&root, "measurement");
        let case = "flock-prove-4096";
        let directory = run.output.join("cases").join(case);
        let scratch = run.snapshot.root.join(".profile-scratch").join(case);
        fs::create_dir_all(&directory)?;
        fs::create_dir_all(&scratch)?;
        assert_eq!(next_attempt(&run, case, "repeat")?, 1);
        fs::create_dir(directory.join("repeat-001"))?;
        fs::write(
            directory.join("repeat-001/attempt.json"),
            "interrupted first episode",
        )?;
        fs::create_dir(scratch.join("repeat-002"))?;
        assert_eq!(next_attempt(&run, case, "repeat")?, 3);
        fs::create_dir(directory.join("repeat-003"))?;
        assert_eq!(next_attempt(&run, case, "repeat")?, 4);
        assert_eq!(
            fs::read_to_string(directory.join("repeat-001/attempt.json"))?,
            "interrupted first episode"
        );
        fs::remove_dir_all(root)?;
        Ok(())
    }
    #[test]
    fn selection_keys_cover_exact_slots() {
        let mut slots = std::collections::BTreeSet::new();
        for kind in [
            AttemptKind::Smoke,
            AttemptKind::Primary,
            AttemptKind::Repeat,
        ] {
            let cases = if kind == AttemptKind::Primary {
                records::all_cases()
            } else {
                records::endpoints()
            };
            for case in cases {
                assert!(slots.insert(selection_key(kind, &case)));
            }
        }
        assert_eq!(slots.len(), 44);
    }
}

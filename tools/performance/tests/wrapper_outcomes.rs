mod common;

use common::Temporary;
use flock_performance::{Result, StageStatus, process::CommandOutcome};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

#[test]
fn recorder_spawn_failures_preserve_both_command_and_stage_outcomes() -> Result<()> {
    let temp = Temporary::new("recorder-spawn-failure")?;
    let scratch = temp.join("scratch");
    fs::create_dir(&scratch)?;
    let nonexecutable = temp.join("nonexecutable-recorder");
    fs::write(&nonexecutable, "fixture without executable permission")?;
    fs::set_permissions(&nonexecutable, fs::Permissions::from_mode(0o600))?;
    for stage in ["record", "export"] {
        let attempt = temp.join(stage);
        fs::create_dir(&attempt)?;
        let mut command = Command::new(env!("CARGO_BIN_EXE_xctrace_capture"));
        command
            .current_dir(&scratch)
            .env("FLOCK_PROFILE_XCTRACE_BIN", &nonexecutable)
            .env("FLOCK_PROFILE_ATTEMPT_DIR", &attempt)
            .env("FLOCK_PROFILE_ATTEMPT_ID", "spawn-failure-fixture")
            .arg(stage);
        if stage == "record" {
            command.arg("--output").arg(scratch.join("trace"));
        }
        let output = command.output()?;
        assert!(!output.status.success());
        let outcome: CommandOutcome =
            serde_json::from_slice(&fs::read(attempt.join(format!("{stage}-process.json")))?)?;
        assert!(!outcome.success);
        assert!(outcome.spawn_error.is_some());
        assert!(outcome.exit_code.is_none());
        assert!(outcome.signal.is_none());
        assert!(outcome.elapsed_seconds.is_finite() && outcome.elapsed_seconds >= 0.0);
        assert!(!outcome.cleanup.attempted);
        let status: StageStatus =
            serde_json::from_slice(&fs::read(attempt.join(format!("{stage}-status.json")))?)?;
        assert!(!status.success);
        assert!(!status.io_ok);
        assert_eq!(status.error, outcome.spawn_error);
        assert_eq!(status.attempt_id, "spawn-failure-fixture");
        assert_eq!(status.stage, stage);
    }
    Ok(())
}

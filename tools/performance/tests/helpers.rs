#![cfg(unix)]

mod common;

use common::Temporary;
use flock_performance::{
    StageStatus, archive_trace, command, environment_keys, reject_overlap, tee,
};
use std::ffi::OsString;
use std::fs;
use std::io::{self, Read, Write};
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn absent_policy_shell() -> String {
    let keys = environment_keys().join(" ");
    format!(
        "for key in {keys}; do\n\
           if /usr/bin/printenv \"$key\" >/dev/null; then exit 91; fi\n\
         done\n\
         test \"$FLOCK_PROFILE_KEEP\" = preserved || exit 92\n"
    )
}

fn fake_recorder(root: &Path) -> PathBuf {
    let path = root.join("fake xctrace");
    let script = format!(
        "#!/bin/sh\n{}\
         stage=$1\nshift\n\
         if test \"$stage\" = record; then\n\
           while test $# -gt 0; do\n\
             if test \"$1\" = --output; then output=$2; shift; fi\n\
             shift\n\
           done\n\
           mkdir -p \"$output/subdirectory\" || exit 93\n\
           printf 'trace\\000bytes\\377' > \"$output/subdirectory/data\"\n\
         else\n\
           /bin/cat \"$FAKE_EXPORT_INPUT\"\n\
         fi\n\
         case \"$FAKE_EXIT\" in\n\
           sigint) kill -INT $$;;\n\
           sigterm) kill -TERM $$;;\n\
           *) exit \"${{FAKE_EXIT:-0}}\";;\n\
         esac\n",
        absent_policy_shell()
    );
    fs::write(&path, script).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
    path
}

fn recorder_command(root: &Path, recorder: &Path, stage: &str) -> Command {
    let scratch = root.join("scratch path");
    let attempt = root.join("evidence path");
    fs::create_dir_all(&scratch).unwrap();
    fs::create_dir_all(&attempt).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_xctrace_capture"));
    command
        .current_dir(scratch)
        .arg(stage)
        .env("FLOCK_PROFILE_XCTRACE_BIN", recorder)
        .env("FLOCK_PROFILE_ATTEMPT_ID", "attempt-1")
        .env("FLOCK_PROFILE_ATTEMPT_DIR", attempt)
        .env("FLOCK_PROFILE_KEEP", "preserved");
    if stage == "record" {
        command.args(["--output", "cargo-flamegraph.trace"]);
    }
    command
}

fn read_status(root: &Path, stage: &str) -> StageStatus {
    serde_json::from_slice(
        &fs::read(root.join(format!("evidence path/{stage}-status.json"))).unwrap(),
    )
    .unwrap()
}

#[test]
fn environment_policy_child_probe() {
    if std::env::var_os("FLOCK_PROFILE_POLICY_PROBE").is_none() {
        return;
    }
    let output = command("/bin/sh")
        .args(["-c", &absent_policy_shell()])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
}

#[test]
fn all_policy_keys_are_removed_from_real_children_without_global_mutation() {
    let values = [
        None,
        Some(OsString::new()),
        Some(OsString::from("0")),
        Some(OsString::from("1")),
        Some(OsString::from_vec(vec![0xff, 0xfe])),
    ];
    for key in environment_keys() {
        for value in &values {
            let mut child = Command::new(std::env::current_exe().unwrap());
            child
                .args(["--exact", "environment_policy_child_probe"])
                .env("FLOCK_PROFILE_POLICY_PROBE", "1")
                .env("FLOCK_PROFILE_KEEP", "preserved")
                .env_remove(&key);
            if let Some(value) = value {
                child.env(&key, value);
            }
            let output = child.output().unwrap();
            assert!(
                output.status.success(),
                "key {key}, value {value:?}: {output:?}"
            );
        }
    }
}

#[test]
fn recorder_clears_diagnostics_and_archives_before_upstream_cleanup() {
    let root = Temporary::new("flock performance helper tests").unwrap();
    let recorder = fake_recorder(root.path());
    let mut child = recorder_command(root.path(), &recorder, "record");
    for key in environment_keys() {
        child.env(key, OsString::from_vec(vec![0xff]));
    }
    let output = child.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let status = read_status(root.path(), "record");
    assert!(status.success && status.io_ok);
    assert_eq!(status.attempt_id, "attempt-1");
    assert_eq!(status.exit_code, Some(0));
    assert_eq!(status.signal, None);
    fs::remove_dir_all(root.path().join("scratch path/cargo-flamegraph.trace")).unwrap();
    assert_eq!(
        fs::read(
            root.path()
                .join("evidence path/raw/recording.trace/subdirectory/data")
        )
        .unwrap(),
        b"trace\0bytes\xff"
    );
}

#[test]
fn failures_and_signals_normalize_to_one_and_preserve_original_status() {
    for stage in ["record", "export"] {
        for (mode, code, signal) in [
            ("0", Some(0), None),
            ("1", Some(1), None),
            ("54", Some(54), None),
            ("sigint", None, Some(2)),
            ("sigterm", None, Some(15)),
        ] {
            let root = Temporary::new("flock performance helper tests").unwrap();
            let recorder = fake_recorder(root.path());
            let input = root.path().join("export input");
            fs::write(&input, b"<trace>data</trace>\n").unwrap();
            let output = recorder_command(root.path(), &recorder, stage)
                .env("FAKE_EXIT", mode)
                .env("FAKE_EXPORT_INPUT", input)
                .output()
                .unwrap();
            let success = mode == "0";
            assert_eq!(output.status.code(), Some(if success { 0 } else { 1 }));
            let status = read_status(root.path(), stage);
            assert_eq!(status.exit_code, code, "{stage}, {mode}");
            assert_eq!(status.signal, signal, "{stage}, {mode}");
            assert_eq!(status.success, success);
            assert!(status.io_ok);
        }
    }
}

#[test]
fn export_and_folded_streams_preserve_large_binary_payloads() {
    let root = Temporary::new("flock performance helper tests").unwrap();
    let recorder = fake_recorder(root.path());
    let input = root.path().join("export input");
    let payload = (0..2_000_000)
        .map(|index| (index % 256) as u8)
        .collect::<Vec<_>>();
    fs::write(&input, &payload).unwrap();
    let output = recorder_command(root.path(), &recorder, "export")
        .env("FAKE_EXPORT_INPUT", input)
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output.stderr);
    assert_eq!(output.stdout, payload);
    assert_eq!(
        fs::read(root.path().join("evidence path/raw/time-profile.xml")).unwrap(),
        payload
    );

    let folded = root.path().join("folded stacks with spaces");
    let mut child = Command::new(env!("CARGO_BIN_EXE_folded_capture"))
        .env("FLOCK_PROFILE_FOLDED_PATH", &folded)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let source = payload.clone();
    let writer = std::thread::spawn(move || stdin.write_all(&source).unwrap());
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, payload);
    assert_eq!(fs::read(folded).unwrap(), payload);
}

#[test]
fn copying_or_writing_failures_cannot_report_success_or_overwrite_evidence() {
    let root = Temporary::new("flock performance helper tests").unwrap();
    let recorder = fake_recorder(root.path());
    let raw = root.path().join("evidence path/raw");
    fs::create_dir_all(raw.join("recording.trace")).unwrap();
    let output = recorder_command(root.path(), &recorder, "record")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let status = read_status(root.path(), "record");
    assert_eq!(status.exit_code, Some(0));
    assert!(!status.success && !status.io_ok);

    fs::create_dir(raw.join("time-profile.xml")).unwrap();
    let output = recorder_command(root.path(), &recorder, "export")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let status = read_status(root.path(), "export");
    assert!(!status.success && !status.io_ok);

    let existing = root.path().join("existing stacks");
    fs::write(&existing, b"retained evidence").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_folded_capture"))
        .env("FLOCK_PROFILE_FOLDED_PATH", &existing)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(fs::read(existing).unwrap(), b"retained evidence");
}

#[test]
fn scratch_archive_overlap_including_symlink_aliases_is_rejected() {
    let root = Temporary::new("flock performance helper tests").unwrap();
    let scratch = root.path().join("scratch");
    fs::create_dir(&scratch).unwrap();
    assert!(reject_overlap(&scratch, &scratch).is_err());
    assert!(reject_overlap(&scratch, &scratch.join("archive")).is_err());
    assert!(reject_overlap(&scratch.join("trace"), &scratch).is_err());
    let alias = root.path().join("alias");
    symlink(&scratch, &alias).unwrap();
    assert!(reject_overlap(&scratch, &alias.join("archive")).is_err());
    assert!(archive_trace(&scratch, &alias.join("archive")).is_err());
    assert!(reject_overlap(&scratch, &root.path().join("independent")).is_ok());
}

#[test]
fn failed_writer_does_not_stop_draining_a_child_pipe() {
    struct FailedWriter;
    impl Write for FailedWriter {
        fn write(&mut self, _: &[u8]) -> io::Result<usize> {
            Err(io::Error::other("simulated full disk"))
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let payload = vec![42_u8; 2_000_000];
    let mut input = io::Cursor::new(&payload);
    let mut other = Vec::new();
    assert!(tee(&mut input, FailedWriter, &mut other).is_err());
    assert_eq!(input.position(), payload.len() as u64);
    assert_eq!(other, payload);

    struct FlushFailure(Vec<u8>);
    impl Write for FlushFailure {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.0.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Err(io::Error::other("simulated flush failure"))
        }
    }
    assert!(
        tee(
            io::Cursor::new(b"stacks"),
            FlushFailure(Vec::new()),
            io::sink()
        )
        .is_err()
    );
    let mut remaining = Vec::new();
    input.read_to_end(&mut remaining).unwrap();
    assert!(remaining.is_empty());
}

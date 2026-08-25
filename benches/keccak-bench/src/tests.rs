//! Unit tests for the keccak_e2e bin: flag parsing and the sweep shape.
//!
//! One file serves the bin's tests (layout directive; precedent:
//! `benches/blake3-bench/src/tests.rs`). It attaches to the `keccak_e2e`
//! bin as a `#[path]` module in `src/keccak.rs`, so the bin-private items
//! stay reachable. The lib's witness builders keep their own inline tests
//! in `src/lib.rs`. No test reads an env var — env-dependent wrappers
//! stay uncovered by design (testing.md forbids order-dependent tests).

use super::{Args, sweep_for};

/// Build an owned-String argument iterator for parser tests.
fn flags(v: &[&str]) -> std::vec::IntoIter<String> {
    v.iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .into_iter()
}

// ---- Flag parsing ----

#[test]
fn from_parts_defaults_follow_env_fallbacks() {
    let full = Args::from_parts(flags(&[]), false, 12);
    assert!(!full.smoke);
    assert_eq!(full.runs, 3);
    assert_eq!(full.max_log, 12);
    assert!(full.json.is_none());

    let smoke = Args::from_parts(flags(&[]), true, 8);
    assert!(smoke.smoke);
    assert_eq!(smoke.runs, 1);
    assert_eq!(smoke.max_log, 8);
}

#[test]
fn from_parts_flags_win_over_env_fallbacks() {
    let args = Args::from_parts(
        flags(&[
            "--smoke",
            "--runs",
            "5",
            "--max-log",
            "8",
            "--json",
            "out.json",
        ]),
        false,
        12,
    );
    assert!(args.smoke);
    assert_eq!(args.runs, 5);
    assert_eq!(args.max_log, 8);
    assert_eq!(args.json.as_deref(), Some("out.json"));
}

#[test]
fn from_parts_accepts_runs_bounds() {
    assert_eq!(Args::from_parts(flags(&["--runs", "1"]), false, 12).runs, 1);
    assert_eq!(
        Args::from_parts(flags(&["--runs", "16"]), false, 12).runs,
        16
    );
}

#[test]
#[should_panic(expected = "unknown flag")]
fn from_parts_rejects_unknown_flags() {
    Args::from_parts(flags(&["--keccak-max-log"]), false, 12);
}

#[test]
#[should_panic(expected = "--runs must be in 1..=16")]
fn from_parts_rejects_out_of_range_runs() {
    Args::from_parts(flags(&["--runs", "0"]), false, 12);
}

#[test]
#[should_panic(expected = "--runs must be an integer")]
fn from_parts_rejects_garbage_runs() {
    Args::from_parts(flags(&["--runs", "3x"]), false, 12);
}

#[test]
#[should_panic(expected = "--max-log must be in 6..=19")]
fn from_parts_rejects_out_of_range_max_log() {
    Args::from_parts(flags(&["--max-log", "20"]), false, 12);
}

#[test]
#[should_panic(expected = "--json needs a file path")]
fn from_parts_rejects_json_without_path() {
    Args::from_parts(flags(&["--json"]), false, 12);
}

// ---- Sweep shape ----

#[test]
fn sweep_for_smoke_returns_single_small_point() {
    assert_eq!(sweep_for(true, 19), vec![64]);
}

#[test]
fn sweep_for_full_steps_by_two_up_to_max() {
    assert_eq!(sweep_for(false, 12), vec![64, 256, 1024, 4096]);
    // An odd bound tops out at the even log below it (the hint's claim).
    assert_eq!(sweep_for(false, 9), vec![64, 256]);
}

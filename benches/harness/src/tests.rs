//! Unit tests for the shared harness. Parser tests cover the MECHANISM against
//! a synthetic spec; each bench crate pins its REAL spec. No env vars (testing.md).

use crate::{
    BenchArgs, BenchRow, MaxLogFlag, RowTimings, SplitMix, fmt_ms, parse_max_log, parse_smoke,
    time_best,
};

/// Synthetic spec for mechanism tests; bounds unlike either real crate.
const TEST_SPEC: MaxLogFlag = MaxLogFlag {
    flag: "--test-max-log",
    env: "BENCH_TEST_MAX_LOG",
    default: 5,
    min: 2,
    max: 9,
    hint: "test hint",
};

// ---- Rng, timing, formatting ----

#[test]
fn splitmix_is_deterministic() {
    let mut a = SplitMix(7);
    let mut b = SplitMix(7);
    for _ in 0..16 {
        assert_eq!(a.next_u64(), b.next_u64());
    }
    let mut c = SplitMix(8);
    assert_ne!(SplitMix(7).next_u64(), c.next_u64());
}

#[test]
fn time_best_returns_output_and_positive_time() {
    let (value, secs) = time_best(3, || 41 + 1);
    assert_eq!(value, 42);
    assert!(secs >= 0.0);
}

#[test]
fn fmt_ms_selects_unit_by_magnitude() {
    assert!(fmt_ms(0.000_5).ends_with("µs"));
    assert!(fmt_ms(0.5).ends_with("ms"));
    assert!(fmt_ms(2.0).ends_with("s "));
}

// ---- Row schema ----

#[test]
fn bench_row_derives_metrics_from_inputs() {
    let timings = RowTimings {
        setup_s: 1.0,
        witness_s: 1.0,
        prove_s: 2.0,
        verify_s: 1.0,
    };
    let row = BenchRow::new("b", "r", 10, 16, timings, 5, 100.0, String::new());
    assert_eq!(row.hashes_per_s, 5.0);
    assert_eq!(row.slowdown, 20.0);
}

// ---- Env parsing cores ----

#[test]
fn parse_smoke_accepts_truthy_and_falsy_forms() {
    for v in ["1", "true", "YES", "On"] {
        assert!(parse_smoke(v), "{v}");
    }
    for v in ["", "0", "false", "NO", "off"] {
        assert!(!parse_smoke(v), "{v:?}");
    }
}

#[test]
#[should_panic(expected = "unrecognized value")]
fn parse_smoke_rejects_unknown_values() {
    parse_smoke("maybe");
}

#[test]
fn parse_max_log_accepts_in_range_values() {
    assert_eq!(parse_max_log("X", " 7 ", 1, 14, "hint"), 7);
}

#[test]
#[should_panic(expected = "must be in 1..=14")]
fn parse_max_log_rejects_out_of_range() {
    parse_max_log("X", "15", 1, 14, "hint");
}

#[test]
#[should_panic(expected = "must be an integer")]
fn parse_max_log_rejects_garbage() {
    parse_max_log("X", "8x", 1, 14, "hint");
}

// ---- Flag parser mechanism ----

#[test]
fn from_parts_defaults_follow_env_fallbacks() {
    let full = BenchArgs::from_parts([] as [&str; 0], &TEST_SPEC, false, 5);
    assert!(!full.smoke);
    assert_eq!(full.runs, 3);
    assert_eq!(full.max_log, 5);
    assert!(full.json.is_none());

    let smoke = BenchArgs::from_parts([] as [&str; 0], &TEST_SPEC, true, 4);
    assert!(smoke.smoke);
    assert_eq!(smoke.runs, 1);
    assert_eq!(smoke.max_log, 4);
}

#[test]
fn from_parts_flags_win_over_env_fallbacks() {
    let args = BenchArgs::from_parts(
        [
            "--smoke",
            "--runs",
            "5",
            "--test-max-log",
            "3",
            "--json",
            "out.json",
        ],
        &TEST_SPEC,
        false,
        5,
    );
    assert!(args.smoke);
    assert_eq!(args.runs, 5);
    assert_eq!(args.max_log, 3);
    assert_eq!(args.json.as_deref(), Some("out.json"));
}

#[test]
fn from_parts_accepts_runs_bounds() {
    let one = BenchArgs::from_parts(["--runs", "1"], &TEST_SPEC, false, 5);
    assert_eq!(one.runs, 1);
    let sixteen = BenchArgs::from_parts(["--runs", "16"], &TEST_SPEC, false, 5);
    assert_eq!(sixteen.runs, 16);
}

#[test]
#[should_panic(expected = "unknown flag")]
fn from_parts_rejects_unknown_flags() {
    BenchArgs::from_parts(["--frames"], &TEST_SPEC, false, 5);
}

#[test]
#[should_panic(expected = "--runs must be in 1..=16")]
fn from_parts_rejects_out_of_range_runs() {
    BenchArgs::from_parts(["--runs", "17"], &TEST_SPEC, false, 5);
}

#[test]
#[should_panic(expected = "--runs must be an integer")]
fn from_parts_rejects_garbage_runs() {
    BenchArgs::from_parts(["--runs", "3x"], &TEST_SPEC, false, 5);
}

#[test]
#[should_panic(expected = "--test-max-log must be in 2..=9")]
fn from_parts_rejects_out_of_range_max_log() {
    BenchArgs::from_parts(["--test-max-log", "10"], &TEST_SPEC, false, 5);
}

#[test]
#[should_panic(expected = "--test-max-log needs a value")]
fn from_parts_rejects_max_log_without_value() {
    BenchArgs::from_parts(["--test-max-log"], &TEST_SPEC, false, 5);
}

#[test]
#[should_panic(expected = "--json needs a file path")]
fn from_parts_rejects_json_without_path() {
    BenchArgs::from_parts(["--json"], &TEST_SPEC, false, 5);
}

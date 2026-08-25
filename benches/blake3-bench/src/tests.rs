//! Unit tests for the blake3-bench crate: the shared harness and the
//! bin's flag parsing and sweep shapes.
//!
//! One file serves both test sets (layout directive; repo precedent:
//! `crates/flock-prover/src/succinct_veil/tests.rs`). It attaches to the
//! `blake3_e2e` bin as a `#[path]` module in `src/blake3.rs`, so the
//! bin-private items stay reachable; the harness is exercised through
//! `blake3_bench::` like any downstream consumer. No test reads an env
//! var — env-dependent wrappers stay uncovered by design (testing.md
//! forbids order-dependent tests).

use blake3_bench::{
    BenchRow, RowTimings, SplitMix, blake3_chain, fmt_ms, json_path_from, parse_max_log,
    parse_smoke, time_best, verify_chain_linkage,
};
use flock_prover::r1cs_hashes::blake3_preimage::DIGEST_BYTES;

use super::{Args, framed_sweep_for, succinct_sweep_for};

/// Build an owned-String argument iterator for parser tests.
fn flags(v: &[&str]) -> std::vec::IntoIter<String> {
    v.iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .into_iter()
}

// ---- Shared harness (lib public API) ----

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
fn blake3_chain_links_and_digests_are_honest() {
    let (messages, digests) = blake3_chain(5, 0xC0FFEE_42);
    assert_eq!(messages.len(), 5);
    assert_eq!(digests.len(), 5);
    for i in 0..5 {
        assert_eq!(*blake3::hash(&messages[i]).as_bytes(), digests[i]);
        assert_eq!(messages[i][DIGEST_BYTES..], [0u8; 32]);
        if i > 0 {
            assert_eq!(messages[i][..DIGEST_BYTES], digests[i - 1]);
        }
    }
}

#[test]
fn time_best_returns_output_and_positive_time() {
    let (value, secs) = time_best(3, || 41 + 1);
    assert_eq!(value, 42);
    assert!(secs >= 0.0);
}

#[test]
fn verify_chain_linkage_accepts_honest_and_rejects_tampered() {
    let (_, digests) = blake3_chain(5, 1);
    assert!(verify_chain_linkage(&digests));
    let mut bad = digests.clone();
    bad[2][0] ^= 1;
    assert!(!verify_chain_linkage(&bad));
    assert!(verify_chain_linkage(&digests[..1]));
}

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

#[test]
fn fmt_ms_selects_unit_by_magnitude() {
    assert!(fmt_ms(0.000_5).ends_with("µs"));
    assert!(fmt_ms(0.5).ends_with("ms"));
    assert!(fmt_ms(2.0).ends_with("s "));
}

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

#[test]
fn json_path_from_finds_flag_and_path() {
    assert_eq!(
        json_path_from(flags(&["--json", "out.json"])),
        Some("out.json".to_string()),
    );
    assert_eq!(json_path_from(flags(&["--other"])), None);
}

#[test]
#[should_panic(expected = "--json needs a file path")]
fn json_path_from_rejects_missing_path() {
    json_path_from(flags(&["--json"]));
}

// ---- Bin: flag parsing ----

#[test]
fn from_parts_defaults_follow_env_fallbacks() {
    let full = Args::from_parts(flags(&[]), false, 6);
    assert!(!full.smoke);
    assert_eq!(full.runs, 3);
    assert_eq!(full.framed_max_log, 6);
    assert!(full.json.is_none());

    let smoke = Args::from_parts(flags(&[]), true, 4);
    assert!(smoke.smoke);
    assert_eq!(smoke.runs, 1);
    assert_eq!(smoke.framed_max_log, 4);
}

#[test]
fn from_parts_flags_win_over_env_fallbacks() {
    let args = Args::from_parts(
        flags(&[
            "--smoke",
            "--runs",
            "5",
            "--framed-max-log",
            "3",
            "--json",
            "out.json",
        ]),
        false,
        6,
    );
    assert!(args.smoke);
    assert_eq!(args.runs, 5);
    assert_eq!(args.framed_max_log, 3);
    assert_eq!(args.json.as_deref(), Some("out.json"));
}

#[test]
fn from_parts_accepts_runs_bounds() {
    assert_eq!(Args::from_parts(flags(&["--runs", "1"]), false, 6).runs, 1);
    assert_eq!(
        Args::from_parts(flags(&["--runs", "16"]), false, 6).runs,
        16
    );
}

#[test]
#[should_panic(expected = "unknown flag")]
fn from_parts_rejects_unknown_flags() {
    Args::from_parts(flags(&["--frames"]), false, 6);
}

#[test]
#[should_panic(expected = "--runs must be in 1..=16")]
fn from_parts_rejects_out_of_range_runs() {
    Args::from_parts(flags(&["--runs", "17"]), false, 6);
}

#[test]
#[should_panic(expected = "--runs must be an integer")]
fn from_parts_rejects_garbage_runs() {
    Args::from_parts(flags(&["--runs", "3x"]), false, 6);
}

#[test]
#[should_panic(expected = "--json needs a file path")]
fn from_parts_rejects_json_without_path() {
    Args::from_parts(flags(&["--json"]), false, 6);
}

// ---- Bin: sweep shapes ----

#[test]
fn framed_sweep_for_smoke_returns_single_small_row() {
    assert_eq!(framed_sweep_for(true, 14), vec![2]);
}

#[test]
fn framed_sweep_for_full_returns_powers_of_two_up_to_max() {
    assert_eq!(framed_sweep_for(false, 3), vec![2, 4, 8]);
}

#[test]
fn succinct_sweep_for_selects_by_smoke_mode() {
    assert_eq!(succinct_sweep_for(true), vec![1]);
    assert_eq!(succinct_sweep_for(false), vec![256, 512, 1024, 2048]);
}

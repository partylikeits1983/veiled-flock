//! Unit tests for the blake3-bench crate: the domain lib and the bin's
//! sweep shapes, plus the pin on this crate's real flag spec.
//!
//! One file serves both test sets (layout directive; repo precedent:
//! `crates/flock-prover/src/succinct_veil/tests.rs`). It attaches to the
//! `blake3_e2e` bin as a `#[path]` module in `src/blake3.rs`; the domain
//! lib is exercised through `blake3_bench::` like any downstream
//! consumer. The harness's own tests (parser mechanism, timer, rows)
//! live in `bench-harness`; the spec test here pins the REAL flag
//! name/env/bounds so a `SPEC` typo fails a test instead of shipping.
//! No test reads an env var (testing.md forbids order-dependent tests).

use bench_harness::BenchArgs;
use blake3_bench::{blake3_chain, verify_chain_linkage};
use flock_prover::r1cs_hashes::blake3_preimage::DIGEST_BYTES;

use super::{SPEC, framed_sweep_for, succinct_sweep_for};

// ---- Domain lib (public API) ----

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
fn verify_chain_linkage_accepts_honest_and_rejects_tampered() {
    let (_, digests) = blake3_chain(5, 1);
    assert!(verify_chain_linkage(&digests));
    let mut bad = digests.clone();
    bad[2][0] ^= 1;
    assert!(!verify_chain_linkage(&bad));
    assert!(verify_chain_linkage(&digests[..1]));
}

// ---- Bin: the real flag spec ----

#[test]
fn spec_pins_the_documented_flag_and_env_fallback() {
    assert_eq!(
        (
            SPEC.max_log.flag,
            SPEC.max_log.env,
            SPEC.max_log.default,
            SPEC.max_log.min,
            SPEC.max_log.max,
        ),
        ("--framed-max-log", "BENCH_FRAMED_MAX_LOG", 6, 1, 14),
    );
    let args = BenchArgs::from_parts(["--framed-max-log", "3"], &SPEC.max_log, false, 6);
    assert_eq!(args.max_log, 3);
}

#[test]
#[should_panic(expected = "--framed-max-log must be in 1..=14")]
fn spec_rejects_out_of_range_framed_max_log() {
    BenchArgs::from_parts(["--framed-max-log", "15"], &SPEC.max_log, false, 6);
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

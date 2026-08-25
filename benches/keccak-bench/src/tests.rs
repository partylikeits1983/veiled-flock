//! Unit tests for the keccak-bench crate: the domain lib, the bin's
//! sweep shape, and the pin on this crate's real flag spec.
//!
//! One file serves both test sets (layout directive; precedent:
//! `benches/blake3-bench/src/tests.rs`). It attaches to the `keccak_e2e`
//! bin as a `#[path]` module in `src/keccak.rs`, so the bin-private items
//! stay reachable; the domain lib is exercised through `keccak_bench::`
//! like any downstream consumer. The harness's tests (parser mechanism,
//! timer, rows) live in `bench-harness`. The spec test here pins the
//! REAL flag name/env/bounds so a `SPEC` typo fails a test instead of
//! shipping. No test reads an env var (testing.md forbids
//! order-dependent tests).

use bench_harness::BenchArgs;
use flock_prover::r1cs_hashes::keccak::{STATE_BITS, keccak_f};
use keccak_bench::{chain_outputs, keccak_honest_chain, verify_state_linkage};

use super::{SPEC, sweep_for};

// ---- Domain lib (public API) ----

#[test]
fn verify_state_linkage_accepts_honest_and_rejects_tampered() {
    let (inputs, _x0, x_last) = keccak_honest_chain(4, 0xFACE);
    let outputs = chain_outputs(&inputs, &x_last);
    assert!(verify_state_linkage(&inputs, &outputs));

    let mut bad = outputs.clone();
    bad[0][3] ^= true;
    assert!(!verify_state_linkage(&inputs, &bad));
    assert!(!verify_state_linkage(&inputs, &outputs[..3]));
    assert!(verify_state_linkage(&inputs[..1], &outputs[..1]));
    assert!(verify_state_linkage(&[], &[]));
}

#[test]
fn chain_outputs_shift_inputs_and_append_last() {
    let (inputs, _x0, x_last) = keccak_honest_chain(4, 0xFACE);
    let outputs = chain_outputs(&inputs, &x_last);
    assert_eq!(outputs.len(), 4);
    assert_eq!(outputs[..3], inputs[1..]);
    assert_eq!(outputs[3], x_last);
}

#[test]
#[should_panic(expected = "at least one link")]
fn chain_outputs_reject_empty_chain() {
    chain_outputs(&[], &[false; STATE_BITS]);
}

#[test]
fn keccak_chain_links_are_honest() {
    let (inputs, x0, x_last) = keccak_honest_chain(4, 0xDEAD_BEEF);
    assert_eq!(inputs.len(), 4);
    assert_eq!(inputs[0], x0);
    for i in 0..3 {
        let mut next = inputs[i];
        keccak_f(&mut next);
        assert_eq!(next, inputs[i + 1]);
    }
    let mut last = inputs[3];
    keccak_f(&mut last);
    assert_eq!(last, x_last);
}

// ---- The real flag spec ----

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
        ("--max-log", "BENCH_KECCAK_MAX_LOG", 12, 6, 19),
    );
    let args = BenchArgs::from_parts(["--max-log", "8"], &SPEC.max_log, false, 12);
    assert_eq!(args.max_log, 8);
}

#[test]
#[should_panic(expected = "--max-log must be in 6..=19")]
fn spec_rejects_out_of_range_max_log() {
    BenchArgs::from_parts(["--max-log", "20"], &SPEC.max_log, false, 12);
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

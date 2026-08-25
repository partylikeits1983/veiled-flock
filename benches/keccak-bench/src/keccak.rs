//! End-to-end keccak-f hash-chain proving runner — the `keccak_e2e` bin.
//!
//! Three rows per sweep point:
//! - `native-ligerito`, relation `chain-in-circuit`: `KeccakSetup::prove_chain`
//!   enforces `state_24[i] == state_0[i + 1]` in the committed witness; only
//!   the endpoints `x_0` / `x_last` are public.
//! - `veil-succinct`, relation `public-chain`: `KeccakZkSetup` proves each
//!   permutation with both states public. The benched verify closure also
//!   checks linkage over the public states (`outputs[i] == inputs[i + 1]`) —
//!   a pure equality check, so the `verify` column covers the full
//!   public-chain relation.
//! - `veil-succinct`, relation `chain-in-circuit`: `prove_succinct_chain`
//!   enforces linkage in the committed witness with only the endpoints
//!   public — the same relation as the native row, so those two rows are
//!   directly comparable.
//!
//! Sweep: n in {64, 256, 1024, 4096} (m = 22, 24, 26, 28). The valid chain
//! range reaches n = 524288 (m = 35), but the upper range is unrunnable on a
//! workstation — set `--max-log` above 12 only after measuring.
//!
//! Run: `cargo run --profile bench -p keccak-bench --bin keccak_e2e --`
//! Smoke: append `--smoke` (the `BENCH_SMOKE=1` env var stays as a
//! fallback; a flag wins over its env var). Flag parsing and the run
//! prologue live in the `bench-harness` driver ([`E2eBench`]); this bin
//! owns the sweep and row functions.

use bench_harness::{BenchRow, BenchSpec, E2eBench, MaxLogFlag, RowTimings, proof_size, time_best};
use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::keccak::{KeccakSetup, KeccakZkSetup};
use flock_prover::zk::ZkRng;
use keccak_bench::{
    chain_outputs, keccak_honest_chain, keccak_native_rate_with, verify_state_linkage,
};

const DOMAIN: &[u8] = b"veiled-flock-bench-keccak-e2e-v0";
const CHAIN_SEED: u64 = 0xC0FFEE_43;
const ZK_SEED: [u8; 32] = [0x43; 32];

/// Hint shown when a sweep override is out of range. The flag and the env
/// fallback share it.
const MAX_LOG_HINT: &str = "m = 16 + log; configs stop at m = 35; the sweep steps by 2, so an odd \
     value tops out at the even log below it";

/// This crate's bench identity: titles, banner phrases, and the sweep-
/// bound flag. The JSON title is the cross-commit tracking key.
static SPEC: BenchSpec = BenchSpec {
    table_title: "keccak hashchain e2e",
    json_title: "keccak_hashchain_e2e",
    smoke_banner: "shrunken sweep",
    rate_label: "native keccak-f chain rate",
    rate_unit: "Mperm/s",
    max_log: MaxLogFlag {
        flag: "--max-log",
        env: "BENCH_KECCAK_MAX_LOG",
        default: 12,
        min: 6,
        max: 19,
        hint: MAX_LOG_HINT,
    },
};

fn main() {
    let mut bench = E2eBench::start(&SPEC, keccak_native_rate_with);
    let (smoke, runs, max_log) = (bench.args().smoke, bench.args().runs, bench.args().max_log);
    let rate = bench.native_rate();
    for n in sweep_for(smoke, max_log) {
        bench.push(native_row(n, rate, runs));
        bench.push(succinct_row(n, rate, runs));
        bench.push(succinct_chain_row(n, rate, runs));
    }
    bench.finish();
}

// ---- Sweep shape. Env-free: the caller resolves smoke mode and
// overrides, so unit tests need no env vars. ----

/// The sweep: `n = 2^6, 2^8, … 2^max_log` (steps by 2), or `[64]` in
/// smoke mode. One sweep feeds all three row functions.
fn sweep_for(smoke: bool, max_log: u32) -> Vec<usize> {
    if smoke {
        return vec![64];
    }
    (6..=max_log).step_by(2).map(|k| 1usize << k).collect()
}

// ---- Row functions. ----

/// Measure one native chain row: `KeccakSetup::prove_chain` and
/// `verify_chain` at `n`, best of `runs`.
fn native_row(n: usize, native_rate: f64, runs: usize) -> BenchRow {
    let (setup, setup_s) = time_best(1, || KeccakSetup::new(n));
    assert_eq!(
        setup.n_keccak_slots(),
        n,
        "chain rows must fill their slots"
    );
    let ((inputs, x0, x_last), witness_s) = time_best(1, || keccak_honest_chain(n, CHAIN_SEED));

    let ((proof, commitment), prove_s) = time_best(runs, || {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup.prove_chain(&inputs, &mut challenger)
    });
    let ((), verify_s) = time_best(runs, || {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .verify_chain(&commitment, &proof, &x0, &x_last, &mut challenger)
            .expect("native chain verify of a fresh proof");
    });

    BenchRow::new(
        "native-ligerito",
        "chain-in-circuit",
        n,
        setup.n_keccak_slots(),
        RowTimings {
            setup_s,
            witness_s,
            prove_s,
            verify_s,
        },
        proof_size(&proof) + proof_size(&commitment),
        native_rate,
        format!("{:?}", setup.pcs_params),
    )
}

/// Measure one succinct public-chain row: `KeccakZkSetup::prove_succinct`
/// and `verify_succinct` at `n`, best of `runs`.
fn succinct_row(n: usize, native_rate: f64, runs: usize) -> BenchRow {
    let (setup, setup_s) = time_best(1, || KeccakZkSetup::new(n));
    let ((inputs, outputs), witness_s) = time_best(1, || {
        let (inputs, _x0, x_last) = keccak_honest_chain(n, CHAIN_SEED);
        let outputs = chain_outputs(&inputs, &x_last);
        (inputs, outputs)
    });

    let ((proof, commitment), prove_s) = time_best(runs, || {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct(&inputs, &outputs, &mut rng, &mut challenger)
            .expect("succinct prove on an honest witness")
    });
    let ((), verify_s) = time_best(runs, || {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .verify_succinct(&commitment, &proof, &inputs, &outputs, &mut challenger)
            .expect("succinct verify of a fresh proof");
        assert!(verify_state_linkage(&inputs, &outputs), "public linkage");
    });

    BenchRow::new(
        "veil-succinct",
        "public-chain",
        n,
        setup.n_keccak_slots(),
        RowTimings {
            setup_s,
            witness_s,
            prove_s,
            verify_s,
        },
        proof_size(&proof) + proof_size(&commitment),
        native_rate,
        format!("{:?}", setup.pcs_params),
    )
}

/// The succinct-VEIL prover with IN-CIRCUIT linkage (Part 7): endpoints
/// only are public; the committed witness enforces every interior link.
/// This row and the native row prove the SAME relation — the first
/// equal-relation cross-backend comparison in the suite.
fn succinct_chain_row(n: usize, native_rate: f64, runs: usize) -> BenchRow {
    let (setup, setup_s) = time_best(1, || KeccakZkSetup::new(n));
    assert_eq!(
        setup.n_keccak_slots(),
        n,
        "chain rows must fill their slots"
    );
    let ((inputs, x0, x_last), witness_s) = time_best(1, || keccak_honest_chain(n, CHAIN_SEED));

    let ((proof, commitment), prove_s) = time_best(runs, || {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct_chain(&inputs, &mut rng, &mut challenger)
            .expect("succinct chain prove on an honest witness")
    });
    let ((), verify_s) = time_best(runs, || {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .verify_succinct_chain(&commitment, &proof, &x0, &x_last, &mut challenger)
            .expect("succinct chain verify of a fresh proof");
    });

    BenchRow::new(
        "veil-succinct",
        "chain-in-circuit",
        n,
        setup.n_keccak_slots(),
        RowTimings {
            setup_s,
            witness_s,
            prove_s,
            verify_s,
        },
        proof_size(&proof) + proof_size(&commitment),
        native_rate,
        format!("{:?}", setup.pcs_params),
    )
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;

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
//! fallback; a flag wins over its env var).

use blake3_bench::{
    BenchRow, RowTimings, max_log_from_env, parse_max_log, print_table, probe_json_path,
    proof_size, runs_for, smoke, time_best, write_json,
};
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

fn main() {
    run(Args::parse());
}

/// Parsed invocation of the `keccak_e2e` bin.
///
/// Flags: `--smoke`, `--runs <1..=16>`, `--max-log <6..=19>`,
/// `--json <path>`. Each flag wins over its env-var fallback
/// (`BENCH_SMOKE`, smoke-derived run count, `BENCH_KECCAK_MAX_LOG`).
struct Args {
    /// Shrink the sweep to one small point.
    smoke: bool,
    /// Timing runs per row (best-of-N).
    runs: usize,
    /// Upper log2 bound of the sweep.
    max_log: u32,
    /// Optional `--json` output path.
    json: Option<String>,
}

impl Args {
    /// Parse the process arguments, fail-loud on anything unknown.
    ///
    /// Env vars serve as fallbacks only; a flag always wins. The
    /// `BENCH_KECCAK_MAX_LOG` fallback is read and validated here even
    /// when the sweep will not use it (smoke mode) — fail-fast on a bad
    /// override is intended, and stricter than the pre-split bench,
    /// which read the var only on the non-smoke path.
    fn parse() -> Self {
        Self::from_parts(
            std::env::args().skip(1),
            smoke(),
            max_log_from_env("BENCH_KECCAK_MAX_LOG", 12, 6, 19, MAX_LOG_HINT),
        )
    }

    /// Env-free core of [`Args::parse`]: `env_smoke` and `env_max_log`
    /// carry the already-resolved env fallbacks, so unit tests need no
    /// env vars.
    fn from_parts(
        mut args: impl Iterator<Item = String>,
        env_smoke: bool,
        env_max_log: u32,
    ) -> Self {
        let mut smoke_flag = false;
        let mut runs_flag: Option<usize> = None;
        let mut max_log_flag: Option<u32> = None;
        let mut json: Option<String> = None;
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--smoke" => smoke_flag = true,
                "--runs" => {
                    let value = args.next().expect("--runs needs a count");
                    let n: usize = value
                        .trim()
                        .parse()
                        .unwrap_or_else(|_| panic!("--runs must be an integer"));
                    assert!((1..=16).contains(&n), "--runs must be in 1..=16");
                    runs_flag = Some(n);
                }
                "--max-log" => {
                    let value = args.next().expect("--max-log needs a value");
                    max_log_flag = Some(parse_max_log("--max-log", &value, 6, 19, MAX_LOG_HINT));
                }
                "--json" => json = Some(args.next().expect("--json needs a file path")),
                other => panic!(
                    "unknown flag {other:?}; known flags: \
                     --smoke --runs --max-log --json"
                ),
            }
        }
        let smoke = smoke_flag || env_smoke;
        let runs = runs_flag.unwrap_or_else(|| runs_for(smoke));
        let max_log = max_log_flag.unwrap_or(env_max_log);
        Args {
            smoke,
            runs,
            max_log,
            json,
        }
    }
}

/// Run the full e2e sweep for the parsed arguments.
///
/// Steps: probe the `--json` path, build the rayon pool, print the smoke
/// banner, calibrate the native rate once, run the sweep — three rows per
/// point with a progress table after each — then print the final table
/// and write the JSON dump.
fn run(args: Args) {
    // Resolve and probe the --json path FIRST: a bad path found after the
    // sweep would discard every measured row.
    if let Some(path) = &args.json {
        probe_json_path(path);
    }
    flock_prover::init_perf_thread_pool();
    if args.smoke {
        println!(
            "smoke mode: shrunken sweep, {} timing run(s) per row",
            args.runs
        );
    }
    let native_rate = keccak_native_rate_with(args.smoke);
    println!(
        "native keccak-f chain rate: {:.2} Mperm/s",
        native_rate / 1e6
    );

    let mut rows = Vec::new();
    for n in sweep_for(args.smoke, args.max_log) {
        rows.push(native_row(n, native_rate, args.runs));
        print_table("keccak hashchain e2e (in progress)", &rows);
        rows.push(succinct_row(n, native_rate, args.runs));
        print_table("keccak hashchain e2e (in progress)", &rows);
        rows.push(succinct_chain_row(n, native_rate, args.runs));
        print_table("keccak hashchain e2e (in progress)", &rows);
    }
    print_table("keccak hashchain e2e (final)", &rows);
    if let Some(path) = args.json {
        // The JSON title stays "keccak_hashchain_e2e": it is the
        // cross-commit tracking key. The target rename is not a schema
        // change.
        write_json(&path, "keccak_hashchain_e2e", &rows).expect("write --json results");
        println!("wrote {path}");
    }
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

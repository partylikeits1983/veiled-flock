//! End-to-end BLAKE3 hash-chain proving runner over both veil-f128
//! backends — the `blake3_e2e` bin.
//!
//! Backends:
//! - `veil-framed`: `VeiledBlake3Setup` over `veil_f128::prove_block_r1cs`.
//! - `veil-succinct`: `Blake3PreimageZkSetup` over
//!   `succinct_veil::prove_succinct_veil_r1cs`.
//!
//! Relation: every row is `public-chain`. Each block proves one preimage
//! relation with a public digest. The circuit does not check chain linkage.
//! The chain rule is public, so the benched verify closure recomputes
//! `blake3(digest_i || zeros) == digest_{i + 1}` for every link — the
//! `verify` column therefore covers the full public-chain relation.
//!
//! Run: `cargo run --profile bench -p blake3-bench --bin blake3_e2e --`
//! Smoke: append `--smoke` (the `BENCH_SMOKE=1` env var stays as a
//! fallback; a flag wins over its env var).

use blake3_bench::{
    BenchRow, RowTimings, blake3_chain, blake3_native_rate_with, max_log_from_env, parse_max_log,
    print_table, probe_json_path, proof_size, runs_for, smoke, time_best, verify_chain_linkage,
    write_json,
};
use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup;
use flock_prover::veiled_preimage::VeiledBlake3Setup;
use flock_prover::zk::ZkRng;

const DOMAIN: &[u8] = b"veiled-flock-bench-blake3-e2e-v0";
const CHAIN_SEED: u64 = 0xC0FFEE_42;
const ZK_SEED: [u8; 32] = [0x42; 32];

/// Hint shown when a framed sweep override is out of range. The flag and
/// the env fallback share it.
const FRAMED_MAX_LOG_HINT: &str = "m = 14 + log; see the memory model on framed_sweep_for";

fn main() {
    run(Args::parse());
}

/// Parsed invocation of the `blake3_e2e` bin.
///
/// Flags: `--smoke`, `--runs <1..=16>`, `--framed-max-log <1..=14>`,
/// `--json <path>`. Each flag wins over its env-var fallback
/// (`BENCH_SMOKE`, smoke-derived run count, `BENCH_FRAMED_MAX_LOG`).
struct Args {
    /// Shrink each sweep to one small row.
    smoke: bool,
    /// Timing runs per row (best-of-N).
    runs: usize,
    /// Upper log2 bound of the framed sweep.
    framed_max_log: u32,
    /// Optional `--json` output path.
    json: Option<String>,
}

impl Args {
    /// Parse the process arguments, fail-loud on anything unknown.
    ///
    /// Env vars serve as fallbacks only; a flag always wins. The
    /// `BENCH_FRAMED_MAX_LOG` fallback is read and validated here even
    /// when the sweep will not use it (smoke mode) — fail-fast on a bad
    /// override is intended, and stricter than the pre-split bench,
    /// which read the var only on the non-smoke path.
    fn parse() -> Self {
        Self::from_parts(
            std::env::args().skip(1),
            smoke(),
            max_log_from_env("BENCH_FRAMED_MAX_LOG", 6, 1, 14, FRAMED_MAX_LOG_HINT),
        )
    }

    /// Env-free core of [`Args::parse`]: `env_smoke` and
    /// `env_framed_max_log` carry the already-resolved env fallbacks, so
    /// unit tests need no env vars.
    fn from_parts(
        mut args: impl Iterator<Item = String>,
        env_smoke: bool,
        env_framed_max_log: u32,
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
                "--framed-max-log" => {
                    let value = args.next().expect("--framed-max-log needs a value");
                    max_log_flag = Some(parse_max_log(
                        "--framed-max-log",
                        &value,
                        1,
                        14,
                        FRAMED_MAX_LOG_HINT,
                    ));
                }
                "--json" => json = Some(args.next().expect("--json needs a file path")),
                other => panic!(
                    "unknown flag {other:?}; known flags: \
                     --smoke --runs --framed-max-log --json"
                ),
            }
        }
        let smoke = smoke_flag || env_smoke;
        let runs = runs_flag.unwrap_or_else(|| runs_for(smoke));
        let framed_max_log = max_log_flag.unwrap_or(env_framed_max_log);
        Args {
            smoke,
            runs,
            framed_max_log,
            json,
        }
    }
}

/// Run the full e2e sweep for the parsed arguments.
///
/// Steps: probe the `--json` path, build the rayon pool, print the smoke
/// banner, calibrate the native rate once, run both sweeps with a
/// progress table per row, then print the final table and write the JSON
/// dump.
fn run(args: Args) {
    // Resolve and probe the --json path FIRST: a bad path found after the
    // sweep would discard every measured row.
    if let Some(path) = &args.json {
        probe_json_path(path);
    }
    flock_prover::init_perf_thread_pool();
    if args.smoke {
        println!(
            "smoke mode: shrunken sweeps, {} timing run(s) per row",
            args.runs
        );
    }
    let native_rate = blake3_native_rate_with(args.smoke);
    println!("native blake3 chain rate: {:.2} Mhash/s", native_rate / 1e6);

    let mut rows = Vec::new();
    for n_blocks in framed_sweep_for(args.smoke, args.framed_max_log) {
        rows.push(framed_row(n_blocks, native_rate, args.runs));
        print_table("blake3 hashchain e2e (in progress)", &rows);
    }
    for n_real in succinct_sweep_for(args.smoke) {
        rows.push(succinct_row(n_real, native_rate, args.runs));
        print_table("blake3 hashchain e2e (in progress)", &rows);
    }
    print_table("blake3 hashchain e2e (final)", &rows);
    if let Some(path) = args.json {
        // The JSON title stays "blake3_hashchain_e2e": it is the
        // cross-commit tracking key. The target rename is not a schema
        // change.
        write_json(&path, "blake3_hashchain_e2e", &rows).expect("write --json results");
        println!("wrote {path}");
    }
}

// ---- Sweep shapes. Env-free: the caller resolves smoke mode and
// overrides, so unit tests need no env vars. ----

/// Framed sweep: `n_blocks = 2^1 ..= 2^max_log`, or `[2]` in smoke mode.
///
/// Framed memory model: let `m = 14 + n_blocks_log` and `N = 2^m` (witness
/// bits). `VeiledBlake3Setup::prove` expands z, a, and b to one `F128` per
/// witness bit — `3 * 16 * N` bytes — and `prove_block_r1cs` commits vectors
/// of length `N + 6` and `2N + 2` at inverse rate 4. At `n_blocks = 64`
/// (m = 20) that is ~50 MB of expansion plus ~0.5 GB of rate-4 codewords —
/// about a 1 GB peak, the default budget. At `n_blocks = 1024` (m = 24) it
/// is ~805 MB of expansion plus multi-GB codewords. Set the sweep bound
/// (`--framed-max-log` or `BENCH_FRAMED_MAX_LOG`) above 6 only after
/// measuring.
fn framed_sweep_for(smoke: bool, max_log: u32) -> Vec<usize> {
    if smoke {
        return vec![2];
    }
    (1..=max_log).map(|k| 1usize << k).collect()
}

/// Succinct sweep, or `[1]` in smoke mode (n_real = 1 pads to the
/// 256-slot succinct floor).
fn succinct_sweep_for(smoke: bool) -> Vec<usize> {
    if smoke {
        vec![1]
    } else {
        vec![256, 512, 1024, 2048]
    }
}

// ---- Row functions. ----

/// Measure one framed row: `VeiledBlake3Setup` prove and verify at
/// `n_blocks`, best of `runs`.
fn framed_row(n_blocks: usize, native_rate: f64, runs: usize) -> BenchRow {
    let (setup, setup_s) = time_best(1, || VeiledBlake3Setup::new(n_blocks));
    let ((messages, digests), witness_s) = time_best(1, || blake3_chain(n_blocks, CHAIN_SEED));

    let (proof, prove_s) = time_best(runs, || {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove(&messages, &digests, &mut rng, &mut challenger)
            .expect("framed prove on an honest witness")
    });
    let ((), verify_s) = time_best(runs, || {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .verify(&proof, &digests, &mut challenger)
            .expect("framed verify of a fresh proof");
        assert!(verify_chain_linkage(&digests), "public chain linkage");
    });

    BenchRow::new(
        "veil-framed",
        "public-chain",
        n_blocks,
        setup.n_block_slots(),
        RowTimings {
            setup_s,
            witness_s,
            prove_s,
            verify_s,
        },
        proof_size(&proof),
        native_rate,
        format!("{:?}", setup.parameters()),
    )
}

/// Measure one succinct row: `Blake3PreimageZkSetup` prove and verify at
/// `n_real`, best of `runs`.
fn succinct_row(n_real: usize, native_rate: f64, runs: usize) -> BenchRow {
    let (setup, setup_s) = time_best(1, || Blake3PreimageZkSetup::new_succinct(n_real));
    let ((messages, digests), witness_s) = time_best(1, || blake3_chain(n_real, CHAIN_SEED));

    let ((proof, commitment), prove_s) = time_best(runs, || {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct(&messages, &digests, &mut rng, &mut challenger)
            .expect("succinct prove on an honest witness")
    });
    let ((), verify_s) = time_best(runs, || {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .verify_succinct(&commitment, &proof, &digests, &mut challenger)
            .expect("succinct verify of a fresh proof");
        assert!(verify_chain_linkage(&digests), "public chain linkage");
    });

    BenchRow::new(
        "veil-succinct",
        "public-chain",
        n_real,
        setup.n_block_slots(),
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

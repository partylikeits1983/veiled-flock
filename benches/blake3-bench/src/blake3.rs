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
//! fallback; a flag wins over its env var). Flag parsing and the run
//! prologue live in the `bench-harness` driver ([`E2eBench`]); this bin
//! owns the sweeps and row functions.

use bench_harness::{BenchRow, BenchSpec, E2eBench, MaxLogFlag, RowTimings, proof_size, time_best};
use blake3_bench::{
    CHAIN_SEED, DOMAIN, ZK_SEED, blake3_chain, blake3_native_rate_with, verify_chain_linkage,
};
use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup;
use flock_prover::veiled_preimage::VeiledBlake3Setup;
use flock_prover::zk::ZkRng;

/// Hint shown when a framed sweep override is out of range. The flag and
/// the env fallback share it.
const FRAMED_MAX_LOG_HINT: &str = "m = 14 + log; see the memory model on framed_sweep_for";

/// This crate's bench identity: titles, banner phrases, and the framed
/// sweep-bound flag. The JSON title is the cross-commit tracking key.
static SPEC: BenchSpec = BenchSpec {
    table_title: "blake3 hashchain e2e",
    json_title: "blake3_hashchain_e2e",
    smoke_banner: "shrunken sweeps",
    rate_label: "native blake3 chain rate",
    rate_unit: "Mhash/s",
    max_log: MaxLogFlag {
        flag: "--framed-max-log",
        env: "BENCH_FRAMED_MAX_LOG",
        default: 6,
        min: 1,
        max: 14,
        hint: FRAMED_MAX_LOG_HINT,
    },
};

fn main() {
    let mut bench = E2eBench::start(&SPEC, blake3_native_rate_with);
    let rate = bench.native_rate();
    for n_blocks in framed_sweep_for(bench.smoke(), bench.max_log()) {
        bench.push(framed_row(n_blocks, rate, bench.runs()));
    }
    for n_real in succinct_sweep_for(bench.smoke()) {
        bench.push(succinct_row(n_real, rate, bench.runs()));
    }
    bench.finish();
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

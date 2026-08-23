//! End-to-end keccak-f hash-chain proving benchmark.
//!
//! Two provers per sweep point:
//! - `native-ligerito`, relation `chain-in-circuit`: `KeccakSetup::prove_chain`
//!   enforces `state_24[i] == state_0[i + 1]` in the committed witness; only
//!   the endpoints `x_0` / `x_last` are public.
//! - `veil-succinct`, relation `public-chain`: `KeccakZkSetup` proves each
//!   permutation with both states public. The benched verify closure also
//!   checks linkage over the public states (`outputs[i] == inputs[i + 1]`) —
//!   a pure equality check, so the `verify` column covers the full
//!   public-chain relation.
//!
//! Sweep: n in {64, 256, 1024, 4096} (m = 22, 24, 26, 28). The valid chain
//! range reaches n = 524288 (m = 35), but the upper range is unrunnable on a
//! workstation — set `BENCH_KECCAK_MAX_LOG` above 12 only after measuring.
//!
//! Run: `cargo bench -p keccak-bench`.
//! Smoke: `BENCH_SMOKE=1 cargo bench -p keccak-bench` (n = 64, 1 run).

use blake3_bench::{
    BenchRow, RowTimings, json_path_from_args, max_log_from_env, print_table, proof_size, runs,
    smoke, time_best, write_json,
};
use flock_prover::challenger::FsChallenger;
use flock_prover::r1cs_hashes::keccak::{KeccakSetup, KeccakZkSetup, State, keccak_f};
use flock_prover::zk::ZkRng;
use keccak_bench::{keccak_honest_chain, keccak_native_rate, verify_state_linkage};

const DOMAIN: &[u8] = b"veiled-flock-bench-keccak-e2e-v0";
const CHAIN_SEED: u64 = 0xC0FFEE_43;
const ZK_SEED: [u8; 32] = [0x43; 32];

fn sweep() -> Vec<usize> {
    if smoke() {
        return vec![64];
    }
    let max_log = max_log_from_env(
        "BENCH_KECCAK_MAX_LOG",
        12,
        6,
        19,
        "m = 16 + log; configs stop at m = 35",
    );
    (6..=max_log).step_by(2).map(|k| 1usize << k).collect()
}

/// The chain's per-block output states: `outputs[i] = inputs[i + 1]`, and
/// the last output is `x_last`.
fn chain_outputs(inputs: &[State], x_last: &State) -> Vec<State> {
    let mut outputs: Vec<State> = inputs[1..].to_vec();
    outputs.push(*x_last);
    outputs
}

fn native_row(n: usize, native_rate: f64) -> BenchRow {
    let (setup, setup_s) = time_best(1, || KeccakSetup::new(n));
    assert_eq!(
        setup.n_keccak_slots(),
        n,
        "chain rows must fill their slots"
    );
    let ((inputs, x0, x_last), witness_s) = time_best(1, || keccak_honest_chain(n, CHAIN_SEED));

    let ((proof, commitment), prove_s) = time_best(runs(), || {
        let mut challenger = FsChallenger::new(DOMAIN);
        setup.prove_chain(&inputs, &mut challenger)
    });
    let ((), verify_s) = time_best(runs(), || {
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

fn succinct_row(n: usize, native_rate: f64) -> BenchRow {
    let (setup, setup_s) = time_best(1, || KeccakZkSetup::new(n));
    let ((inputs, outputs), witness_s) = time_best(1, || {
        let (inputs, _x0, x_last) = keccak_honest_chain(n, CHAIN_SEED);
        let outputs = chain_outputs(&inputs, &x_last);
        (inputs, outputs)
    });

    let ((proof, commitment), prove_s) = time_best(runs(), || {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct(&inputs, &outputs, &mut rng, &mut challenger)
            .expect("succinct prove on an honest witness")
    });
    let ((), verify_s) = time_best(runs(), || {
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

fn main() {
    flock_prover::init_perf_thread_pool();
    if smoke() {
        println!("BENCH_SMOKE: n = 64 only, 1 timing run per row");
    }
    let native_rate = keccak_native_rate();
    println!(
        "native keccak-f chain rate: {:.2} Mperm/s",
        native_rate / 1e6
    );
    // Sanity: keep the two provers' witnesses on the same chain rule.
    {
        let (inputs, _x0, x_last) = keccak_honest_chain(4, CHAIN_SEED);
        let outputs = chain_outputs(&inputs, &x_last);
        let mut image = inputs[0];
        keccak_f(&mut image);
        assert_eq!(image, outputs[0]);
    }

    let mut rows = Vec::new();
    for n in sweep() {
        rows.push(native_row(n, native_rate));
        print_table("keccak hashchain e2e (in progress)", &rows);
        rows.push(succinct_row(n, native_rate));
        print_table("keccak hashchain e2e (in progress)", &rows);
    }
    print_table("keccak hashchain e2e (final)", &rows);
    if let Some(path) = json_path_from_args() {
        write_json(&path, "keccak_hashchain_e2e", &rows).expect("write --json results");
        println!("wrote {path}");
    }
}

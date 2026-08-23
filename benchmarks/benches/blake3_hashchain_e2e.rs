//! End-to-end BLAKE3 hash-chain proving benchmark over both veil-f128
//! backends.
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
//! Framed memory model: let `m = 14 + n_blocks_log` and `N = 2^m` (witness
//! bits). `VeiledBlake3Setup::prove` expands z, a, and b to one `F128` per
//! witness bit — `3 * 16 * N` bytes — and `prove_block_r1cs` commits vectors
//! of length `N + 6` and `2N + 2` at inverse rate 4. At `n_blocks = 64`
//! (m = 20) that is ~50 MB of expansion plus ~0.5 GB of rate-4 codewords —
//! about a 1 GB peak, the default budget. At `n_blocks = 1024` (m = 24) it
//! is ~805 MB of expansion plus multi-GB codewords. Set
//! `BENCH_FRAMED_MAX_LOG` above 6 only after measuring.
//!
//! Run: `cargo bench -p veiled-flock-benchmarks`.
//! Smoke: `BENCH_SMOKE=1 cargo bench -p veiled-flock-benchmarks`.

use bincode::Options;
use flock_prover::challenger::FsChallenger;
use flock_prover::proof_io::fixint_options;
use flock_prover::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup;
use flock_prover::veiled_preimage::VeiledBlake3Setup;
use flock_prover::zk::ZkRng;
use veiled_flock_benchmarks::{
    BenchRow, RowTimings, blake3_chain, blake3_native_rate, print_table, runs, smoke, time_best,
    verify_chain_linkage,
};

const DOMAIN: &[u8] = b"veiled-flock-bench-blake3-e2e-v0";
const CHAIN_SEED: u64 = 0xC0FFEE_42;
const ZK_SEED: [u8; 32] = [0x42; 32];

/// Size a value with the canonical fixint encoder (no size limit — framed
/// proofs exceed the CLI's untrusted-read cap by design).
fn proof_size<T: serde::Serialize>(value: &T) -> usize {
    fixint_options()
        .serialized_size(value)
        .expect("bincode size of an in-memory proof") as usize
}

fn framed_sweep() -> Vec<usize> {
    if smoke() {
        return vec![2];
    }
    let max_log: u32 = match std::env::var("BENCH_FRAMED_MAX_LOG") {
        Err(_) => 6,
        Ok(v) => {
            let k = v
                .trim()
                .parse()
                .expect("BENCH_FRAMED_MAX_LOG must be an integer");
            assert!(
                (1..=14).contains(&k),
                "BENCH_FRAMED_MAX_LOG must be in 1..=14 (m = 14 + log; see the memory model)"
            );
            k
        }
    };
    (1..=max_log).map(|k| 1usize << k).collect()
}

fn succinct_sweep() -> Vec<usize> {
    if smoke() {
        // n_real = 1 pads to the 256-slot succinct floor.
        vec![1]
    } else {
        vec![256, 512, 1024, 2048]
    }
}

fn framed_row(n_blocks: usize, native_rate: f64) -> BenchRow {
    let (setup, setup_s) = time_best(1, || VeiledBlake3Setup::new(n_blocks));
    let ((messages, digests), witness_s) = time_best(1, || blake3_chain(n_blocks, CHAIN_SEED));

    let (proof, prove_s) = time_best(runs(), || {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove(&messages, &digests, &mut rng, &mut challenger)
            .expect("framed prove on an honest witness")
    });
    let ((), verify_s) = time_best(runs(), || {
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

fn succinct_row(n_real: usize, native_rate: f64) -> BenchRow {
    let (setup, setup_s) = time_best(1, || Blake3PreimageZkSetup::new_succinct(n_real));
    let ((messages, digests), witness_s) = time_best(1, || blake3_chain(n_real, CHAIN_SEED));

    let ((proof, commitment), prove_s) = time_best(runs(), || {
        let mut rng = ZkRng::from_seed(ZK_SEED);
        let mut challenger = FsChallenger::new(DOMAIN);
        setup
            .prove_succinct(&messages, &digests, &mut rng, &mut challenger)
            .expect("succinct prove on an honest witness")
    });
    let ((), verify_s) = time_best(runs(), || {
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

fn main() {
    flock_prover::init_perf_thread_pool();
    if smoke() {
        println!("BENCH_SMOKE: shrunken sweeps, 1 timing run per row");
    }
    let native_rate = blake3_native_rate();
    println!("native blake3 chain rate: {:.2} Mhash/s", native_rate / 1e6);

    let mut rows = Vec::new();
    for n_blocks in framed_sweep() {
        rows.push(framed_row(n_blocks, native_rate));
        print_table("blake3 hashchain e2e (in progress)", &rows);
    }
    for n_real in succinct_sweep() {
        rows.push(succinct_row(n_real, native_rate));
        print_table("blake3 hashchain e2e (in progress)", &rows);
    }
    print_table("blake3 hashchain e2e (final)", &rows);
}

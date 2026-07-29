//! Certified zero-knowledge prover cost for the path covered by the ZK claim.
//! No criterion; custom main (repo convention).
//!
//! This is deliberately separate from `zk_vs_baseline`, which measures the
//! optimized `prove_fast_zk` pipeline. That pipeline carries no certified
//! zero-knowledge claim. The numbers here are for `Blake3Setup::prove_zk_a1`
//! and `verify_zk_a1`, which use the production field-valued mask with public
//! Q-star, the A2-masked lincheck, and the extra hiding commitments and
//! openings. The certified path uses naive round-pair kernels by design. It is
//! correctness- and certification-oriented, not optimized.
//!
//! Phases are timed separately so the paper can attribute the overhead:
//!   witness  - zk witness generation + packing (randomizer rows included)
//!   prove    - commitments, masked zerocheck and lincheck, hiding openings
//!   verify   - full certified ZK verification
//!
//! A non-zk `prove_fast` run at the same batch size is included as a
//! context row, clearly labelled as a different pipeline.
//!
//! Machine-parseable lines:
//!   RESULT\tzk_a1_reference\tblake3\t{batch}\t{phase}\t{secs}
//!
//! Env: ZKA1_NS (default "256", the certified configuration), ZKA1_RUNS
//! (default 5). Run alone:
//!   `ZKA1_NS=256 ZKA1_RUNS=5 cargo bench --features zk,symbolic --bench zk_a1_reference`

use flock_core::challenger::FsChallenger;
use flock_core::zk::ZkRng;
use flock_prover::proof_io::{R1csProofBundleLigerito, R1csProofBundleZkA1};
use flock_prover::r1cs_hashes::blake3::{Blake3Setup, Compression};
use std::time::Instant;

struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        (z ^ (z >> 31)) as u32
    }
}

fn gen_blocks(n: usize, rng: &mut Rng) -> Vec<Compression> {
    (0..n)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect()
}

const DOMAIN: &[u8] = b"flock-zka1-bench";

fn main() {
    let ns: Vec<usize> = std::env::var("ZKA1_NS")
        .unwrap_or_else(|_| "256".into())
        .split(',')
        .filter_map(|s| s.trim().parse().ok())
        .collect();
    let runs: usize = std::env::var("ZKA1_RUNS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);

    println!("Certified ZK prover for a BLAKE3 batch");
    println!("threads: {}", rayon::current_num_threads());
    println!("runs per cell: {runs} (best-of), after one verified warm-up");
    println!();
    println!(
        "{:>8} {:>4} {:>10} | {:>10} {:>10} {:>8} | {:>10} {:>10} {:>8} | {:>7} {:>7}",
        "batch",
        "m",
        "witness",
        "zk prove",
        "zk verify",
        "zk KiB",
        "base prove",
        "base verify",
        "base KiB",
        "prove x",
        "size x"
    );

    for &n in &ns {
        let mut rng = Rng(0xA1_BE0_0000 ^ n as u64);
        let blocks = gen_blocks(n, &mut rng);
        let setup = Blake3Setup::with_zk(n);
        let m = setup.m();

        // Warm-up: prove and verify once (also proves the config is
        // certificate-gated; an uncertified batch size errors here).
        let zk_proof_bytes = {
            let mut zk_rng = ZkRng::from_entropy();
            let mut ch = FsChallenger::new(DOMAIN);
            let (proof, comm) = setup
                .prove_zk_a1_with_rng(&blocks, &mut zk_rng, &mut ch)
                .expect("benchmark requires a certified configuration");
            let mut chv = FsChallenger::new(DOMAIN);
            setup
                .verify_zk_a1(&comm, &proof, &mut chv)
                .expect("warm-up proof must verify");
            R1csProofBundleZkA1 {
                commitment: comm,
                proof,
            }
            .to_bytes()
            .len()
        };

        let mut best_prove = f64::MAX;
        let mut best_verify = f64::MAX;
        for _ in 0..runs {
            let mut zk_rng = ZkRng::from_entropy();
            let mut ch = FsChallenger::new(DOMAIN);
            let t0 = Instant::now();
            let (proof, comm) = setup
                .prove_zk_a1_with_rng(&blocks, &mut zk_rng, &mut ch)
                .expect("certified");
            best_prove = best_prove.min(t0.elapsed().as_secs_f64());

            let mut chv = FsChallenger::new(DOMAIN);
            let t1 = Instant::now();
            setup.verify_zk_a1(&comm, &proof, &mut chv).expect("verify");
            best_verify = best_verify.min(t1.elapsed().as_secs_f64());
        }

        // Witness generation alone, for attribution (the same call the
        // gated prove entry makes internally).
        let mut best_witness = f64::MAX;
        for _ in 0..runs {
            let t0 = Instant::now();
            let w = setup.generate_witness(&blocks);
            best_witness = best_witness.min(t0.elapsed().as_secs_f64());
            std::hint::black_box(&w);
        }

        // Context row: the optimized NON-zk pipeline at the same batch.
        let base_setup = Blake3Setup::new(n);
        let mut best_fast = f64::MAX;
        let mut best_fast_verify = f64::MAX;
        let base_proof_bytes = {
            let mut ch = FsChallenger::new(b"flock-zka1-bench-base");
            let (proof, commitment, _) = base_setup.prove_fast(&blocks, &mut ch);
            let mut chv = FsChallenger::new(b"flock-zka1-bench-base");
            base_setup
                .verify(&commitment, &proof, &mut chv)
                .expect("non-zk warm-up proof must verify");
            let bytes = R1csProofBundleLigerito { commitment, proof }
                .to_bytes()
                .len();
            for _ in 0..runs {
                let mut ch = FsChallenger::new(b"flock-zka1-bench-base");
                let t0 = Instant::now();
                let (proof, commitment, _) = base_setup.prove_fast(&blocks, &mut ch);
                best_fast = best_fast.min(t0.elapsed().as_secs_f64());
                let mut chv = FsChallenger::new(b"flock-zka1-bench-base");
                let t1 = Instant::now();
                base_setup
                    .verify(&commitment, &proof, &mut chv)
                    .expect("non-zk proof must verify");
                best_fast_verify = best_fast_verify.min(t1.elapsed().as_secs_f64());
                std::hint::black_box((&proof, &commitment));
            }
            bytes
        };

        println!(
            "{n:>8} {m:>4} {best_witness:>10.4} | {best_prove:>10.4} {best_verify:>10.4} \
             {:>8} | {best_fast:>10.4} {best_fast_verify:>10.4} {:>8} | {:>7.2} {:>7.2}",
            zk_proof_bytes / 1024,
            base_proof_bytes / 1024,
            best_prove / best_fast,
            zk_proof_bytes as f64 / base_proof_bytes as f64,
        );
        println!("RESULT\tzk_a1_reference\tblake3\t{n}\twitness\t{best_witness:.6}");
        println!("RESULT\tzk_a1_reference\tblake3\t{n}\tprove\t{best_prove:.6}");
        println!("RESULT\tzk_a1_reference\tblake3\t{n}\tverify\t{best_verify:.6}");
        println!("RESULT\tzk_a1_reference\tblake3\t{n}\tfast_nonzk_prove\t{best_fast:.6}");
        println!("RESULT\tzk_a1_reference\tblake3\t{n}\tfast_nonzk_verify\t{best_fast_verify:.6}");
        println!("RESULT\tzk_a1_reference\tblake3\t{n}\tzk_proof_bytes\t{zk_proof_bytes}");
        println!(
            "RESULT\tzk_a1_reference\tblake3\t{n}\tfast_nonzk_proof_bytes\t{base_proof_bytes}"
        );
        println!(
            "  certified/non-zk prove ratio: {:.2}x  (the certified path is \
             unoptimized by design)",
            best_prove / best_fast
        );
    }
}

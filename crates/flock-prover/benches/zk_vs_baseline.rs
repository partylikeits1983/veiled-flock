//! zk vs baseline BLAKE3 batch proving — the headline comparison for the
//! zero-knowledge PoC. No criterion; custom main (repo convention).
//!
//! For each batch size: prove wall time (best of `ZKB_RUNS` after one
//! verified warm-up), single verify wall time, and serialized proof size,
//! for the baseline (`Blake3Setup::new`) and zk (`Blake3Setup::with_zk`)
//! pipelines, plus the zk/baseline ratios.
//!
//! Machine-parseable lines:
//!   RESULT\tzk_vs_baseline\tblake3\t{batch}\t{mode}\t{prove_s}\t{verify_s}\t{proof_bytes}
//!
//! Env: ZKB_LOG2S (default "10,12,14"), ZKB_RUNS (default 3).
//! Run alone (`cargo bench --features zk --bench zk_vs_baseline`).

use flock_core::challenger::FsChallenger;
use flock_prover::proof_io::R1csProofBundleLigerito;
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

struct Cell {
    prove_s: f64,
    verify_s: f64,
    proof_bytes: usize,
}

fn bench_mode(zk: bool, n: usize, blocks: &[Compression], runs: usize) -> Cell {
    let setup = if zk {
        Blake3Setup::with_zk(n)
    } else {
        Blake3Setup::new(n)
    };
    let domain: &[u8] = if zk {
        b"flock-zkb-blake3-zk"
    } else {
        b"flock-zkb-blake3"
    };
    let prove = |ch: &mut FsChallenger| {
        if zk {
            setup.prove_fast_zk(blocks, ch)
        } else {
            setup.prove_fast(blocks, ch)
        }
    };

    // Warm-up: also verified, and its proof is measured for size.
    let mut ch = FsChallenger::new(domain);
    let (proof, commitment, _) = prove(&mut ch);
    let t = Instant::now();
    let mut ch_v = FsChallenger::new(domain);
    setup
        .verify(&commitment, &proof, &mut ch_v)
        .expect("warm-up proof must verify");
    let mut verify_s = t.elapsed().as_secs_f64();
    let proof_bytes = R1csProofBundleLigerito { commitment, proof }
        .to_bytes()
        .len();

    let mut prove_s = f64::INFINITY;
    for _ in 0..runs {
        let mut ch = FsChallenger::new(domain);
        let t = Instant::now();
        let (proof, commitment, _) = std::hint::black_box(prove(&mut ch));
        prove_s = prove_s.min(t.elapsed().as_secs_f64());
        let t = Instant::now();
        let mut ch_v = FsChallenger::new(domain);
        setup
            .verify(&commitment, &proof, &mut ch_v)
            .expect("proof must verify");
        verify_s = verify_s.min(t.elapsed().as_secs_f64());
    }
    Cell {
        prove_s,
        verify_s,
        proof_bytes,
    }
}

fn main() {
    flock_prover::init_perf_thread_pool();
    let log2s: Vec<usize> = std::env::var("ZKB_LOG2S")
        .unwrap_or_else(|_| "10,12,14".into())
        .split(',')
        .map(|s| s.trim().parse().expect("ZKB_LOG2S"))
        .collect();
    let runs: usize = std::env::var("ZKB_RUNS")
        .unwrap_or_else(|_| "3".into())
        .parse()
        .expect("ZKB_RUNS");
    let threads = rayon::current_num_threads();
    println!("zk vs baseline — BLAKE3 batch proving ({threads} threads, best of {runs})\n");
    println!(
        "{:>7} {:>6} | {:>10} {:>10} {:>7} | {:>10} {:>10} {:>7} | {:>6} {:>6} {:>6}",
        "batch",
        "m",
        "base prove",
        "verify",
        "KiB",
        "zk prove",
        "verify",
        "KiB",
        "pr×",
        "vf×",
        "sz×"
    );

    let mut rng = Rng(0x2B3D_5EED);
    for &lg in &log2s {
        let n = 1usize << lg;
        let blocks = gen_blocks(n, &mut rng);
        let base = bench_mode(false, n, &blocks, runs);
        let zk = bench_mode(true, n, &blocks, runs);
        let m = Blake3Setup::new(n).m();
        println!(
            "{:>7} {:>6} | {:>10.3} {:>10.4} {:>7} | {:>10.3} {:>10.4} {:>7} | {:>6.2} {:>6.2} {:>6.2}",
            n,
            m,
            base.prove_s,
            base.verify_s,
            base.proof_bytes / 1024,
            zk.prove_s,
            zk.verify_s,
            zk.proof_bytes / 1024,
            zk.prove_s / base.prove_s,
            zk.verify_s / base.verify_s,
            zk.proof_bytes as f64 / base.proof_bytes as f64,
        );
        for (mode, c) in [("baseline", &base), ("zk", &zk)] {
            println!(
                "RESULT\tzk_vs_baseline\tblake3\t{}\t{}\t{:.6}\t{:.6}\t{}",
                n, mode, c.prove_s, c.verify_s, c.proof_bytes
            );
        }
    }
}

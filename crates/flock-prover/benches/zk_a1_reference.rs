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
//! Machine-parseable lines report median, median absolute deviation (MAD),
//! min, max, proof bytes, and peak incremental heap.
//!
//! Env: ZKA1_NS (default "256", the certified configuration), ZKA1_RUNS
//! (default 5). Run alone:
//!   `ZKA1_NS=256 ZKA1_RUNS=5 cargo bench --features zk,symbolic --bench zk_a1_reference`

use flock_core::challenger::FsChallenger;
use flock_core::zk::ZkRng;
use flock_prover::proof_io::{R1csProofBundleLigerito, R1csProofBundleZkA1};
use flock_prover::r1cs_hashes::blake3::{Blake3Setup, Compression};
use std::alloc::{GlobalAlloc, Layout, System};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

struct PeakAlloc;
static CURRENT_HEAP: AtomicUsize = AtomicUsize::new(0);
static PEAK_HEAP: AtomicUsize = AtomicUsize::new(0);
static BASE_HEAP: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for PeakAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            let current = CURRENT_HEAP.fetch_add(layout.size(), Ordering::Relaxed) + layout.size();
            PEAK_HEAP.fetch_max(current, Ordering::Relaxed);
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) };
        CURRENT_HEAP.fetch_sub(layout.size(), Ordering::Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let out = unsafe { System.realloc(ptr, layout, new_size) };
        if !out.is_null() {
            if new_size >= layout.size() {
                let delta = new_size - layout.size();
                let current = CURRENT_HEAP.fetch_add(delta, Ordering::Relaxed) + delta;
                PEAK_HEAP.fetch_max(current, Ordering::Relaxed);
            } else {
                CURRENT_HEAP.fetch_sub(layout.size() - new_size, Ordering::Relaxed);
            }
        }
        out
    }
}

#[global_allocator]
static ALLOCATOR: PeakAlloc = PeakAlloc;

fn reset_peak_heap() {
    let current = CURRENT_HEAP.load(Ordering::Relaxed);
    BASE_HEAP.store(current, Ordering::Relaxed);
    PEAK_HEAP.store(current, Ordering::Relaxed);
}

fn peak_incremental_heap_bytes() -> usize {
    PEAK_HEAP
        .load(Ordering::Relaxed)
        .saturating_sub(BASE_HEAP.load(Ordering::Relaxed))
}

#[derive(Clone, Copy)]
struct Stats {
    median: f64,
    mad: f64,
    min: f64,
    max: f64,
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(f64::total_cmp);
    let mid = values.len() / 2;
    if values.len().is_multiple_of(2) {
        (values[mid - 1] + values[mid]) * 0.5
    } else {
        values[mid]
    }
}

fn stats(values: &[f64]) -> Stats {
    assert!(!values.is_empty());
    let mut sorted = values.to_vec();
    let median_value = median(&mut sorted);
    let mut deviations = values
        .iter()
        .map(|value| (value - median_value).abs())
        .collect::<Vec<_>>();
    Stats {
        median: median_value,
        mad: median(&mut deviations),
        min: sorted[0],
        max: *sorted.last().unwrap(),
    }
}

fn command_output(program: &str, args: &[&str]) -> String {
    Command::new(program)
        .args(args)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
        .unwrap_or_else(|| "unavailable".to_owned())
}

fn print_stats(batch: usize, phase: &str, stats: Stats) {
    println!(
        "RESULT\tzk_a1_reference\tblake3\t{batch}\t{phase}_median\t{:.9}",
        stats.median
    );
    println!(
        "RESULT\tzk_a1_reference\tblake3\t{batch}\t{phase}_mad\t{:.9}",
        stats.mad
    );
    println!(
        "RESULT\tzk_a1_reference\tblake3\t{batch}\t{phase}_min\t{:.9}",
        stats.min
    );
    println!(
        "RESULT\tzk_a1_reference\tblake3\t{batch}\t{phase}_max\t{:.9}",
        stats.max
    );
}

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
    println!("commit: {}", command_output("git", &["rev-parse", "HEAD"]));
    println!(
        "rustc: {}",
        command_output("rustc", &["-Vv"]).replace('\n', "; ")
    );
    println!("cargo: {}", command_output("cargo", &["-V"]));
    println!(
        "RUSTFLAGS: {}",
        std::env::var("RUSTFLAGS").unwrap_or_else(|_| "<unset>".to_owned())
    );
    println!("profile: Cargo bench (optimized, debug assertions disabled)");
    println!("threads: {}", rayon::current_num_threads());
    println!("runs per cell: {runs} (median and MAD), after one verified warm-up");
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
        {
            let mut zk_rng = ZkRng::from_entropy();
            let mut ch = FsChallenger::new(DOMAIN);
            let (proof, comm) = setup
                .prove_zk_a1_with_rng(&blocks, &mut zk_rng, &mut ch)
                .expect("benchmark requires a certified configuration");
            let mut chv = FsChallenger::new(DOMAIN);
            setup
                .verify_zk_a1(&comm, &proof, &mut chv)
                .expect("warm-up proof must verify");
        }

        let mut zk_prove_times = Vec::with_capacity(runs);
        let mut zk_verify_times = Vec::with_capacity(runs);
        let mut zk_proof_sizes = Vec::with_capacity(runs);
        let mut zk_peak_heap = 0usize;
        for _ in 0..runs {
            let mut zk_rng = ZkRng::from_entropy();
            let mut ch = FsChallenger::new(DOMAIN);
            reset_peak_heap();
            let t0 = Instant::now();
            let (proof, comm) = setup
                .prove_zk_a1_with_rng(&blocks, &mut zk_rng, &mut ch)
                .expect("certified");
            zk_prove_times.push(t0.elapsed().as_secs_f64());
            zk_peak_heap = zk_peak_heap.max(peak_incremental_heap_bytes());

            let mut chv = FsChallenger::new(DOMAIN);
            let t1 = Instant::now();
            setup.verify_zk_a1(&comm, &proof, &mut chv).expect("verify");
            zk_verify_times.push(t1.elapsed().as_secs_f64());
            zk_proof_sizes.push(
                R1csProofBundleZkA1 {
                    commitment: comm,
                    proof,
                }
                .to_bytes()
                .len() as f64,
            );
        }
        let zk_prove = stats(&zk_prove_times);
        let zk_verify = stats(&zk_verify_times);
        let zk_size = stats(&zk_proof_sizes);

        // Witness generation alone, for attribution (the same call the
        // gated prove entry makes internally).
        let mut witness_times = Vec::with_capacity(runs);
        for _ in 0..runs {
            let t0 = Instant::now();
            let w = setup.generate_witness(&blocks);
            witness_times.push(t0.elapsed().as_secs_f64());
            std::hint::black_box(&w);
        }
        let witness = stats(&witness_times);

        // Context row: the optimized NON-zk pipeline at the same batch.
        let base_setup = Blake3Setup::new(n);
        let mut base_prove_times = Vec::with_capacity(runs);
        let mut base_verify_times = Vec::with_capacity(runs);
        let mut base_proof_sizes = Vec::with_capacity(runs);
        let mut base_peak_heap = 0usize;
        {
            let mut ch = FsChallenger::new(b"flock-zka1-bench-base");
            let (proof, commitment, _) = base_setup.prove_fast(&blocks, &mut ch);
            let mut chv = FsChallenger::new(b"flock-zka1-bench-base");
            base_setup
                .verify(&commitment, &proof, &mut chv)
                .expect("non-zk warm-up proof must verify");
            for _ in 0..runs {
                let mut ch = FsChallenger::new(b"flock-zka1-bench-base");
                reset_peak_heap();
                let t0 = Instant::now();
                let (proof, commitment, _) = base_setup.prove_fast(&blocks, &mut ch);
                base_prove_times.push(t0.elapsed().as_secs_f64());
                base_peak_heap = base_peak_heap.max(peak_incremental_heap_bytes());
                let mut chv = FsChallenger::new(b"flock-zka1-bench-base");
                let t1 = Instant::now();
                base_setup
                    .verify(&commitment, &proof, &mut chv)
                    .expect("non-zk proof must verify");
                base_verify_times.push(t1.elapsed().as_secs_f64());
                base_proof_sizes.push(
                    R1csProofBundleLigerito { commitment, proof }
                        .to_bytes()
                        .len() as f64,
                );
            }
        }
        let base_prove = stats(&base_prove_times);
        let base_verify = stats(&base_verify_times);
        let base_size = stats(&base_proof_sizes);

        println!(
            "{n:>8} {m:>4} {:>10.4} | {:>10.4} {:>10.4} \
             {:>8} | {:>10.4} {:>10.4} {:>8} | {:>7.2} {:>7.2}",
            witness.median,
            zk_prove.median,
            zk_verify.median,
            (zk_size.median / 1024.0).round() as usize,
            base_prove.median,
            base_verify.median,
            (base_size.median / 1024.0).round() as usize,
            zk_prove.median / base_prove.median,
            zk_size.median / base_size.median,
        );
        println!(
            "dispersion (MAD): witness {:.3} ms, ZK prove {:.3} ms, ZK verify {:.3} ms, \
             non-ZK prove {:.3} ms, non-ZK verify {:.3} ms",
            witness.mad * 1e3,
            zk_prove.mad * 1e3,
            zk_verify.mad * 1e3,
            base_prove.mad * 1e3,
            base_verify.mad * 1e3,
        );
        print_stats(n, "witness", witness);
        print_stats(n, "prove", zk_prove);
        print_stats(n, "verify", zk_verify);
        print_stats(n, "fast_nonzk_prove", base_prove);
        print_stats(n, "fast_nonzk_verify", base_verify);
        print_stats(n, "zk_proof_bytes", zk_size);
        print_stats(n, "fast_nonzk_proof_bytes", base_size);
        println!(
            "RESULT\tzk_a1_reference\tblake3\t{n}\tzk_peak_incremental_heap_bytes\t{zk_peak_heap}"
        );
        println!(
            "RESULT\tzk_a1_reference\tblake3\t{n}\tfast_nonzk_peak_incremental_heap_bytes\t{base_peak_heap}"
        );
        println!(
            "  certified/non-zk prove ratio: {:.2}x  (the certified path is \
             unoptimized by design)",
            zk_prove.median / base_prove.median
        );
    }
}

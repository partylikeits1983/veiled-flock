//! BLAKE3 hash-chain benchmark.

use std::time::Instant;

const ITERATIONS: u64 = 1_000_000;
const RUNS: u64 = 3;

#[inline(never)]
fn hash_chain(mut state: [u8; 32]) -> [u8; 32] {
    for _ in 0..ITERATIONS {
        state = *blake3::hash(&state).as_bytes();
    }
    state
}

fn main() {
    let input = [0x42; 32];
    let mut best = None;

    for run in 1..=RUNS {
        let start = Instant::now();
        let output = std::hint::black_box(hash_chain(std::hint::black_box(input)));
        let elapsed = start.elapsed();
        best = Some(best.map_or(elapsed, |current| elapsed.min(current)));

        println!(
            "run {run}/{RUNS}: {:.2} Mhash/s ({:.2?}, {:02x?})",
            ITERATIONS as f64 / elapsed.as_secs_f64() / 1_000_000.0,
            elapsed,
            &output[..4],
        );
    }

    println!("best: {:.2?}", best.expect("at least one run"));
}

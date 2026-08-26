//! Timing and native-rate calibration.

use std::time::Instant;

/// Time one closure and keep the best of `runs` executions. Returns the last
/// output and the best wall time in seconds; `runs` must be at least 1.
pub fn time_best<T>(runs: usize, mut f: impl FnMut() -> T) -> (T, f64) {
    assert!(runs >= 1, "time_best needs at least one run");
    let start = Instant::now();
    let mut out = std::hint::black_box(f());
    let mut best = start.elapsed().as_secs_f64();
    for _ in 1..runs {
        // Drop the previous output BEFORE the timer starts. A multi-MB
        // proof's teardown must not land inside the measured window.
        drop(out);
        let start = Instant::now();
        out = std::hint::black_box(f());
        best = best.min(start.elapsed().as_secs_f64());
    }
    (out, best)
}

/// Measure an amortized native rate: warm up on `links / 10`, then time `links`
/// executions. One calibration serves every row — chains scale linearly.
pub fn amortized_rate(links: usize, chain: impl Fn(usize)) -> f64 {
    assert!(links >= 10, "too few links for a warmup pass");
    chain(links / 10); // warmup
    let start = Instant::now();
    chain(links);
    links as f64 / start.elapsed().as_secs_f64()
}

/// The calibration link count: small in smoke mode. Env-free: the caller
/// resolves smoke mode.
pub fn calibration_links_for(smoke: bool) -> usize {
    if smoke { 10_000 } else { 100_000 }
}

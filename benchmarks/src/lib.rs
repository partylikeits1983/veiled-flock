//! Shared harness for the end-to-end proving benchmarks.
//!
//! This crate holds the workspace-level e2e benchmarks. The bench targets
//! measure full prove and verify cycles. The existing micro-benches in
//! `crates/flock-prover/benches/` stay separate. They measure raw hash
//! throughput only.
//!
//! The Rng, the time formatter, and the keccak chain builder come from
//! `crates/flock-prover/examples/keccak_chain_bench.rs`.

use std::time::Instant;

use flock_prover::r1cs_hashes::blake3_preimage::{DIGEST_BYTES, MESSAGE_BYTES};
use flock_prover::r1cs_hashes::keccak::{STATE_BITS, State, keccak_f};

/// Deterministic splitmix64 generator for bench inputs.
pub struct SplitMix(pub u64);

impl SplitMix {
    /// Return the next pseudo-random word.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Return 32 pseudo-random bytes.
    pub fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.as_chunks_mut::<8>().0 {
            *chunk = self.next_u64().to_le_bytes();
        }
        out
    }

    /// Return one pseudo-random keccak state.
    pub fn keccak_state(&mut self) -> State {
        let mut s = [false; STATE_BITS];
        for b in s.iter_mut() {
            *b = self.next_u64() & 1 == 1;
        }
        s
    }
}

/// Build an honest keccak-f chain of `n` permutations.
///
/// Returns `(inputs, x0, x_last)` with `inputs[i] = keccak_f^i(x0)` and
/// `x_last = keccak_f(inputs[n - 1])`.
pub fn keccak_honest_chain(n: usize, seed: u64) -> (Vec<State>, State, State) {
    let mut rng = SplitMix(seed);
    let x0 = rng.keccak_state();
    let mut inputs = Vec::with_capacity(n);
    let mut cur = x0;
    for _ in 0..n {
        inputs.push(cur);
        keccak_f(&mut cur);
    }
    (inputs, x0, cur)
}

/// Build an honest BLAKE3 hash chain of `n` single-block messages.
///
/// The chain rule is: `message_0 = seed_bytes || zeros`, then
/// `digest_i = blake3(message_i)` and `message_{i+1} = digest_i || zeros`.
/// Returns `(messages, digests)`, one pair per chain link.
pub fn blake3_chain(n: usize, seed: u64) -> (Vec<[u8; MESSAGE_BYTES]>, Vec<[u8; DIGEST_BYTES]>) {
    let mut rng = SplitMix(seed);
    let mut messages = Vec::with_capacity(n);
    let mut digests = Vec::with_capacity(n);
    let mut head = rng.bytes32();
    for _ in 0..n {
        let mut message = [0u8; MESSAGE_BYTES];
        message[..DIGEST_BYTES].copy_from_slice(&head);
        let digest: [u8; DIGEST_BYTES] = *blake3::hash(&message).as_bytes();
        messages.push(message);
        digests.push(digest);
        head = digest;
    }
    (messages, digests)
}

/// Time one closure and keep the best of `runs` executions.
///
/// Returns the last output and the best wall time in seconds. `runs` must
/// be at least 1.
pub fn time_best<T>(runs: usize, mut f: impl FnMut() -> T) -> (T, f64) {
    assert!(runs >= 1, "time_best needs at least one run");
    let start = Instant::now();
    let mut out = std::hint::black_box(f());
    let mut best = start.elapsed().as_secs_f64();
    for _ in 1..runs {
        let start = Instant::now();
        out = std::hint::black_box(f());
        best = best.min(start.elapsed().as_secs_f64());
    }
    (out, best)
}

/// Time one native BLAKE3 chain pass of `n` hashes. Returns seconds.
pub fn blake3_native_chain_secs(n: usize, seed: u64) -> f64 {
    let mut rng = SplitMix(seed);
    let mut head = rng.bytes32();
    let start = Instant::now();
    for _ in 0..n {
        let mut message = [0u8; MESSAGE_BYTES];
        message[..DIGEST_BYTES].copy_from_slice(&head);
        head = *blake3::hash(std::hint::black_box(&message)).as_bytes();
    }
    let elapsed = start.elapsed().as_secs_f64();
    std::hint::black_box(head);
    elapsed
}

/// Format a duration in seconds as an aligned human-readable string.
pub fn fmt_ms(s: f64) -> String {
    let ms = s * 1000.0;
    if ms < 1.0 {
        format!("{:>9.2} µs", s * 1e6)
    } else if ms < 1000.0 {
        format!("{:>9.2} ms", ms)
    } else {
        format!("{:>9.3} s ", s)
    }
}

/// Report `true` when `BENCH_SMOKE=1` is set.
///
/// Smoke mode shrinks each sweep and the run count. CI uses it.
pub fn smoke() -> bool {
    std::env::var("BENCH_SMOKE")
        .map(|v| v == "1")
        .unwrap_or(false)
}

/// Number of timing runs per row: 1 in smoke mode, 3 otherwise.
pub fn runs() -> usize {
    if smoke() { 1 } else { 3 }
}

/// One measured benchmark row.
pub struct BenchRow {
    /// Backend label, for example `veil-framed`.
    pub backend: &'static str,
    /// Relation label: `chain-in-circuit` or `public-chain`.
    pub relation: &'static str,
    /// Number of real chain links in the statement.
    pub n_real: usize,
    /// Number of witness slots after padding.
    pub n_slots: usize,
    /// Setup construction time, seconds.
    pub setup_s: f64,
    /// Witness generation time, seconds.
    pub witness_s: f64,
    /// Prove time, seconds (best of N).
    pub prove_s: f64,
    /// Verify time, seconds (best of N).
    pub verify_s: f64,
    /// Proof size in bytes, one fixint bincode encoder for all rows.
    pub proof_bytes: usize,
    /// Proven hashes per second, `n_real / prove_s`.
    pub hashes_per_s: f64,
    /// Prove time divided by the native chain time at the same `n_real`.
    pub slowdown: f64,
    /// Parameter set that produced this row.
    pub params: String,
}

/// Print rows as one aligned table with a title line.
pub fn print_table(title: &str, rows: &[BenchRow]) {
    println!("\n== {title} ==");
    println!(
        "{:<14} {:<17} {:>7} {:>7} {:>6} | {:>12} {:>12} {:>12} {:>12} | {:>10} {:>12} {:>10} | params",
        "backend",
        "relation",
        "n_real",
        "n_slots",
        "util",
        "setup",
        "witness",
        "prove",
        "verify",
        "bytes",
        "hash/s",
        "slowdown",
    );
    for r in rows {
        println!(
            "{:<14} {:<17} {:>7} {:>7} {:>6.3} | {} {} {} {} | {:>10} {:>12.2} {:>9.1}x | {}",
            r.backend,
            r.relation,
            r.n_real,
            r.n_slots,
            r.n_real as f64 / r.n_slots as f64,
            fmt_ms(r.setup_s),
            fmt_ms(r.witness_s),
            fmt_ms(r.prove_s),
            fmt_ms(r.verify_s),
            r.proof_bytes,
            r.hashes_per_s,
            r.slowdown,
            r.params,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splitmix_is_deterministic() {
        let mut a = SplitMix(7);
        let mut b = SplitMix(7);
        for _ in 0..16 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
        let mut c = SplitMix(8);
        assert_ne!(SplitMix(7).next_u64(), c.next_u64());
    }

    #[test]
    fn blake3_chain_links_and_digests_are_honest() {
        let (messages, digests) = blake3_chain(5, 0xC0FFEE_42);
        assert_eq!(messages.len(), 5);
        assert_eq!(digests.len(), 5);
        for i in 0..5 {
            assert_eq!(*blake3::hash(&messages[i]).as_bytes(), digests[i]);
            assert_eq!(messages[i][DIGEST_BYTES..], [0u8; 32]);
            if i > 0 {
                assert_eq!(messages[i][..DIGEST_BYTES], digests[i - 1]);
            }
        }
    }

    #[test]
    fn keccak_chain_links_are_honest() {
        let (inputs, x0, x_last) = keccak_honest_chain(4, 0xDEAD_BEEF);
        assert_eq!(inputs.len(), 4);
        assert_eq!(inputs[0], x0);
        for i in 0..3 {
            let mut next = inputs[i];
            keccak_f(&mut next);
            assert_eq!(next, inputs[i + 1]);
        }
        let mut last = inputs[3];
        keccak_f(&mut last);
        assert_eq!(last, x_last);
    }

    #[test]
    fn time_best_returns_output_and_positive_time() {
        let (value, secs) = time_best(3, || 41 + 1);
        assert_eq!(value, 42);
        assert!(secs >= 0.0);
    }

    #[test]
    fn fmt_ms_selects_unit_by_magnitude() {
        assert!(fmt_ms(0.000_5).ends_with("µs"));
        assert!(fmt_ms(0.5).ends_with("ms"));
        assert!(fmt_ms(2.0).ends_with("s "));
    }
}

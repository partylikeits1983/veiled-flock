//! End-to-end BLAKE3 proving benchmark and the shared bench harness.
//!
//! The e2e bench crates live under `benches/`: this crate (BLAKE3) and
//! `keccak-bench`. This lib also holds the generic harness (Rng, timer,
//! row/table reporter), which `keccak-bench` reuses via a path dependency.
//! The bench targets measure full prove and verify cycles. The existing
//! micro-benches in `crates/flock-prover/benches/` stay separate. They
//! measure raw hash throughput only.
//!
//! The Rng and the time formatter come from
//! `crates/flock-prover/examples/keccak_chain_bench.rs`.

use std::time::Instant;

use flock_prover::r1cs_hashes::blake3_preimage::{DIGEST_BYTES, MESSAGE_BYTES};

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
}

/// Build an honest BLAKE3 hash chain of `n` single-block messages.
///
/// The head of `message_0` is 32 pseudo-random bytes derived from `seed`
/// via splitmix64. Then `digest_i = blake3(message_i)` and
/// `message_{i+1} = digest_i || zeros`. Returns `(messages, digests)`,
/// one pair per chain link.
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
        // Drop the previous output BEFORE the timer starts. A multi-MB
        // proof's teardown must not land inside the measured window.
        drop(out);
        let start = Instant::now();
        out = std::hint::black_box(f());
        best = best.min(start.elapsed().as_secs_f64());
    }
    (out, best)
}

/// Check chain linkage over a public digest list.
///
/// The chain rule is public, so linkage needs no witness: the check is
/// `blake3(digest_i || zeros) == digest_{i + 1}` for every link. Returns
/// `true` when every link holds. Benched verify paths run this so the
/// measured time covers the full public-chain relation.
pub fn verify_chain_linkage(digests: &[[u8; DIGEST_BYTES]]) -> bool {
    digests.windows(2).all(|pair| {
        let mut message = [0u8; MESSAGE_BYTES];
        message[..DIGEST_BYTES].copy_from_slice(&pair[0]);
        *blake3::hash(&message).as_bytes() == pair[1]
    })
}

/// Measure an amortized native rate: warm up on `links / 10`, then time
/// `links` executions of `chain` and return executions per second.
///
/// One calibration serves every bench row: hash chains scale linearly, so
/// `native seconds at n = n / rate`, and small-n rows never divide by a
/// noise-level baseline.
pub fn amortized_rate(links: usize, chain: impl Fn(usize)) -> f64 {
    chain(links / 10); // warmup
    let start = Instant::now();
    chain(links);
    links as f64 / start.elapsed().as_secs_f64()
}

/// The calibration link count: small in smoke mode.
pub fn calibration_links() -> usize {
    if smoke() { 10_000 } else { 100_000 }
}

/// Measure the native BLAKE3 chain rate once, in hashes per second.
pub fn blake3_native_rate() -> f64 {
    amortized_rate(calibration_links(), |count| {
        let mut head = SplitMix(0xBA5E_11E5).bytes32();
        for _ in 0..count {
            let mut message = [0u8; MESSAGE_BYTES];
            message[..DIGEST_BYTES].copy_from_slice(&head);
            head = *blake3::hash(std::hint::black_box(&message)).as_bytes();
        }
        std::hint::black_box(head);
    })
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

/// Report `true` when `BENCH_SMOKE` is set to a truthy value.
///
/// Smoke mode shrinks each sweep and the run count. CI uses it. Accepted
/// truthy values: `1`, `true`, `yes`, `on` (case-insensitive). Any other
/// non-empty value stops the bench loudly — a silently ignored setting
/// would run the full sweep against the operator's intent.
pub fn smoke() -> bool {
    match std::env::var("BENCH_SMOKE") {
        Err(_) => false,
        Ok(v) if v.is_empty() => false,
        Ok(v) => match v.to_ascii_lowercase().as_str() {
            "1" | "true" | "yes" | "on" => true,
            "0" | "false" | "no" | "off" => false,
            other => panic!("BENCH_SMOKE set to unrecognized value {other:?}; use 1 or 0"),
        },
    }
}

/// Number of timing runs per row: 1 in smoke mode, 3 otherwise.
pub fn runs() -> usize {
    if smoke() { 1 } else { 3 }
}

/// One measured benchmark row.
///
/// Serializes for the `--json` dump. Every field is mandatory — a row
/// without its `params`, `backend`, and `relation` is not comparable
/// across commits, and the schema does not permit one.
#[derive(serde::Serialize)]
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

/// The four timed sections of one row, in seconds.
pub struct RowTimings {
    /// Setup construction time.
    pub setup_s: f64,
    /// Witness generation time.
    pub witness_s: f64,
    /// Prove time (best of N).
    pub prove_s: f64,
    /// Verify time (best of N).
    pub verify_s: f64,
}

impl BenchRow {
    /// Build a row and compute the derived metrics in one place.
    ///
    /// `hashes_per_s = n_real / prove_s` and
    /// `slowdown = prove_s / (n_real / native_rate)`. Every backend row
    /// function uses this constructor, so the formulas exist once.
    pub fn new(
        backend: &'static str,
        relation: &'static str,
        n_real: usize,
        n_slots: usize,
        timings: RowTimings,
        proof_bytes: usize,
        native_rate: f64,
        params: String,
    ) -> Self {
        let native_s = n_real as f64 / native_rate;
        Self {
            backend,
            relation,
            n_real,
            n_slots,
            setup_s: timings.setup_s,
            witness_s: timings.witness_s,
            prove_s: timings.prove_s,
            verify_s: timings.verify_s,
            proof_bytes,
            hashes_per_s: n_real as f64 / timings.prove_s,
            slowdown: timings.prove_s / native_s,
            params,
        }
    }
}

/// Size a value with the canonical fixint encoder
/// ([`flock_prover::proof_io::fixint_options`], no size limit — framed
/// proofs exceed the CLI's untrusted-read cap by design). One encoder
/// serves every proof-size column.
pub fn proof_size<T: serde::Serialize>(value: &T) -> usize {
    use bincode::Options;
    flock_prover::proof_io::fixint_options()
        .serialized_size(value)
        .expect("bincode size of an in-memory proof") as usize
}

/// Read an optional `MAX_LOG`-style sweep override from the environment.
///
/// Returns `default` when `name` is unset. A value that does not parse as
/// an integer, or falls outside `min..=max`, stops the bench loudly —
/// a silently adjusted override would run the wrong sweep.
pub fn max_log_from_env(name: &str, default: u32, min: u32, max: u32, hint: &str) -> u32 {
    match std::env::var(name) {
        Err(_) => default,
        Ok(v) => {
            let k: u32 = v
                .trim()
                .parse()
                .unwrap_or_else(|_| panic!("{name} must be an integer"));
            assert!(
                (min..=max).contains(&k),
                "{name} must be in {min}..={max} ({hint})"
            );
            k
        }
    }
}

/// Return the path after a `--json` argument, or `None` when absent.
///
/// Cargo forwards bench arguments after `--`, so the call shape is:
/// `cargo bench -p <crate> -- --json results.json`. A `--json` flag
/// without a path stops the bench loudly.
pub fn json_path_from_args() -> Option<String> {
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg == "--json" {
            return Some(args.next().expect("--json needs a file path"));
        }
    }
    None
}

/// Write the rows as pretty JSON: `{ "bench": <title>, "rows": [...] }`.
pub fn write_json(path: &str, title: &str, rows: &[BenchRow]) -> std::io::Result<()> {
    let doc = serde_json::json!({ "bench": title, "rows": rows });
    let mut text = serde_json::to_string_pretty(&doc).expect("bench rows serialize");
    text.push('\n');
    std::fs::write(path, text)
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
    fn time_best_returns_output_and_positive_time() {
        let (value, secs) = time_best(3, || 41 + 1);
        assert_eq!(value, 42);
        assert!(secs >= 0.0);
    }

    #[test]
    fn verify_chain_linkage_accepts_honest_and_rejects_tampered() {
        let (_, digests) = blake3_chain(5, 1);
        assert!(verify_chain_linkage(&digests));
        let mut bad = digests.clone();
        bad[2][0] ^= 1;
        assert!(!verify_chain_linkage(&bad));
        assert!(verify_chain_linkage(&digests[..1]));
    }

    #[test]
    fn bench_row_derives_metrics_from_inputs() {
        let timings = RowTimings {
            setup_s: 1.0,
            witness_s: 1.0,
            prove_s: 2.0,
            verify_s: 1.0,
        };
        let row = BenchRow::new("b", "r", 10, 16, timings, 5, 100.0, String::new());
        assert_eq!(row.hashes_per_s, 5.0);
        assert_eq!(row.slowdown, 20.0);
    }

    #[test]
    fn fmt_ms_selects_unit_by_magnitude() {
        assert!(fmt_ms(0.000_5).ends_with("µs"));
        assert!(fmt_ms(0.5).ends_with("ms"));
        assert!(fmt_ms(2.0).ends_with("s "));
    }
}

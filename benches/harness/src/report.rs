//! Row schema and reporters: aligned table, JSON dump, proof sizing.

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

/// One measured benchmark row, serialized for the `--json` dump. Every field is
/// mandatory — a row without `params`/`backend`/`relation` is not comparable.
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
    /// Build a row and compute the derived metrics in one place, so the formulas
    /// exist once. Precondition: `prove_s > 0` and `native_rate > 0`.
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

/// Size a value with the canonical fixint encoder (no size limit — framed proofs
/// exceed the CLI's untrusted-read cap by design). One encoder, every size column.
pub fn proof_size<T: serde::Serialize>(value: &T) -> usize {
    use bincode::Options;
    flock_prover::proof_io::fixint_options()
        .serialized_size(value)
        .expect("bincode size of an in-memory proof") as usize
}

/// Fail fast on an unwritable `--json` path. Call at the TOP of `main`: a bad
/// path discovered after the sweep discards every measured row.
pub fn probe_json_path(path: &str) {
    std::fs::write(path, b"").unwrap_or_else(|error| panic!("--json path {path:?}: {error}"));
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

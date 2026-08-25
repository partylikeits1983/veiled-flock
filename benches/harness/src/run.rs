//! The e2e run driver: prologue, reporting cadence, finalization.

use crate::cli::{BenchArgs, MaxLogFlag};
use crate::report::{BenchRow, print_table, probe_json_path, write_json};

/// Per-crate bench identity, defined once next to the domain code.
pub struct BenchSpec {
    /// Table title, for example `"keccak hashchain e2e"` — the driver
    /// appends `" (in progress)"` / `" (final)"`.
    pub table_title: &'static str,
    /// JSON `bench` title, for example `"keccak_hashchain_e2e"`. This is
    /// the cross-commit tracking key — renames are schema changes.
    pub json_title: &'static str,
    /// Smoke-banner phrase substituted into
    /// `"smoke mode: {phrase}, {runs} timing run(s) per row"`.
    pub smoke_banner: &'static str,
    /// Native-rate line label, for example `"native keccak-f chain rate"`.
    pub rate_label: &'static str,
    /// Native-rate unit printed after the M-scaled value, for example
    /// `"Mperm/s"`.
    pub rate_unit: &'static str,
    /// The crate-specific sweep-bound flag.
    pub max_log: MaxLogFlag,
}

/// One e2e bench run: parsed args, calibrated rate, accumulated rows.
///
/// [`E2eBench::start`] owns the order-sensitive prologue; the bin owns
/// only its sweep loops and row functions.
pub struct E2eBench {
    spec: &'static BenchSpec,
    args: BenchArgs,
    native_rate: f64,
    rows: Vec<BenchRow>,
}

impl E2eBench {
    /// Parse the args and run the prologue, in the load-bearing order:
    ///
    /// 1. probe the `--json` path BEFORE anything — a bad path found
    ///    after the sweep would discard every measured row;
    /// 2. build the perf rayon pool;
    /// 3. print the smoke banner;
    /// 4. calibrate the native rate once via `calibrate(smoke)` and
    ///    print the rate line.
    pub fn start(spec: &'static BenchSpec, calibrate: impl FnOnce(bool) -> f64) -> Self {
        let args = BenchArgs::parse(&spec.max_log);
        if let Some(path) = &args.json {
            probe_json_path(path);
        }
        flock_prover::init_perf_thread_pool();
        if args.smoke {
            println!(
                "smoke mode: {}, {} timing run(s) per row",
                spec.smoke_banner, args.runs
            );
        }
        let native_rate = calibrate(args.smoke);
        println!(
            "{}: {:.2} {}",
            spec.rate_label,
            native_rate / 1e6,
            spec.rate_unit
        );
        Self {
            spec,
            args,
            native_rate,
            rows: Vec::new(),
        }
    }

    /// Smoke mode, resolved from flag and env fallback.
    pub fn smoke(&self) -> bool {
        self.args.smoke
    }

    /// Timing runs per row (best-of-N).
    pub fn runs(&self) -> usize {
        self.args.runs
    }

    /// Upper log2 bound of the sweep.
    pub fn max_log(&self) -> u32 {
        self.args.max_log
    }

    /// The calibrated native rate, in executions per second.
    pub fn native_rate(&self) -> f64 {
        self.native_rate
    }

    /// Record one row and print the in-progress table — multi-hour runs
    /// stay observable row by row.
    pub fn push(&mut self, row: BenchRow) {
        self.rows.push(row);
        print_table(
            &format!("{} (in progress)", self.spec.table_title),
            &self.rows,
        );
    }

    /// Print the final table and write the `--json` dump when requested.
    pub fn finish(self) {
        print_table(&format!("{} (final)", self.spec.table_title), &self.rows);
        if let Some(path) = self.args.json {
            write_json(&path, self.spec.json_title, &self.rows).expect("write --json results");
            println!("wrote {path}");
        }
    }
}

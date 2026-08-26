//! Shared harness for the e2e bench crates: timing, CLI, run driver, rows.
//! Row schema and JSON `bench` titles are cross-commit keys — schema, not refactor.

mod cli;
mod env;
mod report;
mod rng;
mod run;
mod timing;

pub use cli::{BenchArgs, MaxLogFlag};
pub use env::{max_log_from_env, parse_max_log, parse_smoke, runs_for, smoke};
pub use report::{
    BenchRow, RowTimings, fmt_ms, print_table, probe_json_path, proof_size, write_json,
};
pub use rng::SplitMix;
pub use run::{BenchSpec, E2eBench};
pub use timing::{amortized_rate, calibration_links_for, time_best};

#[cfg(test)]
#[path = "tests.rs"]
mod tests;

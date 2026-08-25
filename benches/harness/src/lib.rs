//! Shared harness for the e2e proving bench crates.
//!
//! The bench crates under `benches/` (`blake3-bench`, `keccak-bench`)
//! keep only domain code — chain builders, native-rate closures, sweep
//! shapes, row functions — and import everything generic from here:
//!
//! - [`SplitMix`] — deterministic Rng for bench inputs;
//! - [`time_best`], [`amortized_rate`], [`calibration_links_for`] —
//!   timing and calibration;
//! - [`smoke`], [`runs_for`], [`max_log_from_env`] and their pure
//!   cores — the env-var fallback UX both bins share;
//! - [`MaxLogFlag`], [`BenchArgs`] — the shared flag parser
//!   (`--smoke`, `--runs`, one crate-specific sweep-bound flag,
//!   `--json`);
//! - [`BenchSpec`], [`E2eBench`] — the run driver owning the
//!   order-sensitive prologue and the reporting cadence;
//! - [`BenchRow`], [`RowTimings`], [`print_table`], [`write_json`],
//!   [`proof_size`] — the row schema and reporters.
//!
//! The row schema and each crate's JSON `bench` title are cross-commit
//! tracking keys — changes here are schema changes, not refactors.
//!
//! The Rng and the time formatter come from
//! `crates/flock-prover/examples/keccak_chain_bench.rs`.

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

//! Shared flag parser for the e2e bins.
//!
//! Both bins take the same flag shape — `--smoke`, `--runs`, one
//! crate-specific sweep-bound flag, `--json` — with env vars as
//! fallbacks; a flag always wins over its env var.

use crate::env::{max_log_from_env, parse_max_log, runs_for, smoke};

/// Spec for the one crate-specific sweep-bound flag.
///
/// The bench crate defines this once next to its domain code (inside its
/// [`crate::BenchSpec`]); the parser and the run driver read it.
pub struct MaxLogFlag {
    /// Flag name, for example `"--max-log"`.
    pub flag: &'static str,
    /// Env-var fallback name, for example `"BENCH_KECCAK_MAX_LOG"`.
    pub env: &'static str,
    /// Default when neither flag nor env var is set.
    pub default: u32,
    /// Inclusive lower bound.
    pub min: u32,
    /// Inclusive upper bound.
    pub max: u32,
    /// Range hint appended to out-of-range panics.
    pub hint: &'static str,
}

/// Parsed invocation of one e2e bin.
///
/// Flags: `--smoke`, `--runs <1..=16>`, the spec's sweep-bound flag,
/// `--json <path>`. Each flag wins over its env-var fallback
/// (`BENCH_SMOKE`, smoke-derived run count, the spec's env var).
pub struct BenchArgs {
    /// Shrink the sweep to one small point.
    pub smoke: bool,
    /// Timing runs per row (best-of-N).
    pub runs: usize,
    /// Upper log2 bound of the sweep.
    pub max_log: u32,
    /// Optional `--json` output path.
    pub json: Option<String>,
}

impl BenchArgs {
    /// Parse the process arguments, fail-loud on anything unknown.
    ///
    /// Env vars serve as fallbacks only; a flag always wins. The spec's
    /// env fallback is read and validated here even when the sweep will
    /// not use it (smoke mode) — fail-fast on a bad override is
    /// intended.
    pub fn parse(spec: &MaxLogFlag) -> Self {
        Self::from_parts(
            std::env::args().skip(1),
            spec,
            smoke(),
            max_log_from_env(spec.env, spec.default, spec.min, spec.max, spec.hint),
        )
    }

    /// Env-free core of [`BenchArgs::parse`]: `env_smoke` and
    /// `env_max_log` carry the already-resolved env fallbacks, so unit
    /// tests need no env vars.
    pub fn from_parts(
        mut args: impl Iterator<Item = String>,
        spec: &MaxLogFlag,
        env_smoke: bool,
        env_max_log: u32,
    ) -> Self {
        let mut smoke_flag = false;
        let mut runs_flag: Option<usize> = None;
        let mut max_log_flag: Option<u32> = None;
        let mut json: Option<String> = None;
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--smoke" => smoke_flag = true,
                "--runs" => {
                    let value = args.next().expect("--runs needs a count");
                    let n: usize = value
                        .trim()
                        .parse()
                        .unwrap_or_else(|_| panic!("--runs must be an integer"));
                    assert!((1..=16).contains(&n), "--runs must be in 1..=16");
                    runs_flag = Some(n);
                }
                other if other == spec.flag => {
                    let value = args
                        .next()
                        .unwrap_or_else(|| panic!("{} needs a value", spec.flag));
                    max_log_flag = Some(parse_max_log(
                        spec.flag, &value, spec.min, spec.max, spec.hint,
                    ));
                }
                "--json" => json = Some(args.next().expect("--json needs a file path")),
                other => panic!(
                    "unknown flag {other:?}; known flags: --smoke --runs {} --json",
                    spec.flag
                ),
            }
        }
        let smoke = smoke_flag || env_smoke;
        let runs = runs_flag.unwrap_or_else(|| runs_for(smoke));
        let max_log = max_log_flag.unwrap_or(env_max_log);
        BenchArgs {
            smoke,
            runs,
            max_log,
            json,
        }
    }
}

//! Env-var fallback UX shared by the e2e bins, with pure cores for tests.

/// Report `true` when `BENCH_SMOKE` is truthy (`1`/`true`/`yes`/`on`). Any other
/// non-empty value stops the bench loudly — a silently ignored setting is worse.
pub fn smoke() -> bool {
    match std::env::var("BENCH_SMOKE") {
        Err(_) => false,
        Ok(v) => parse_smoke(&v),
    }
}

/// Pure core of [`smoke`]: parse one `BENCH_SMOKE` value.
/// Panics on an unrecognized non-empty value.
pub fn parse_smoke(value: &str) -> bool {
    if value.is_empty() {
        return false;
    }
    match value.to_ascii_lowercase().as_str() {
        "1" | "true" | "yes" | "on" => true,
        "0" | "false" | "no" | "off" => false,
        other => panic!("BENCH_SMOKE set to unrecognized value {other:?}; use 1 or 0"),
    }
}

/// Number of timing runs per row: 1 in smoke mode, 3 otherwise. Env-free:
/// the caller resolves smoke mode.
pub fn runs_for(smoke: bool) -> usize {
    if smoke { 1 } else { 3 }
}

/// Read an optional `MAX_LOG`-style sweep override; `default` when `name` is unset.
/// A bad or out-of-range value stops the bench loudly, never silently adjusts.
pub fn max_log_from_env(name: &str, default: u32, min: u32, max: u32, hint: &str) -> u32 {
    match std::env::var(name) {
        Err(_) => default,
        Ok(v) => parse_max_log(name, &v, min, max, hint),
    }
}

/// Pure core of [`max_log_from_env`]: parse and range-check one value.
pub fn parse_max_log(name: &str, value: &str, min: u32, max: u32, hint: &str) -> u32 {
    let k: u32 = value
        .trim()
        .parse()
        .unwrap_or_else(|_| panic!("{name} must be an integer"));
    assert!(
        (min..=max).contains(&k),
        "{name} must be in {min}..={max} ({hint})"
    );
    k
}

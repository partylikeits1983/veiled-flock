//! Deterministic pseudo-random helpers for the workspace test targets.
//!
//! Every test in the workspace used to carry its own copy of this SplitMix64
//! generator. The copies were byte-identical, so this crate keeps the exact
//! same seed-to-stream mapping: a test that moves to [`SplitMix64`] sees the
//! same values it saw before.
//!
//! The crate is a dev-dependency only. It never enters the build graph of
//! `flock-core` or `flock-prover`, so it adds nothing to their public API.
//! Dev-dependencies reach `src` unit tests, integration tests, benches, and
//! examples alike, so one copy serves all four.
//!
//! # Why there is no `f128` method here
//!
//! This crate depends on nothing. A dependency on `flock-core` would make the
//! `F128` type unusable from `flock-core`'s own unit tests: `cargo test`
//! builds that crate a second time under `--test`, and the two instances are
//! distinct types. Tests that need field elements add a local extension trait
//! over [`Rng`] instead — a few lines, and the generator itself stays here.

/// SplitMix64. The state is public, so `SplitMix64(seed)` and
/// [`SplitMix64::new`] are interchangeable.
pub struct SplitMix64(pub u64);

/// The name the call sites use.
pub use SplitMix64 as Rng;

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    /// One state step.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    /// The low 32 bits of one state step.
    pub fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    /// The low bit of one state step.
    pub fn bit(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }

    /// `n` bits, one state step each.
    pub fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.bit()).collect()
    }

    /// `n` words, one state step each.
    pub fn words(&mut self, n: usize) -> Vec<u64> {
        (0..n).map(|_| self.next_u64()).collect()
    }
}

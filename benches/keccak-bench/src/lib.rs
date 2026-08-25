//! Keccak chain builders for the end-to-end keccak proving benchmark
//! (the `keccak_e2e` bin, `src/keccak.rs` in this crate). This lib holds
//! the keccak-side witness builders, lifted from
//! `crates/flock-prover/examples/keccak_chain_bench.rs`, plus the keccak
//! native-rate calibration and the public linkage check.

use bench_harness::SplitMix;
use flock_prover::r1cs_hashes::keccak::{STATE_BITS, State, keccak_f};

/// Return one pseudo-random keccak state drawn from `rng`.
pub fn random_state(rng: &mut SplitMix) -> State {
    let mut s = [false; STATE_BITS];
    for b in s.iter_mut() {
        *b = rng.next_u64() & 1 == 1;
    }
    s
}

/// Build an honest keccak-f chain of `n` permutations.
///
/// Returns `(inputs, x0, x_last)` with `inputs[i] = keccak_f^i(x0)` and
/// `x_last = keccak_f(inputs[n - 1])`.
pub fn keccak_honest_chain(n: usize, seed: u64) -> (Vec<State>, State, State) {
    let mut rng = SplitMix(seed);
    let x0 = random_state(&mut rng);
    let mut inputs = Vec::with_capacity(n);
    let mut cur = x0;
    for _ in 0..n {
        inputs.push(cur);
        keccak_f(&mut cur);
    }
    (inputs, x0, cur)
}

/// Measure the native keccak-f chain rate once, in permutations per second.
///
/// One calibration serves every row: state chains scale linearly, so
/// `native seconds at n = n / rate`. The measurement warms up first and
/// then times a fixed link count, so small-n rows never divide by a
/// noise-level baseline. Env-free: the caller resolves smoke mode. Not
/// pure — it measures wall time, so it does not belong in a unit test.
pub fn keccak_native_rate_with(smoke: bool) -> f64 {
    bench_harness::amortized_rate(bench_harness::calibration_links_for(smoke), |count| {
        let mut state = random_state(&mut SplitMix(0xBA5E_11E5));
        for _ in 0..count {
            keccak_f(std::hint::black_box(&mut state));
        }
        std::hint::black_box(state);
    })
}

/// The chain's per-block output states: `outputs[i] = inputs[i + 1]`, and
/// the last output is `x_last`.
///
/// Builds the public `outputs` list that `KeccakZkSetup::prove_succinct`
/// and `verify_succinct` take alongside `inputs`.
pub fn chain_outputs(inputs: &[State], x_last: &State) -> Vec<State> {
    assert!(!inputs.is_empty(), "a chain has at least one link");
    let mut outputs: Vec<State> = inputs[1..].to_vec();
    outputs.push(*x_last);
    outputs
}

/// Check chain linkage over public state lists: `outputs[i] == inputs[i+1]`
/// for every interior link. With every state public, linkage is a pure
/// equality check — no hashing. Benched verify paths run this so the
/// measured time covers the full public-chain relation.
pub fn verify_state_linkage(inputs: &[State], outputs: &[State]) -> bool {
    inputs.len() == outputs.len() && (1..inputs.len()).all(|i| outputs[i - 1] == inputs[i])
}

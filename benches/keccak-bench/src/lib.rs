//! Keccak chain builders for the end-to-end keccak proving benchmark.
//!
//! The bench target itself lands with Phase 2 of the e2e bench plan
//! (`KeccakZkSetup` over succinct VEIL, plus the native `prove_chain`
//! reference rows). This lib holds the keccak-side witness builders,
//! lifted from `crates/flock-prover/examples/keccak_chain_bench.rs`.

use blake3_bench::SplitMix;
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
/// noise-level baseline.
pub fn keccak_native_rate() -> f64 {
    let links = if blake3_bench::smoke() {
        10_000
    } else {
        100_000
    };
    let chain = |count: usize| {
        let mut state = random_state(&mut SplitMix(0xBA5E_11E5));
        for _ in 0..count {
            keccak_f(std::hint::black_box(&mut state));
        }
        std::hint::black_box(state);
    };
    chain(links / 10); // warmup
    let start = std::time::Instant::now();
    chain(links);
    links as f64 / start.elapsed().as_secs_f64()
}

/// Check chain linkage over public state lists: `outputs[i] == inputs[i+1]`
/// for every interior link. With every state public, linkage is a pure
/// equality check — no hashing. Benched verify paths run this so the
/// measured time covers the full public-chain relation.
pub fn verify_state_linkage(inputs: &[State], outputs: &[State]) -> bool {
    inputs.len() == outputs.len() && (1..inputs.len()).all(|i| outputs[i - 1] == inputs[i])
}

#[cfg(test)]
mod tests {
    use super::*;

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
}

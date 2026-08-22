use crate::{challenger::Challenger, field::F128, zerocheck::SmallMaskSpec};

pub(super) struct ScriptedEqChallenger {
    pub(super) vector_calls: usize,
}

impl Challenger for ScriptedEqChallenger {
    fn observe_f128(&mut self, _value: F128) {}

    fn sample_f128(&mut self) -> F128 {
        panic!("sample_eq_point uses framed vector sampling")
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.vector_calls += 1;
        match self.vector_calls {
            1 => vec![F128::ZERO; n],
            2 => vec![F128::ONE; n],
            3 => vec![F128::new(2, 0); n],
            _ => panic!("unexpected vector challenge request"),
        }
    }
}

/// SplitMix64 PRNG, deterministic.
pub(super) struct Rng(u64);

impl Rng {
    pub(super) fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub(super) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    pub(super) fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.next_u64() & 1 == 1).collect()
    }

    pub(super) fn field_mask(&mut self, m: usize) -> Vec<F128> {
        (0..SmallMaskSpec::default().d(m))
            .map(|_| F128::new(self.next_u64(), self.next_u64()))
            .collect()
    }
}

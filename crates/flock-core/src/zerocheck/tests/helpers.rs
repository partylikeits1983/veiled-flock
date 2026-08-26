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

pub(super) use flock_test_util::Rng;

/// Mask helper over the shared [`Rng`]. It lives here because a foreign trait
/// cannot be implemented for a foreign type, and `flock-test-util` depends on
/// nothing (see that crate's docs).
pub(super) trait RngMask {
    fn field_mask(&mut self, m: usize) -> Vec<F128>;
}

impl RngMask for Rng {
    fn field_mask(&mut self, m: usize) -> Vec<F128> {
        (0..SmallMaskSpec::default().d(m))
            .map(|_| F128::new(self.next_u64(), self.next_u64()))
            .collect()
    }
}

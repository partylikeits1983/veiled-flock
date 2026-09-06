//! Transcript adapters shared by the prover and the verifier.

use flock_core::{
    challenger::Challenger, field::F128, oracle_budget::OracleLimitError,
    pcs::ligerito::LigeritoProof, ro::RoContext,
};

use crate::pcs::{MAX_LIGERITO_GRIND_SITES, MAX_LIGERITO_GRIND_TRIALS};

/// Caps every Ligerito grind at `max_attempts` trials so the prover fails
/// closed instead of searching without bound. Mirrors the production adapter
/// in `flock-prover/src/succinct_veil.rs`.
pub(crate) struct BoundedGrindingChallenger<'a, C> {
    inner: &'a mut C,
    max_attempts: u64,
    pub(crate) exhausted: bool,
}

impl<'a, C> BoundedGrindingChallenger<'a, C> {
    pub(crate) fn new(inner: &'a mut C, max_attempts: u64) -> Self {
        Self {
            inner,
            max_attempts,
            exhausted: false,
        }
    }
}

impl<C: Challenger> Challenger for BoundedGrindingChallenger<'_, C> {
    fn ro_context(&self, nonce: [u8; 32]) -> RoContext {
        self.inner.ro_context(nonce)
    }

    fn observe_label(&mut self, label: &[u8]) {
        self.inner.observe_label(label);
    }

    fn observe_f128(&mut self, value: F128) {
        self.inner.observe_f128(value);
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.inner.observe_f128_slice(values);
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.inner.observe_bytes(bytes);
    }

    fn sample_f128(&mut self) -> F128 {
        self.inner.sample_f128()
    }

    fn try_sample_f128(&mut self) -> Result<F128, OracleLimitError> {
        self.inner.try_sample_f128()
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.inner.sample_f128_vec(n)
    }

    fn try_sample_f128_vec(&mut self, n: usize) -> Result<Vec<F128>, OracleLimitError> {
        self.inner.try_sample_f128_vec(n)
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        match self.inner.grind_pow_bounded(bits, self.max_attempts) {
            Ok(nonce) => nonce,
            Err(OracleLimitError::GrindingLimitExceeded) => {
                self.exhausted = true;
                self.max_attempts
            }
            Err(err) => panic!("bounded Ligerito grinding failed: {err}"),
        }
    }

    fn grind_pow_bounded(&mut self, bits: u32, max_trials: u64) -> Result<u64, OracleLimitError> {
        let cap = max_trials.min(self.max_attempts);
        match self.inner.grind_pow_bounded(bits, cap) {
            Ok(nonce) => Ok(nonce),
            Err(OracleLimitError::GrindingLimitExceeded) => {
                self.exhausted = true;
                Err(OracleLimitError::GrindingLimitExceeded)
            }
            Err(err) => Err(err),
        }
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.verify_pow_bounded(nonce, bits, self.max_attempts)
            .unwrap_or(false)
    }

    fn verify_pow_bounded(
        &mut self,
        nonce: u64,
        bits: u32,
        max_trials: u64,
    ) -> Result<bool, OracleLimitError> {
        let cap = max_trials.min(self.max_attempts);
        if nonce >= cap {
            self.exhausted = true;
        }
        self.inner.verify_pow_bounded(nonce, bits, cap)
    }
}

/// Verifier-side mirror of the bounded grind: every Ligerito nonce must be a
/// canonical first success below the trial cap.
pub(crate) fn ligerito_grinding_is_bounded(proof: &LigeritoProof) -> bool {
    proof
        .grinding_nonces
        .iter()
        .chain(&proof.fold_grinding_nonces)
        .all(|nonce| *nonce < MAX_LIGERITO_GRIND_TRIALS)
        && proof.fold_grinding_nonces.len() <= MAX_LIGERITO_GRIND_SITES
}

/// Fail-closed cap for rejection-sampled field challenges, the value the
/// production composition pins.
pub(crate) const MAX_CHALLENGE_SAMPLING_TRIALS: usize = 4096;

/// Sample uniformly from `F128 \ {0}` with a fail-closed trial cap.
pub(crate) fn sample_nonzero<C: Challenger>(challenger: &mut C) -> Option<F128> {
    for _ in 0..MAX_CHALLENGE_SAMPLING_TRIALS {
        let value = challenger.sample_f128();
        if !value.is_zero() {
            return Some(value);
        }
    }
    None
}

/// Observe a prover message with framing decided by its length: one element
/// is a scalar, two or more form a slice. The prover and the verifier apply
/// the same rule, so `send_values(&[x])` and `read_one()` share a transcript.
pub(crate) fn observe_framed<C: Challenger>(challenger: &mut C, values: &[F128]) {
    match values {
        [] => {}
        [value] => challenger.observe_f128(*value),
        many => challenger.observe_f128_slice(many),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use flock_core::challenger::FsChallenger;

    #[test]
    fn bounded_grinding_challenger_fails_closed_without_unbounded_search() {
        let mut inner = FsChallenger::new(b"example-bounded-grind");
        inner.observe_bytes(b"prefix");
        let mut bounded = BoundedGrindingChallenger::new(&mut inner, 3);

        assert_eq!(
            bounded.grind_pow_bounded(256, MAX_LIGERITO_GRIND_TRIALS),
            Err(OracleLimitError::GrindingLimitExceeded)
        );
        assert!(bounded.exhausted);
    }

    #[test]
    fn bounded_grinding_challenger_verifier_checks_cap() {
        let mut inner = FsChallenger::new(b"example-bounded-verify");
        let mut bounded = BoundedGrindingChallenger::new(&mut inner, 3);

        assert_eq!(
            bounded.verify_pow_bounded(3, 0, MAX_LIGERITO_GRIND_TRIALS),
            Ok(false)
        );
        assert!(bounded.exhausted);
    }
}

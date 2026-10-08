//! Transcript adapters shared by the prover and the verifier.

use flock_core::{challenger::Challenger, field::F128, pcs::ligerito::LigeritoProof};

pub(crate) use flock_core::challenger::BoundedGrindingChallenger;

use crate::pcs::{MAX_LIGERITO_GRIND_SITES, MAX_LIGERITO_GRIND_TRIALS};

/// Verifier-side mirror of the bounded grind: every Ligerito nonce must be a
/// successful nonce below the trial cap. Minimality is not checked.
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

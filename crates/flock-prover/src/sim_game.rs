//! Concrete classical programmable-random-oracle accounting for VEIL-FLOCK.

/// Deterministic upper bound on oracle calls made by one completed proof,
/// including Merkle hashing, transcript squeezes, and bounded grinding.
pub const MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF: u64 = 1_000_000;

/// Multi-theorem classical-pROM zero-knowledge bound for the active protocol.
/// This is not an unconditional statement about SHA-256 and does not cover
/// quantum oracle queries.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ClassicalPromZkBound {
    pub adversary_query_log2: u32,
    pub max_oracle_queries_per_proof: u64,
    pub programmed_points: u64,
    pub proofs: u64,
}

impl ClassicalPromZkBound {
    pub fn prequery_probability(self) -> f64 {
        let adversary_queries = 2f64.powi(self.adversary_query_log2 as i32);
        self.proofs as f64 * self.programmed_points as f64 * adversary_queries * 2f64.powi(-256)
    }

    pub fn collision_probability(self) -> f64 {
        let adversary_queries = 2f64.powi(self.adversary_query_log2 as i32);
        let total =
            adversary_queries + self.proofs as f64 * self.max_oracle_queries_per_proof as f64;
        total * (total - 1.0) * 0.5 * 2f64.powi(-256)
    }

    /// Cost of replacing witness-dependent initial Merkle subtrees. Each
    /// initial leaf carries an independent 256-bit salt and each unrevealed
    /// subtree boundary contains a fresh random-oracle child.
    pub fn hidden_merkle_input_probability(self) -> f64 {
        let adversary_queries = 2f64.powi(self.adversary_query_log2 as i32);
        self.proofs as f64
            * self.max_oracle_queries_per_proof as f64
            * adversary_queries
            * 2f64.powi(-256)
    }

    pub fn nonce_collision_probability(self) -> f64 {
        let proofs = self.proofs as f64;
        // One Fiat--Shamir proof nonce and three independently sampled
        // initial-tree nonces. Channel framing excludes cross-kind aliases;
        // charge each kind's multi-proof birthday event conservatively.
        4.0 * proofs * (proofs - 1.0) * 0.5 * 2f64.powi(-256)
    }

    /// Worst-case fail-closed grinding tails across every registered shape.
    pub fn grinding_abort_probability(self) -> f64 {
        let blind_failure =
            1.0 - 2f64.powi(-(crate::succinct_veil::MAX_BLIND_GRINDING_BITS as i32));
        let ligerito_failure =
            1.0 - 2f64.powi(-(crate::succinct_veil::MAX_LIGERITO_GRINDING_BITS as i32));
        self.proofs as f64
            * (blind_failure.powf(crate::succinct_veil::MAX_BLIND_GRIND_TRIALS as f64)
                + crate::succinct_veil::MAX_LIGERITO_GRIND_SITES as f64
                    * ligerito_failure.powf(crate::succinct_veil::MAX_LIGERITO_GRIND_TRIALS as f64))
    }

    /// Fail-closed tails for the four nonzero challenges and the one
    /// multiplication challenge excluding both zero and one.  The exact
    /// rational terms are proved in Lean; `MIN_POSITIVE` prevents this
    /// floating-point diagnostic from rounding a positive tail down to zero.
    pub fn challenge_sampling_abort_probability(self) -> f64 {
        let trials = veil_f128::dot_product::MAX_CHALLENGE_SAMPLING_TRIALS as f64;
        let nonzero_tail = 2f64.powi(-128).powf(trials).max(f64::MIN_POSITIVE);
        let not_zero_or_one_tail = 2f64.powi(-127).powf(trials).max(f64::MIN_POSITIVE);
        let equality_vector_failure =
            crate::succinct_veil::MAX_EQ_POINT_OUTER_COORDINATES as f64 * 2f64.powi(-128);
        let equality_point_tail = equality_vector_failure
            .powf(flock_core::zerocheck::MAX_EQ_POINT_SAMPLING_TRIALS as f64)
            .max(f64::MIN_POSITIVE);
        self.proofs as f64
            * (crate::succinct_veil::MAX_NONZERO_CHALLENGE_SITES as f64 * nonzero_tail
                + crate::succinct_veil::MAX_NOT_ZERO_OR_ONE_CHALLENGE_SITES as f64
                    * not_zero_or_one_tail
                + equality_point_tail)
    }

    /// Coupon-collector tails for the two fail-closed distinct-position
    /// samplers.  If fewer than 160 coordinates have appeared after 4096
    /// draws, every draw lies in some 159-element subset.  Union-bounding over
    /// those subsets gives `choose(N,159) * (159/N)^4096`.
    pub fn position_sampling_abort_probability(self) -> f64 {
        fn tail(domain: u64) -> f64 {
            let support = crate::succinct_veil::UNIQUE_POSITION_QUERY_COUNT - 1;
            let log2_choose = (0..support)
                .map(|index| ((domain - index) as f64 / (index + 1) as f64).log2())
                .sum::<f64>();
            let trials = veil_f128::dot_product::MAX_UNIQUE_POSITION_SAMPLING_TRIALS as f64;
            let log2_tail = log2_choose + trials * (support as f64 / domain as f64).log2();
            2f64.powf(log2_tail).max(f64::MIN_POSITIVE)
        }

        self.proofs as f64
            * (tail(crate::succinct_veil::HADAMARD_POSITION_DOMAIN)
                + tail(crate::succinct_veil::LINEAR_POSITION_DOMAIN))
    }

    pub fn distinguishing_probability(self) -> f64 {
        self.prequery_probability()
            + self.hidden_merkle_input_probability()
            + self.collision_probability()
            + self.nonce_collision_probability()
            + self.grinding_abort_probability()
            + self.challenge_sampling_abort_probability()
            + self.position_sampling_abort_probability()
    }

    pub fn distinguishing_bits(self) -> f64 {
        -self.distinguishing_probability().log2()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn active_bound_composes_across_proofs() {
        let one = ClassicalPromZkBound {
            adversary_query_log2: 64,
            max_oracle_queries_per_proof: MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF,
            programmed_points: 32,
            proofs: 1,
        };
        let many = ClassicalPromZkBound {
            proofs: 1024,
            ..one
        };
        assert!(one.distinguishing_bits() > 126.0);
        assert!(many.prequery_probability() <= 1024.0 * one.prequery_probability());
        assert!(one.position_sampling_abort_probability() > 0.0);
        assert!(many.distinguishing_probability() > one.distinguishing_probability());
    }
}

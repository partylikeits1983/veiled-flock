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

    /// The active two-bit grind is capped at 1024 trials and fails closed.
    pub fn grinding_abort_probability(self) -> f64 {
        self.proofs as f64
            * (0.75f64.powi(1024)
                + crate::succinct_veil::MAX_LIGERITO_GRIND_SITES as f64 * 0.5f64.powi(1024))
    }

    pub fn distinguishing_probability(self) -> f64 {
        self.prequery_probability()
            + self.hidden_merkle_input_probability()
            + self.collision_probability()
            + self.nonce_collision_probability()
            + self.grinding_abort_probability()
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
        assert!(many.distinguishing_probability() > one.distinguishing_probability());
    }
}

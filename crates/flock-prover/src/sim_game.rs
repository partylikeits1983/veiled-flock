//! Concrete classical programmable-random-oracle accounting for VEIL-FLOCK.

/// Deterministic upper bound on oracle calls made by one completed proof,
/// including Merkle hashing, transcript squeezes, and bounded grinding.
pub const MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF: u64 =
    flock_core::oracle_budget::MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF;

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

    /// Fail-closed tails for the bounded nonzero, not-zero-or-one, and
    /// zerocheck equality-point rejection samplers.
    pub fn rejection_abort_probability(self) -> f64 {
        let trials = flock_core::oracle_budget::REJECTION_SAMPLING_TRIALS as f64;
        let nonzero = 2f64.powf(-128.0 * trials);
        let not_zero_or_one = 2f64.powf(-127.0 * trials);
        let equality_point = 2f64.powf((13.0f64.log2() - 128.0) * trials);
        self.proofs as f64 * (5.0 * nonzero + not_zero_or_one + equality_point)
    }

    /// Fail-closed tails for bounded distinct-position sampling in the outer
    /// PCS L0 opening and the two VEIL matrix commitments.
    pub fn position_sampling_abort_probability(self) -> f64 {
        let trials = flock_core::oracle_budget::REJECTION_SAMPLING_TRIALS;
        let outer = [
            (2048usize, 294usize),
            (4096, 292),
            (8192, 291),
            (16384, 290),
            (32768, 290),
        ]
        .into_iter()
        .map(|(domain, target)| position_abort_bound(domain, target, trials))
        .sum::<f64>();
        let veil =
            position_abort_bound(2048, 160, trials) + position_abort_bound(8192, 160, trials);
        self.proofs as f64 * (outer + veil)
    }

    pub fn distinguishing_probability(self) -> f64 {
        self.prequery_probability()
            + self.hidden_merkle_input_probability()
            + self.collision_probability()
            + self.nonce_collision_probability()
            + self.grinding_abort_probability()
            + self.rejection_abort_probability()
            + self.position_sampling_abort_probability()
    }

    pub fn distinguishing_bits(self) -> f64 {
        -self.distinguishing_probability().log2()
    }
}

fn log2_binomial(n: usize, k: usize) -> f64 {
    if k > n {
        return f64::NEG_INFINITY;
    }
    let k = k.min(n - k);
    (1..=k)
        .map(|i| ((n + 1 - i) as f64).log2() - (i as f64).log2())
        .sum()
}

fn position_abort_bound(domain: usize, target: usize, trials: usize) -> f64 {
    if target == 0 || target > domain {
        return 0.0;
    }
    let support = target - 1;
    let log2_bound = log2_binomial(domain, support)
        + trials as f64 * ((support as f64).log2() - (domain as f64).log2());
    2f64.powf(log2_bound)
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

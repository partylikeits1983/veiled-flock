//! Executable description and concrete ledger for the fixed-digest ZK game.

use std::collections::HashSet;

use flock_core::ro::{ROLE_LEAF, ROLE_NODE, ROLE_POW};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SimGameHop {
    G0Honest,
    G1PiopTranslation,
    G2PcsTranslation,
    G3MerkleBoundary,
    G4ProgrammedChallenges,
    G5SealedSimulator,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HopEntry {
    pub hop: SimGameHop,
    pub change: &'static str,
    pub charged_term: &'static str,
}

pub const GAME_HOPS: &[HopEntry] = &[
    HopEntry {
        hop: SimGameHop::G0Honest,
        change: "honest prover on a valid preimage witness",
        charged_term: "0",
    },
    HopEntry {
        hop: SimGameHop::G1PiopTranslation,
        change: "translate field-valued PIOP masks at fixed challenges",
        charged_term: "epsilon_s2_rank",
    },
    HopEntry {
        hop: SimGameHop::G2PcsTranslation,
        change: "translate mu and g while preserving every algebraic opening value",
        charged_term: "Pr[c=0]+epsilon_query_solve",
    },
    HopEntry {
        hop: SimGameHop::G3MerkleBoundary,
        change: "replace hidden codeword leaves behind framed Merkle hashes",
        charged_term: "epsilon_sibling+epsilon_hash",
    },
    HopEntry {
        hop: SimGameHop::G4ProgrammedChallenges,
        change: "sample simulator challenges first and program their fresh RO points",
        charged_term: "epsilon_prequery+epsilon_prefix_collision",
    },
    HopEntry {
        hop: SimGameHop::G5SealedSimulator,
        change: "solve the zerocheck in one pass from the public sealed statement",
        charged_term: "Pr[degenerate rho or comb]",
    },
];

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SimGameLedger {
    pub q_hash_log2: u32,
    pub protocol_query_bound: u64,
    pub s2_degree: u64,
    pub programmed_points: u64,
    pub minimum_sibling_entropy_bits: u32,
    pub degenerate_challenge_numerator: u64,
    pub grinding_tail_bits: u32,
}

impl SimGameLedger {
    pub const fn production(q_hash_log2: u32, protocol_query_bound: u64) -> Self {
        Self {
            q_hash_log2,
            protocol_query_bound,
            s2_degree: 720,
            programmed_points: 18,
            minimum_sibling_entropy_bits: 16_384,
            // Only the final rho solve rejects rho in {0,1}. The Lagrange
            // weights cannot all vanish because they sum to one.
            degenerate_challenge_numerator: 2,
            grinding_tail_bits: 128,
        }
    }

    pub fn s2_rank_bits(self) -> f64 {
        128.0 - (self.s2_degree as f64).log2()
    }

    pub fn c_zero_bits(self) -> f64 {
        128.0
    }

    pub fn prequery_bits(self) -> f64 {
        256.0 - self.q_hash_log2 as f64 - (self.programmed_points as f64).log2()
    }

    pub fn sibling_bits(self) -> f64 {
        -self.sibling_probability().log2()
    }

    pub fn total_oracle_queries(self) -> f64 {
        2f64.powi(self.q_hash_log2 as i32) + self.protocol_query_bound as f64
    }

    pub fn oracle_collision_probability(self) -> f64 {
        let q = self.total_oracle_queries();
        q * (q - 1.0) * 0.5 * 2f64.powi(-256)
    }

    pub fn prequery_probability(self) -> f64 {
        self.programmed_points as f64 * 2f64.powi(self.q_hash_log2 as i32) * 2f64.powi(-256)
    }

    pub fn sibling_probability(self) -> f64 {
        self.total_oracle_queries() * 2f64.powi(-(self.minimum_sibling_entropy_bits as i32))
    }

    pub fn grinding_tail_probability(self) -> f64 {
        2f64.powi(-(self.grinding_tail_bits as i32))
    }

    pub fn algebraic_probability(self) -> f64 {
        (self.s2_degree + 1 + self.degenerate_challenge_numerator) as f64 * 2f64.powi(-128)
    }

    pub fn final_probability(self) -> f64 {
        self.algebraic_probability()
            + self.prequery_probability()
            + self.sibling_probability()
            + self.oracle_collision_probability()
            + self.grinding_tail_probability()
    }

    pub fn final_bits(self) -> f64 {
        -self.final_probability().log2()
    }
}

/// The nonzero proof-of-work difficulties in one registered PCS opening:
/// one 10-bit blinder challenge, six L0 folds, three L1 folds, and one L2
/// fold. Five independent PCS openings use this schedule in each proof.
pub const PRODUCTION_GRIND_BITS_PER_OPENING: &[u32] = &[10, 9, 8, 7, 6, 5, 4, 4, 3, 2, 1];
pub const PRODUCTION_PCS_OPENINGS: u64 = 5;

/// Bound the total candidate hashes used by all registered grinding sites.
/// A `b`-bit site fails to find a nonce in `a` trials with probability at
/// most `exp(-a/2^b)`. Allocating `2^-tail_bits / sites` to every site and
/// taking a union bound gives the returned deterministic query budget outside
/// a failure event of at most `2^-tail_bits`.
pub fn production_grinding_candidate_bound(tail_bits: u32) -> u64 {
    let sites = PRODUCTION_PCS_OPENINGS * PRODUCTION_GRIND_BITS_PER_OPENING.len() as u64;
    let exponent = tail_bits as f64 * std::f64::consts::LN_2 + (sites as f64).ln();
    PRODUCTION_PCS_OPENINGS
        * PRODUCTION_GRIND_BITS_PER_OPENING
            .iter()
            .map(|bits| (2f64.powi(*bits as i32) * exponent).ceil() as u64)
            .sum::<u64>()
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OracleQueryCounts {
    pub total_calls: u64,
    pub unique_points: u64,
    pub merkle_leaves: u64,
    pub merkle_nodes: u64,
    pub pow_candidates: u64,
    pub transcript_and_state: u64,
}

impl OracleQueryCounts {
    pub fn classify(points: &[Vec<u8>]) -> Self {
        let mut out = Self {
            total_calls: points.len() as u64,
            unique_points: points.iter().collect::<HashSet<_>>().len() as u64,
            ..Self::default()
        };
        for point in points {
            match point.first().copied() {
                Some(ROLE_LEAF) => out.merkle_leaves += 1,
                Some(ROLE_NODE) => out.merkle_nodes += 1,
                Some(ROLE_POW) => out.pow_candidates += 1,
                _ => out.transcript_and_state += 1,
            }
        }
        out
    }

    pub fn non_pow_calls(self) -> u64 {
        self.total_calls - self.pow_candidates
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn game_hops_are_complete_and_ordered() {
        assert_eq!(GAME_HOPS.len(), 6);
        assert_eq!(GAME_HOPS[0].hop, SimGameHop::G0Honest);
        assert_eq!(GAME_HOPS[5].hop, SimGameHop::G5SealedSimulator);
        assert!(GAME_HOPS.iter().all(|entry| !entry.charged_term.is_empty()));
    }

    #[test]
    fn production_ledger_exposes_recursive_sibling_gate_at_q64() {
        let ledger = SimGameLedger::production(64, 1_000_000);
        assert!(ledger.s2_rank_bits() > 118.0);
        assert!(ledger.prequery_bits() > 187.0);
        assert!(ledger.sibling_bits() > 16_000.0);
        assert!(ledger.final_bits() < ledger.s2_rank_bits());
        assert!(ledger.final_bits() > 118.49);

        let artifact: serde_json::Value = serde_json::from_str(include_str!(
            "../../../docs/artifacts/sim_game_error_table.json"
        ))
        .expect("game artifact must be valid JSON");
        let pinned = artifact["final_zk_bits_at_q64"]
            .as_f64()
            .expect("numeric bound");
        let protocol_bound = artifact["random_oracle_ledger"]["protocol_query_bound"]
            .as_u64()
            .expect("protocol query bound");
        let pinned_ledger = SimGameLedger::production(64, protocol_bound);
        assert!((pinned - pinned_ledger.final_bits()).abs() < 1e-12);
        assert!(production_grinding_candidate_bound(128) < 1_000_000);
    }
}

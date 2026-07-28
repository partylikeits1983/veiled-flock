//! Executable description and concrete ledger for the fixed-digest ZK game.

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
    pub s2_degree: u64,
    pub programmed_points: u64,
    pub minimum_sibling_entropy_bits: u32,
    pub degenerate_challenge_numerator: u64,
}

impl SimGameLedger {
    pub const fn production(q_hash_log2: u32) -> Self {
        Self {
            q_hash_log2,
            s2_degree: 720,
            programmed_points: 18,
            minimum_sibling_entropy_bits: 16_384,
            // Only the final rho solve rejects rho in {0,1}. The Lagrange
            // weights cannot all vanish because they sum to one.
            degenerate_challenge_numerator: 2,
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
        self.minimum_sibling_entropy_bits as f64 - self.q_hash_log2 as f64
    }

    pub fn conservative_bits(self) -> f64 {
        let probability = 2f64.powf(-self.s2_rank_bits())
            + 2f64.powf(-self.c_zero_bits())
            + (self.degenerate_challenge_numerator as f64) * 2f64.powf(-128.0)
            + 2f64.powf(-self.prequery_bits())
            + 2f64.powf(-self.sibling_bits());
        -probability.log2()
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
        let ledger = SimGameLedger::production(64);
        assert!(ledger.s2_rank_bits() > 118.0);
        assert!(ledger.prequery_bits() > 187.0);
        assert!(ledger.sibling_bits() > 16_000.0);
        assert!(ledger.conservative_bits() < ledger.s2_rank_bits());
        assert!(ledger.conservative_bits() > 118.50);

        let artifact: serde_json::Value = serde_json::from_str(include_str!(
            "../../../docs/artifacts/sim_game_error_table.json"
        ))
        .expect("game artifact must be valid JSON");
        let pinned = artifact["conservative_zk_bits_at_q64"]
            .as_f64()
            .expect("numeric bound");
        assert!((pinned - ledger.conservative_bits()).abs() < 1e-12);
    }
}

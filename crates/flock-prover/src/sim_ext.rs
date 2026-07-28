//! Fresh-prefix weak simulation extractability for fixed-digest proofs.

use std::collections::HashSet;

use flock_core::pcs::PcsParams;

use crate::digest_bind::DigestStatement;
use crate::preimage_extractor::{
    ExtractError, extract_preimages, recover_witness_from_leaf_queries,
};
use crate::prover::R1csProofZkA1;
use crate::r1cs_hashes::blake3_preimage::{DIGEST_BYTES, MESSAGE_BYTES};
use crate::zk_certificate::PROTOCOL_VERSION;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SimulatedPrefix {
    pub statement_digest: [u8; 32],
    pub proof_nonce: [u8; 32],
    pub protocol_version: &'static str,
}

impl SimulatedPrefix {
    pub fn new(statement: &DigestStatement, proof_nonce: [u8; 32]) -> Self {
        Self {
            statement_digest: statement.public_digest(),
            proof_nonce,
            protocol_version: PROTOCOL_VERSION,
        }
    }
}

#[derive(Default)]
pub struct SimulatedPrefixSet {
    prefixes: HashSet<SimulatedPrefix>,
}

impl SimulatedPrefixSet {
    pub fn record(&mut self, statement: &DigestStatement, proof: &R1csProofZkA1) {
        self.prefixes
            .insert(SimulatedPrefix::new(statement, proof.proof_nonce));
    }

    pub fn contains(&self, statement: &DigestStatement, proof_nonce: [u8; 32]) -> bool {
        self.prefixes
            .contains(&SimulatedPrefix::new(statement, proof_nonce))
    }

    pub fn len(&self) -> usize {
        self.prefixes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.prefixes.is_empty()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum SimExtError {
    ReusedSimulatedPrefix,
    Extraction(ExtractError),
}

/// Extract on a fresh `(statement digest, proof nonce, protocol version)`
/// prefix. Same-prefix simulation extractability is intentionally not claimed.
pub fn extract_on_fresh_prefix(
    simulated: &SimulatedPrefixSet,
    statement: &DigestStatement,
    proof_nonce: [u8; 32],
    recorded_leaves: &[(u64, Vec<u8>)],
    params: &PcsParams,
    digests: &[[u8; DIGEST_BYTES]],
    n_block_slots: usize,
) -> Result<Vec<[u8; MESSAGE_BYTES]>, SimExtError> {
    if simulated.contains(statement, proof_nonce) {
        return Err(SimExtError::ReusedSimulatedPrefix);
    }
    let witness = recover_witness_from_leaf_queries(recorded_leaves, params)
        .map_err(SimExtError::Extraction)?;
    extract_preimages(&witness, digests, n_block_slots).map_err(SimExtError::Extraction)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup;

    #[test]
    fn prefix_diverges_on_statement_nonce_and_version_tuple() {
        let setup = Blake3PreimageZkSetup::new(256);
        let a = vec![[1u8; DIGEST_BYTES]; 256];
        let mut b = a.clone();
        b[0][0] ^= 1;
        let stmt_a = setup.statement(&a);
        let stmt_b = setup.statement(&b);
        let nonce_a = [7u8; 32];
        let mut nonce_b = nonce_a;
        nonce_b[0] ^= 1;
        let prefix = SimulatedPrefix::new(&stmt_a, nonce_a);
        assert_ne!(prefix, SimulatedPrefix::new(&stmt_b, nonce_a));
        assert_ne!(prefix, SimulatedPrefix::new(&stmt_a, nonce_b));
        assert_eq!(prefix.protocol_version, PROTOCOL_VERSION);
    }

    #[test]
    fn simulated_prefix_is_rejected_and_fresh_prefix_reaches_extractor() {
        let setup = Blake3PreimageZkSetup::new(256);
        let digests = vec![[3u8; DIGEST_BYTES]; 256];
        let statement = setup.statement(&digests);
        let simulated_nonce = [9u8; 32];
        let mut simulated = SimulatedPrefixSet::default();
        simulated
            .prefixes
            .insert(SimulatedPrefix::new(&statement, simulated_nonce));

        assert_eq!(
            extract_on_fresh_prefix(
                &simulated,
                &statement,
                simulated_nonce,
                &[],
                &setup.pcs_params,
                &digests,
                setup.n_block_slots(),
            ),
            Err(SimExtError::ReusedSimulatedPrefix)
        );
        assert_eq!(
            extract_on_fresh_prefix(
                &simulated,
                &statement,
                [10u8; 32],
                &[],
                &setup.pcs_params,
                &digests,
                setup.n_block_slots(),
            ),
            Err(SimExtError::Extraction(ExtractError::BadLeafQueries))
        );
    }
}

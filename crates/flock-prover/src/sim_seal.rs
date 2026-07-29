//! Public-only capability passed to the fixed-digest simulator.
//!
//! The fields are private and the constructor accepts only a setup and public
//! digest list. No preimage or witness type is reachable from the simulator
//! signature.

use crate::digest_bind::DigestStatement;
use crate::r1cs_hashes::blake3_preimage::{Blake3PreimageZkSetup, DIGEST_BYTES, PreimageError};

pub struct SealedStatement<'a> {
    setup: &'a Blake3PreimageZkSetup,
    digests: Vec<[u8; DIGEST_BYTES]>,
    statement: DigestStatement,
}

impl<'a> SealedStatement<'a> {
    pub fn new(
        setup: &'a Blake3PreimageZkSetup,
        digests: &[[u8; DIGEST_BYTES]],
    ) -> Result<Self, PreimageError> {
        crate::zk_certificate::require_certified(
            crate::zk_certificate::StatementFamily::Blake3Preimage,
            setup.n_blocks,
            &setup.r1cs,
            &setup.pcs_params,
        )
        .map_err(|_| PreimageError::Uncertified)?;
        if digests.len() != setup.n_blocks {
            return Err(PreimageError::BatchSizeMismatch {
                expected: setup.n_blocks,
                got: digests.len(),
            });
        }
        let statement = setup.statement(digests);
        statement.validate();
        Ok(Self {
            setup,
            digests: digests.to_vec(),
            statement,
        })
    }

    pub(crate) fn setup(&self) -> &'a Blake3PreimageZkSetup {
        self.setup
    }

    pub(crate) fn digests(&self) -> &[[u8; DIGEST_BYTES]] {
        &self.digests
    }

    pub(crate) fn statement(&self) -> &DigestStatement {
        &self.statement
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SimCoins {
    seed: u64,
}

impl SimCoins {
    pub const fn new(seed: u64) -> Self {
        Self { seed }
    }

    pub(crate) const fn seed(self) -> u64 {
        self.seed
    }
}

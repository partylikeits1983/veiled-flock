//! Hiding Ligerito PCS adapter for FLOCK bit witnesses.
//!
//! A committed object is a Boolean vector of `2^m` bits packed into `2^(m-7)`
//! `F128` words. Its multilinear extension is opened at a FLOCK quirky point
//! through ring switching: the prover reveals the 128 slice evaluations
//! `s_hat_v` and the verifier folds them with public claim weights.

use flock_core::{
    field::F128,
    lincheck::QuirkyPoint,
    pcs::{
        LOG_PACKING, PcsParams,
        ligerito::{
            LigeritoProfile, ProverConfig, VerifierConfig, prover_config_for, verifier_config_for,
        },
        ring_switch::{build_claim_weights, claim_check, s_hat_v_at_point},
    },
};

use crate::error::VeilError;

/// The production composition pins these bounds in
/// `flock-prover/src/succinct_veil.rs`. They are copied here because the
/// examples do not depend on that crate.
pub(crate) const MAX_BLIND_GRINDING_BITS: u32 = 5;
pub(crate) const MAX_BLIND_GRIND_TRIALS: u64 = 4096;
pub(crate) const MAX_LIGERITO_GRIND_TRIALS: u64 = 4096;
pub(crate) const MAX_LIGERITO_GRIND_SITES: u64 = 16;

const LOG_BATCH_SIZE: usize = 6;

/// Width of one ring-switch slice vector.
pub const RING_WIDTH: usize = 1 << LOG_PACKING;

/// Hiding PCS for bit witnesses of a fixed size `2^m`.
#[derive(Clone, Debug)]
pub struct BitPcs {
    params: PcsParams,
    prover_config: ProverConfig,
    verifier_config: VerifierConfig,
}

impl BitPcs {
    /// The committed ZK message is `[mask || z]`, so the Ligerito config is
    /// loaded for `params.log_msg_len() = m - 6`; `m = 22` therefore uses the
    /// embedded `m23_secure` config. The registry floor is `m = 21`.
    pub fn new(m: usize) -> Result<Self, VeilError> {
        if m < LOG_PACKING + LOG_BATCH_SIZE {
            return Err(VeilError::Ligerito(format!(
                "m = {m} is below the PCS floor {}",
                LOG_PACKING + LOG_BATCH_SIZE
            )));
        }
        let params = PcsParams {
            m,
            log_inv_rate: 1,
            log_batch_size: LOG_BATCH_SIZE,
            profile: LigeritoProfile::Secure,
            zk: true,
        };
        let log_n = params.log_msg_len();
        let prover_config = prover_config_for(log_n, LOG_BATCH_SIZE, LigeritoProfile::Secure)
            .map_err(VeilError::Ligerito)?;
        let verifier_config = verifier_config_for(log_n, LOG_BATCH_SIZE, LigeritoProfile::Secure)
            .map_err(VeilError::Ligerito)?;
        let pcs = Self {
            params,
            prover_config,
            verifier_config,
        };
        pcs.blind_grinding_bits()?;
        Ok(pcs)
    }

    /// Log of the number of committed bits.
    pub fn m(&self) -> usize {
        self.params.m
    }

    /// Number of `F128` words in a packed witness.
    pub fn packed_len(&self) -> usize {
        1usize << (self.params.m - LOG_PACKING)
    }

    pub fn params(&self) -> &PcsParams {
        &self.params
    }

    pub(crate) fn prover_config(&self) -> &ProverConfig {
        &self.prover_config
    }

    pub(crate) fn verifier_config(&self) -> &VerifierConfig {
        &self.verifier_config
    }

    /// Bits of the bounded grind that prices the blinding challenge: one
    /// more than the first Ligerito fold grind, as in production.
    pub fn blind_grinding_bits(&self) -> Result<u32, VeilError> {
        let bits = self
            .prover_config
            .fold_grinding_bits
            .first()
            .copied()
            .unwrap_or(0) as u32
            + 1;
        if (1..=MAX_BLIND_GRINDING_BITS).contains(&bits) {
            Ok(bits)
        } else {
            Err(VeilError::ProofShape("blind grinding bits"))
        }
    }

    /// Check that a quirky point addresses `2^m` bits.
    pub(crate) fn check_point(&self, point: &QuirkyPoint) -> Result<(), VeilError> {
        let coords = 1 + point.x_inner_rest.len() + point.x_outer.len();
        let expected = self.params.m - flock_core::zerocheck::K_SKIP + 1;
        if coords != expected {
            return Err(VeilError::PointShape {
                expected,
                actual: coords,
            });
        }
        Ok(())
    }
}

/// The ring-switch suffix of a quirky point: inner-rest then outer
/// coordinates. Its first entry pairs with `z_skip` in the claim weights.
pub fn x_full(point: &QuirkyPoint) -> Vec<F128> {
    let mut full = Vec::with_capacity(point.x_inner_rest.len() + point.x_outer.len());
    full.extend_from_slice(&point.x_inner_rest);
    full.extend_from_slice(&point.x_outer);
    full
}

/// Public weights that fold a slice vector into the claimed evaluation.
pub fn claim_weights(point: &QuirkyPoint) -> Vec<F128> {
    let full = x_full(point);
    build_claim_weights(point.z_skip, full[0])
}

/// Ring-switch slice evaluations of a packed vector at a quirky point.
pub fn ring_slices(packed: &[F128], point: &QuirkyPoint) -> Vec<F128> {
    s_hat_v_at_point(packed, &x_full(point))
}

/// Evaluate the multilinear extension of a packed bit witness at a quirky
/// point. This is the value a FLOCK claim asserts.
pub fn bit_mle_eval(packed: &[F128], point: &QuirkyPoint) -> F128 {
    claim_check(&claim_weights(point), &ring_slices(packed, point))
}

/// LSB-first bit packing of a Boolean vector into bytes, the layout the
/// native zerocheck prover consumes.
pub fn bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    assert!(bits.len().is_multiple_of(8));
    bits.as_chunks::<8>()
        .0
        .iter()
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0u8, |byte, (r, &bit)| byte | (u8::from(bit) << r))
        })
        .collect()
}

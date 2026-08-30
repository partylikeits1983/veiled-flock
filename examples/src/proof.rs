use flock_core::{
    field::F128,
    pcs::{BatchOpeningProofLigerito, Commitment},
};
use serde::{Deserialize, Serialize};
use veil_f128::ConstraintProof;

/// Wire format of one full-ZK example proof.
///
/// The proof carries no prover message in the clear: every field value in
/// `masked_transcript` is one-time padded, every commitment is hiding, and
/// every ring-switch slice that the PCS opens is blinded by the committed
/// blinder.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZkProof {
    pub proof_nonce: [u8; 32],
    pub veil_linear_nonce: [u8; 32],
    pub veil_hadamard_nonce: [u8; 32],
    /// One tree nonce per committed bit witness, in commitment order.
    pub oracle_nonces: Vec<[u8; 32]>,
    /// Every prover message, one-time padded, in send order. The PIOP
    /// messages come first; the masked witness and blinder ring slices of
    /// every evaluation claim follow, in claim order.
    pub masked_transcript: Vec<F128>,
    /// Hiding PCS commitments, in commitment order.
    pub commitments: Vec<Commitment>,
    pub blind_grind_nonce: u64,
    /// Blinded ring slices `s(z) + c * s(g_top)` per claim, in claim order.
    pub blinded_slices: Vec<Vec<F128>>,
    /// One opening per commitment that carries at least one claim, in
    /// commitment order.
    pub pcs_openings: Vec<BatchOpeningProofLigerito>,
    pub veil: ConstraintProof,
}

#![forbid(unsafe_code)]
//! Full-ZK examples of FLOCK's own protocols under the VEIL compilation.
//!
//! The upstream `slop-veil` examples are generic over three compiler traits:
//! a single `verify` body runs on a mask counter, on the prover (as a replay
//! that emits the constraints), and on the verifier. This crate keeps that
//! structure but builds it on the primitives of this repository:
//!
//! - the FLOCK zerocheck with univariate skip and the FLOCK lincheck are the
//!   sumchecks; the prover context is itself a masking [`Challenger`], so the
//!   native provers run through it unchanged and every message they emit is
//!   one-time padded;
//! - committed objects are Boolean witnesses under the hiding Ligerito PCS,
//!   opened at FLOCK quirky points by ring switching with masked slices and a
//!   blinded joint opening;
//! - the verify bodies are ports of the production shifted verifier circuit
//!   (`flock-prover/src/succinct_veil.rs`), expressed over affine
//!   `veil_f128::LinearCombination`s and discharged by the ZK VEIL constraint
//!   proof.
//!
//! [`Challenger`]: flock_core::challenger::Challenger

mod challenger;
mod ctx;
mod error;
mod flock;
mod pcs;
mod proof;

pub use ctx::{
    ConstraintCtx, Expr, MaskCounter, OracleId, ReadingCtx, SendingCtx, ZkProverCtx, ZkVerifierCtx,
    compute_mask_length, linear_combination,
};
pub use error::VeilError;
pub use flock::{
    LincheckOutput, ZerocheckOutput, lincheck_prove, lincheck_verify, sample_quirky_point,
    zerocheck_prove, zerocheck_verify,
};
pub use flock_core::challenger::Challenger;
pub use flock_core::field::F128;
pub use flock_core::lincheck::QuirkyPoint;
pub use flock_core::zk::{MaskSampler, ZkRng};
pub use pcs::{
    BitPcs, RING_WIDTH, bit_mle_eval, bits_to_bytes, claim_weights, ring_slices, x_full,
};
pub use proof::ZkProof;

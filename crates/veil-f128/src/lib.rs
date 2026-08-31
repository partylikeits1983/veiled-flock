#![forbid(unsafe_code)]
//! Native `GF(2^128)` components for the VEIL compilation of FLOCK.
//!
//! The upstream VEIL implementation uses a two-adic prime-field code. FLOCK's
//! transcript lives in `GF(2^128)`, whose multiplicative group has odd order,
//! so this crate supplies the corresponding additive-domain code directly.

pub mod code;
pub mod commitment;
pub mod constraints;
pub mod dot_product;
pub mod hadamard;
pub mod ntt;
pub use code::{AdditiveRsCode, CodeError, CodeParameters};
pub use commitment::{MerkleMatrix, MerkleMatrixOpening};
pub use constraints::{
    ArithmeticCircuit, CircuitBuilder, ConstraintCommitment, ConstraintError, ConstraintParameters,
    ConstraintProof, ConstraintSoundnessBound, LinearCombination,
    SUCCINCT_FLOCK_MIN_SOUNDNESS_BITS, certify_constraint_soundness, commit_constraint_inputs,
    prove_constraints, prove_constraints_from_commitment, prove_constraints_with_parameters,
    verify_constraints,
};
pub use dot_product::{
    DotProductError, DotProductProof, DotProductProverData, VectorParameters, commit_vectors,
    prove_dot_product, verify_dot_product,
};
pub use flock_core::field::F128;
pub use hadamard::{
    HadamardError, HadamardProof, HadamardProverData, commit_hadamard, prove_hadamard_and_dots,
    verify_hadamard_and_dots,
};
pub use ntt::AdditiveCosetNtt;

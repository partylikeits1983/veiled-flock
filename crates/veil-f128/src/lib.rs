#![forbid(unsafe_code)]
//! Native `GF(2^128)` components for the VEIL compilation of FLOCK.
//!
//! The upstream VEIL implementation uses a two-adic prime-field code. FLOCK's
//! transcript lives in `GF(2^128)`, whose multiplicative group has odd order,
//! so this crate supplies the corresponding additive-domain code directly.

pub mod block_r1cs;
pub mod code;
pub mod commitment;
pub mod constraints;
pub mod dot_product;
pub mod hadamard;
pub mod ntt;
pub mod simulator;

pub use block_r1cs::{
    BlockR1csError, BlockR1csParameters, BlockR1csProof, PublicEquality, prove_block_r1cs,
    prove_block_r1cs_framed, verify_block_r1cs, verify_block_r1cs_framed,
};
pub use code::{AdditiveRsCode, CodeError, CodeParameters};
pub use commitment::{MerkleMatrix, MerkleMatrixOpening};
pub use constraints::{
    ArithmeticCircuit, CircuitBuilder, ConstraintCommitment, ConstraintError, ConstraintParameters,
    ConstraintProof, LinearCombination, commit_constraint_inputs, prove_constraints,
    prove_constraints_from_commitment, prove_constraints_with_parameters, verify_constraints,
};
pub use dot_product::{
    DotProductError, DotProductProof, DotProductProverData, VectorParameters, commit_vectors,
    commit_vectors_framed, prove_dot_product, verify_dot_product, verify_dot_product_framed,
};
pub use flock_core::field::F128;
pub use hadamard::{
    HadamardError, HadamardProof, HadamardProverData, commit_hadamard, commit_hadamard_framed,
    prove_hadamard_and_dots, verify_hadamard_and_dots, verify_hadamard_and_dots_framed,
};
pub use ntt::AdditiveCosetNtt;
pub use simulator::{
    OracleProgrammer, OracleProgrammingError, SimulationError, simulate_block_r1cs,
};

//! VEIL zero-knowledge dot-product protocol over the additive RS code.
//!
//! This is the native-`F128` counterpart of VEIL's `ZkDotProduct`: commit to
//! one or more vectors together with an additive masking vector, reveal a
//! random linear combination, and proximity-test that combination at Merkle
//! committed codeword coordinates.

use std::collections::BTreeSet;

use flock_core::{
    challenger::Challenger,
    field::F128,
    merkle::Hash,
    ro::{RoChannel, RoContext},
    zk::MaskSampler,
};
use serde::{Deserialize, Serialize};

use crate::{
    code::{AdditiveRsCode, CodeError, CodeParameters, certify_zk_code},
    commitment::{MerkleMatrix, MerkleMatrixOpening},
};

pub const DEFAULT_INVERSE_RATE: usize = 16;
pub const DEFAULT_QUERY_COUNT: usize = 112;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VectorParameters {
    pub vector_length: usize,
    pub padding_length: usize,
    pub code_length: usize,
    pub num_vectors: usize,
}

impl VectorParameters {
    pub fn new(vector_length: usize, num_vectors: usize) -> Result<Self, DotProductError> {
        Self::with_security(
            vector_length,
            num_vectors,
            DEFAULT_QUERY_COUNT,
            DEFAULT_INVERSE_RATE,
        )
    }

    pub fn with_security(
        vector_length: usize,
        num_vectors: usize,
        padding_length: usize,
        inverse_rate: usize,
    ) -> Result<Self, DotProductError> {
        if vector_length == 0 || num_vectors == 0 || padding_length == 0 {
            return Err(DotProductError::InvalidParameters);
        }
        if !inverse_rate.is_power_of_two() || inverse_rate < 2 {
            return Err(DotProductError::InvalidParameters);
        }
        let message_length = vector_length
            .checked_add(padding_length)
            .ok_or(DotProductError::InvalidParameters)?;
        let code_length = message_length
            .next_power_of_two()
            .checked_mul(inverse_rate)
            .ok_or(DotProductError::InvalidParameters)?;
        CodeParameters::new(message_length, code_length)?;
        // Every commitment is opened once at exactly `padding_length`
        // distinct coordinates. Keep the k-ZK budget executable rather than
        // relying on a caller-side convention.
        certify_zk_code(vector_length, padding_length, padding_length, code_length)?;
        if padding_length > code_length {
            return Err(DotProductError::InvalidParameters);
        }
        Ok(Self {
            vector_length,
            padding_length,
            code_length,
            num_vectors,
        })
    }

    pub fn message_length(self) -> usize {
        self.vector_length + self.padding_length
    }

    pub fn commitment_width(self) -> usize {
        self.num_vectors + 1
    }

    fn code(self) -> AdditiveRsCode {
        AdditiveRsCode::new(
            CodeParameters::new(self.message_length(), self.code_length)
                .expect("validated vector parameters"),
        )
    }
}

#[derive(Clone, Debug)]
pub struct DotProductProverData {
    parameters: VectorParameters,
    vectors: Vec<Vec<F128>>,
    mask: Vec<F128>,
    padding_rows: Vec<F128>,
    commitment: MerkleMatrix,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DotProductProof {
    pub parameters: VectorParameters,
    pub commitment: Hash,
    pub claimed_dot_products: Vec<F128>,
    pub mask_dot_product: F128,
    pub rlc_vector: Vec<F128>,
    pub rlc_padding: Vec<F128>,
    pub opening: MerkleMatrixOpening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DotProductError {
    InvalidParameters,
    WrongVectorCount,
    WrongVectorLength,
    WrongDotVectorLength,
    WrongProofShape,
    RlcDotProductMismatch,
    InvalidMerkleOpening,
    RevealedCodewordMismatch(usize),
    Code(CodeError),
}

impl From<CodeError> for DotProductError {
    fn from(value: CodeError) -> Self {
        Self::Code(value)
    }
}

pub fn commit_vectors<R: MaskSampler + ?Sized>(
    vectors: &[Vec<F128>],
    parameters: VectorParameters,
    rng: &mut R,
    ctx: &RoContext,
    channel: RoChannel,
) -> Result<DotProductProverData, DotProductError> {
    if vectors.len() != parameters.num_vectors {
        return Err(DotProductError::WrongVectorCount);
    }
    if vectors
        .iter()
        .any(|vector| vector.len() != parameters.vector_length)
    {
        return Err(DotProductError::WrongVectorLength);
    }

    let mut mask = vec![F128::ZERO; parameters.vector_length];
    rng.fill_f128(&mut mask);
    let width = parameters.commitment_width();
    let mut padding_rows = vec![F128::ZERO; parameters.padding_length * width];
    rng.fill_f128(&mut padding_rows);

    let mut messages = Vec::with_capacity(width);
    for vector in vectors.iter().chain(std::iter::once(&mask)) {
        let column = messages.len();
        let mut message = vector.clone();
        message.extend(padding_rows.chunks_exact(width).map(|row| row[column]));
        messages.push(message);
    }
    let codewords = parameters.code().encode_batch(&messages)?;
    let commitment = MerkleMatrix::new(&codewords, rng, ctx, channel);

    Ok(DotProductProverData {
        parameters,
        vectors: vectors.to_vec(),
        mask,
        padding_rows,
        commitment,
    })
}

impl DotProductProverData {
    pub fn root(&self) -> Hash {
        self.commitment.root()
    }
}

pub fn prove_dot_product<C: Challenger>(
    dot_vector: &[F128],
    data: DotProductProverData,
    challenger: &mut C,
) -> Result<DotProductProof, DotProductError> {
    let DotProductProverData {
        parameters,
        vectors,
        mask,
        padding_rows,
        commitment,
    } = data;
    if dot_vector.len() != parameters.vector_length {
        return Err(DotProductError::WrongDotVectorLength);
    }

    challenger.observe_label(b"veil-f128-dot-product");
    let claimed_dot_products: Vec<F128> = vectors
        .iter()
        .map(|vector| dot_product(vector, dot_vector))
        .collect();
    let mask_dot_product = dot_product(&mask, dot_vector);
    let root = commitment.root();

    challenger.observe_f128_slice(dot_vector);
    challenger.observe_f128_slice(&claimed_dot_products);
    challenger.observe_f128(mask_dot_product);
    challenger.observe_bytes(&root);
    let rho = sample_nonzero(challenger);

    let rlc_vector = (0..parameters.vector_length)
        .map(|index| {
            vectors
                .iter()
                .rev()
                .fold(mask[index], |accumulator, vector| {
                    vector[index] + rho * accumulator
                })
        })
        .collect::<Vec<_>>();
    let rlc_padding = padding_rows
        .chunks_exact(parameters.commitment_width())
        .map(|row| {
            row.iter()
                .rev()
                .fold(F128::ZERO, |accumulator, value| *value + rho * accumulator)
        })
        .collect::<Vec<_>>();

    challenger.observe_f128_slice(&rlc_vector);
    challenger.observe_f128_slice(&rlc_padding);
    let positions = sample_unique_positions(
        challenger,
        parameters.code_length,
        parameters.padding_length,
    );
    let opening = commitment.open(&positions);

    Ok(DotProductProof {
        parameters,
        commitment: root,
        claimed_dot_products,
        mask_dot_product,
        rlc_vector,
        rlc_padding,
        opening,
    })
}

pub fn verify_dot_product<C: Challenger>(
    dot_vector: &[F128],
    proof: &DotProductProof,
    challenger: &mut C,
    ctx: &RoContext,
    channel: RoChannel,
) -> Result<(), DotProductError> {
    let parameters = proof.parameters;
    VectorParameters::with_security(
        parameters.vector_length,
        parameters.num_vectors,
        parameters.padding_length,
        parameters.code_length / parameters.message_length().next_power_of_two(),
    )
    .map_err(|_| DotProductError::InvalidParameters)
    .and_then(|expected| {
        if expected == parameters {
            Ok(())
        } else {
            Err(DotProductError::InvalidParameters)
        }
    })?;
    if dot_vector.len() != parameters.vector_length
        || proof.claimed_dot_products.len() != parameters.num_vectors
        || proof.rlc_vector.len() != parameters.vector_length
        || proof.rlc_padding.len() != parameters.padding_length
    {
        return Err(DotProductError::WrongProofShape);
    }

    challenger.observe_label(b"veil-f128-dot-product");
    challenger.observe_f128_slice(dot_vector);
    challenger.observe_f128_slice(&proof.claimed_dot_products);
    challenger.observe_f128(proof.mask_dot_product);
    challenger.observe_bytes(&proof.commitment);
    let rho = sample_nonzero(challenger);

    let expected_dot = proof
        .claimed_dot_products
        .iter()
        .chain(std::iter::once(&proof.mask_dot_product))
        .rev()
        .fold(F128::ZERO, |accumulator, value| *value + rho * accumulator);
    if expected_dot != dot_product(&proof.rlc_vector, dot_vector) {
        return Err(DotProductError::RlcDotProductMismatch);
    }

    challenger.observe_f128_slice(&proof.rlc_vector);
    challenger.observe_f128_slice(&proof.rlc_padding);
    let positions = sample_unique_positions(
        challenger,
        parameters.code_length,
        parameters.padding_length,
    );
    if positions != proof.opening.positions {
        return Err(DotProductError::WrongProofShape);
    }
    if !proof.opening.verify(
        &proof.commitment,
        parameters.code_length,
        parameters.commitment_width(),
        ctx,
        channel,
    ) {
        return Err(DotProductError::InvalidMerkleOpening);
    }

    let mut rlc_message = proof.rlc_vector.clone();
    rlc_message.extend_from_slice(&proof.rlc_padding);
    let encoded_rlc = parameters.code().encode(&rlc_message)?;
    for &position in &positions {
        let row = proof
            .opening
            .row(position, parameters.commitment_width())
            .ok_or(DotProductError::WrongProofShape)?;
        let row_rlc = row
            .iter()
            .rev()
            .fold(F128::ZERO, |accumulator, value| *value + rho * accumulator);
        if row_rlc != encoded_rlc[position] {
            return Err(DotProductError::RevealedCodewordMismatch(position));
        }
    }
    Ok(())
}

pub(crate) fn sample_unique_positions<C: Challenger>(
    challenger: &mut C,
    code_length: usize,
    count: usize,
) -> Vec<usize> {
    assert!(code_length.is_power_of_two());
    assert!(count <= code_length);
    let mask = code_length - 1;
    let mut positions = BTreeSet::new();
    while positions.len() < count {
        positions.insert((challenger.sample_f128().lo as usize) & mask);
    }
    positions.into_iter().collect()
}

/// Sample uniformly from `F128 \ {0}`. The last proximity-generator
/// coefficient must be non-zero: at zero the additive masking vector drops
/// out and the revealed linear combination is the witness itself.
pub(crate) fn sample_nonzero<C: Challenger>(challenger: &mut C) -> F128 {
    loop {
        let value = challenger.sample_f128();
        if !value.is_zero() {
            return value;
        }
    }
}

/// Sample uniformly from `F128 \ {0, 1}`. VEIL's six-value multiplication
/// padding is invertible only away from these two exceptional challenges.
pub(crate) fn sample_not_zero_or_one<C: Challenger>(challenger: &mut C) -> F128 {
    loop {
        let value = challenger.sample_f128();
        if !value.is_zero() && value != F128::ONE {
            return value;
        }
    }
}

pub(crate) fn dot_product(left: &[F128], right: &[F128]) -> F128 {
    assert_eq!(left.len(), right.len());
    left.iter()
        .zip(right)
        .fold(F128::ZERO, |sum, (left, right)| sum + *left * *right)
}

#[cfg(test)]
mod tests {
    use flock_core::{challenger::FsChallenger, zk::ZkRng};

    use super::*;

    fn vector(length: usize, offset: u64) -> Vec<F128> {
        (0..length)
            .map(|index| F128::new(offset + index as u64, (index as u64).rotate_left(9)))
            .collect()
    }

    #[test]
    fn dot_product_proof_roundtrip() {
        let parameters = VectorParameters::with_security(19, 3, 8, 4).unwrap();
        let vectors = vec![vector(19, 10), vector(19, 100), vector(19, 1000)];
        let dot_vector = vector(19, 77);
        let mut rng = ZkRng::from_seed([7; 32]);
        let ctx = RoContext::native([1; 32]);
        let data =
            commit_vectors(&vectors, parameters, &mut rng, &ctx, RoChannel::Witness).unwrap();
        let mut prover_challenger = FsChallenger::new(b"veil-f128-dot-test");
        let proof = prove_dot_product(&dot_vector, data, &mut prover_challenger).unwrap();
        let mut verifier_challenger = FsChallenger::new(b"veil-f128-dot-test");
        verify_dot_product(
            &dot_vector,
            &proof,
            &mut verifier_challenger,
            &ctx,
            RoChannel::Witness,
        )
        .unwrap();
        assert_eq!(
            proof.claimed_dot_products,
            vectors
                .iter()
                .map(|value| dot_product(value, &dot_vector))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn dot_product_proof_rejects_claim_and_opening_mutations() {
        let parameters = VectorParameters::with_security(8, 1, 4, 4).unwrap();
        let vectors = vec![vector(8, 10)];
        let dot_vector = vector(8, 77);
        let ctx = RoContext::native([2; 32]);
        let make_proof = || {
            let mut rng = ZkRng::from_seed([9; 32]);
            let data =
                commit_vectors(&vectors, parameters, &mut rng, &ctx, RoChannel::Witness).unwrap();
            let mut challenger = FsChallenger::new(b"veil-f128-dot-mutation");
            prove_dot_product(&dot_vector, data, &mut challenger).unwrap()
        };

        let mut bad_claim = make_proof();
        bad_claim.claimed_dot_products[0] += F128::ONE;
        let mut challenger = FsChallenger::new(b"veil-f128-dot-mutation");
        assert!(
            verify_dot_product(
                &dot_vector,
                &bad_claim,
                &mut challenger,
                &ctx,
                RoChannel::Witness,
            )
            .is_err()
        );

        let mut bad_opening = make_proof();
        bad_opening.opening.rows[0] += F128::ONE;
        let mut challenger = FsChallenger::new(b"veil-f128-dot-mutation");
        assert!(
            verify_dot_product(
                &dot_vector,
                &bad_opening,
                &mut challenger,
                &ctx,
                RoChannel::Witness,
            )
            .is_err()
        );
    }
}

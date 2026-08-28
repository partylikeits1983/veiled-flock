//! VEIL zero-knowledge Hadamard-product protocol over `F128`.
//!
//! The protocol proves `a[i] * b[i] = c[i]` while simultaneously proving
//! random-linear-combination dot products of `a`, `b`, and `c`. It uses the
//! additive RS product code from [`crate::code`] and shares one Merkle opening
//! across both checks.

use flock_core::{
    challenger::Challenger,
    field::F128,
    merkle::Hash,
    ro::{RoChannel, RoContext},
    zk::MaskSampler,
};
use serde::{Deserialize, Serialize};

use crate::{
    code::{AdditiveRsCode, CodeError, CodeParameters},
    commitment::{MerkleMatrix, MerkleMatrixOpening},
    dot_product::{VectorParameters, dot_product, sample_nonzero, sample_unique_positions},
};

#[derive(Clone, Debug)]
pub struct HadamardProverData {
    parameters: VectorParameters,
    a: Vec<F128>,
    b: Vec<F128>,
    c: Vec<F128>,
    additive_mask: Vec<F128>,
    padding_rows: Vec<F128>,
    product_mask_intermediate: Vec<F128>,
    codewords: Vec<Vec<F128>>,
    commitment: MerkleMatrix,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HadamardProof {
    pub parameters: VectorParameters,
    pub commitment: Hash,
    pub gamma: F128,
    pub phi: Vec<F128>,
    pub claimed_dot_products: [F128; 3],
    pub mask_dot_product: F128,
    pub rlc_vector: Vec<F128>,
    pub rlc_padding: Vec<F128>,
    pub opening: MerkleMatrixOpening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HadamardError {
    InvalidParameters,
    WrongVectorLength,
    WrongDotVectorLength,
    WrongProofShape,
    ReductionCheckFailed,
    RlcDotProductMismatch,
    InvalidMerkleOpening,
    ProductCodewordMismatch(usize),
    DotCodewordMismatch(usize),
    Code(CodeError),
}

impl From<CodeError> for HadamardError {
    fn from(value: CodeError) -> Self {
        Self::Code(value)
    }
}

impl HadamardProverData {
    pub fn root(&self) -> Hash {
        self.commitment.root()
    }
}

pub fn commit_hadamard<R: MaskSampler + ?Sized>(
    a: &[F128],
    b: &[F128],
    c: &[F128],
    parameters: VectorParameters,
    rng: &mut R,
    ctx: &RoContext,
    channel: RoChannel,
) -> Result<HadamardProverData, HadamardError> {
    if parameters.num_vectors != 3 || parameters.padding_length == 0 {
        return Err(HadamardError::InvalidParameters);
    }
    if a.len() != parameters.vector_length
        || b.len() != parameters.vector_length
        || c.len() != parameters.vector_length
    {
        return Err(HadamardError::WrongVectorLength);
    }

    let mut additive_mask = vec![F128::ZERO; parameters.vector_length];
    rng.fill_f128(&mut additive_mask);
    let mut padding_rows = vec![F128::ZERO; parameters.padding_length * 4];
    rng.fill_f128(&mut padding_rows);

    let code = code_for(parameters)?;
    let mut messages = Vec::with_capacity(4);
    for vector in [a, b, c, &additive_mask] {
        let column = messages.len();
        let mut message = vector.to_vec();
        message.extend(
            padding_rows
                .as_chunks::<4>()
                .0
                .iter()
                .map(|row| row[column]),
        );
        messages.push(message);
    }
    let mut codewords = code.encode_batch(&messages)?;

    let mut product_mask_intermediate = vec![F128::ZERO; code.parameters().square_message_length()];
    rng.fill_f128(&mut product_mask_intermediate);
    codewords.push(code.encode_square(&product_mask_intermediate)?);
    let commitment = MerkleMatrix::new(&codewords, ctx, channel);

    Ok(HadamardProverData {
        parameters,
        a: a.to_vec(),
        b: b.to_vec(),
        c: c.to_vec(),
        additive_mask,
        padding_rows,
        product_mask_intermediate,
        codewords,
        commitment,
    })
}

pub fn prove_hadamard_and_dots<C: Challenger>(
    dot_vector: &[F128],
    data: HadamardProverData,
    challenger: &mut C,
) -> Result<HadamardProof, HadamardError> {
    let HadamardProverData {
        parameters,
        a,
        b,
        c,
        additive_mask,
        padding_rows,
        product_mask_intermediate,
        codewords,
        commitment,
    } = data;
    if dot_vector.len() != parameters.vector_length {
        return Err(HadamardError::WrongDotVectorLength);
    }
    let code = code_for(parameters)?;
    let root = commitment.root();

    challenger.observe_label(b"veil-f128-hadamard");
    challenger.observe_bytes(&root);
    let evaluation_point = challenger.sample_f128();
    let product_mask_reduced = code.square_to_base(&product_mask_intermediate)?;
    let gamma = dot_product(
        &powers(evaluation_point, parameters.vector_length),
        &product_mask_reduced[..parameters.vector_length],
    );
    challenger.observe_f128(gamma);
    let product_mask_coefficient = sample_nonzero(challenger);

    let product_word = (0..parameters.code_length)
        .map(|index| {
            codewords[0][index] * codewords[1][index]
                + codewords[2][index]
                + product_mask_coefficient * codewords[4][index]
        })
        .collect::<Vec<_>>();
    let phi = code.decode_square(&product_word)?;
    challenger.observe_f128_slice(&phi);

    let claimed_dot_products = [
        dot_product(&a, dot_vector),
        dot_product(&b, dot_vector),
        dot_product(&c, dot_vector),
    ];
    let mask_dot_product = dot_product(&additive_mask, dot_vector);
    challenger.observe_f128_slice(dot_vector);
    challenger.observe_f128_slice(&claimed_dot_products);
    challenger.observe_f128(mask_dot_product);
    challenger.observe_bytes(&root);
    let rho = sample_nonzero(challenger);

    let rlc_vector = (0..parameters.vector_length)
        .map(|index| a[index] + rho * (b[index] + rho * (c[index] + rho * additive_mask[index])))
        .collect::<Vec<_>>();
    let rlc_padding = padding_rows
        .as_chunks::<4>()
        .0
        .iter()
        .map(|row| row[0] + rho * (row[1] + rho * (row[2] + rho * row[3])))
        .collect::<Vec<_>>();
    challenger.observe_f128_slice(&rlc_vector);
    challenger.observe_f128_slice(&rlc_padding);

    let positions = sample_unique_positions(
        challenger,
        parameters.code_length,
        parameters.padding_length,
    );
    let opening = commitment.open(&positions);

    Ok(HadamardProof {
        parameters,
        commitment: root,
        gamma,
        phi,
        claimed_dot_products,
        mask_dot_product,
        rlc_vector,
        rlc_padding,
        opening,
    })
}

pub fn verify_hadamard_and_dots<C: Challenger>(
    dot_vector: &[F128],
    proof: &HadamardProof,
    challenger: &mut C,
    ctx: &RoContext,
    channel: RoChannel,
) -> Result<(), HadamardError> {
    let parameters = proof.parameters;
    validate_parameters(parameters)?;
    if dot_vector.len() != parameters.vector_length
        || proof.phi.len() != 2 * parameters.message_length().next_power_of_two()
        || proof.rlc_vector.len() != parameters.vector_length
        || proof.rlc_padding.len() != parameters.padding_length
    {
        return Err(HadamardError::WrongProofShape);
    }
    let code = code_for(parameters)?;

    challenger.observe_label(b"veil-f128-hadamard");
    challenger.observe_bytes(&proof.commitment);
    let evaluation_point = challenger.sample_f128();
    challenger.observe_f128(proof.gamma);
    let product_mask_coefficient = sample_nonzero(challenger);
    challenger.observe_f128_slice(&proof.phi);

    let phi_reduced = code.square_to_base(&proof.phi)?;
    if dot_product(
        &powers(evaluation_point, parameters.vector_length),
        &phi_reduced[..parameters.vector_length],
    ) != product_mask_coefficient * proof.gamma
    {
        return Err(HadamardError::ReductionCheckFailed);
    }

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
    if dot_product(&proof.rlc_vector, dot_vector) != expected_dot {
        return Err(HadamardError::RlcDotProductMismatch);
    }
    challenger.observe_f128_slice(&proof.rlc_vector);
    challenger.observe_f128_slice(&proof.rlc_padding);

    let positions = sample_unique_positions(
        challenger,
        parameters.code_length,
        parameters.padding_length,
    );
    if positions != proof.opening.positions {
        return Err(HadamardError::WrongProofShape);
    }
    if !proof
        .opening
        .verify(&proof.commitment, parameters.code_length, 5, ctx, channel)
    {
        return Err(HadamardError::InvalidMerkleOpening);
    }

    let phi_codeword = code.encode_square(&proof.phi)?;
    let mut rlc_message = proof.rlc_vector.clone();
    rlc_message.extend_from_slice(&proof.rlc_padding);
    let rlc_codeword = code.encode(&rlc_message)?;
    for &position in &positions {
        let row = proof
            .opening
            .row(position, 5)
            .ok_or(HadamardError::WrongProofShape)?;
        if phi_codeword[position] != row[0] * row[1] + row[2] + product_mask_coefficient * row[4] {
            return Err(HadamardError::ProductCodewordMismatch(position));
        }
        if rlc_codeword[position] != row[0] + rho * (row[1] + rho * (row[2] + rho * row[3])) {
            return Err(HadamardError::DotCodewordMismatch(position));
        }
    }
    Ok(())
}

fn validate_parameters(parameters: VectorParameters) -> Result<(), HadamardError> {
    if parameters.num_vectors != 3
        || parameters.vector_length == 0
        || parameters.padding_length == 0
        || !parameters.code_length.is_power_of_two()
    {
        return Err(HadamardError::InvalidParameters);
    }
    let inverse_rate = parameters.code_length / parameters.message_length().next_power_of_two();
    let expected = VectorParameters::with_security(
        parameters.vector_length,
        3,
        parameters.padding_length,
        inverse_rate,
    )
    .map_err(|_| HadamardError::InvalidParameters)?;
    if expected != parameters {
        return Err(HadamardError::InvalidParameters);
    }
    Ok(())
}

fn code_for(parameters: VectorParameters) -> Result<AdditiveRsCode, HadamardError> {
    validate_parameters(parameters)?;
    Ok(AdditiveRsCode::new(CodeParameters::new(
        parameters.message_length(),
        parameters.code_length,
    )?))
}

fn powers(base: F128, length: usize) -> Vec<F128> {
    let mut current = F128::ONE;
    (0..length)
        .map(|_| {
            let result = current;
            current *= base;
            result
        })
        .collect()
}

#[cfg(test)]
mod tests;

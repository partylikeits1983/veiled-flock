//! Memory-linear VEIL compiler for FLOCK's native Boolean block R1CS.
//!
//! Expanding FLOCK's substituted BLAKE3 matrices into generic field-valued
//! linear combinations is prohibitively large.  This module keeps the sparse
//! binary matrices in their native form.  One Hadamard proof simultaneously
//! enforces
//!
//! ```text
//!     (A z) * (B z) = z       and       z * z = z,
//! ```
//!
//! while one dot-product proof links the three Hadamard claims back to the
//! same committed `z` and batches the public input equalities.

use flock_core::{
    challenger::Challenger,
    field::F128,
    r1cs::BlockR1cs,
    ro::{RoChannel, RoContext},
    zk::MaskSampler,
};
use serde::{Deserialize, Serialize};

use crate::{
    dot_product::{
        DotProductError, DotProductProof, VectorParameters, commit_vectors, prove_dot_product,
        sample_not_zero_or_one, verify_dot_product,
    },
    hadamard::{
        HadamardError, HadamardProof, commit_hadamard, prove_hadamard_and_dots,
        verify_hadamard_and_dots,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockR1csParameters {
    pub query_count: usize,
    pub inverse_rate: usize,
}

impl BlockR1csParameters {
    /// Reference profile used by the end-to-end experiment. The base code has
    /// rate 1/4, so its square/product code has rate 1/2 and retains a
    /// non-trivial proximity gap. This is still not a reviewed production
    /// parameter set.
    pub const fn experimental() -> Self {
        Self {
            query_count: 128,
            inverse_rate: 4,
        }
    }

    fn validate(self) -> Result<Self, BlockR1csError> {
        if self.query_count == 0 || self.inverse_rate < 4 || !self.inverse_rate.is_power_of_two() {
            return Err(BlockR1csError::InvalidParameters);
        }
        Ok(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicEquality {
    pub index: usize,
    pub value: F128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockR1csProof {
    pub parameters: BlockR1csParameters,
    pub witness_length: usize,
    pub hadamard: HadamardProof,
    pub witness: DotProductProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockR1csError {
    InvalidParameters,
    UnsupportedR1cs,
    WrongWitnessLength,
    WrongProofShape,
    UnsatisfiedR1cs,
    NonBooleanWitness,
    PublicInputMismatch(usize),
    LinkClaimMismatch,
    Dot(DotProductError),
    Hadamard(HadamardError),
}

impl From<DotProductError> for BlockR1csError {
    fn from(value: DotProductError) -> Self {
        Self::Dot(value)
    }
}

impl From<HadamardError> for BlockR1csError {
    fn from(value: HadamardError) -> Self {
        Self::Hadamard(value)
    }
}

/// Prove a FLOCK block-R1CS witness.  `a` and `b` are accepted separately so
/// callers can use FLOCK's fast circuit-specific witness generator instead
/// of re-applying the very dense substituted matrices.
#[allow(clippy::too_many_arguments)]
pub fn prove_block_r1cs<C: Challenger, R: MaskSampler + ?Sized>(
    r1cs: &BlockR1cs,
    z: &[F128],
    a: &[F128],
    b: &[F128],
    public: &[PublicEquality],
    parameters: BlockR1csParameters,
    rng: &mut R,
    challenger: &mut C,
    ctx: &RoContext,
) -> Result<BlockR1csProof, BlockR1csError> {
    let parameters = parameters.validate()?;
    validate_relation_shape(r1cs, z, a, b, public)?;
    for index in 0..z.len() {
        if z[index] * z[index] != z[index] {
            return Err(BlockR1csError::NonBooleanWitness);
        }
        if a[index] * b[index] != z[index] {
            return Err(BlockR1csError::UnsatisfiedR1cs);
        }
    }
    for equality in public {
        if z[equality.index] != equality.value {
            return Err(BlockR1csError::PublicInputMismatch(equality.index));
        }
    }

    let n = z.len();
    let mut random = [F128::ZERO; 3];
    rng.fill_f128(&mut random);
    let [r, s, t] = random;
    let r_plus_one = r + F128::ONE;
    let multiplication_padding = [r, s, r * s, r_plus_one, t, r_plus_one * t];
    let mut extended_witness = Vec::with_capacity(n + 6);
    extended_witness.extend_from_slice(z);
    extended_witness.extend_from_slice(&multiplication_padding);

    let mut hadamard_a = Vec::with_capacity(2 * n + 2);
    hadamard_a.extend_from_slice(a);
    hadamard_a.extend_from_slice(z);
    hadamard_a.extend_from_slice(&[r, r_plus_one]);
    let mut hadamard_b = Vec::with_capacity(2 * n + 2);
    hadamard_b.extend_from_slice(b);
    hadamard_b.extend_from_slice(z);
    hadamard_b.extend_from_slice(&[s, t]);
    let mut hadamard_c = Vec::with_capacity(2 * n + 2);
    hadamard_c.extend_from_slice(z);
    hadamard_c.extend_from_slice(z);
    hadamard_c.extend_from_slice(&[r * s, r_plus_one * t]);

    let witness_parameters = vector_parameters(n + 6, 1, parameters)?;
    let hadamard_parameters = vector_parameters(2 * n + 2, 3, parameters)?;
    let witness_data = commit_vectors(
        &[extended_witness],
        witness_parameters,
        rng,
        ctx,
        RoChannel::Witness,
    )?;
    let hadamard_data = commit_hadamard(
        &hadamard_a,
        &hadamard_b,
        &hadamard_c,
        hadamard_parameters,
        rng,
        ctx,
        RoChannel::MaskP,
    )?;

    challenger.observe_label(b"veil-f128-flock-block-r1cs-v1");
    challenger.observe_bytes(&witness_data.root());
    challenger.observe_bytes(&hadamard_data.root());
    let multiplication_rlc = sample_not_zero_or_one(challenger);
    let dot_vector = powers(multiplication_rlc, 2 * n + 2);
    let hadamard = prove_hadamard_and_dots(&dot_vector, hadamard_data, challenger)?;

    let link_rlc = challenger.sample_f128();
    let (link_vector, expected_dot) = build_link_claim(
        r1cs,
        public,
        &dot_vector,
        hadamard.claimed_dot_products,
        link_rlc,
    )?;
    let witness = prove_dot_product(&link_vector, witness_data, challenger)?;
    if witness.claimed_dot_products.as_slice() != [expected_dot] {
        return Err(BlockR1csError::LinkClaimMismatch);
    }

    Ok(BlockR1csProof {
        parameters,
        witness_length: n,
        hadamard,
        witness,
    })
}

pub fn verify_block_r1cs<C: Challenger>(
    r1cs: &BlockR1cs,
    public: &[PublicEquality],
    proof: &BlockR1csProof,
    challenger: &mut C,
    ctx: &RoContext,
) -> Result<(), BlockR1csError> {
    let parameters = proof.parameters.validate()?;
    let n = r1cs.n();
    validate_public(r1cs, public)?;
    if proof.witness_length != n
        || proof.witness.parameters != vector_parameters(n + 6, 1, parameters)?
        || proof.hadamard.parameters != vector_parameters(2 * n + 2, 3, parameters)?
    {
        return Err(BlockR1csError::WrongProofShape);
    }
    challenger.observe_label(b"veil-f128-flock-block-r1cs-v1");
    challenger.observe_bytes(&proof.witness.commitment);
    challenger.observe_bytes(&proof.hadamard.commitment);
    let multiplication_rlc = sample_not_zero_or_one(challenger);
    let dot_vector = powers(multiplication_rlc, 2 * n + 2);
    verify_hadamard_and_dots(
        &dot_vector,
        &proof.hadamard,
        challenger,
        ctx,
        RoChannel::MaskP,
    )?;

    let link_rlc = challenger.sample_f128();
    let (link_vector, expected_dot) = build_link_claim(
        r1cs,
        public,
        &dot_vector,
        proof.hadamard.claimed_dot_products,
        link_rlc,
    )?;
    if proof.witness.claimed_dot_products.as_slice() != [expected_dot] {
        return Err(BlockR1csError::LinkClaimMismatch);
    }
    verify_dot_product(
        &link_vector,
        &proof.witness,
        challenger,
        ctx,
        RoChannel::Witness,
    )?;
    Ok(())
}

pub(crate) fn vector_parameters(
    length: usize,
    width: usize,
    parameters: BlockR1csParameters,
) -> Result<VectorParameters, BlockR1csError> {
    Ok(VectorParameters::with_security(
        length,
        width,
        parameters.query_count,
        parameters.inverse_rate,
    )?)
}

fn validate_relation_shape(
    r1cs: &BlockR1cs,
    z: &[F128],
    a: &[F128],
    b: &[F128],
    public: &[PublicEquality],
) -> Result<(), BlockR1csError> {
    if z.len() != r1cs.n() || a.len() != z.len() || b.len() != z.len() {
        return Err(BlockR1csError::WrongWitnessLength);
    }
    validate_public(r1cs, public)
}

pub(crate) fn validate_public(
    r1cs: &BlockR1cs,
    public: &[PublicEquality],
) -> Result<(), BlockR1csError> {
    if !r1cs.c0_is_identity() || r1cs.a_0.num_rows != r1cs.k() || r1cs.b_0.num_rows != r1cs.k() {
        return Err(BlockR1csError::UnsupportedR1cs);
    }
    if public.iter().any(|equality| equality.index >= r1cs.n()) {
        return Err(BlockR1csError::WrongWitnessLength);
    }
    Ok(())
}

pub(crate) fn build_link_claim(
    r1cs: &BlockR1cs,
    public: &[PublicEquality],
    dot_vector: &[F128],
    claims: [F128; 3],
    link_rlc: F128,
) -> Result<(Vec<F128>, F128), BlockR1csError> {
    let n = r1cs.n();
    if dot_vector.len() != 2 * n + 2 {
        return Err(BlockR1csError::WrongProofShape);
    }
    let r1cs_weights = &dot_vector[..n];
    let boolean_weights = &dot_vector[n..2 * n];
    let a_transpose = transpose_apply(r1cs, &r1cs.a_0.rows, r1cs_weights);
    let b_transpose = transpose_apply(r1cs, &r1cs.b_0.rows, r1cs_weights);

    let pad_weights = &dot_vector[2 * n..];
    let equation_count = 4 + public.len();
    let equation_weights = powers(link_rlc, equation_count);
    let mut combined = vec![F128::ZERO; n + 6];
    for index in 0..n {
        combined[index] = equation_weights[0] * (a_transpose[index] + boolean_weights[index])
            + equation_weights[1] * (b_transpose[index] + boolean_weights[index])
            + equation_weights[2] * (r1cs_weights[index] + boolean_weights[index]);
    }
    // The six VEIL padding values remain private in the same witness
    // commitment. Their two product relations are the final two Hadamard
    // triples; this linear link only needs to tie each side's dot claim to
    // the corresponding private values.
    const R: usize = 0;
    const S: usize = 1;
    const RS: usize = 2;
    const R_PLUS_ONE: usize = 3;
    const T: usize = 4;
    const R_PLUS_ONE_TIMES_T: usize = 5;
    combined[n + R] += equation_weights[0] * pad_weights[0];
    combined[n + R_PLUS_ONE] += equation_weights[0] * pad_weights[1];
    combined[n + S] += equation_weights[1] * pad_weights[0];
    combined[n + T] += equation_weights[1] * pad_weights[1];
    combined[n + RS] += equation_weights[2] * pad_weights[0];
    combined[n + R_PLUS_ONE_TIMES_T] += equation_weights[2] * pad_weights[1];

    let mut expected = equation_weights[0] * claims[0]
        + equation_weights[1] * claims[1]
        + equation_weights[2] * claims[2];
    // r_plus_one = r + 1 (subtraction is addition in characteristic two).
    combined[n + R] += equation_weights[3];
    combined[n + R_PLUS_ONE] += equation_weights[3];
    expected += equation_weights[3];
    for (offset, equality) in public.iter().enumerate() {
        let weight = equation_weights[4 + offset];
        combined[equality.index] += weight;
        expected += weight * equality.value;
    }
    Ok((combined, expected))
}

fn transpose_apply(r1cs: &BlockR1cs, rows: &[Vec<usize>], weights: &[F128]) -> Vec<F128> {
    let mut output = vec![F128::ZERO; r1cs.n()];
    let k = r1cs.k();
    for block in 0..r1cs.n_outer() {
        let base = block * k;
        for (row, columns) in rows.iter().enumerate() {
            let weight = weights[base + row];
            for &column in columns {
                output[base + column] += weight;
            }
        }
    }
    output
}

pub(crate) fn powers(base: F128, length: usize) -> Vec<F128> {
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
mod tests {
    use flock_core::{
        challenger::FsChallenger,
        r1cs::{SparseBinaryMatrix, WitnessLayout},
        zk::ZkRng,
    };

    use super::*;

    fn tiny_r1cs() -> BlockR1cs {
        let a = SparseBinaryMatrix {
            num_rows: 4,
            num_cols: 4,
            rows: vec![vec![0], vec![1], vec![1], vec![0, 2]],
        };
        let b = SparseBinaryMatrix {
            num_rows: 4,
            num_cols: 4,
            rows: vec![vec![0], vec![0], vec![2], vec![1]],
        };
        let c = SparseBinaryMatrix {
            num_rows: 4,
            num_cols: 4,
            rows: (0..4).map(|index| vec![index]).collect(),
        };
        BlockR1cs {
            m: 2,
            k_log: 2,
            k_skip: 0,
            useful_bits: 4,
            a_0: a,
            b_0: b,
            c_0: c,
            layout: WitnessLayout::RowMajor,
            const_pin: Some(0),
            zk: None,
            digest_cache: Default::default(),
            csc_cache: Default::default(),
        }
    }

    #[test]
    fn block_r1cs_roundtrip_and_public_binding() {
        let r1cs = tiny_r1cs();
        let z = vec![F128::ONE, F128::ONE, F128::ZERO, F128::ONE];
        let a = r1cs.apply_a(&[true, true, false, true]);
        let b = r1cs.apply_b(&[true, true, false, true]);
        let lift = |bits: Vec<bool>| {
            bits.into_iter()
                .map(|bit| if bit { F128::ONE } else { F128::ZERO })
                .collect::<Vec<_>>()
        };
        let public = [PublicEquality {
            index: 1,
            value: F128::ONE,
        }];
        let parameters = BlockR1csParameters {
            query_count: 8,
            inverse_rate: 4,
        };
        let mut rng = ZkRng::from_seed([61; 32]);
        let mut prover = FsChallenger::new(b"block-r1cs-test");
        let ctx = RoContext::native([1; 32]);
        let proof = prove_block_r1cs(
            &r1cs,
            &z,
            &lift(a),
            &lift(b),
            &public,
            parameters,
            &mut rng,
            &mut prover,
            &ctx,
        )
        .unwrap();
        let mut verifier = FsChallenger::new(b"block-r1cs-test");
        verify_block_r1cs(&r1cs, &public, &proof, &mut verifier, &ctx).unwrap();

        let wrong = [PublicEquality {
            index: 1,
            value: F128::ZERO,
        }];
        let mut verifier = FsChallenger::new(b"block-r1cs-test");
        assert!(verify_block_r1cs(&r1cs, &wrong, &proof, &mut verifier, &ctx).is_err());
    }

    #[test]
    fn characteristic_two_six_value_padding_map_is_invertible() {
        // Normalize away the nonzero q_L factor. For q_{L+1} = alpha*q_L,
        // the three claim contributions are the map below. Its inverse exists
        // exactly when alpha is neither 0 nor 1.
        let alpha = F128::new(0x1234_5678_9abc_def0, 0xfedc_ba98_7654_3210);
        assert!(!alpha.is_zero() && alpha != F128::ONE);
        for offset in 1..32u64 {
            let r = F128::new(offset, offset.rotate_left(7));
            let s = F128::new(offset * 3, offset.rotate_left(19));
            let t = F128::new(offset * 5, offset.rotate_left(31));
            let claim_a = r + alpha * (r + F128::ONE);
            let claim_b = s + alpha * t;
            let claim_c = r * s + alpha * (r + F128::ONE) * t;

            let recovered_r = (claim_a + alpha) * (F128::ONE + alpha).inv();
            let recovered_t = (claim_c + recovered_r * claim_b) * alpha.inv();
            let recovered_s = claim_b + alpha * recovered_t;
            assert_eq!((recovered_r, recovered_s, recovered_t), (r, s, t));
        }
    }

    #[test]
    fn registered_profile_keeps_the_square_code_below_rate_one() {
        let parameters = BlockR1csParameters::experimental();
        assert_eq!(parameters.inverse_rate, 4);
        assert!(
            BlockR1csParameters {
                query_count: 128,
                inverse_rate: 2,
            }
            .validate()
            .is_err(),
            "a rate-1 square code has no useful proximity gap"
        );

        let vector = vector_parameters(16_390, 1, parameters).unwrap();
        let base_dimension = vector.message_length().next_power_of_two();
        let square_dimension = 2 * base_dimension;
        assert_eq!(vector.code_length, 2 * square_dimension);
    }
}

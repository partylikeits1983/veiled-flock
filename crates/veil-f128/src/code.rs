//! Reed--Solomon code over additive domains.
//!
//! A message consists of evaluations of a polynomial on an additive subspace.
//! Encoding evaluates the same polynomial on a disjoint affine coset.
//! Pointwise products of codewords therefore encode the product polynomial;
//! VEIL uses the resulting square code for its Hadamard checks.
//!
//! Uniform padding hides queried codeword symbols. Let `X` be the interpolation
//! domain, `P` the padding positions in `X`, and `Y` a set of queried positions
//! in the encoding domain. For `x` in `P` and `y` in `Y`, the padding-to-query
//! matrix has entry
//!
//! `L_x(y) = Z_X(y) / (Z_X'(x) (y - x))`,
//!
//! where `L_x` is the Lagrange basis polynomial for `x`. Removing the non-zero
//! row and column factors leaves a Cauchy matrix. Because the two domains are
//! disjoint and contain distinct points, every square submatrix is invertible.
//! Thus, when `|Y| <= |P|`, the padding-to-query map has full row rank and
//! uniform padding makes the queried symbols uniform for any fixed message.

use std::fmt;

use flock_core::field::F128;
use serde::{Deserialize, Serialize};

use crate::ntt::{AdditiveCosetNtt, disjoint_coset_offset};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodeParameters {
    pub message_length: usize,
    pub code_length: usize,
}

impl CodeParameters {
    pub fn new(message_length: usize, code_length: usize) -> Result<Self, CodeError> {
        if message_length == 0 {
            return Err(CodeError::EmptyMessage);
        }
        if !code_length.is_power_of_two() {
            return Err(CodeError::CodeLengthNotPowerOfTwo(code_length));
        }
        let padded = message_length.next_power_of_two();
        if code_length < 2 * padded {
            return Err(CodeError::InsufficientProductDistance {
                code_length,
                required: 2 * padded,
            });
        }
        if code_length.trailing_zeros() as usize >= 128 {
            return Err(CodeError::DomainTooLarge);
        }
        Ok(Self {
            message_length,
            code_length,
        })
    }

    pub fn padded_message_length(self) -> usize {
        self.message_length.next_power_of_two()
    }

    pub fn square_message_length(self) -> usize {
        2 * self.padded_message_length()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CodeError {
    EmptyMessage,
    CodeLengthNotPowerOfTwo(usize),
    InsufficientProductDistance { code_length: usize, required: usize },
    DomainTooLarge,
    WrongInputLength { expected: usize, actual: usize },
    WrongCodewordLength { expected: usize, actual: usize },
}

impl fmt::Display for CodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyMessage => write!(f, "message must not be empty"),
            Self::CodeLengthNotPowerOfTwo(length) => {
                write!(f, "code length {length} is not a power of two")
            }
            Self::InsufficientProductDistance {
                code_length,
                required,
            } => write!(
                f,
                "code length {code_length} is too small for the square code; need at least {required}"
            ),
            Self::DomainTooLarge => write!(f, "code domain exhausts GF(2^128)"),
            Self::WrongInputLength { expected, actual } => {
                write!(f, "wrong input length: expected {expected}, got {actual}")
            }
            Self::WrongCodewordLength { expected, actual } => write!(
                f,
                "wrong codeword length: expected {expected}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for CodeError {}

#[derive(Clone, Debug)]
pub struct AdditiveRsCode {
    parameters: CodeParameters,
    base: AdditiveCosetNtt,
    square_base: AdditiveCosetNtt,
    output: AdditiveCosetNtt,
}

impl AdditiveRsCode {
    pub fn new(parameters: CodeParameters) -> Self {
        let padded = parameters.padded_message_length();
        let base_log = padded.trailing_zeros() as usize;
        let code_log = parameters.code_length.trailing_zeros() as usize;
        Self {
            parameters,
            base: AdditiveCosetNtt::new(base_log, F128::ZERO),
            square_base: AdditiveCosetNtt::new(base_log + 1, F128::ZERO),
            output: AdditiveCosetNtt::new(code_log, disjoint_coset_offset(code_log)),
        }
    }

    pub fn parameters(&self) -> CodeParameters {
        self.parameters
    }

    pub fn encode(&self, message: &[F128]) -> Result<Vec<F128>, CodeError> {
        if message.len() != self.parameters.message_length {
            return Err(CodeError::WrongInputLength {
                expected: self.parameters.message_length,
                actual: message.len(),
            });
        }
        let mut coefficients = message.to_vec();
        coefficients.resize(self.parameters.padded_message_length(), F128::ZERO);
        self.base.inverse(&mut coefficients);
        coefficients.resize(self.parameters.code_length, F128::ZERO);
        self.output.forward(&mut coefficients);
        Ok(coefficients)
    }

    pub fn decode(&self, codeword: &[F128]) -> Result<Vec<F128>, CodeError> {
        self.check_codeword(codeword)?;
        let mut coefficients = codeword.to_vec();
        self.output.inverse(&mut coefficients);
        coefficients.truncate(self.parameters.padded_message_length());
        self.base.forward(&mut coefficients);
        coefficients.truncate(self.parameters.message_length);
        Ok(coefficients)
    }

    pub fn encode_batch(&self, messages: &[Vec<F128>]) -> Result<Vec<Vec<F128>>, CodeError> {
        messages
            .iter()
            .map(|message| self.encode(message))
            .collect()
    }

    /// Decode a word from the product code into evaluations on the twice-wide
    /// base domain.
    pub fn decode_square(&self, codeword: &[F128]) -> Result<Vec<F128>, CodeError> {
        self.check_codeword(codeword)?;
        let mut coefficients = codeword.to_vec();
        self.output.inverse(&mut coefficients);
        coefficients.truncate(self.parameters.square_message_length());
        self.square_base.forward(&mut coefficients);
        Ok(coefficients)
    }

    pub fn encode_square(&self, intermediate: &[F128]) -> Result<Vec<F128>, CodeError> {
        let expected = self.parameters.square_message_length();
        if intermediate.len() != expected {
            return Err(CodeError::WrongInputLength {
                expected,
                actual: intermediate.len(),
            });
        }
        let mut coefficients = intermediate.to_vec();
        self.square_base.inverse(&mut coefficients);
        coefficients.resize(self.parameters.code_length, F128::ZERO);
        self.output.forward(&mut coefficients);
        Ok(coefficients)
    }

    /// VEIL's reduction `D`: restrict evaluations on the twice-wide base
    /// subspace back to the original message points.
    pub fn square_to_base(&self, intermediate: &[F128]) -> Result<Vec<F128>, CodeError> {
        let expected = self.parameters.square_message_length();
        if intermediate.len() != expected {
            return Err(CodeError::WrongInputLength {
                expected,
                actual: intermediate.len(),
            });
        }
        Ok(intermediate[..self.parameters.message_length].to_vec())
    }

    fn check_codeword(&self, codeword: &[F128]) -> Result<(), CodeError> {
        if codeword.len() != self.parameters.code_length {
            return Err(CodeError::WrongCodewordLength {
                expected: self.parameters.code_length,
                actual: codeword.len(),
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SUCCINCT_MASK_VECTOR_LENGTH: usize = 248;
    const SUCCINCT_PRODUCT_VECTOR_LENGTH: usize = 3;
    const MAX_SQUARE_RATE: f64 = 0.25;
    const MIN_PROXIMITY_BITS: f64 = 108.0;

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> F128 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let lo = self.0 ^ self.0.rotate_left(23);
            self.0 = self.0.wrapping_mul(0xbf58_476d_1ce4_e5b9);
            F128::new(lo, self.0 ^ self.0.rotate_right(19))
        }

        fn vector(&mut self, length: usize) -> Vec<F128> {
            (0..length).map(|_| self.next()).collect()
        }
    }

    fn rank(mut matrix: Vec<Vec<F128>>) -> usize {
        if matrix.is_empty() {
            return 0;
        }
        let rows = matrix.len();
        let columns = matrix[0].len();
        let mut pivot_row = 0;
        for column in 0..columns {
            let Some(pivot) = (pivot_row..rows).find(|row| !matrix[*row][column].is_zero()) else {
                continue;
            };
            matrix.swap(pivot_row, pivot);
            let inverse = matrix[pivot_row][column].inv();
            for entry in &mut matrix[pivot_row][column..] {
                *entry *= inverse;
            }
            let pivot_values = matrix[pivot_row].clone();
            for (row, values) in matrix.iter_mut().enumerate() {
                if row == pivot_row || values[column].is_zero() {
                    continue;
                }
                let scale = values[column];
                for index in column..columns {
                    values[index] += scale * pivot_values[index];
                }
            }
            pivot_row += 1;
            if pivot_row == rows {
                break;
            }
        }
        pivot_row
    }

    fn domain_point(log_size: usize, offset: F128, index: usize) -> F128 {
        let mut point = offset;
        for bit in 0..log_size {
            if (index >> bit) & 1 == 1 {
                point += if bit < 64 {
                    F128::new(1u64 << bit, 0)
                } else {
                    F128::new(0, 1u64 << (bit - 64))
                };
            }
        }
        point
    }

    fn lagrange_evaluation(points: &[F128], values: &[F128], query: F128) -> F128 {
        assert_eq!(points.len(), values.len());
        points
            .iter()
            .enumerate()
            .fold(F128::ZERO, |sum, (index, point)| {
                let (numerator, denominator) = points
                    .iter()
                    .enumerate()
                    .filter(|(other_index, _)| *other_index != index)
                    .fold(
                        (F128::ONE, F128::ONE),
                        |(numerator, denominator), (_, other)| {
                            (
                                numerator * (query + *other),
                                denominator * (*point + *other),
                            )
                        },
                    );
                sum + values[index] * numerator * denominator.inv()
            })
    }

    #[test]
    fn encode_decode_roundtrip() {
        for length in [1usize, 2, 3, 8, 13, 64] {
            let padded = length.next_power_of_two();
            let code = AdditiveRsCode::new(CodeParameters::new(length, 16 * padded).unwrap());
            let message = Rng(length as u64).vector(length);
            assert_eq!(
                code.decode(&code.encode(&message).unwrap()).unwrap(),
                message
            );
        }
    }

    #[test]
    fn product_code_is_multiplicative_and_reduces_pointwise() {
        for length in [1usize, 3, 8, 13, 32] {
            let padded = length.next_power_of_two();
            let code = AdditiveRsCode::new(CodeParameters::new(length, 16 * padded).unwrap());
            let a = Rng(0xa000 + length as u64).vector(length);
            let b = Rng(0xb000 + length as u64).vector(length);
            let encoded_a = code.encode(&a).unwrap();
            let encoded_b = code.encode(&b).unwrap();
            let encoded_product: Vec<_> = encoded_a
                .iter()
                .zip(encoded_b)
                .map(|(a, b)| *a * b)
                .collect();
            let intermediate = code.decode_square(&encoded_product).unwrap();
            assert_eq!(code.encode_square(&intermediate).unwrap(), encoded_product);
            let reduced = code.square_to_base(&intermediate).unwrap();
            assert_eq!(
                reduced,
                a.iter().zip(b).map(|(a, b)| *a * b).collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn encoding_matches_lagrange_interpolation() {
        for message_length in [3usize, 5, 8] {
            let padded = message_length.next_power_of_two();
            let code_length = 4 * padded;
            let code =
                AdditiveRsCode::new(CodeParameters::new(message_length, code_length).unwrap());
            let mut base_values = Rng(0x6e77 + message_length as u64).vector(message_length);
            base_values.resize(padded, F128::ZERO);
            let base_log = padded.trailing_zeros() as usize;
            let base_points = (0..padded)
                .map(|index| domain_point(base_log, F128::ZERO, index))
                .collect::<Vec<_>>();
            let output_log = code_length.trailing_zeros() as usize;
            let output_offset = disjoint_coset_offset(output_log);
            let expected = (0..code_length)
                .map(|index| {
                    lagrange_evaluation(
                        &base_points,
                        &base_values,
                        domain_point(output_log, output_offset, index),
                    )
                })
                .collect::<Vec<_>>();
            assert_eq!(
                code.encode(&base_values[..message_length]).unwrap(),
                expected,
                "message_length={message_length}"
            );
        }
    }

    #[test]
    fn every_two_queries_are_masked_by_two_padding_symbols_in_tiny_code() {
        // Four base-domain message evaluations: two data followed by two
        // uniform pads. Check all C(16, 2) query sets exactly.
        let code = AdditiveRsCode::new(CodeParameters::new(4, 16).unwrap());
        let mut columns = Vec::new();
        for padding_index in 2..4 {
            let mut basis = vec![F128::ZERO; 4];
            basis[padding_index] = F128::ONE;
            columns.push(code.encode(&basis).unwrap());
        }
        for first in 0..16 {
            for second in first + 1..16 {
                let projection = vec![
                    vec![columns[0][first], columns[1][first]],
                    vec![columns[0][second], columns[1][second]],
                ];
                assert_eq!(rank(projection), 2, "queries [{first}, {second}]");
            }
        }
    }

    fn unique_positions(code_length: usize, count: usize, seed: u64) -> Vec<usize> {
        let mut state = seed;
        let mut positions = std::collections::BTreeSet::new();
        while positions.len() < count {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut value = state;
            value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            value ^= value >> 31;
            positions.insert(value as usize & (code_length - 1));
        }
        positions.into_iter().collect()
    }

    fn production_veil_geometries() -> [(usize, usize, usize); 2] {
        let profile = crate::constraints::ConstraintParameters::succinct_flock_experimental();
        [
            (
                SUCCINCT_MASK_VECTOR_LENGTH,
                profile.linear_padding,
                profile.inverse_rate,
            ),
            (
                SUCCINCT_PRODUCT_VECTOR_LENGTH,
                profile.hadamard_padding,
                profile.inverse_rate,
            ),
        ]
    }

    fn assert_sampled_padding_projections_have_full_rank(
        vector_length: usize,
        padding_length: usize,
        inverse_rate: usize,
    ) {
        let message_length = vector_length + padding_length;
        let code_length = message_length.next_power_of_two() * inverse_rate;
        let code = AdditiveRsCode::new(CodeParameters::new(message_length, code_length).unwrap());
        let padding_columns = (0..padding_length)
            .map(|padding_index| {
                let mut basis = vec![F128::ZERO; message_length];
                basis[vector_length + padding_index] = F128::ONE;
                code.encode(&basis).unwrap()
            })
            .collect::<Vec<_>>();

        let mut query_sets = vec![
            (0..padding_length).collect::<Vec<_>>(),
            (code_length - padding_length..code_length).collect::<Vec<_>>(),
            (0..padding_length)
                .map(|index| index * code_length / padding_length)
                .collect::<Vec<_>>(),
        ];
        query_sets.push(unique_positions(code_length, padding_length, 0x51a7));
        query_sets.push(unique_positions(code_length, padding_length, 0xc0de));

        for positions in query_sets {
            let projection = positions
                .iter()
                .map(|position| {
                    padding_columns
                        .iter()
                        .map(|column| column[*position])
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            assert_eq!(
                rank(projection),
                padding_length,
                "padding projection lost rank for vector={vector_length}, padding={padding_length}, \
                 inverse_rate={inverse_rate}, positions={positions:?}"
            );
        }
    }

    #[test]
    fn sampled_production_queries_have_full_rank_padding_maps() {
        for (vector_length, padding_length, inverse_rate) in production_veil_geometries() {
            assert_sampled_padding_projections_have_full_rank(
                vector_length,
                padding_length,
                inverse_rate,
            );
        }
    }

    #[test]
    fn production_square_code_proximity_bound_exceeds_108_bits() {
        for (vector_length, padding_length, inverse_rate) in production_veil_geometries() {
            let message_length = vector_length + padding_length;
            let padded = message_length.next_power_of_two();
            let parameters = CodeParameters::new(message_length, inverse_rate * padded).unwrap();
            let square_rate =
                parameters.square_message_length() as f64 / parameters.code_length as f64;
            let proximity_bits = -(padding_length as f64) * ((1.0 + square_rate) / 2.0).log2();
            assert!(square_rate <= MAX_SQUARE_RATE);
            assert!(proximity_bits > MIN_PROXIMITY_BITS);
        }
    }

    #[test]
    fn malformed_parameters_fail_closed() {
        assert_eq!(CodeParameters::new(0, 16), Err(CodeError::EmptyMessage));
        assert_eq!(
            CodeParameters::new(8, 12),
            Err(CodeError::CodeLengthNotPowerOfTwo(12))
        );
        assert!(matches!(
            CodeParameters::new(9, 16),
            Err(CodeError::InsufficientProductDistance { .. })
        ));
    }
}

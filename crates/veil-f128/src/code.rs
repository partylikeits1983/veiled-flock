//! Multiplicative Reed--Solomon code over disjoint additive domains.
//!
//! The message is represented by evaluations on a linear subspace `V`. The
//! codeword evaluates the interpolating polynomial on an affine coset disjoint
//! from the larger output subspace. Random message padding therefore masks any
//! bounded set of codeword coordinates by the usual RS interpolation argument.
//! Pointwise codeword products are evaluations of the product polynomial, so a
//! twice-degree square code supplies VEIL's Hadamard reduction.

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

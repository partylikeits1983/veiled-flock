use crate::field::F128;

use super::scalar::SymScalar;

/// Sound component-wise degree upper bound. Addition uses `max`; it never
/// assumes cancellation, while multiplication adds bounds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DegBound {
    degrees: Vec<u32>,
    definitely_zero: bool,
}

impl DegBound {
    pub fn variable(index: usize, variable_count: usize) -> Self {
        assert!(index < variable_count);
        let mut degrees = vec![0; variable_count];
        degrees[index] = 1;
        Self {
            degrees,
            definitely_zero: false,
        }
    }

    pub fn degrees(&self) -> &[u32] {
        &self.degrees
    }

    pub fn degree_of(&self, variable: usize) -> u32 {
        self.degrees.get(variable).copied().unwrap_or(0)
    }

    pub fn total_degree_bound(&self) -> u64 {
        self.degrees.iter().map(|degree| u64::from(*degree)).sum()
    }

    fn with_len(variable_count: usize, definitely_zero: bool) -> Self {
        Self {
            degrees: vec![0; variable_count],
            definitely_zero,
        }
    }

    fn aligned_degrees(&self, other: &Self) -> (Vec<u32>, Vec<u32>) {
        let len = self.degrees.len().max(other.degrees.len());
        assert!(self.degrees.is_empty() || self.degrees.len() == len);
        assert!(other.degrees.is_empty() || other.degrees.len() == len);
        let left = if self.degrees.is_empty() {
            vec![0; len]
        } else {
            self.degrees.clone()
        };
        let right = if other.degrees.is_empty() {
            vec![0; len]
        } else {
            other.degrees.clone()
        };
        (left, right)
    }
}

impl SymScalar for DegBound {
    fn zero() -> Self {
        Self::with_len(0, true)
    }

    fn one() -> Self {
        Self::with_len(0, false)
    }

    fn from_const(value: F128) -> Self {
        Self::with_len(0, value == F128::ZERO)
    }

    fn add(&self, other: &Self) -> Self {
        let (left, right) = self.aligned_degrees(other);
        if self.definitely_zero {
            return Self {
                degrees: right,
                definitely_zero: other.definitely_zero,
            };
        }
        if other.definitely_zero {
            return Self {
                degrees: left,
                definitely_zero: self.definitely_zero,
            };
        }
        Self {
            degrees: left.iter().zip(&right).map(|(a, b)| (*a).max(*b)).collect(),
            definitely_zero: false,
        }
    }

    fn mul(&self, other: &Self) -> Self {
        let (left, right) = self.aligned_degrees(other);
        if self.definitely_zero || other.definitely_zero {
            return Self::with_len(left.len(), true);
        }
        Self {
            degrees: left
                .iter()
                .zip(&right)
                .map(|(a, b)| a.checked_add(*b).expect("symbolic degree overflow"))
                .collect(),
            definitely_zero: false,
        }
    }
}

impl DegBound {
    pub fn zero_with_vars(variable_count: usize) -> Self {
        Self::with_len(variable_count, true)
    }

    pub fn one_with_vars(variable_count: usize) -> Self {
        Self::with_len(variable_count, false)
    }

    pub fn constant(value: F128, variable_count: usize) -> Self {
        Self::with_len(variable_count, value == F128::ZERO)
    }
}

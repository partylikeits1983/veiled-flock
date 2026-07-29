use std::collections::BTreeMap;

use crate::field::F128;

use super::scalar::SymScalar;

/// Exact sparse multivariate polynomial for toy-scale validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMvPoly {
    variable_count: usize,
    terms: BTreeMap<Vec<u16>, F128>,
}

impl SparseMvPoly {
    pub fn zero_with_vars(variable_count: usize) -> Self {
        Self {
            variable_count,
            terms: BTreeMap::new(),
        }
    }

    pub fn constant(value: F128, variable_count: usize) -> Self {
        let mut out = Self::zero_with_vars(variable_count);
        if value != F128::ZERO {
            out.terms.insert(vec![0; variable_count], value);
        }
        out
    }

    pub fn variable(index: usize, variable_count: usize) -> Self {
        assert!(index < variable_count);
        let mut exponents = vec![0; variable_count];
        exponents[index] = 1;
        let mut terms = BTreeMap::new();
        terms.insert(exponents, F128::ONE);
        Self {
            variable_count,
            terms,
        }
    }

    pub fn variable_count(&self) -> usize {
        self.variable_count
    }

    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    pub fn degree_of(&self, variable: usize) -> u16 {
        assert!(variable < self.variable_count);
        self.terms
            .keys()
            .map(|exponents| exponents[variable])
            .max()
            .unwrap_or(0)
    }

    pub fn evaluate(&self, assignment: &[F128]) -> F128 {
        assert_eq!(assignment.len(), self.variable_count);
        self.terms
            .iter()
            .fold(F128::ZERO, |acc, (exponents, coefficient)| {
                let monomial = exponents.iter().zip(assignment).fold(
                    *coefficient,
                    |value, (exponent, point)| {
                        let mut power = F128::ONE;
                        for _ in 0..*exponent {
                            power *= *point;
                        }
                        value * power
                    },
                );
                acc + monomial
            })
    }

    fn expanded_to(&self, variable_count: usize) -> Self {
        assert!(self.variable_count == 0 || self.variable_count == variable_count);
        if self.variable_count == variable_count {
            return self.clone();
        }
        let terms = self
            .terms
            .values()
            .map(|coefficient| (vec![0; variable_count], *coefficient))
            .collect();
        Self {
            variable_count,
            terms,
        }
    }
}

impl SymScalar for SparseMvPoly {
    fn zero() -> Self {
        Self::zero_with_vars(0)
    }

    fn one() -> Self {
        Self::constant(F128::ONE, 0)
    }

    fn from_const(value: F128) -> Self {
        Self::constant(value, 0)
    }

    fn add(&self, other: &Self) -> Self {
        let variable_count = self.variable_count.max(other.variable_count);
        let mut out = self.expanded_to(variable_count);
        let other = other.expanded_to(variable_count);
        for (exponents, coefficient) in &other.terms {
            let entry = out.terms.entry(exponents.clone()).or_insert(F128::ZERO);
            *entry += *coefficient;
            if *entry == F128::ZERO {
                out.terms.remove(exponents);
            }
        }
        out
    }

    fn mul(&self, other: &Self) -> Self {
        let variable_count = self.variable_count.max(other.variable_count);
        let left = self.expanded_to(variable_count);
        let right = other.expanded_to(variable_count);
        let mut out = Self::zero_with_vars(variable_count);
        for (left_exp, left_coefficient) in &left.terms {
            for (right_exp, right_coefficient) in &right.terms {
                let exponents = left_exp
                    .iter()
                    .zip(right_exp)
                    .map(|(a, b)| a.checked_add(*b).expect("polynomial exponent overflow"))
                    .collect::<Vec<_>>();
                let entry = out.terms.entry(exponents.clone()).or_insert(F128::ZERO);
                *entry += *left_coefficient * *right_coefficient;
                if *entry == F128::ZERO {
                    out.terms.remove(&exponents);
                }
            }
        }
        out
    }
}

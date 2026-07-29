use crate::field::F128;

/// Operations used by the polynomial straight-line programs. Challenge-
/// dependent inversion is deliberately absent: any such inverse must be
/// represented as a named denominator atom instead.
pub trait SymScalar: Clone + PartialEq {
    fn zero() -> Self;
    fn one() -> Self;
    fn from_const(value: F128) -> Self;
    fn add(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;

    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }
}

impl SymScalar for F128 {
    fn zero() -> Self {
        Self::ZERO
    }

    fn one() -> Self {
        Self::ONE
    }

    fn from_const(value: F128) -> Self {
        value
    }

    fn add(&self, other: &Self) -> Self {
        *self + *other
    }

    fn mul(&self, other: &Self) -> Self {
        *self * *other
    }
}

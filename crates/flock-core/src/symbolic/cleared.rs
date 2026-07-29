#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DenAtom {
    Gamma,
    OnePlusROuter(u8),
    C,
    MinorDet,
}

/// A numerator together with named challenge-dependent denominator atoms.
/// The determinant and rational translator are never expanded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cleared<T> {
    pub num: T,
    pub den: Vec<DenAtom>,
}

impl<T> Cleared<T> {
    pub fn polynomial(num: T) -> Self {
        Self {
            num,
            den: Vec::new(),
        }
    }

    pub fn with_denominator(num: T, mut den: Vec<DenAtom>) -> Self {
        den.sort();
        Self { num, den }
    }
}

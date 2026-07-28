use std::collections::BTreeMap;

use super::scalar::SymScalar;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Channel {
    P,
    S,
    Sc,
    Sh,
    Mu(u8),
    G(u8),
    Witness,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CoordId {
    pub channel: Channel,
    pub index: u32,
}

impl CoordId {
    pub const fn new(channel: Channel, index: u32) -> Self {
        Self { channel, index }
    }
}

/// Affine form in secret/mask coordinates with challenge-polynomial
/// coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinForm<S> {
    pub constant: S,
    pub coeffs: BTreeMap<CoordId, S>,
}

impl<S: SymScalar> LinForm<S> {
    pub fn zero_like(zero: S) -> Self {
        Self {
            constant: zero,
            coeffs: BTreeMap::new(),
        }
    }

    pub fn constant(value: S) -> Self {
        Self {
            constant: value,
            coeffs: BTreeMap::new(),
        }
    }

    pub fn coordinate(id: CoordId, one: S, zero: S) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(id, one);
        Self {
            constant: zero,
            coeffs,
        }
    }

    pub fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        out.constant = out.constant.add(&other.constant);
        for (id, coefficient) in &other.coeffs {
            let value = out
                .coeffs
                .get(id)
                .map_or_else(|| coefficient.clone(), |left| left.add(coefficient));
            if value.is_zero() {
                out.coeffs.remove(id);
            } else {
                out.coeffs.insert(*id, value);
            }
        }
        out
    }

    pub fn scale(&self, scalar: &S) -> Self {
        let constant = self.constant.mul(scalar);
        let coeffs = self
            .coeffs
            .iter()
            .filter_map(|(id, coefficient)| {
                let value = coefficient.mul(scalar);
                (!value.is_zero()).then_some((*id, value))
            })
            .collect();
        Self { constant, coeffs }
    }

    /// Multiply affine forms when at most one contains secret coordinates.
    /// Mask-by-mask products are outside the L1 representation and rejected.
    pub fn mul_linear(&self, other: &Self) -> Self {
        assert!(
            self.is_constant() || other.is_constant(),
            "nonlinear product of two coordinate-bearing forms"
        );
        if self.is_constant() {
            other.scale(&self.constant)
        } else {
            self.scale(&other.constant)
        }
    }
}

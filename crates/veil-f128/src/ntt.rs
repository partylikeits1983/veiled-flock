//! Scalar additive NTT over an affine `GF(2)` subspace of `GF(2^128)`.
//!
//! FLOCK's optimized NTT fixes the affine offset to zero. VEIL's
//! multiplicative/ZK code needs two disjoint domains, so this module implements
//! the same Lin--Chung--Han butterfly with an explicit offset. It is a
//! correctness-first path; the optimized zero-offset implementation remains in
//! `flock-core` for the main PCS.

#[cfg(not(feature = "std"))]
use std::prelude::v1::*;

use flock_core::field::F128;
use rayon::prelude::*;

#[inline]
fn next_subspace_value(value: F128, root_value: F128) -> F128 {
    value * (value + root_value)
}

#[inline]
fn span_element(basis: &[F128], index: usize) -> F128 {
    let mut value = F128::ZERO;
    for (bit, basis_element) in basis.iter().enumerate() {
        if (index >> bit) & 1 == 1 {
            value += *basis_element;
        }
    }
    value
}

fn standard_basis_element(index: usize) -> F128 {
    assert!(index < 128, "GF(2^128) has only 128 binary basis elements");
    if index < 64 {
        F128::new(1u64 << index, 0)
    } else {
        F128::new(0, 1u64 << (index - 64))
    }
}

/// Twiddles for a size-`2^log_size` affine domain
/// `offset + span(1, x, ..., x^(log_size-1))`.
fn compute_twiddles(log_size: usize, offset: F128) -> Vec<F128> {
    if log_size == 0 {
        return Vec::new();
    }
    assert!(
        log_size < 128,
        "the affine domain must leave room for its offset"
    );

    let basis: Vec<F128> = (0..log_size).map(standard_basis_element).collect();
    let size = 1usize << log_size;
    let mut twiddles = vec![F128::ZERO; size - 1];

    // At the first layer, pair points that differ by basis[0]. The retained
    // representatives range over the span of basis[1..].
    let mut layer: Vec<F128> = (0..(size >> 1))
        .map(|index| offset + span_element(&basis[1..], index))
        .collect();
    let mut root_value = basis[0];
    let mut write_at = layer.len();

    let root_inverse = root_value.inv();
    for (slot, value) in twiddles[write_at - 1..write_at - 1 + layer.len()]
        .iter_mut()
        .zip(layer.iter())
    {
        *slot = root_inverse * *value;
    }

    for _ in 1..log_size {
        write_at >>= 1;
        let next_root = next_subspace_value(layer[1] + layer[0], root_value);
        for index in 0..write_at {
            layer[index] = next_subspace_value(layer[2 * index], root_value);
        }
        layer.truncate(write_at);
        root_value = next_root;

        let root_inverse = root_value.inv();
        for (slot, value) in twiddles[write_at - 1..write_at - 1 + layer.len()]
            .iter_mut()
            .zip(layer.iter())
        {
            *slot = root_inverse * *value;
        }
    }

    twiddles
}

#[inline]
fn forward_butterfly(values: &mut [F128], twiddle: F128) {
    let half = values.len() >> 1;
    let (low, high) = values.split_at_mut(half);
    if half >= 1 << 14 {
        low.par_iter_mut()
            .zip(high.par_iter_mut())
            .for_each(|(low, high)| {
                let old_high = *high;
                *low += twiddle * old_high;
                *high = old_high + *low;
            });
    } else {
        for (low, high) in low.iter_mut().zip(high) {
            let old_high = *high;
            *low += twiddle * old_high;
            *high = old_high + *low;
        }
    }
}

fn forward_recursive(values: &mut [F128], twiddles: &[F128], index: usize) {
    if values.len() == 1 {
        return;
    }
    forward_butterfly(values, twiddles[index - 1]);
    let half = values.len() >> 1;
    let (low, high) = values.split_at_mut(half);
    if half >= 1 << 14 {
        rayon::join(
            || forward_recursive(low, twiddles, 2 * index),
            || forward_recursive(high, twiddles, 2 * index + 1),
        );
    } else {
        forward_recursive(low, twiddles, 2 * index);
        forward_recursive(high, twiddles, 2 * index + 1);
    }
}

#[inline]
fn inverse_butterfly(values: &mut [F128], twiddle: F128) {
    let half = values.len() >> 1;
    let (low, high) = values.split_at_mut(half);
    if half >= 1 << 14 {
        low.par_iter_mut()
            .zip(high.par_iter_mut())
            .for_each(|(low, high)| {
                *high += *low;
                *low += twiddle * *high;
            });
    } else {
        for (low, high) in low.iter_mut().zip(high) {
            *high += *low;
            *low += twiddle * *high;
        }
    }
}

fn inverse_recursive(values: &mut [F128], twiddles: &[F128], index: usize) {
    if values.len() == 1 {
        return;
    }
    let half = values.len() >> 1;
    let (low, high) = values.split_at_mut(half);
    if half >= 1 << 14 {
        rayon::join(
            || inverse_recursive(low, twiddles, 2 * index),
            || inverse_recursive(high, twiddles, 2 * index + 1),
        );
    } else {
        inverse_recursive(low, twiddles, 2 * index);
        inverse_recursive(high, twiddles, 2 * index + 1);
    }
    inverse_butterfly(values, twiddles[index - 1]);
}

/// Additive NTT for one affine binary subspace.
#[derive(Clone, Debug)]
pub struct AdditiveCosetNtt {
    log_size: usize,
    offset: F128,
    twiddles: Vec<F128>,
}

impl AdditiveCosetNtt {
    pub fn new(log_size: usize, offset: F128) -> Self {
        assert!(log_size < usize::BITS as usize, "domain does not fit usize");
        Self {
            log_size,
            offset,
            twiddles: compute_twiddles(log_size, offset),
        }
    }

    pub fn log_size(&self) -> usize {
        self.log_size
    }

    pub fn size(&self) -> usize {
        1usize << self.log_size
    }

    pub fn offset(&self) -> F128 {
        self.offset
    }

    /// Transform novel-basis coefficients into evaluations on this domain.
    pub fn forward(&self, values: &mut [F128]) {
        assert_eq!(values.len(), self.size(), "wrong forward transform length");
        if values.len() > 1 {
            forward_recursive(values, &self.twiddles, 1);
        }
    }

    /// Interpolate domain evaluations back into novel-basis coefficients.
    pub fn inverse(&self, values: &mut [F128]) {
        assert_eq!(values.len(), self.size(), "wrong inverse transform length");
        if values.len() > 1 {
            inverse_recursive(values, &self.twiddles, 1);
        }
    }
}

/// The first standard-basis element outside the size-`2^log_domain` linear
/// subspace. Its coset is disjoint from that subspace.
pub(crate) fn disjoint_coset_offset(log_domain: usize) -> F128 {
    standard_basis_element(log_domain)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn samples(count: usize, seed: u64) -> Vec<F128> {
        let mut state = seed;
        (0..count)
            .map(|_| {
                state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let lo = state ^ state.rotate_left(17);
                state = state.wrapping_mul(0xbf58_476d_1ce4_e5b9);
                let hi = state ^ state.rotate_right(11);
                F128::new(lo, hi)
            })
            .collect()
    }

    #[test]
    fn forward_inverse_roundtrip_on_linear_and_affine_domains() {
        for log_size in 0..=8 {
            for offset in [F128::ZERO, disjoint_coset_offset(log_size)] {
                let transform = AdditiveCosetNtt::new(log_size, offset);
                let original = samples(transform.size(), 0xfeed_0000 + log_size as u64);
                let mut values = original.clone();
                transform.forward(&mut values);
                transform.inverse(&mut values);
                assert_eq!(values, original, "log_size={log_size}, offset={offset:?}");
            }
        }
    }

    #[test]
    fn transform_is_linear() {
        let transform = AdditiveCosetNtt::new(7, disjoint_coset_offset(7));
        let a = samples(transform.size(), 1);
        let b = samples(transform.size(), 2);
        let mut sum: Vec<_> = a.iter().zip(&b).map(|(a, b)| *a + *b).collect();
        let mut encoded_a = a.clone();
        let mut encoded_b = b.clone();
        transform.forward(&mut encoded_a);
        transform.forward(&mut encoded_b);
        transform.forward(&mut sum);
        assert_eq!(
            sum,
            encoded_a
                .iter()
                .zip(encoded_b)
                .map(|(a, b)| *a + b)
                .collect::<Vec<_>>()
        );
    }
}

use crate::field::{F128, PHI_8_TABLE};
use crate::zerocheck::{K_SKIP, SmallMaskSpec};

use super::{LinForm, SymScalar};

pub fn build_eq_sym<S: SymScalar>(r: &[S]) -> Vec<S> {
    let mut eq = vec![S::one()];
    for challenge in r {
        let old_len = eq.len();
        eq.resize(2 * old_len, S::zero());
        for index in (0..old_len).rev() {
            let value = eq[index].clone();
            eq[index + old_len] = value.mul(challenge);
            eq[index] = value.mul(&S::one().add(challenge));
        }
    }
    eq
}

pub fn round_pair_naive_sym<S: SymScalar>(
    a: &[LinForm<S>],
    b: &[LinForm<S>],
    r: &[S],
) -> (LinForm<S>, LinForm<S>) {
    assert_eq!(a.len(), b.len());
    assert!(a.len().is_power_of_two() && a.len() >= 2);
    assert_eq!(r.len(), a.len().trailing_zeros() as usize);
    let eq = build_eq_sym(&r[1..]);
    let zero = LinForm::zero_like(S::zero());
    let mut g_one = zero.clone();
    let mut g_inf = zero;
    for index in 0..a.len() / 2 {
        let a_delta = a[2 * index].add(&a[2 * index + 1]);
        let b_delta = b[2 * index].add(&b[2 * index + 1]);
        g_one = g_one.add(
            &a[2 * index + 1]
                .mul_linear(&b[2 * index + 1])
                .scale(&eq[index]),
        );
        g_inf = g_inf.add(&a_delta.mul_linear(&b_delta).scale(&eq[index]));
    }
    (g_one.scale(&r[0]), g_inf)
}

pub fn fold_in_place_pair_sym<S: SymScalar>(
    a: &mut Vec<LinForm<S>>,
    b: &mut Vec<LinForm<S>>,
    challenge: &S,
) {
    assert_eq!(a.len(), b.len());
    assert!(a.len().is_power_of_two() && a.len() >= 2);
    for index in 0..a.len() / 2 {
        let a_delta = a[2 * index].add(&a[2 * index + 1]);
        let b_delta = b[2 * index].add(&b[2 * index + 1]);
        a[index] = a[2 * index].add(&a_delta.scale(challenge));
        b[index] = b[2 * index].add(&b_delta.scale(challenge));
    }
    a.truncate(a.len() / 2);
    b.truncate(b.len() / 2);
}

fn lagrange_weights_on_nodes_sym<S: SymScalar>(nodes: &[F128], z: &S) -> Vec<S> {
    nodes
        .iter()
        .enumerate()
        .map(|(i, node_i)| {
            let mut numerator = S::one();
            let mut denominator = F128::ONE;
            for (j, node_j) in nodes.iter().enumerate() {
                if i == j {
                    continue;
                }
                numerator = numerator.mul(&z.add(&S::from_const(*node_j)));
                denominator *= *node_i + *node_j;
            }
            numerator.mul(&S::from_const(denominator.inv()))
        })
        .collect()
}

pub fn lagrange_weights_sym<S: SymScalar>(k_skip: usize, z: &S) -> Vec<S> {
    let len = 1usize << k_skip;
    assert!(len <= PHI_8_TABLE.len());
    lagrange_weights_on_nodes_sym(&PHI_8_TABLE[..len], z)
}

pub fn lagrange_weights_lambda_sym<S: SymScalar>(k_skip: usize, z: &S) -> Vec<S> {
    let len = 1usize << k_skip;
    assert!(2 * len <= PHI_8_TABLE.len());
    lagrange_weights_on_nodes_sym(&PHI_8_TABLE[len..2 * len], z)
}

pub fn interpolate_sym<S: SymScalar>(values: &[LinForm<S>], weights: &[S]) -> LinForm<S> {
    assert_eq!(values.len(), weights.len());
    values
        .iter()
        .zip(weights)
        .fold(LinForm::zero_like(S::zero()), |acc, (value, weight)| {
            acc.add(&value.scale(weight))
        })
}

pub fn vanishing_s_at_sym<S: SymScalar>(k_skip: usize, z: &S) -> S {
    PHI_8_TABLE[..1usize << k_skip]
        .iter()
        .fold(S::one(), |acc, node| acc.mul(&z.add(&S::from_const(*node))))
}

/// Symbolic straight-line program for the corrected field-mask functionals.
/// Its concrete specialization is checked against
/// `zerocheck::mask_functional_matrix_fv` in the artifact test.
pub fn mask_functional_matrix_fv_sym<S: SymScalar>(
    spec: SmallMaskSpec,
    m: usize,
    r_rest: &[S],
    rhos: &[S],
) -> Vec<Vec<S>> {
    let n = m - K_SKIP;
    assert_eq!(r_rest.len(), n);
    assert_eq!(rhos.len(), n);
    let d = spec.d(m);
    let mut rows = vec![vec![S::zero(); d]; 2 * n + 2];
    let mut q = spec
        .q_star_dense(m)
        .into_iter()
        .map(S::from_const)
        .collect::<Vec<_>>();
    let mut indices = (0..d)
        .map(|index| spec.support_index(index, m))
        .collect::<Vec<_>>();
    let mut scales = vec![S::one(); d];

    let eq_full = build_eq_sym(r_rest);
    for column in 0..d {
        let index = indices[column];
        rows[2 * n][column] = eq_full[index].mul(&q[index]);
    }

    for round in 0..n {
        let eq_remaining = build_eq_sym(&r_rest[round + 1..]);
        for column in 0..d {
            let index = indices[column];
            let pair = index >> 1;
            let q0 = &q[2 * pair];
            let q1 = &q[2 * pair + 1];
            if index & 1 == 1 {
                rows[2 * round][column] = eq_remaining[pair].mul(&scales[column]).mul(q1);
            }
            rows[2 * round + 1][column] = eq_remaining[pair].mul(&scales[column]).mul(&q0.add(q1));
        }

        let half = q.len() / 2;
        for index in 0..half {
            q[index] = q[2 * index]
                .mul(&S::one().add(&rhos[round]))
                .add(&q[2 * index + 1].mul(&rhos[round]));
        }
        q.truncate(half);
        for column in 0..d {
            let factor = if indices[column] & 1 == 0 {
                S::one().add(&rhos[round])
            } else {
                rhos[round].clone()
            };
            scales[column] = scales[column].mul(&factor);
            indices[column] >>= 1;
        }
    }

    let eq_terminal = build_eq_sym(rhos);
    for column in 0..d {
        rows[2 * n + 1][column] = eq_terminal[spec.support_index(column, m)].clone();
    }
    rows
}

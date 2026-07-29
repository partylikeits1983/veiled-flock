#![cfg(feature = "symbolic")]

use flock_core::field::F128;
use flock_core::symbolic::kernels::{
    build_eq_sym, fold_in_place_pair_sym, lagrange_weights_sym, round_pair_naive_sym,
    vanishing_s_at_sym,
};
use flock_core::symbolic::{DegBound, LinForm, SparseMvPoly, SymScalar};
use flock_core::zerocheck::multilinear::{
    fold_in_place_pair, lagrange_weights_naive, round_pair_naive, vanishing_s_at,
};
use flock_core::zerocheck::univariate_skip::build_eq;

fn next(state: &mut u64) -> F128 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    let lo = *state;
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    F128::new(lo, *state)
}

fn constants(values: &[F128]) -> Vec<LinForm<F128>> {
    values.iter().copied().map(LinForm::constant).collect()
}

#[test]
fn concrete_symbolic_kernels_match_native_references() {
    let mut state = 0x51a9_1c0d_4455_7788;
    for log_len in 1..=8 {
        for _ in 0..32 {
            let len = 1usize << log_len;
            let a = (0..len).map(|_| next(&mut state)).collect::<Vec<_>>();
            let b = (0..len).map(|_| next(&mut state)).collect::<Vec<_>>();
            let r = (0..log_len).map(|_| next(&mut state)).collect::<Vec<_>>();

            assert_eq!(build_eq_sym(&r), build_eq(&r));

            let expected = round_pair_naive(&a, &b, &r);
            let got = round_pair_naive_sym(&constants(&a), &constants(&b), &r);
            assert_eq!(got.0.constant, expected.0);
            assert_eq!(got.1.constant, expected.1);
            assert!(got.0.coeffs.is_empty() && got.1.coeffs.is_empty());

            let challenge = next(&mut state);
            let mut expected_a = a.clone();
            let mut expected_b = b.clone();
            fold_in_place_pair(&mut expected_a, &mut expected_b, challenge);
            let mut got_a = constants(&a);
            let mut got_b = constants(&b);
            fold_in_place_pair_sym(&mut got_a, &mut got_b, &challenge);
            assert_eq!(
                got_a.iter().map(|value| value.constant).collect::<Vec<_>>(),
                expected_a
            );
            assert_eq!(
                got_b.iter().map(|value| value.constant).collect::<Vec<_>>(),
                expected_b
            );
        }
    }
}

#[test]
fn toy_exact_polynomials_match_evaluation_and_degree_semantics() {
    let z_poly = SparseMvPoly::variable(0, 1);
    let exact_weights = lagrange_weights_sym(3, &z_poly);
    let exact_vanishing = vanishing_s_at_sym(3, &z_poly);
    assert!(exact_weights.iter().all(|weight| weight.degree_of(0) == 7));
    assert_eq!(exact_vanishing.degree_of(0), 8);

    let z_degree = DegBound::variable(0, 1);
    let degree_weights = lagrange_weights_sym(3, &z_degree);
    let degree_vanishing = vanishing_s_at_sym(3, &z_degree);
    assert!(degree_weights.iter().all(|weight| weight.degrees()[0] >= 7));
    assert!(degree_vanishing.degrees()[0] >= 8);

    let mut state = 0xd00d_f00d_1234_5678;
    for _ in 0..64 {
        let z = next(&mut state);
        let expected_weights = lagrange_weights_naive(3, z);
        for (exact, expected) in exact_weights.iter().zip(expected_weights) {
            assert_eq!(exact.evaluate(&[z]), expected);
        }
        assert_eq!(exact_vanishing.evaluate(&[z]), vanishing_s_at(3, z));
    }
}

#[test]
fn challenge_dependent_inversion_is_not_part_of_sym_scalar() {
    fn straight_line_only<S: SymScalar>(x: &S) -> S {
        x.mul(x).add(&S::one())
    }
    let x = SparseMvPoly::variable(0, 1);
    assert_eq!(straight_line_only(&x).degree_of(0), 2);
}

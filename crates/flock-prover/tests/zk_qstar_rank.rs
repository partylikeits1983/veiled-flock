use flock_core::field::F128;
use flock_core::linalg::F128Span;
use flock_core::zerocheck::{
    K_SKIP, SmallMaskSpec, mask_functional_matrix_fv,
    multilinear::{fold_in_place_pair, round_pair_naive},
    univariate_skip::build_eq,
};

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn sample_f128(state: &mut u64) -> F128 {
    F128::new(splitmix64(state), splitmix64(state))
}

fn nondegenerate_f128(state: &mut u64) -> F128 {
    loop {
        let value = sample_f128(state);
        if value != F128::ZERO && value != F128::ONE {
            return value;
        }
    }
}

fn matrix_column_rank(rows: &[Vec<F128>]) -> usize {
    let target = rows.len();
    let mut span = F128Span::default();
    for column in 0..rows[0].len() {
        span.insert(rows.iter().map(|row| row[column]).collect());
        if span.rank() == target {
            break;
        }
    }
    span.rank()
}

fn matrix_times_vector(rows: &[Vec<F128>], vector: &[F128]) -> Vec<F128> {
    rows.iter()
        .map(|row| {
            row.iter()
                .zip(vector)
                .fold(F128::ZERO, |acc, (a, b)| acc + *a * *b)
        })
        .collect()
}

#[test]
fn qstar_functional_matrix_matches_dense_schedule() {
    let spec = SmallMaskSpec::default();
    let m = 13;
    let n = m - K_SKIP;
    let mut state = 0x7c39_87a4_d213_ee91;
    let r_rest = (0..n)
        .map(|_| nondegenerate_f128(&mut state))
        .collect::<Vec<_>>();
    let rhos = (0..n)
        .map(|_| nondegenerate_f128(&mut state))
        .collect::<Vec<_>>();
    let p_small = (0..spec.d(m))
        .map(|_| sample_f128(&mut state))
        .collect::<Vec<_>>();
    let rows = mask_functional_matrix_fv(spec, m, &r_rest, &rhos);
    let from_matrix = matrix_times_vector(&rows, &p_small);

    let mut p = spec.expand(&p_small, m);
    let mut q = spec.q_star_dense(m);
    let eq = build_eq(&r_rest);
    let mask_init = eq
        .iter()
        .zip(&p)
        .zip(&q)
        .fold(F128::ZERO, |acc, ((e, p), q)| acc + *e * *p * *q);
    let mut from_dense = Vec::with_capacity(2 * n + 2);
    for round in 0..n {
        let mut round_arg = vec![F128::ONE; n - round];
        round_arg[1..].copy_from_slice(&r_rest[round + 1..]);
        let pair = round_pair_naive(&p, &q, &round_arg);
        from_dense.extend([pair.0, pair.1]);
        fold_in_place_pair(&mut p, &mut q, rhos[round]);
    }
    from_dense.push(mask_init);
    from_dense.push(p[0]);

    assert_eq!(from_matrix, from_dense);
    assert_eq!(q[0], spec.q_star_at(&rhos));
}

#[test]
fn affine_linear_qstar_has_full_conditioned_rank_across_certified_shapes() {
    let spec = SmallMaskSpec { d_log: 12 };
    for m in [13usize, 15, 22] {
        let n = m - K_SKIP;
        assert!(
            spec.q_star_dense(m)
                .into_iter()
                .all(|value| value != F128::ZERO),
            "Q-star has a zero cube value at m={m}"
        );
        for seed in 0..200u64 {
            let mut state = seed ^ ((m as u64) << 48) ^ 0xa189_744d_3c6e_2f50;
            let r_rest = (0..n)
                .map(|_| nondegenerate_f128(&mut state))
                .collect::<Vec<_>>();
            let rhos = (0..n)
                .map(|_| nondegenerate_f128(&mut state))
                .collect::<Vec<_>>();
            let rows = mask_functional_matrix_fv(spec, m, &r_rest, &rhos);
            let pair_rank = matrix_column_rank(&rows[..2 * n]);
            let leakage_rank = matrix_column_rank(&rows[2 * n..]);
            let joint_rank = matrix_column_rank(&rows);
            assert_eq!(
                pair_rank,
                2 * n,
                "round-message rank defect at m={m}, seed={seed}"
            );
            assert_eq!(leakage_rank, 2, "leakage rank defect at m={m}, seed={seed}");
            assert_eq!(
                joint_rank - leakage_rank,
                2 * n - 2,
                "conditioned-image rank defect at m={m}, seed={seed}"
            );
        }
    }
}

#![cfg(feature = "symbolic")]

use flock_core::field::F128;
use flock_core::linalg::{F128Mat, conditioned_image};
use flock_core::symbolic::DegBound;
use flock_core::symbolic::kernels::mask_functional_matrix_fv_sym;
use flock_core::zerocheck::{SmallMaskSpec, mask_functional_matrix_fv};

fn challenge(m: usize, seed: u64, domain: u8, index: usize) -> F128 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"flock-zerocheck-mask-coverage");
    hasher.update(&(m as u64).to_le_bytes());
    hasher.update(&seed.to_le_bytes());
    hasher.update(&[domain]);
    hasher.update(&(index as u64).to_le_bytes());
    let digest = hasher.finalize();
    F128::new(
        u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap()),
        u64::from_le_bytes(digest.as_bytes()[8..16].try_into().unwrap()),
    )
}

fn assert_mask_coverage(m: usize, seed: u64, expected_total_degree: u64) {
    let spec = SmallMaskSpec::default();
    let n = m - flock_core::zerocheck::K_SKIP;
    let r_rest = (0..n)
        .map(|index| challenge(m, seed, 0, index))
        .collect::<Vec<_>>();
    let rhos = (0..n)
        .map(|index| challenge(m, seed, 1, index))
        .collect::<Vec<_>>();
    let rows = mask_functional_matrix_fv(spec, m, &r_rest, &rhos);
    let full = F128Mat::from_rows(&rows);
    let round_rows = F128Mat::from_rows(&rows[..2 * n]);
    let leakage = F128Mat::from_rows(&rows[2 * n..]);
    let conditioned = conditioned_image(&round_rows, &leakage);

    assert_eq!(leakage.rank(), 2, "leakage functionals must be independent");
    assert_eq!(full.rank(), 2 * n, "stacked mask map must saturate V_c");
    assert_eq!(
        conditioned.rank(),
        2 * n - 2,
        "round messages conditioned on leakage must retain full allowed image"
    );

    let minor = full.minor_select(2 * n);
    let variable_count = 2 * n;
    let r_rest_degree = (0..n)
        .map(|index| DegBound::variable(index, variable_count))
        .collect::<Vec<_>>();
    let rho_degree = (0..n)
        .map(|index| DegBound::variable(n + index, variable_count))
        .collect::<Vec<_>>();
    let degree_rows = mask_functional_matrix_fv_sym(spec, m, &r_rest_degree, &rho_degree);
    let mut determinant_degrees = vec![0u64; variable_count];
    for &row in &minor.row_ids {
        for variable in 0..variable_count {
            let row_degree = minor
                .col_ids
                .iter()
                .map(|&column| u64::from(degree_rows[row][column].degree_of(variable)))
                .max()
                .unwrap_or(0);
            determinant_degrees[variable] += row_degree;
        }
    }
    let total_degree: u64 = determinant_degrees.iter().sum();
    assert_ne!(
        minor.det,
        F128::ZERO,
        "selected determinant must be nonzero"
    );
    assert_eq!(
        total_degree, expected_total_degree,
        "mask determinant degree changed for m={m}"
    );
    assert!(
        total_degree < 1 << 28,
        "Schwartz-Zippel loss must remain below 2^-100"
    );
}

#[test]
fn symbolic_mask_matrix_matches_native_and_has_100_bit_margin() {
    let spec = SmallMaskSpec::default();
    for m in [13, 15, 22] {
        let n = m - flock_core::zerocheck::K_SKIP;
        let r_rest = (0..n)
            .map(|index| challenge(m, 7, 0, index))
            .collect::<Vec<_>>();
        let rhos = (0..n)
            .map(|index| challenge(m, 7, 1, index))
            .collect::<Vec<_>>();
        assert_eq!(
            mask_functional_matrix_fv_sym(spec, m, &r_rest, &rhos),
            mask_functional_matrix_fv(spec, m, &r_rest, &rhos)
        );
    }
    for (m, expected_total_degree) in [(13, 126), (15, 216), (22, 720)] {
        assert_mask_coverage(m, 0x5a32_0017_900d_cafe, expected_total_degree);
    }
}

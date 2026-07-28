#![cfg(feature = "symbolic")]

use flock_core::field::F128;
use flock_core::linalg::{F128Mat, conditioned_image};
use flock_core::symbolic::DegBound;
use flock_core::symbolic::kernels::mask_functional_matrix_fv_sym;
use flock_core::zerocheck::{SmallMaskSpec, mask_functional_matrix_fv};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FieldElement {
    lo: u64,
    hi: u64,
}

impl From<F128> for FieldElement {
    fn from(value: F128) -> Self {
        Self {
            lo: value.lo,
            hi: value.hi,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CoverageProfile {
    m: usize,
    n_rounds: usize,
    d_log: usize,
    seed: u64,
    matrix_rank: usize,
    leakage_rank: usize,
    conditioned_rank: usize,
    minor_rows: Vec<usize>,
    minor_columns: Vec<usize>,
    determinant: FieldElement,
    determinant_degree_by_variable: Vec<u64>,
    determinant_total_degree_bound: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CoverageArtifact {
    protocol: String,
    theorem: String,
    profiles: Vec<CoverageProfile>,
}

fn challenge(m: usize, seed: u64, domain: u8, index: usize) -> F128 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"flock-s2-mask-coverage-v0");
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

fn profile(m: usize, seed: u64) -> CoverageProfile {
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
    let total_degree = determinant_degrees.iter().sum();
    assert!(
        total_degree < 1 << 28,
        "Schwartz-Zippel loss must remain below 2^-100"
    );

    CoverageProfile {
        m,
        n_rounds: n,
        d_log: spec.d_log_for(m),
        seed,
        matrix_rank: full.rank(),
        leakage_rank: leakage.rank(),
        conditioned_rank: conditioned.rank(),
        minor_rows: minor.row_ids,
        minor_columns: minor.col_ids,
        determinant: minor.det.into(),
        determinant_degree_by_variable: determinant_degrees,
        determinant_total_degree_bound: total_degree,
    }
}

fn generate_artifact() -> CoverageArtifact {
    CoverageArtifact {
        protocol: "flock-zk-fv-v3".to_owned(),
        theorem: "rank([R;L])=2n and rank(L)=2 imply dim R(ker L)=2n-2 off the emitted determinant zero set".to_owned(),
        profiles: [13, 15, 22]
            .into_iter()
            .map(|m| profile(m, 0x5a32_0017_900d_cafe))
            .collect(),
    }
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
    let generated = generate_artifact();
    assert!(
        generated
            .profiles
            .iter()
            .all(|profile| profile.determinant != FieldElement { lo: 0, hi: 0 })
    );
    let pinned: CoverageArtifact = serde_json::from_str(include_str!(
        "../../../docs/artifacts/s2_mask_coverage.json"
    ))
    .unwrap();
    assert_eq!(generated, pinned, "coverage artifact is stale");
}

#[test]
#[ignore = "prints the checked artifact for an intentional repository re-pin"]
fn emit_symbolic_mask_coverage_artifact() {
    println!(
        "{}",
        serde_json::to_string_pretty(&generate_artifact()).unwrap()
    );
}

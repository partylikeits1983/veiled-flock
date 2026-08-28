//! Regression certificate for the field-valued zerocheck mask channel.
//!
//! At a fixed challenge schedule, write `R` for the `2n` round-message
//! functionals and `L` for the disclosed `(mask_init, P(rho))` functionals.
//! Sumcheck consistency forces `L` into the row span of `R`, so the old
//! `rank([R;L]) = 2n+2` criterion is impossible. The relevant conditioned
//! image is `R(ker L)`, whose dimension is
//! `rank([R;L]) - rank(L)`. The shipped affine-linear Q-star and diagonal
//! support must have `rank(R) = 2n`, `rank(L) = 2`, and conditioned dimension
//! `2n-2`.
//!
//! This is a structural CI/certification check, not a per-proof resampling
//! event: P is uniform over F128 coordinates and Q-star is fixed and public.

use flock_core::field::F128;
use flock_core::linalg::F128Span;
use flock_core::zerocheck::{self, SmallMaskSpec};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RankCheckReport {
    /// Target conditioned dimension, retained in bits for compatibility with
    /// the existing certificate output.
    pub target_bits: usize,
    pub rank: usize,
    /// Number of field-valued mask coordinates inspected.
    pub probes: usize,
    /// Structural checks never resample a mask draw.
    pub resamples: usize,
}

impl RankCheckReport {
    pub fn covered(&self) -> bool {
        self.rank == self.target_bits
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaskCoverageFailed {
    pub report: RankCheckReport,
}

impl std::fmt::Display for MaskCoverageFailed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "field mask conditioned image has {} of {} required bits",
            self.report.rank, self.report.target_bits
        )
    }
}

impl std::error::Error for MaskCoverageFailed {}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn sample_nondegenerate(state: &mut u64) -> F128 {
    loop {
        let value = F128::new(splitmix64(state), splitmix64(state));
        if value != F128::ZERO && value != F128::ONE {
            return value;
        }
    }
}

fn row_rank(rows: &[Vec<F128>]) -> usize {
    let mut span = F128Span::default();
    for column in 0..rows[0].len() {
        span.insert(rows.iter().map(|row| row[column]).collect());
        if span.rank() == rows.len() {
            break;
        }
    }
    span.rank()
}

pub fn check_mask_coverage_fv(
    spec: SmallMaskSpec,
    m: usize,
    seed: u64,
) -> Result<RankCheckReport, MaskCoverageFailed> {
    let n = m - zerocheck::K_SKIP;
    let mut state = seed ^ ((m as u64) << 48) ^ 0xa189_744d_3c6e_2f50;
    let r_rest = (0..n)
        .map(|_| sample_nondegenerate(&mut state))
        .collect::<Vec<_>>();
    let rhos = (0..n)
        .map(|_| sample_nondegenerate(&mut state))
        .collect::<Vec<_>>();
    let rows = zerocheck::mask_functional_matrix_fv(spec, m, &r_rest, &rhos);
    let pair_rank = row_rank(&rows[..2 * n]);
    let leakage_rank = row_rank(&rows[2 * n..]);
    let joint_rank = row_rank(&rows);
    let conditioned_rank = joint_rank.saturating_sub(leakage_rank);
    let target_field = 2 * n - 2;
    let structural_ok = pair_rank == 2 * n && leakage_rank == 2;
    let report = RankCheckReport {
        target_bits: target_field * 128,
        rank: if structural_ok {
            conditioned_rank * 128
        } else {
            0
        },
        probes: spec.d(m),
        resamples: 0,
    };
    if report.covered() {
        Ok(report)
    } else {
        Err(MaskCoverageFailed { report })
    }
}

/// Compatibility wrapper for old certificate call sites. The Q bytes and
/// challenger are intentionally ignored because Q is now fixed and public.
pub fn check_mask_coverage<Ch>(
    _legacy_q_packed: &[u8],
    m: usize,
    seed: u64,
    _challenger: &Ch,
) -> Result<RankCheckReport, MaskCoverageFailed> {
    check_mask_coverage_fv(SmallMaskSpec::default(), m, seed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certified_shapes_have_full_conditioned_image() {
        for m in [13usize, 15, 22] {
            for seed in 0..16 {
                let report = check_mask_coverage_fv(SmallMaskSpec::default(), m, seed)
                    .expect("default field mask must cover");
                assert!(report.covered());
                assert_eq!(report.resamples, 0);
            }
        }
    }

    #[test]
    fn undersized_latent_support_fails() {
        let spec = SmallMaskSpec { d_log: 1 };
        let failed = check_mask_coverage_fv(spec, 22, 0)
            .expect_err("one latent bit cannot cover 32 round coordinates");
        assert!(!failed.report.covered());
    }
}

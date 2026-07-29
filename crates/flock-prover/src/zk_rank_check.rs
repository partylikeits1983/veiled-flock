//! Per-proof mask-coverage self-check — the replacement for the withdrawn
//! Schwartz–Zippel bound on `ε_rank`.
//!
//! **Why the old bound is gone.** `docs/zk-proof.md` §8 used to bound the
//! bad-mask probability by Schwartz–Zippel over "uniform mask entries in
//! F₂¹²⁸". The implemented `P,Q` are *Boolean* — one bit per cube entry — so
//! the entries range over `{0,1}`, where Schwartz–Zippel at the relevant
//! degrees is vacuous. (The argument had two further defects: it used a
//! single matrix entry's degree where a `~2304×2304` determinant's was
//! needed, and it took the probability over a different variable set from
//! the one the degree was counted in.)
//!
//! **What replaces it.** Whether the degree-2 channel covers the round-pair
//! block at *this* proof's `(Q, challenges)` is an F₂ rank condition on data
//! the prover already holds. So the prover checks it for its own draw and
//! **aborts and resamples** on failure, rather than emitting a proof whose
//! hiding rests on an unproven probability bound. The failure event depends
//! only on the mask draw and the challenges — both witness-independent — so
//! resampling leaks nothing about the witness.
//!
//! Consequently `ε_rank = 0` for every emitted proof. What remains
//! unquantified is the *resample probability*, which affects liveness, not
//! privacy, and is reported by [`RankCheckReport`].
//!
//! **How the rank is measured.** By probing the real fold kernels, not a
//! re-implementation: the map `P ↦ (round-pair coordinates of the P·Q
//! sumcheck)` is F₂-linear at fixed `Q` and fixed challenges, so random
//! probe directions through [`zerocheck::mask_round_pairs`] span its image
//! with certainty of *under*-estimating, never over-estimating, the rank.
//! Reaching full output rank is therefore a proof of surjectivity, not
//! evidence for it.

use flock_core::challenger::Challenger;
use flock_core::field::F128;
use flock_core::zerocheck;

/// Outcome of one coverage self-check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RankCheckReport {
    /// Bit dimension of the round-pair block that must be covered.
    pub target_bits: usize,
    /// Rank actually spanned by the probes.
    pub rank: usize,
    /// Number of probe directions used.
    pub probes: usize,
    /// How many times the mask had to be resampled before this draw passed.
    pub resamples: usize,
}

impl RankCheckReport {
    pub fn covered(&self) -> bool {
        self.rank == self.target_bits
    }
}

/// The mask draw did not cover the round-pair block; the prover must
/// resample `P,Q` (a witness-independent event) and retry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaskCoverageFailed {
    pub report: RankCheckReport,
}

impl std::fmt::Display for MaskCoverageFailed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "mask draw does not cover the round-pair block ({} of {} bits from \
             {} probes) — resample P,Q",
            self.report.rank, self.report.target_bits, self.report.probes
        )
    }
}

impl std::error::Error for MaskCoverageFailed {}

/// Simple F₂ row-reduction accumulator.
struct F2Span {
    rows: Vec<Vec<u64>>,
    pivots: Vec<usize>,
}

impl F2Span {
    fn new() -> Self {
        Self {
            rows: Vec::new(),
            pivots: Vec::new(),
        }
    }
    fn insert(&mut self, mut v: Vec<u64>) {
        for (row, &p) in self.rows.iter().zip(&self.pivots) {
            let (w, m) = (p / 64, 1u64 << (p % 64));
            if v[w] & m != 0 {
                for (a, b) in v.iter_mut().zip(row) {
                    *a ^= *b;
                }
            }
        }
        if let Some(p) = v
            .iter()
            .enumerate()
            .find_map(|(i, w)| (*w != 0).then(|| i * 64 + w.trailing_zeros() as usize))
        {
            self.rows.push(v);
            self.pivots.push(p);
        }
    }
    fn rank(&self) -> usize {
        self.rows.len()
    }
}

fn flatten(v: &[(F128, F128)]) -> Vec<u64> {
    let mut out = Vec::with_capacity(v.len() * 4);
    for (a, b) in v {
        out.push(a.lo);
        out.push(a.hi);
        out.push(b.lo);
        out.push(b.hi);
    }
    out
}

/// Check that the degree-2 mask channel covers the round-pair block for this
/// `(Q, challenge)` draw.
///
/// `q_packed` is the bit-packed `Q` cube, `m` the number of variables, and
/// `challenger` a *clone* of the prover's challenger positioned exactly where
/// `prove_packed_padded_zk` samples its schedule — the check must see the
/// same challenges the proof will use, and must not perturb the real
/// transcript.
///
/// Returns the report on success; `Err` (with the same report) when the draw
/// fails to cover, which the caller must handle by resampling.
pub fn check_mask_coverage<Ch: Challenger + Clone>(
    q_packed: &[u8],
    m: usize,
    probe_seed: u64,
    challenger: &Ch,
) -> Result<RankCheckReport, MaskCoverageFailed> {
    let n_rounds = m - zerocheck::K_SKIP;
    let target_bits = n_rounds * 2 * 128;
    // Probe with margin over the target dimension: random F₂ directions span
    // an r-dimensional image with overwhelming probability once the count
    // exceeds r by a modest margin, and under-spanning can only cause a
    // false ABORT (costing a resample), never a false pass.
    let probes = target_bits + 64;

    let n = 1usize << m;
    let bytes = n / 8;
    let mut span = F2Span::new();
    let mut state = probe_seed;
    let mut buf = vec![0u8; bytes];
    for _ in 0..probes {
        // A pseudorandom probe direction for P.
        for byte in buf.iter_mut() {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *byte = (state >> 33) as u8;
        }
        let mut ch = challenger.clone();
        let pairs = zerocheck::mask_round_pairs(&buf, q_packed, m, &mut ch);
        span.insert(flatten(&pairs));
        if span.rank() == target_bits {
            break;
        }
    }
    let report = RankCheckReport {
        target_bits,
        rank: span.rank(),
        probes,
        resamples: 0,
    };
    if report.covered() {
        Ok(report)
    } else {
        Err(MaskCoverageFailed { report })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use flock_core::challenger::FsChallenger;

    fn pack(bits: &[bool]) -> Vec<u8> {
        let mut out = vec![0u8; bits.len() / 8];
        for (i, b) in bits.iter().enumerate() {
            if *b {
                out[i / 8] |= 1 << (i % 8);
            }
        }
        out
    }

    struct Rng(u64);
    impl Rng {
        fn bits(&mut self, n: usize) -> Vec<bool> {
            (0..n)
                .map(|_| {
                    self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
                    let mut z = self.0;
                    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
                    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
                    (z ^ (z >> 31)) & 1 == 1
                })
                .collect()
        }
    }

    /// An honest uniform `Q` covers the block; a constant `Q` does not (it
    /// reaches the `G(1)` half but not the degree-2 `G(∞)` half). The second
    /// half is what makes the check non-vacuous: a check that passed for
    /// every draw would establish nothing.
    #[test]
    fn coverage_check_passes_uniform_q_and_fails_constant_q() {
        let m = 13;
        let n = 1usize << m;
        let mut rng = Rng(0x9A55);
        let q = pack(&rng.bits(n));
        let ch = FsChallenger::new(b"flock-rank-check-test");
        let ok = check_mask_coverage(&q, m, 0xC0FFEE, &ch).expect("uniform Q must cover");
        assert!(ok.covered());
        assert_eq!(ok.rank, ok.target_bits);

        let q_const = pack(&vec![true; n]);
        let bad = check_mask_coverage(&q_const, m, 0xC0FFEE, &ch)
            .expect_err("a constant Q must NOT cover the degree-2 half");
        assert!(bad.report.rank < bad.report.target_bits);
        // It should reach about half the block (the G(1) coordinates).
        assert!(bad.report.rank * 2 >= bad.report.target_bits - 256);
    }

    /// The check must be a pure observer: running it does not disturb the
    /// challenger the real proof will use.
    #[test]
    fn coverage_check_does_not_perturb_the_transcript() {
        let m = 13;
        let n = 1usize << m;
        let mut rng = Rng(0x1234);
        let q = pack(&rng.bits(n));
        let mut ch = FsChallenger::new(b"flock-rank-check-observer");
        let before = ch.sample_f128();
        let mut ch2 = FsChallenger::new(b"flock-rank-check-observer");
        let _ = check_mask_coverage(&q, m, 7, &ch2);
        let after = ch2.sample_f128();
        assert_eq!(before, after, "the self-check must not consume challenges");
    }
}

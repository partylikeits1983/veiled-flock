//! Zerocheck PIOP: prove a(y) · b(y) ⊕ c(y) = 0 for all y ∈ {0,1}^m.
//!
//! Inputs are three bit vectors of length 2^m. Output is an evaluation claim
//! on the multilinear extensions â, b̂, ĉ at the protocol-derived point.
//!
//! Protocol shape (m = log_n, k_skip = [`K_SKIP`] = 6):
//!   1. Verifier samples `r ∈ F_{2^128}^m` (the zerocheck challenge).
//!   2. Prover sends `P^{AB}(λ)` and `P^C(λ)` for λ ∈ Λ, |Λ| = 2^k_skip.
//!   3. Verifier samples `z ∈ F_{2^128}` (univariate-skip fold point).
//!   4. For each of the `m - k_skip` multilinear rounds, prover sends
//!      `(P_r(1), P_r(∞))` and verifier samples `ρ_r`.
//!   5. Prover sends final MLE evaluations `(â, b̂, ĉ)` at the resulting point.
//!
//! Both `prove` and `verify` are wired end-to-end. The prove→verify roundtrip
//! is tested on honest witnesses; verify also rejects byte-mutated proofs and
//! shape-corrupted ones.

use crate::challenger::{Challenger, sample_f128_vec_matching};
use crate::field::{F8, F128};
use crate::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
use crate::oracle_budget::{OracleLimitError, REJECTION_SAMPLING_TRIALS};
use serde::{Deserialize, Serialize};

pub mod multilinear;
pub mod univariate_skip;
pub mod univariate_skip_deg4;
pub mod univariate_skip_deg4_optimized;
pub mod univariate_skip_optimized;

use multilinear::{
    UniSkipFoldTable, fold_and_compute_round_pair_into, fold_in_place_pair,
    interpolate_at_z_combined, interpolate_at_z_on_lambda, round_pair_naive,
    uni_skip_fold_and_round_pair_optimized_packed_padded, vanishing_s_at, vanishing_s_on_lambda,
};
use univariate_skip_optimized::{
    c_s_f128, medium_challenges_ghash, round1_shift_reduce_extract_c_packed_padded,
    small_challenges_ghash,
};

/// Number of variables folded in round 1 via the additive-NTT univariate skip.
/// |Λ| = 2^K_SKIP = 64 elements; the round-1 prover message is two length-64
/// vectors of F128.
pub const K_SKIP: usize = 6;

/// Number of protocol-fixed equality coordinates used by the optimized
/// zerocheck after the univariate skip.
pub const N_INNER: usize = 7;

/// Derive the equality point shared by every zerocheck prover, verifier, and
/// simulator. The multilinear recurrence reconstructs `G(0)` by dividing by
/// `1 + r_i`, so sampled rest coordinates must exclude `1`.
pub fn sample_eq_point<C: Challenger>(m: usize, challenger: &mut C) -> Vec<F128> {
    sample_eq_point_bounded(m, challenger, REJECTION_SAMPLING_TRIALS)
        .expect("zerocheck equality-point sampler exhausted")
}

/// Fallible bounded equality-point sampler used by production proof paths.
pub fn sample_eq_point_bounded<C: Challenger>(
    m: usize,
    challenger: &mut C,
    max_trials: usize,
) -> Result<Vec<F128>, OracleLimitError> {
    assert!(
        m >= K_SKIP + N_INNER,
        "zerocheck equality point is too short"
    );

    let r_skip = challenger.try_sample_f128_vec(K_SKIP)?;
    let outer_len = m - K_SKIP - N_INNER;
    let r_outer = sample_f128_vec_matching(challenger, outer_len, max_trials, |point| {
        point.iter().all(|value| *value != F128::ONE)
    })?;

    let small = small_challenges_ghash();
    let medium = medium_challenges_ghash();
    debug_assert!(small.iter().chain(&medium).all(|value| *value != F128::ONE));

    let mut r = vec![F128::ZERO; m];
    r[..K_SKIP].copy_from_slice(&r_skip);
    r[K_SKIP..K_SKIP + 3].copy_from_slice(&small);
    r[K_SKIP + 3..K_SKIP + N_INNER].copy_from_slice(&medium);
    r[K_SKIP + N_INNER..].copy_from_slice(&r_outer);
    Ok(r)
}

/// Linear weights taking `(running, G(1), G(∞))` to `G(rho)` for one
/// compressed quadratic sumcheck round. Returning `None` keeps every verifier
/// fail-closed if a custom challenge source supplies the excluded `r_eq = 1`.
pub fn sumcheck_round_weights(r_eq: F128, rho: F128) -> Option<[F128; 3]> {
    let denominator = F128::ONE + r_eq;
    if denominator.is_zero() {
        return None;
    }
    let one_plus_rho = F128::ONE + rho;
    let running_weight = one_plus_rho * denominator.inv();
    let one_weight = r_eq * running_weight + rho;
    let infinity_weight = rho * one_plus_rho;
    Some([running_weight, one_weight, infinity_weight])
}

fn fold_sumcheck_round(
    running: F128,
    msg_1: F128,
    msg_inf: F128,
    r_eq: F128,
    rho: F128,
) -> Option<F128> {
    let [running_weight, one_weight, infinity_weight] = sumcheck_round_weights(r_eq, rho)?;
    Some(running * running_weight + msg_1 * one_weight + msg_inf * infinity_weight)
}

/// Protocol description of the small-domain field-valued mask channel.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmallMaskSpec {
    pub d_log: usize,
}

impl Default for SmallMaskSpec {
    fn default() -> Self {
        Self { d_log: 12 }
    }
}

impl SmallMaskSpec {
    fn hash_coefficient(label: &[u8], index: u64) -> F128 {
        let mut counter = 0u64;
        loop {
            let mut h = blake3::Hasher::new();
            h.update(label);
            h.update(&index.to_le_bytes());
            h.update(&counter.to_le_bytes());
            let digest = h.finalize();
            let bytes = digest.as_bytes();
            let coefficient = F128 {
                lo: u64::from_le_bytes(bytes[..8].try_into().unwrap()),
                hi: u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            };
            if coefficient != F128::ZERO {
                return coefficient;
            }
            counter = counter.wrapping_add(1);
        }
    }

    pub fn d_log_for(self, m: usize) -> usize {
        self.d_log.min((m - K_SKIP).saturating_sub(1))
    }

    pub fn d(self, m: usize) -> usize {
        1usize << self.d_log_for(m)
    }

    /// Embed a small-domain index into the full round cube. Each latent bit
    /// is repeated cyclically, so every round variable varies on the support
    /// even when the full cube has more variables than the small domain.
    pub fn support_index(self, small_index: usize, m: usize) -> usize {
        let n = m - K_SKIP;
        let d_log = self.d_log_for(m);
        assert!(small_index < 1usize << d_log);
        let mut full_index = 0usize;
        for round in 0..n {
            if small_index >> (round % d_log) & 1 == 1 {
                full_index |= 1usize << round;
            }
        }
        full_index
    }

    /// Coefficient vector for the packed-message claim `P(rho)`. The first
    /// `d(m)` message coordinates hold `p_small`; remaining coordinates are
    /// zero padding.
    pub fn terminal_basis(self, rho: &[F128], packed_len: usize) -> Vec<F128> {
        let m = rho.len() + K_SKIP;
        assert!(self.d(m) <= packed_len);
        let eq = univariate_skip::build_eq(rho);
        let mut basis = vec![F128::ZERO; packed_len];
        for (small_index, value) in basis.iter_mut().enumerate().take(self.d(m)) {
            *value = eq[self.support_index(small_index, m)];
        }
        basis
    }

    /// Nothing-up-my-sleeve coefficients for `Q★ = c + Σ α_j X_j`.
    pub fn alphas(self, m: usize) -> Vec<F128> {
        let n = m - K_SKIP;
        (0..n)
            .map(|j| Self::hash_coefficient(b"flock-qstar-affine-lin", j as u64 + 1))
            .collect()
    }

    pub fn q_star_constant(self) -> F128 {
        Self::hash_coefficient(b"flock-qstar-affine-lin", 0)
    }

    pub fn q_star_at(self, rho: &[F128]) -> F128 {
        let m = rho.len() + K_SKIP;
        self.alphas(m)
            .into_iter()
            .zip(rho)
            .fold(self.q_star_constant(), |acc, (alpha, value)| {
                acc + alpha * *value
            })
    }

    pub fn q_star_dense(self, m: usize) -> Vec<F128> {
        let n = m - K_SKIP;
        let alphas = self.alphas(m);
        let mut values = vec![F128::ZERO; 1usize << n];
        values[0] = self.q_star_constant();
        for index in 1..values.len() {
            let bit = index.trailing_zeros() as usize;
            let previous = index ^ (1usize << bit);
            values[index] = values[previous] + alphas[bit];
        }
        values
    }

    /// Expand the small mask on its diagonal support. Variable zero is the
    /// low bit, matching the fold kernels.
    pub fn expand(self, p_small: &[F128], m: usize) -> Vec<F128> {
        assert_eq!(p_small.len(), self.d(m));
        let n = m - K_SKIP;
        let mut dense = vec![F128::ZERO; 1usize << n];
        for (index, value) in p_small.iter().enumerate() {
            dense[self.support_index(index, m)] = *value;
        }
        dense
    }
}

/// Exact F128-linear functional matrix of the Q-star mask channel at a fixed
/// schedule. Rows are `(M_i(1), M_i(∞))` for every round, followed by the two
/// revealed functionals `mask_init` and `p_hat(rho_J)`. Columns are the
/// coordinates of `p_small`.
///
/// The last two rows are necessarily in the span of the round-message rows:
/// the sumcheck recurrence derives the terminal product from the initial
/// claim and round messages. Coverage must therefore be checked on the
/// conditioned image `R(ker L)`, not by requiring all `2n+2` rows to be
/// independent.
pub fn mask_functional_matrix_fv(
    spec: SmallMaskSpec,
    m: usize,
    r_rest: &[F128],
    rhos: &[F128],
) -> Vec<Vec<F128>> {
    let n = m - K_SKIP;
    assert_eq!(r_rest.len(), n);
    assert_eq!(rhos.len(), n);
    let d = spec.d(m);
    let mut rows = vec![vec![F128::ZERO; d]; 2 * n + 2];
    let mut q = spec.q_star_dense(m);
    let mut indices = (0..d)
        .map(|index| spec.support_index(index, m))
        .collect::<Vec<_>>();
    let mut scales = vec![F128::ONE; d];

    let eq_full = univariate_skip::build_eq(r_rest);
    for column in 0..d {
        let index = indices[column];
        rows[2 * n][column] = eq_full[index] * q[index];
    }

    for round in 0..n {
        let eq_remaining = univariate_skip::build_eq(&r_rest[round + 1..]);
        for column in 0..d {
            let index = indices[column];
            let pair = index >> 1;
            let q0 = q[2 * pair];
            let q1 = q[2 * pair + 1];
            if index & 1 == 1 {
                rows[2 * round][column] = eq_remaining[pair] * scales[column] * q1;
            }
            rows[2 * round + 1][column] = eq_remaining[pair] * scales[column] * (q0 + q1);
        }

        let half = q.len() / 2;
        for i in 0..half {
            q[i] = q[2 * i] * (F128::ONE + rhos[round]) + q[2 * i + 1] * rhos[round];
        }
        q.truncate(half);
        for column in 0..d {
            scales[column] *= if indices[column] & 1 == 0 {
                F128::ONE + rhos[round]
            } else {
                rhos[round]
            };
            indices[column] >>= 1;
        }
    }

    let eq_terminal = univariate_skip::build_eq(rhos);
    for column in 0..d {
        rows[2 * n + 1][column] = eq_terminal[spec.support_index(column, m)];
    }
    rows
}

/// Witness padding descriptor for URM work-skipping.
///
/// The witness is a sequence of `2^(m - k_log)` blocks of `2^k_log` bits each;
/// inside each block, bits `[0, useful_bits_per_block)` carry real data and
/// bits `[useful_bits_per_block, 2^k_log)` are zero padding. URM contributions
/// from a chunk of all-zero bits are themselves zero, so we can skip those
/// chunks and produce byte-identical output.
///
/// Use [`PaddingSpec::dense`] when the witness has no padding holes.
#[derive(Clone, Copy, Debug)]
pub struct PaddingSpec {
    pub k_log: usize,
    pub useful_bits_per_block: usize,
}

impl PaddingSpec {
    /// "No padding": every bit of the witness is treated as useful. Equivalent
    /// to the legacy URM path with no skipping.
    pub fn dense(m: usize) -> Self {
        Self {
            k_log: m,
            useful_bits_per_block: 1usize << m,
        }
    }
}

// ---------------------------------------------------------------------------
// Public types: claim, proof, error.
// ---------------------------------------------------------------------------

/// Evaluation claims on the multilinear extensions of a, b, c. **Note that
/// `a_eval`/`b_eval` and `c_eval` are claimed at *different points*** —
/// extract_c separates C from the AB sumcheck:
///
/// - `a_eval`, `b_eval` are at `(z, mlv_challenges)` — the AB sumcheck binds
///   the rest variables one at a time to fresh `ρ_r` challenges.
/// - `c_eval` is at `(z, r_rest)` — C is linear, so its eq-weighted sum
///   collapses immediately to an MLE evaluation at the original eq weights;
///   no per-round folding needed. Here `r_rest = r[K_SKIP..m]` from the
///   zerocheck challenge.
///
/// The downstream caller (R1CS prover + PCS) opens each commitment at its
/// own claim point. Two openings for a, b at the same point; one for c at
/// a different point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZerocheckClaim {
    /// Univariate-skip challenge sampled after round 1 (binds the K_SKIP
    /// skip variables).
    pub z: F128,
    /// AB sumcheck bind challenges, one per multilinear round; length = `m - K_SKIP`.
    pub mlv_challenges: Vec<F128>,
    /// Eq weights for the rest variables = the zerocheck challenge restricted
    /// to `r[K_SKIP..m]`. This is the *rest part of the c-claim's point*.
    /// Length = `m - K_SKIP`.
    pub r_rest: Vec<F128>,
    /// `â(z, mlv_challenges)`.
    pub a_eval: F128,
    /// `b̂(z, mlv_challenges)`.
    pub b_eval: F128,
    /// `ĉ(z, r_rest)` — at a *different point* than a_eval, b_eval.
    pub c_eval: F128,
}

/// All round messages the prover sends, in order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZerocheckProof {
    /// Round 1 (univariate skip): `P^{AB}(λ)` for λ ∈ Λ, length 2^K_SKIP.
    pub round1_ab: Vec<F128>,
    /// Round 1 (extract_c): `P^C(λ)` for λ ∈ Λ, length 2^K_SKIP. Sent separately
    /// from `round1_ab` so the verifier can evaluate the C-claim immediately
    /// and skip the C-column in all subsequent rounds.
    pub round1_c: Vec<F128>,
    /// Multilinear sumcheck rounds: each entry is `(P_r(1), P_r(∞))` via the
    /// Karatsuba ∞-trick. Length = `m - K_SKIP`.
    pub multilinear_rounds: Vec<(F128, F128)>,
    /// Final MLE evaluations sent at the end of the protocol.
    pub final_a_eval: F128,
    pub final_b_eval: F128,
    pub final_c_eval: F128,
}

/// Reasons the verifier may reject a proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// `log_n` doesn't satisfy `log_n >= K_SKIP`.
    LogNTooSmall { log_n: usize, k_skip: usize },
    /// Round-1 messages have the wrong length (expected `2^K_SKIP`).
    BadRound1Length { expected: usize, got: usize },
    /// Wrong number of multilinear-round messages (expected `log_n - K_SKIP`).
    BadMultilinearRoundsLength { expected: usize, got: usize },
    /// `proof.final_c_eval` doesn't match the verifier's reconstruction
    /// `C_s · interpolate_at_z_on_lambda(round1_c, k_skip, z)`. Catches
    /// dishonesty in the round-1 C message or in the final c-eval claim.
    CEvalMismatch,
    /// The AB sumcheck final consistency check failed: the inner running
    /// claim after all rounds should equal `final_a_eval · final_b_eval`.
    /// Any inconsistency in `round1_ab`, in a multilinear round's
    /// `(P_r(1), P_r(∞))`, or in `final_a_eval` / `final_b_eval` propagates
    /// to this check.
    SumcheckFinalFailed,
}

// ---------------------------------------------------------------------------
// API: prove / verify.
// ---------------------------------------------------------------------------

/// Prove that `a(y) · b(y) ⊕ c(y) = 0` for all `y ∈ {0,1}^m`.
///
/// Inputs are LSB-first bit-packed byte vectors (each of length `2^m / 8`).
/// `m ≥ K_SKIP + N_INNER` (= 13). `challenger` supplies all verifier
/// randomness; the prover absorbs each of its messages into the challenger
/// before sampling the next challenge so the verifier (using the same
/// challenger implementation in lockstep) derives identical challenges.
///
/// Returns:
///   - the [`ZerocheckProof`] (raw round messages), and
///   - the [`ZerocheckClaim`] the higher-level caller will pass to its PCS.
pub fn prove_packed<C: Challenger>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    challenger: &mut C,
) -> (ZerocheckProof, ZerocheckClaim) {
    prove_packed_padded(
        a_packed,
        b_packed,
        c_packed,
        m,
        &PaddingSpec::dense(m),
        challenger,
    )
}

/// Same as [`prove_packed`] but lets the caller declare a per-block padding
/// pattern so URM can skip work for chunks that fall entirely in the zero
/// padding of every block. Output is byte-identical to the dense path when
/// the padding bits are honestly zero.
pub fn prove_packed_padded<C: Challenger>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    challenger: &mut C,
) -> (ZerocheckProof, ZerocheckClaim) {
    let (proof, claim, _) =
        prove_packed_padded_inner(a_packed, b_packed, c_packed, m, padding, false, challenger);
    (proof, claim)
}

/// Variant of [`prove_packed_padded`] that ALSO returns the canonical
/// `s_hat_v_c` produced by the fused two-bank round-1 kernel. The downstream
/// PCS open uses this to skip `fold_1b_rows` for the c-claim — see
/// [`crate::pcs::ring_switch::round1_shift_reduce_extract_c_packed_padded_with_s_hat_v`].
///
/// Wire output `(ZerocheckProof, ZerocheckClaim)` is byte-identical to
/// [`prove_packed_padded`].
pub fn prove_packed_padded_capture_s_hat_v_c<C: Challenger>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    challenger: &mut C,
) -> (ZerocheckProof, ZerocheckClaim, Vec<F128>) {
    let (proof, claim, captured) =
        prove_packed_padded_inner(a_packed, b_packed, c_packed, m, padding, true, challenger);
    (
        proof,
        claim,
        captured.expect("capture=true must produce s_hat_v_c"),
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_packed_padded_inner<C: Challenger>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    capture_s_hat_v_c: bool,
    challenger: &mut C,
) -> (ZerocheckProof, ZerocheckClaim, Option<Vec<F128>>) {
    let k_skip = K_SKIP;
    assert!(
        m >= k_skip + N_INNER,
        "prove requires m >= k_skip + N_INNER (= {})",
        k_skip + N_INNER
    );
    let expected_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), expected_bytes);
    assert_eq!(b_packed.len(), expected_bytes);
    assert_eq!(c_packed.len(), expected_bytes);
    let n_mlv = m - k_skip;

    challenger.observe_label(b"flock-zerocheck");

    // ---- 1. Sample r (with protocol-fixed constants in the inner 7 dims) ----
    //
    // r layout:
    //   r[0..k_skip]                — sampled (used by verifier for the
    //                                  final check at S; not by the URM)
    //   r[k_skip..k_skip+3]         — protocol small-eq constants φ_8(0xF7..)
    //   r[k_skip+3..k_skip+7]       — protocol medium-eq constants β_i
    //   r[k_skip+7..m]              — sampled (the "outer" eq weights for
    //                                  the URM and multilinear rounds)
    let r = sample_eq_point(m, challenger);

    // ---- 3. Round 1: URM (extract_c, parallel) ----
    //
    // The optimized URM drops a `C_s = φ_8(0x1C)` scalar from its accumulators
    // (a prover-side optimization tied to the small-eq trick — see the
    // C_s factor analysis in `univariate_skip_optimized`). The wire format
    // must be in "naive" convention so the verifier doesn't need to know
    // about this internal optimization; we restore the C_s factor here.
    let zc_timing = std::env::var_os("FLOCK_ZC_TIMING").is_some();
    let t_round1 = std::time::Instant::now();
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let (round1_ab_opt, round1_c_opt, s_hat_v_c) = if capture_s_hat_v_c {
        let (ab, c, s) =
            crate::zerocheck::univariate_skip_optimized::round1_shift_reduce_extract_c_packed_padded_with_s_hat_v(
                a_packed,
                b_packed,
                c_packed,
                m,
                k_skip,
                &r,
                &inv_table,
                padding,
            );
        (ab, c, Some(s))
    } else {
        let (ab, c) = round1_shift_reduce_extract_c_packed_padded(
            a_packed, b_packed, c_packed, m, k_skip, &r, &inv_table, padding,
        );
        (ab, c, None)
    };
    let c_s = c_s_f128();
    let round1_ab: Vec<F128> = round1_ab_opt.iter().map(|x| c_s * *x).collect();
    let round1_c: Vec<F128> = round1_c_opt.iter().map(|x| c_s * *x).collect();
    if zc_timing {
        eprintln!(
            "[zc-timing] round1 URM: {:.2} ms",
            t_round1.elapsed().as_secs_f64() * 1e3
        );
    }

    // ---- 4. Observe round-1 message, sample z (URM fold point) ----
    challenger.observe_f128_slice(&round1_ab);
    challenger.observe_f128_slice(&round1_c);
    let z = challenger.sample_f128();

    // ---- 5. c_eval = ĉ(z, r_rest) via interpolation of round1_c at z ----
    //
    // round1_c (now in naive convention) carries `P^C(λ) = Σ_x eq(r_rest, x) · ĉ(λ, x)`
    // as its 2^k_skip evaluations on Λ. Interpolating to λ=z gives
    // `ĉ(z, r_rest)` directly (the eq-weighted sum collapses to the MLE
    // evaluation because ĉ is linear). This is **the c-claim** — at point
    // `(z, r_rest)`, *not* `(z, ρ-values)`. ~64 F128 muls + Lagrange weights.
    let final_c_eval = interpolate_at_z_on_lambda(&round1_c, k_skip, z);

    // ---- 6. Round 2: fused fold + first multilinear message ----
    //
    // Convention A wrapping: pass `mlv_arg[0] = ONE` so the function's output
    // `mlv_arg[0] · G(1)` becomes the bare `G(1)` we send on the wire. The
    // verifier samples ρ_1 after observing this message.
    let t_round2 = std::time::Instant::now();
    let fold_table = UniSkipFoldTable::new(k_skip, z);
    let mut mlv_arg = vec![F128::ONE; n_mlv];
    mlv_arg[1..].copy_from_slice(&r[k_skip + 1..]);
    let (mut a_mlv, mut b_mlv, msg_1, msg_inf) =
        uni_skip_fold_and_round_pair_optimized_packed_padded(
            a_packed,
            b_packed,
            m,
            k_skip,
            &fold_table,
            &mlv_arg,
            padding,
        );

    if zc_timing {
        eprintln!(
            "[zc-timing] round2 fused fold: {:.2} ms",
            t_round2.elapsed().as_secs_f64() * 1e3
        );
    }
    let t_tail = std::time::Instant::now();
    let mut multilinear_msgs = Vec::with_capacity(n_mlv);
    multilinear_msgs.push((msg_1, msg_inf));
    challenger.observe_f128(msg_1);
    challenger.observe_f128(msg_inf);
    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    mlv_rhos.push(challenger.sample_f128());

    // ---- 7. Rounds 3..(n_mlv + 1) — AB only (c is done) ----
    //
    // Iter i: fold (a, b) at ρ_{i+1}, compute round (i+3) message, sample
    // ρ_{i+2}. Use the fused parallel path while log_n ≥ 10; below that the
    // SplitEqGhash inner can't form lo_size ≥ 2, so we fall back to
    // fold_in_place_pair + round_pair_naive.
    //
    // Ping-pong scratch buffers for the fused path: each fused round folds
    // (a_mlv, b_mlv) of size N into size N/2. Rather than allocating — and,
    // worse, `munmap`-ing, which is single-threaded and caps the tail's
    // parallel speedup — a fresh 64 MB buffer per round, we alternate between
    // two persistent buffers. Scratch capacity = N/2 (the largest fused
    // output); only needed when the first round is actually fused.
    let n_in = a_mlv.len();
    let (mut a_nxt, mut b_nxt) = if n_in >= 1024 {
        (
            crate::scratch::take_f128(n_in / 2),
            crate::scratch::take_f128(n_in / 2),
        )
    } else {
        (Vec::new(), Vec::new())
    };

    for i in 0..(n_mlv - 1) {
        let rho_prev = mlv_rhos[i];
        let log_n_before = a_mlv.len().trailing_zeros() as usize;

        // r_next for the next round's message: length log_n_before - 1.
        // r_next[0] = ONE (Convention A factor); r_next[1..] are the eq
        // weights for the remaining variables = r[k_skip + i + 2..m].
        let mut r_next = vec![F128::ONE; log_n_before - 1];
        r_next[1..].copy_from_slice(&r[k_skip + i + 2..]);

        let (m1, mi) = if log_n_before >= 10 {
            let half = a_mlv.len() / 2;
            let (m1, mi) = fold_and_compute_round_pair_into(
                &a_mlv,
                &b_mlv,
                &mut a_nxt[..half],
                &mut b_nxt[..half],
                rho_prev,
                &r_next,
            );
            // Swap current <-> scratch, then shrink the new current to the
            // folded size. The old (larger) buffer becomes scratch; we only
            // ever write its leading `half` slots next round, so its stale
            // length is harmless.
            std::mem::swap(&mut a_mlv, &mut a_nxt);
            std::mem::swap(&mut b_mlv, &mut b_nxt);
            a_mlv.truncate(half);
            b_mlv.truncate(half);
            (m1, mi)
        } else {
            fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_prev);
            round_pair_naive(&a_mlv, &b_mlv, &r_next)
        };

        multilinear_msgs.push((m1, mi));
        challenger.observe_f128(m1);
        challenger.observe_f128(mi);
        mlv_rhos.push(challenger.sample_f128());
    }

    // ---- 8. Final binding at ρ_{n_mlv} (the last challenge) ----
    let rho_last = *mlv_rhos.last().expect("at least one ρ sampled");
    fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_last);
    debug_assert_eq!(a_mlv.len(), 1);
    debug_assert_eq!(b_mlv.len(), 1);

    let final_a_eval = a_mlv[0];
    let final_b_eval = b_mlv[0];

    // ---- Fiat–Shamir: bind the final â, b̂ claims into the transcript ----
    //
    // These two claims are reduced downstream by lincheck via a *single*
    // random-linear-combination check with coefficient α (`target = α·v_a + v_b`,
    // see `lincheck`). That batching is only sound if α is sampled *after*
    // (v_a, v_b) are committed to the transcript — otherwise a prover that knows
    // α can pick (v_a, v_b) to satisfy the one batched equation while violating
    // the individual checks. So observe them here, before any later challenge
    // (the next one drawn is lincheck's α). `final_c_eval` needs no observe — the
    // verifier recomputes it from the already-absorbed `round1_c`/`z` and rejects
    // on mismatch (see `verify`), so it is already transcript-bound.
    challenger.observe_f128(final_a_eval);
    challenger.observe_f128(final_b_eval);

    // Recycle the four tail buffers (the two len-1 survivors still own their
    // full round-2 capacity) for the next phase/prove.
    crate::scratch::give_f128(a_mlv);
    crate::scratch::give_f128(b_mlv);
    crate::scratch::give_f128(a_nxt);
    crate::scratch::give_f128(b_nxt);

    if zc_timing {
        eprintln!(
            "[zc-timing] rounds 3+ tail: {:.2} ms",
            t_tail.elapsed().as_secs_f64() * 1e3
        );
    }

    let r_rest: Vec<F128> = r[k_skip..].to_vec();

    let proof = ZerocheckProof {
        round1_ab,
        round1_c,
        multilinear_rounds: multilinear_msgs,
        final_a_eval,
        final_b_eval,
        final_c_eval,
    };
    let claim = ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    };
    (proof, claim, s_hat_v_c)
}

/// Verify a zerocheck proof for an instance over `{0,1}^log_n`.
///
/// Walks the challenger in lockstep with the prover, samples the same
/// challenges, and checks every round's consistency equation.
///
/// On accept: returns the [`ZerocheckClaim`] the caller must check against
/// its PCS opening of `â`, `b̂`, `ĉ`.
/// On reject: returns a [`VerifyError`] indicating which check failed.
pub fn verify<C: Challenger>(
    log_n: usize,
    proof: &ZerocheckProof,
    challenger: &mut C,
) -> Result<ZerocheckClaim, VerifyError> {
    let m = log_n;
    let k_skip = K_SKIP;

    if m < k_skip + N_INNER {
        return Err(VerifyError::LogNTooSmall { log_n: m, k_skip });
    }
    let n_mlv = m - k_skip;
    let ell = 1usize << k_skip;

    // ---- Shape checks ----
    if proof.round1_ab.len() != ell {
        return Err(VerifyError::BadRound1Length {
            expected: ell,
            got: proof.round1_ab.len(),
        });
    }
    if proof.round1_c.len() != ell {
        return Err(VerifyError::BadRound1Length {
            expected: ell,
            got: proof.round1_c.len(),
        });
    }
    if proof.multilinear_rounds.len() != n_mlv {
        return Err(VerifyError::BadMultilinearRoundsLength {
            expected: n_mlv,
            got: proof.multilinear_rounds.len(),
        });
    }

    challenger.observe_label(b"flock-zerocheck");

    // ---- Re-derive r (in lockstep with prove_packed) ----
    let r = sample_eq_point(m, challenger);

    // ---- Observe round-1 messages, sample z ----
    challenger.observe_f128_slice(&proof.round1_ab);
    challenger.observe_f128_slice(&proof.round1_c);
    let z = challenger.sample_f128();

    // ---- Reconstruct ĉ(z, r_rest) from round1_c ----
    //
    // P^C has degree < 2^k_skip in λ (C is linear, summed against eq); ell
    // evaluations on Λ uniquely interpolate to z. round1_c is in naive
    // convention (the prover restored the C_s factor before sending), so
    // `ĉ(z, r_rest) = P^C(z)` directly.
    let computed_c_eval = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
    if computed_c_eval != proof.final_c_eval {
        return Err(VerifyError::CEvalMismatch);
    }

    // ---- Reconstruct the initial AB running claim ----
    //
    // P^{AB}(z) requires the polynomial in λ of degree < 2·ell to be evaluated
    // at z. The prover sent only ell evaluations on Λ — not enough on its own.
    // The verifier uses the **zerocheck assumption** `P^{AB}(λ) + P^C(λ) = 0`
    // for `λ ∈ S`. Together with the ell Λ-evaluations of the combined
    // polynomial, that's 2·ell evaluations — enough to interpolate the
    // combined polynomial at z. Then `P^{AB}(z) = P^{combined}(z) − P^C(z)`,
    // which in char-2 is `P^{combined}(z) + P^C(z)`.
    //
    // If the prover's witness is dishonest the S-zero assumption fails, the
    // reconstructed c_0 is wrong, and the running-claim chain ends at a value
    // inconsistent with `â · b̂`. We catch that at the final sumcheck check.
    let combined_at_lambda: Vec<F128> = proof
        .round1_ab
        .iter()
        .zip(&proof.round1_c)
        .map(|(x, y)| *x + *y)
        .collect();
    let combined_at_z = interpolate_at_z_combined(&combined_at_lambda, k_skip, z);
    let p_c_at_z = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
    let mut c_running = combined_at_z + p_c_at_z;

    // ---- Multilinear sumcheck chain ----
    //
    // The propagated running claim is the *inner* polynomial value G(ρ),
    // not the full per-round polynomial P(ρ) = eq(r_eq, ρ) · G(ρ). The eq
    // factor for the just-bound variable is absorbed by the next round's
    // consistency check via the identity
    //   G_{r-1}(ρ_{r-1}) = (1 + r_eq_r) · G_r(0) + r_eq_r · G_r(1).
    //
    // Round r (0-indexed i = r − 2) binds the i-th rest variable with eq weight
    // r[k_skip + i]. The prover sends `(G(1), G(∞))` (Convention A — no
    // factor). Verifier:
    //   1. reconstruct G(0) from consistency `c_running = (1+r_eq)·G(0) + r_eq·G(1)`,
    //   2. observe message, sample ρ_i,
    //   3. update `c_running ← G(ρ_i)`,
    //      where `G(X) = G(0)·(1+X) + G(1)·X + G(∞)·X·(X+1)` (char-2 quadratic
    //      interpolation through G(0), G(1), G(∞)).
    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    for (i, &(msg_1, msg_inf)) in proof.multilinear_rounds.iter().enumerate() {
        let r_eq = r[k_skip + i];
        let g1 = msg_1;
        let g_inf = msg_inf;

        challenger.observe_f128(msg_1);
        challenger.observe_f128(msg_inf);
        let rho = challenger.sample_f128();
        mlv_rhos.push(rho);

        c_running = fold_sumcheck_round(c_running, g1, g_inf, r_eq, rho)
            .ok_or(VerifyError::SumcheckFinalFailed)?;
    }

    // ---- AB sumcheck final consistency ----
    //
    // After all variables are bound, the inner running claim is just the
    // polynomial without the eq weighting:
    //   G_final(ρ_all) = â(z, ρ) · b̂(z, ρ) = final_a_eval · final_b_eval.
    // (The eq factors were absorbed round-by-round into the consistency checks,
    // never accumulating into the running claim.)
    let r_rest: Vec<F128> = r[k_skip..].to_vec();
    let expected_final = proof.final_a_eval * proof.final_b_eval;
    if c_running != expected_final {
        return Err(VerifyError::SumcheckFinalFailed);
    }

    // ---- Fiat–Shamir: bind the final â, b̂ claims (mirrors `prove_packed_padded_inner`) ----
    //
    // Must observe at the same transcript position as the prover, before the
    // next challenge (lincheck's α) is drawn, so the α-batched reduction of
    // these two claims is sound. `final_c_eval` is already bound via the
    // recompute-and-compare above, so it is not observed.
    challenger.observe_f128(proof.final_a_eval);
    challenger.observe_f128(proof.final_b_eval);

    Ok(ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: proof.final_a_eval,
        b_eval: proof.final_b_eval,
        c_eval: proof.final_c_eval,
    })
}

// ===========================================================================
// Field mask: P times the public affine Q-star (reference path)
// ===========================================================================
//
// The zerocheck's revealed round messages `(G_j(1), G_j(∞))` are degree-2 in
// the fold variable, and `G_j(∞)` — the leading coefficient — cannot be masked
// by any degree-1 channel (in characteristic 2 the classical separable mask
// also vanishes over the cube). We run the AB sumcheck on `â·b̂ + γ·P·Q★`,
// where P is a fresh witness-free multilinear committed before the
// Fiat–Shamir challenge `γ` and Q-star is fixed and public. Because P carries
// no witness, the mask contribution's distribution is witness-independent by
// construction; hiding reduces to the conditioned-image theorem.
//
// This is a REFERENCE implementation: correctness- and certification-oriented,
// reusing the naive round-pair kernels rather than the fused hot path. The
// optimized fused variant is a follow-up and must be differential-tested
// against this one. `P(ρ)` is returned for the caller to authenticate against
// the P commitment through a hiding general-linear PCS opening.

/// Zerocheck proof with a combined field mask. `round1_ab`/`round1_c` are the
/// unmasked round-1 messages (already randomizer-covered); `mask_init` is the
/// `P·Q★` sumcheck's post-skip initial claim `σ_z` (witness-free);
/// `multilinear_rounds` are the COMBINED pairs `G_j + γ·M_j`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZkZerocheckProof {
    pub round1_ab: Vec<F128>,
    pub round1_c: Vec<F128>,
    pub mask_init: F128,
    pub multilinear_rounds: Vec<(F128, F128)>,
    pub final_a_eval: F128,
    pub final_b_eval: F128,
    pub final_c_eval: F128,
    pub final_p_eval: F128,
}

/// Prove the zerocheck with a combined field mask. `p_small` is a field-valued
/// vector on [`SmallMaskSpec`]'s diagonal support. It MUST already be committed
/// and its commitment bound into the transcript before this call (so `γ`
/// cannot depend on a later mask choice).
/// Round-1 mask channel.
///
/// Round 1 is the one PIOP class the degree-2 `γ·P·Q★` channel cannot touch:
/// the verifier reconstructs the AB running claim from the **zerocheck
/// assumption** `P^AB + P^C = 0` on `S`, and a mask that does not vanish
/// there destroys that reconstruction. `P·Q★` does not vanish on `S`, which is
/// why the product-mask channel starts at round 2.
///
/// The round-1 channel masks it with a *pair* whose sum vanishes on `S`.
/// With `M_c` the C-side mask and `M_ab = M_c + V_S·h` the AB-side one, the
/// combined polynomial gains `M_ab + M_c = V_S·h`, which is zero on `S` — so the
/// reconstruction is untouched — while the two sides move independently.
/// That independence is the point: the measured escaping direction is
/// supported on `round1_c` and *not* on `round1_ab`, so a diagonal mask
/// (`M_ab = M_c`) provably cannot reach it.
///
/// Both cubes are witness-free and committed before any challenge; `V_S` has
/// no zero on `Λ`, so the reachable pair `(M_c|_Λ, M_ab|_Λ)` is unconstrained.
pub struct Round1Mask<'a> {
    /// Witness-free cube supplying the C-side mask `M_c`.
    pub s_c_packed: &'a [u8],
    /// Witness-free cube supplying `h`, the off-diagonal generator.
    pub s_h_packed: &'a [u8],
}

/// The two scalars the verifier needs to undo a round-1 mask. Both are
/// witness-free and both must be opened against their commitments — the
/// verifier consumes them to recover the C-claim and the AB running claim, so
/// an unbound value would leave both unconstrained.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Round1MaskTranscript {
    /// `M_c(z) = Ŝ_c(z, r_rest)` — an evaluation of the committed cube at
    /// exactly the c-claim point.
    pub mc_at_z: F128,
    /// `h(z) = Ŝ_h(z, r_rest)`, at the same point.
    pub h_at_z: F128,
}

pub fn prove_packed_padded_zk<C: Challenger>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    p_small: &[F128],
    m: usize,
    padding: &PaddingSpec,
    challenger: &mut C,
) -> (ZkZerocheckProof, ZerocheckClaim) {
    let (proof, claim, _) = prove_packed_padded_zk_masked(
        a_packed, b_packed, c_packed, p_small, m, padding, None, challenger,
    );
    (proof, claim)
}

/// [`prove_packed_padded_zk`] with the optional round-1 mask channel.
///
/// The returned [`ZerocheckClaim`] carries the **un-shifted** `c_eval`, so
/// downstream claim handling is unchanged; the proof's `final_c_eval` carries
/// the masked value the verifier recomputes from `round1_c`.
#[allow(clippy::too_many_arguments)]
pub fn prove_packed_padded_zk_masked<C: Challenger>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    p_small: &[F128],
    m: usize,
    padding: &PaddingSpec,
    mask: Option<Round1Mask<'_>>,
    challenger: &mut C,
) -> (
    ZkZerocheckProof,
    ZerocheckClaim,
    Option<Round1MaskTranscript>,
) {
    let k_skip = K_SKIP;
    assert!(
        m >= k_skip + N_INNER,
        "prove_zk requires m >= {}",
        k_skip + N_INNER
    );
    let expected_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), expected_bytes);
    let n_mlv = m - k_skip;
    let mask_spec = SmallMaskSpec::default();
    assert_eq!(p_small.len(), mask_spec.d(m));
    let dense = PaddingSpec::dense(m);

    challenger.observe_label(b"flock-zerocheck-zk");

    // ---- r (identical layout to prove_packed_padded_inner) ----
    let r = sample_eq_point(m, challenger);

    // ---- round 1 (â·b̂ only; unmasked) ----
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let (round1_ab_opt, round1_c_opt) = round1_shift_reduce_extract_c_packed_padded(
        a_packed, b_packed, c_packed, m, k_skip, &r, &inv_table, padding,
    );
    let c_s = c_s_f128();
    let mut round1_ab: Vec<F128> = round1_ab_opt.iter().map(|x| c_s * *x).collect();
    let mut round1_c: Vec<F128> = round1_c_opt.iter().map(|x| c_s * *x).collect();

    // ---- round-1 mask pair ----
    //
    // `M_c` masks the C side; the AB side gets `M_c + V_S·h`, so the combined
    // polynomial gains `V_S·h`, which vanishes on S — leaving the verifier's
    // reconstruction (and the zerocheck assumption behind it) exactly as it
    // was, while the two sides move independently. The mask cubes are folded
    // over their FULL support (`dense`), because the value the verifier will
    // open, `Ŝ_c(z, r_rest)`, sums over the whole cube.
    let mask_lambda: Option<(Vec<F128>, Vec<F128>)> = mask.map(|mk| {
        assert_eq!(mk.s_c_packed.len(), expected_bytes);
        assert_eq!(mk.s_h_packed.len(), expected_bytes);
        let zeros = vec![0u8; expected_bytes];
        let (_, mc_opt) = round1_shift_reduce_extract_c_packed_padded(
            &zeros,
            &zeros,
            mk.s_c_packed,
            m,
            k_skip,
            &r,
            &inv_table,
            &dense,
        );
        let (_, mh_opt) = round1_shift_reduce_extract_c_packed_padded(
            &zeros,
            &zeros,
            mk.s_h_packed,
            m,
            k_skip,
            &r,
            &inv_table,
            &dense,
        );
        let mc: Vec<F128> = mc_opt.iter().map(|x| c_s * *x).collect();
        let mh: Vec<F128> = mh_opt.iter().map(|x| c_s * *x).collect();
        let vs = vanishing_s_on_lambda(k_skip);
        for i in 0..round1_c.len() {
            round1_ab[i] += mc[i] + vs[i] * mh[i];
            round1_c[i] += mc[i];
        }
        (mc, mh)
    });

    challenger.observe_f128_slice(&round1_ab);
    challenger.observe_f128_slice(&round1_c);
    let z = challenger.sample_f128();
    // The proof field is the MASKED value: the verifier recomputes exactly
    // this from `round1_c` and compares, so that check is unchanged.
    let final_c_eval = interpolate_at_z_on_lambda(&round1_c, k_skip, z);
    let mask_transcript = mask_lambda.map(|(mc, mh)| Round1MaskTranscript {
        mc_at_z: interpolate_at_z_on_lambda(&mc, k_skip, z),
        h_at_z: interpolate_at_z_on_lambda(&mh, k_skip, z),
    });
    // The CLAIM carries the un-shifted ĉ(z, r_rest): the PCS binds ẑ, not the
    // masked message.
    let claim_c_eval = match &mask_transcript {
        Some(mt) => final_c_eval + mt.mc_at_z,
        None => final_c_eval,
    };

    // ---- round 2 fold (both â·b̂ and P·Q★) at z ----
    let fold_table = UniSkipFoldTable::new(k_skip, z);
    let mut mlv_arg = vec![F128::ONE; n_mlv];
    mlv_arg[1..].copy_from_slice(&r[k_skip + 1..]);
    let (mut a_mlv, mut b_mlv, g2_1, g2_inf) = uni_skip_fold_and_round_pair_optimized_packed_padded(
        a_packed,
        b_packed,
        m,
        k_skip,
        &fold_table,
        &mlv_arg,
        padding,
    );
    let mut p_mlv = mask_spec.expand(p_small, m);
    let mut q_mlv = mask_spec.q_star_dense(m);
    let (mm2_1, mm2_inf) = round_pair_naive(&p_mlv, &q_mlv, &mlv_arg);

    // ---- σ_z = Σ_x eq(r[k_skip..m], x)·P_mlv(x)·Q_mlv(x); observe; sample γ ----
    let eq_rest = crate::zerocheck::univariate_skip::build_eq(&r[k_skip..]);
    debug_assert_eq!(eq_rest.len(), p_mlv.len());
    let mask_init: F128 = eq_rest
        .iter()
        .zip(&p_mlv)
        .zip(&q_mlv)
        .fold(F128::ZERO, |acc, ((e, p), q)| acc + *e * *p * *q);
    challenger.observe_f128(mask_init);
    let gamma = challenger.sample_f128();

    // ---- combined round 2 message ----
    let mut multilinear_msgs: Vec<(F128, F128)> = Vec::with_capacity(n_mlv);
    let c2 = (g2_1 + gamma * mm2_1, g2_inf + gamma * mm2_inf);
    multilinear_msgs.push(c2);
    challenger.observe_f128(c2.0);
    challenger.observe_f128(c2.1);
    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    mlv_rhos.push(challenger.sample_f128());

    // ---- tail rounds (naive path for both cubes; reference-correct) ----
    for i in 0..(n_mlv - 1) {
        let rho_prev = mlv_rhos[i];
        let log_n_before = a_mlv.len().trailing_zeros() as usize;
        let mut r_next = vec![F128::ONE; log_n_before - 1];
        r_next[1..].copy_from_slice(&r[k_skip + i + 2..]);
        fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_prev);
        let (mg1, mginf) = round_pair_naive(&a_mlv, &b_mlv, &r_next);
        fold_in_place_pair(&mut p_mlv, &mut q_mlv, rho_prev);
        let (mm1, mminf) = round_pair_naive(&p_mlv, &q_mlv, &r_next);
        let c = (mg1 + gamma * mm1, mginf + gamma * mminf);
        multilinear_msgs.push(c);
        challenger.observe_f128(c.0);
        challenger.observe_f128(c.1);
        mlv_rhos.push(challenger.sample_f128());
    }

    // ---- final binding ----
    let rho_last = *mlv_rhos.last().expect("at least one ρ");
    fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_last);
    fold_in_place_pair(&mut p_mlv, &mut q_mlv, rho_last);
    debug_assert_eq!(a_mlv.len(), 1);
    let final_a_eval = a_mlv[0];
    let final_b_eval = b_mlv[0];
    let final_p_eval = p_mlv[0];
    challenger.observe_f128(final_a_eval);
    challenger.observe_f128(final_b_eval);
    challenger.observe_f128(final_p_eval);

    let r_rest: Vec<F128> = r[k_skip..].to_vec();
    let proof = ZkZerocheckProof {
        round1_ab,
        round1_c,
        mask_init,
        multilinear_rounds: multilinear_msgs,
        final_a_eval,
        final_b_eval,
        final_c_eval,
        final_p_eval,
    };
    let claim = ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: claim_c_eval,
    };
    (proof, claim, mask_transcript)
}

/// Terminal values of the honest masked zerocheck at a fixed challenge
/// schedule. The ROM simulator uses this evaluator to solve its transcript in
/// one pass without first running an honest proof to discover these values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZkTerminalEvaluations {
    pub a_eval: F128,
    pub b_eval: F128,
    /// Unmasked C evaluation authenticated by the witness opening.
    pub c_eval: F128,
    pub p_eval: F128,
    pub mask_init: F128,
    pub mc_at_z: F128,
    pub h_at_z: F128,
}

/// Evaluate every zerocheck terminal used by the simulator using the shipped
/// folding and round-1 kernels. `r` is the verifier's full equality point and
/// `rhos` is the complete multilinear-fold challenge vector.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_zk_terminals_packed_padded(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    p_small: &[F128],
    s_c_packed: &[u8],
    s_h_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    r: &[F128],
    z: F128,
    rhos: &[F128],
) -> ZkTerminalEvaluations {
    let k_skip = K_SKIP;
    let n_mlv = m - k_skip;
    let expected_bytes = (1usize << m) / 8;
    assert_eq!(r.len(), m);
    assert_eq!(rhos.len(), n_mlv);
    for packed in [a_packed, b_packed, c_packed, s_c_packed, s_h_packed] {
        assert_eq!(packed.len(), expected_bytes);
    }
    let mask_spec = SmallMaskSpec::default();
    assert_eq!(p_small.len(), mask_spec.d(m));

    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let c_s = c_s_f128();
    let dense = PaddingSpec::dense(m);

    let zeros = vec![0u8; expected_bytes];
    let (_, c_lambda_opt) = round1_shift_reduce_extract_c_packed_padded(
        &zeros, &zeros, c_packed, m, k_skip, r, &inv_table, padding,
    );
    let (_, mc_lambda_opt) = round1_shift_reduce_extract_c_packed_padded(
        &zeros, &zeros, s_c_packed, m, k_skip, r, &inv_table, &dense,
    );
    let (_, h_lambda_opt) = round1_shift_reduce_extract_c_packed_padded(
        &zeros, &zeros, s_h_packed, m, k_skip, r, &inv_table, &dense,
    );
    let scale = |values: &[F128]| -> Vec<F128> { values.iter().map(|v| c_s * *v).collect() };
    let c_lambda = scale(&c_lambda_opt);
    let mc_lambda = scale(&mc_lambda_opt);
    let h_lambda = scale(&h_lambda_opt);

    let fold_table = UniSkipFoldTable::new(k_skip, z);
    let mut mlv_arg = vec![F128::ONE; n_mlv];
    mlv_arg[1..].copy_from_slice(&r[k_skip + 1..]);
    let (mut a_mlv, mut b_mlv, _, _) = uni_skip_fold_and_round_pair_optimized_packed_padded(
        a_packed,
        b_packed,
        m,
        k_skip,
        &fold_table,
        &mlv_arg,
        padding,
    );
    let mut p_mlv = mask_spec.expand(p_small, m);
    let mut q_mlv = mask_spec.q_star_dense(m);

    let eq_rest = crate::zerocheck::univariate_skip::build_eq(&r[k_skip..]);
    let mask_init = eq_rest
        .iter()
        .zip(&p_mlv)
        .zip(&q_mlv)
        .fold(F128::ZERO, |acc, ((e, p), q)| acc + *e * *p * *q);
    for rho in rhos {
        fold_in_place_pair(&mut a_mlv, &mut b_mlv, *rho);
        fold_in_place_pair(&mut p_mlv, &mut q_mlv, *rho);
    }
    debug_assert_eq!(a_mlv.len(), 1);
    debug_assert_eq!(p_mlv.len(), 1);

    ZkTerminalEvaluations {
        a_eval: a_mlv[0],
        b_eval: b_mlv[0],
        c_eval: interpolate_at_z_on_lambda(&c_lambda, k_skip, z),
        p_eval: p_mlv[0],
        mask_init,
        mc_at_z: interpolate_at_z_on_lambda(&mc_lambda, k_skip, z),
        h_at_z: interpolate_at_z_on_lambda(&h_lambda, k_skip, z),
    }
}

/// The degree-2 mask channel's contribution to the round messages, in
/// isolation: the round pairs `(M_j(1), M_j(∞))` of the `P·Q★` product
/// sumcheck, at the same challenge schedule the masked prover uses.
///
/// This is the map whose F2 image is measured by the symbolic mask coverage
/// test. It runs the SAME
/// kernels as [`prove_packed_padded_zk`] — the skip fold and the naive
/// round-pair kernel on the same folded cubes — so what is measured is the
/// shipped map, not a re-derivation of it.
///
/// `challenger` is consumed by value: callers pass a clone, since sampling
/// the schedule here must not disturb the real proof transcript.
pub fn mask_round_pairs<C: Challenger>(
    p_small: &[F128],
    m: usize,
    challenger: &mut C,
) -> Vec<(F128, F128)> {
    let k_skip = K_SKIP;
    assert!(m >= k_skip + N_INNER);
    let n_mlv = m - k_skip;
    let mask_spec = SmallMaskSpec::default();
    assert_eq!(p_small.len(), mask_spec.d(m));

    challenger.observe_label(b"flock-zerocheck-zk");
    let r = sample_eq_point(m, challenger);
    let _z = challenger.sample_f128();

    let mut mlv_arg = vec![F128::ONE; n_mlv];
    mlv_arg[1..].copy_from_slice(&r[k_skip + 1..]);
    let mut p_mlv = mask_spec.expand(p_small, m);
    let mut q_mlv = mask_spec.q_star_dense(m);
    let (mm2_1, mm2_inf) = round_pair_naive(&p_mlv, &q_mlv, &mlv_arg);
    let mut out = Vec::with_capacity(n_mlv);
    out.push((mm2_1, mm2_inf));
    // The fold challenges ρ_j are whatever the caller's challenger yields at
    // this position; the map is linear in P for any fixed schedule.
    let mut rho = challenger.sample_f128();
    for i in 0..(n_mlv - 1) {
        let log_n_before = p_mlv.len().trailing_zeros() as usize;
        let mut r_next = vec![F128::ONE; log_n_before - 1];
        r_next[1..].copy_from_slice(&r[k_skip + i + 2..]);
        fold_in_place_pair(&mut p_mlv, &mut q_mlv, rho);
        out.push(round_pair_naive(&p_mlv, &q_mlv, &r_next));
        rho = challenger.sample_f128();
    }
    out
}

/// Verify a combined masked zerocheck proof. Checks the sumcheck equation
/// `running == â(ρ)·b̂(ρ) + γ·P(ρ)·Q★(ρ)`. The caller MUST additionally
/// authenticate `proof.final_p_eval == P(ρ)` against the P commitment
/// (through the PCS). Returns the standard
/// `ZerocheckClaim` (for the â·b̂/ĉ openings) on accept.
pub fn verify_zk<C: Challenger>(
    log_n: usize,
    proof: &ZkZerocheckProof,
    challenger: &mut C,
) -> Result<ZerocheckClaim, VerifyError> {
    verify_zk_masked(log_n, proof, None, challenger)
}

/// [`verify_zk`] with the optional round-1 mask engaged.
///
/// `mask` is `(M_c(z), h(z))` taken from the proof. **Both are unchecked
/// here**: this function only uses them to un-shift the AB running claim and
/// the C-claim. The caller MUST verify each against its commitment at the
/// c-claim point, or a prover picks them after `z` and both derived values
/// are unconstrained.
pub fn verify_zk_masked<C: Challenger>(
    log_n: usize,
    proof: &ZkZerocheckProof,
    mask: Option<(F128, F128)>,
    challenger: &mut C,
) -> Result<ZerocheckClaim, VerifyError> {
    let m = log_n;
    let k_skip = K_SKIP;
    if m < k_skip + N_INNER {
        return Err(VerifyError::LogNTooSmall { log_n: m, k_skip });
    }
    let n_mlv = m - k_skip;
    let ell = 1usize << k_skip;
    if proof.round1_ab.len() != ell || proof.round1_c.len() != ell {
        return Err(VerifyError::BadRound1Length {
            expected: ell,
            got: proof.round1_ab.len(),
        });
    }
    if proof.multilinear_rounds.len() != n_mlv {
        return Err(VerifyError::BadMultilinearRoundsLength {
            expected: n_mlv,
            got: proof.multilinear_rounds.len(),
        });
    }

    challenger.observe_label(b"flock-zerocheck-zk");
    let r = sample_eq_point(m, challenger);

    challenger.observe_f128_slice(&proof.round1_ab);
    challenger.observe_f128_slice(&proof.round1_c);
    let z = challenger.sample_f128();

    let computed_c_eval = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
    if computed_c_eval != proof.final_c_eval {
        return Err(VerifyError::CEvalMismatch);
    }

    // AB initial claim (identical reconstruction to `verify`).
    let combined_at_lambda: Vec<F128> = proof
        .round1_ab
        .iter()
        .zip(&proof.round1_c)
        .map(|(x, y)| *x + *y)
        .collect();
    let combined_at_z = interpolate_at_z_combined(&combined_at_lambda, k_skip, z);
    let p_c_at_z = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
    // The masked C side carries `P^C + M_c`, and the masked combined
    // polynomial carries `combined + V_S·h` — the latter still zero on S, so
    // the reconstruction above is valid. What comes out is therefore
    // `P^AB(z) + M_ab(z)`; un-shift by `M_ab(z) = M_c(z) + V_S(z)·h(z)`.
    let ab_init = match mask {
        Some((mc_at_z, h_at_z)) => {
            combined_at_z + p_c_at_z + mc_at_z + vanishing_s_at(k_skip, z) * h_at_z
        }
        None => combined_at_z + p_c_at_z,
    };

    // Observe σ_z, sample γ — mirrors the prover; γ is bound to (root, σ_z).
    challenger.observe_f128(proof.mask_init);
    let gamma = challenger.sample_f128();

    // Combined initial claim.
    let mut c_running = ab_init + gamma * proof.mask_init;

    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    for (i, &(msg_1, msg_inf)) in proof.multilinear_rounds.iter().enumerate() {
        let r_eq = r[k_skip + i];
        let g1 = msg_1;
        let g_inf = msg_inf;
        challenger.observe_f128(msg_1);
        challenger.observe_f128(msg_inf);
        let rho = challenger.sample_f128();
        mlv_rhos.push(rho);
        c_running = fold_sumcheck_round(c_running, g1, g_inf, r_eq, rho)
            .ok_or(VerifyError::SumcheckFinalFailed)?;
    }

    // Combined final check: â(ρ)·b̂(ρ) + γ·P(ρ)·Q★(ρ).
    let expected = proof.final_a_eval * proof.final_b_eval
        + gamma * proof.final_p_eval * SmallMaskSpec::default().q_star_at(&mlv_rhos);
    if c_running != expected {
        return Err(VerifyError::SumcheckFinalFailed);
    }

    challenger.observe_f128(proof.final_a_eval);
    challenger.observe_f128(proof.final_b_eval);
    challenger.observe_f128(proof.final_p_eval);

    Ok(ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest: r[k_skip..].to_vec(),
        a_eval: proof.final_a_eval,
        b_eval: proof.final_b_eval,
        // The PCS binds ẑ, so hand on the unshifted claim.
        c_eval: match mask {
            Some((mc_at_z, _)) => proof.final_c_eval + mc_at_z,
            None => proof.final_c_eval,
        },
    })
}

#[cfg(test)]
mod tests;

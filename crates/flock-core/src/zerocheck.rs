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

use crate::challenger::Challenger;
use crate::field::{F8, F128};
use crate::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
use serde::{Deserialize, Serialize};

pub mod multilinear;
pub mod univariate_skip;
pub mod univariate_skip_deg4;
pub mod univariate_skip_deg4_optimized;
pub mod univariate_skip_optimized;

use multilinear::{
    UniSkipFoldTable, fold_and_compute_round_pair_into, fold_in_place_pair,
    interpolate_at_z_combined, interpolate_at_z_on_lambda, round_pair_naive,
    uni_skip_fold_and_round_pair_optimized_packed_padded,
};
use univariate_skip_optimized::{
    c_s_f128, medium_challenges_ghash, round1_shift_reduce_extract_c_packed_padded,
    small_challenges_ghash,
};

/// Number of variables folded in round 1 via the additive-NTT univariate skip.
/// |Λ| = 2^K_SKIP = 64 elements; the round-1 prover message is two length-64
/// vectors of F128.
pub const K_SKIP: usize = 6;

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
    const N_INNER: usize = 7; // 3 small + 4 medium fixed-constant eq dims
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

    challenger.observe_label(b"flock-zerocheck-v0");

    // ---- 1. Sample r (with protocol-fixed constants in the inner 7 dims) ----
    //
    // r layout:
    //   r[0..k_skip]                — sampled (used by verifier for the
    //                                  final check at S; not by the URM)
    //   r[k_skip..k_skip+3]         — protocol small-eq constants φ_8(0xF7..)
    //   r[k_skip+3..k_skip+7]       — protocol medium-eq constants β_i
    //   r[k_skip+7..m]              — sampled (the "outer" eq weights for
    //                                  the URM and multilinear rounds)
    let r_skip = challenger.sample_f128_vec(k_skip);
    let r_outer = challenger.sample_f128_vec(m - k_skip - N_INNER);
    let mut r = vec![F128::ZERO; m];
    r[..k_skip].copy_from_slice(&r_skip);
    for (i, val) in small_challenges_ghash().iter().enumerate() {
        r[k_skip + i] = *val;
    }
    for (i, val) in medium_challenges_ghash().iter().enumerate() {
        r[k_skip + 3 + i] = *val;
    }
    r[k_skip + N_INNER..].copy_from_slice(&r_outer);

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
    const N_INNER: usize = 7;

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

    challenger.observe_label(b"flock-zerocheck-v0");

    // ---- Re-derive r (in lockstep with prove_packed) ----
    let r_skip = challenger.sample_f128_vec(k_skip);
    let r_outer = challenger.sample_f128_vec(m - k_skip - N_INNER);
    let mut r = vec![F128::ZERO; m];
    r[..k_skip].copy_from_slice(&r_skip);
    for (i, val) in small_challenges_ghash().iter().enumerate() {
        r[k_skip + i] = *val;
    }
    for (i, val) in medium_challenges_ghash().iter().enumerate() {
        r[k_skip + 3 + i] = *val;
    }
    r[k_skip + N_INNER..].copy_from_slice(&r_outer);

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
        let one_plus_r_eq = F128::ONE + r_eq;

        let g1 = msg_1;
        let g_inf = msg_inf;
        let g0 = (c_running + r_eq * g1) * one_plus_r_eq.inv();

        challenger.observe_f128(msg_1);
        challenger.observe_f128(msg_inf);
        let rho = challenger.sample_f128();
        mlv_rhos.push(rho);

        let one_plus_rho = F128::ONE + rho;
        // G(ρ) = G(0)·(1+ρ) + G(1)·ρ + G(∞)·ρ·(1+ρ).
        c_running = g0 * one_plus_rho + g1 * rho + g_inf * rho * one_plus_rho;
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
// A1′ amendment: the degree-2 committed mask channel (reference implementation)
// ===========================================================================
//
// The zerocheck's revealed round messages `(G_j(1), G_j(∞))` are degree-2 in
// the fold variable, and `G_j(∞)` — the leading coefficient — cannot be masked
// by any degree-1 channel (in characteristic 2 the classical separable mask
// also vanishes over the cube). We run the AB sumcheck on `â·b̂ + γ·P·Q`,
// where `P, Q` are two fresh witness-free multilinears committed before the
// Fiat–Shamir challenge `γ`. Because `P, Q` carry no witness, the mask
// contribution's distribution is witness-independent by construction; the
// hiding of the round messages reduces to the conditional joint-coverage
// certificate (see `docs/zk-joint-coverage-plan.md`).
//
// This is a REFERENCE implementation: correctness- and certification-oriented,
// reusing the naive round-pair kernels rather than the fused hot path. The
// optimized fused variant is a follow-up and must be differential-tested
// against this one. `P(ρ)`, `Q(ρ)` are returned for the caller to authenticate
// against the `P, Q` commitments through the PCS (a HIDING opening — only
// `P(ρ)`/`Q(ρ)` may leak, not the opened codeword rows).

/// Zerocheck proof under the A1′ amendment. `round1_ab`/`round1_c` are the
/// unmasked round-1 messages (already randomizer-covered); `mask_init` is the
/// `P·Q` sumcheck's post-skip initial claim `σ_z` (witness-free);
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
    pub final_q_eval: F128,
}

/// Prove the zerocheck under the A1′ amendment. `p_packed`/`q_packed` are the
/// LSB-first bit-packed mask cubes (same layout as `a_packed`), full support
/// (dense). They MUST already be committed and their commitment bound into the
/// transcript before this call (so `γ` cannot depend on a later mask choice).
pub fn prove_packed_padded_zk<C: Challenger>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    p_packed: &[u8],
    q_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    challenger: &mut C,
) -> (ZkZerocheckProof, ZerocheckClaim) {
    let k_skip = K_SKIP;
    const N_INNER: usize = 7;
    assert!(m >= k_skip + N_INNER, "prove_zk requires m >= {}", k_skip + N_INNER);
    let expected_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), expected_bytes);
    assert_eq!(p_packed.len(), expected_bytes);
    assert_eq!(q_packed.len(), expected_bytes);
    let n_mlv = m - k_skip;
    let dense = PaddingSpec::dense(m);

    challenger.observe_label(b"flock-zerocheck-zk-v0");

    // ---- r (identical layout to prove_packed_padded_inner) ----
    let r_skip = challenger.sample_f128_vec(k_skip);
    let r_outer = challenger.sample_f128_vec(m - k_skip - N_INNER);
    let mut r = vec![F128::ZERO; m];
    r[..k_skip].copy_from_slice(&r_skip);
    for (i, val) in small_challenges_ghash().iter().enumerate() {
        r[k_skip + i] = *val;
    }
    for (i, val) in medium_challenges_ghash().iter().enumerate() {
        r[k_skip + 3 + i] = *val;
    }
    r[k_skip + N_INNER..].copy_from_slice(&r_outer);

    // ---- round 1 (â·b̂ only; unmasked) ----
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let (round1_ab_opt, round1_c_opt) = round1_shift_reduce_extract_c_packed_padded(
        a_packed, b_packed, c_packed, m, k_skip, &r, &inv_table, padding,
    );
    let c_s = c_s_f128();
    let round1_ab: Vec<F128> = round1_ab_opt.iter().map(|x| c_s * *x).collect();
    let round1_c: Vec<F128> = round1_c_opt.iter().map(|x| c_s * *x).collect();
    challenger.observe_f128_slice(&round1_ab);
    challenger.observe_f128_slice(&round1_c);
    let z = challenger.sample_f128();
    let final_c_eval = interpolate_at_z_on_lambda(&round1_c, k_skip, z);

    // ---- round 2 fold (both â·b̂ and P·Q) at z ----
    let fold_table = UniSkipFoldTable::new(k_skip, z);
    let mut mlv_arg = vec![F128::ONE; n_mlv];
    mlv_arg[1..].copy_from_slice(&r[k_skip + 1..]);
    let (mut a_mlv, mut b_mlv, g2_1, g2_inf) =
        uni_skip_fold_and_round_pair_optimized_packed_padded(
            a_packed, b_packed, m, k_skip, &fold_table, &mlv_arg, padding,
        );
    let (mut p_mlv, mut q_mlv, mm2_1, mm2_inf) =
        uni_skip_fold_and_round_pair_optimized_packed_padded(
            p_packed, q_packed, m, k_skip, &fold_table, &mlv_arg, &dense,
        );

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
    let final_q_eval = q_mlv[0];
    challenger.observe_f128(final_a_eval);
    challenger.observe_f128(final_b_eval);
    challenger.observe_f128(final_p_eval);
    challenger.observe_f128(final_q_eval);

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
        final_q_eval,
    };
    let claim = ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    };
    (proof, claim)
}

/// The degree-2 mask channel's contribution to the round messages, in
/// isolation: the round pairs `(M_j(1), M_j(∞))` of the `P·Q` product
/// sumcheck, at the same challenge schedule the amended prover uses.
///
/// This is the map whose F₂ image the prover's per-proof coverage
/// self-check measures (`flock_prover::zk_rank_check`). It runs the SAME
/// kernels as [`prove_packed_padded_zk`] — the skip fold and the naive
/// round-pair kernel on the same folded cubes — so what is measured is the
/// shipped map, not a re-derivation of it.
///
/// `challenger` is consumed by value: callers pass a clone, since sampling
/// the schedule here must not disturb the real proof transcript.
pub fn mask_round_pairs<C: Challenger>(
    p_packed: &[u8],
    q_packed: &[u8],
    m: usize,
    challenger: &mut C,
) -> Vec<(F128, F128)> {
    let k_skip = K_SKIP;
    const N_INNER: usize = 7;
    assert!(m >= k_skip + N_INNER);
    let n_mlv = m - k_skip;
    let dense = PaddingSpec::dense(m);

    challenger.observe_label(b"flock-zerocheck-zk-v0");
    let r_skip = challenger.sample_f128_vec(k_skip);
    let r_outer = challenger.sample_f128_vec(m - k_skip - N_INNER);
    let mut r = vec![F128::ZERO; m];
    r[..k_skip].copy_from_slice(&r_skip);
    for (i, val) in small_challenges_ghash().iter().enumerate() {
        r[k_skip + i] = *val;
    }
    for (i, val) in medium_challenges_ghash().iter().enumerate() {
        r[k_skip + 3 + i] = *val;
    }
    r[k_skip + N_INNER..].copy_from_slice(&r_outer);
    let z = challenger.sample_f128();

    let fold_table = UniSkipFoldTable::new(k_skip, z);
    let mut mlv_arg = vec![F128::ONE; n_mlv];
    mlv_arg[1..].copy_from_slice(&r[k_skip + 1..]);
    let (mut p_mlv, mut q_mlv, mm2_1, mm2_inf) =
        uni_skip_fold_and_round_pair_optimized_packed_padded(
            p_packed, q_packed, m, k_skip, &fold_table, &mlv_arg, &dense,
        );
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

/// Verify an A1′ zerocheck proof. Checks the combined sumcheck equation
/// `running == â(ρ)·b̂(ρ) + γ·P(ρ)·Q(ρ)`. The caller MUST additionally
/// authenticate `proof.final_p_eval == P(ρ)` and `proof.final_q_eval == Q(ρ)`
/// against the `P, Q` commitments (through the PCS). Returns the standard
/// `ZerocheckClaim` (for the â·b̂/ĉ openings) on accept.
pub fn verify_zk<C: Challenger>(
    log_n: usize,
    proof: &ZkZerocheckProof,
    challenger: &mut C,
) -> Result<ZerocheckClaim, VerifyError> {
    let m = log_n;
    let k_skip = K_SKIP;
    const N_INNER: usize = 7;
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

    challenger.observe_label(b"flock-zerocheck-zk-v0");
    let r_skip = challenger.sample_f128_vec(k_skip);
    let r_outer = challenger.sample_f128_vec(m - k_skip - N_INNER);
    let mut r = vec![F128::ZERO; m];
    r[..k_skip].copy_from_slice(&r_skip);
    for (i, val) in small_challenges_ghash().iter().enumerate() {
        r[k_skip + i] = *val;
    }
    for (i, val) in medium_challenges_ghash().iter().enumerate() {
        r[k_skip + 3 + i] = *val;
    }
    r[k_skip + N_INNER..].copy_from_slice(&r_outer);

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
    let ab_init = combined_at_z + p_c_at_z;

    // Observe σ_z, sample γ — mirrors the prover; γ is bound to (root, σ_z).
    challenger.observe_f128(proof.mask_init);
    let gamma = challenger.sample_f128();

    // Combined initial claim.
    let mut c_running = ab_init + gamma * proof.mask_init;

    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    for (i, &(msg_1, msg_inf)) in proof.multilinear_rounds.iter().enumerate() {
        let r_eq = r[k_skip + i];
        let one_plus_r_eq = F128::ONE + r_eq;
        let g1 = msg_1;
        let g_inf = msg_inf;
        let g0 = (c_running + r_eq * g1) * one_plus_r_eq.inv();
        challenger.observe_f128(msg_1);
        challenger.observe_f128(msg_inf);
        let rho = challenger.sample_f128();
        mlv_rhos.push(rho);
        let one_plus_rho = F128::ONE + rho;
        c_running = g0 * one_plus_rho + g1 * rho + g_inf * rho * one_plus_rho;
    }

    // Combined final check: â(ρ)·b̂(ρ) + γ·P(ρ)·Q(ρ).
    let expected =
        proof.final_a_eval * proof.final_b_eval + gamma * proof.final_p_eval * proof.final_q_eval;
    if c_running != expected {
        return Err(VerifyError::SumcheckFinalFailed);
    }

    challenger.observe_f128(proof.final_a_eval);
    challenger.observe_f128(proof.final_b_eval);
    challenger.observe_f128(proof.final_p_eval);
    challenger.observe_f128(proof.final_q_eval);

    Ok(ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest: r[k_skip..].to_vec(),
        a_eval: proof.final_a_eval,
        b_eval: proof.final_b_eval,
        c_eval: proof.final_c_eval,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsChallenger;

    /// SplitMix64 PRNG, deterministic.
    struct Rng(u64);
    impl Rng {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
        fn bits(&mut self, n: usize) -> Vec<bool> {
            (0..n).map(|_| self.next_u64() & 1 == 1).collect()
        }
    }

    /// Pack three Boolean vectors into the (a_packed, b_packed, c_packed)
    /// shape that `prove_packed` consumes.
    fn pack_abc(a: &[bool], b: &[bool], c: &[bool]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        use univariate_skip::pack_bits;
        (pack_bits(a), pack_bits(b), pack_bits(c))
    }

    /// `prove` runs end-to-end at the smallest valid m (= k_skip + N_INNER = 13)
    /// without panicking, and produces output of the right shape.
    ///
    /// We can't yet check the proof is *accepted* (verify is a stub), but the
    /// structural sanity here catches:
    ///   - mismatched challenger observe/sample sequence
    ///   - wrong slice lengths in r / mlv_arg / r_next at any round
    ///   - any unreachable assert in the underlying functions
    #[test]
    fn prove_runs_end_to_end() {
        for &m in &[13usize, 14, 15, 16] {
            let mut rng = Rng::new(m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            // Honest witness: c = a AND b, so a·b ⊕ c = 0 on the hypercube.
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut challenger = FsChallenger::new(b"flock-test-v0");
            let (proof, claim) = prove_packed(&a_p, &b_p, &c_p, m, &mut challenger);

            // Shape checks.
            assert_eq!(proof.round1_ab.len(), 1usize << K_SKIP, "m={m}");
            assert_eq!(proof.round1_c.len(), 1usize << K_SKIP, "m={m}");
            assert_eq!(proof.multilinear_rounds.len(), m - K_SKIP, "m={m}");
            assert_eq!(claim.mlv_challenges.len(), m - K_SKIP, "m={m}");

            // Claim's eval fields agree with the proof's final evals.
            assert_eq!(claim.a_eval, proof.final_a_eval, "m={m}");
            assert_eq!(claim.b_eval, proof.final_b_eval, "m={m}");
            assert_eq!(claim.c_eval, proof.final_c_eval, "m={m}");
        }
    }

    /// **Prove→verify roundtrip**: an honest proof verifies cleanly, and the
    /// claim returned by `verify` is byte-for-byte equal to the claim returned
    /// by `prove`.
    #[test]
    fn prove_verify_roundtrip_honest() {
        for &m in &[13usize, 14, 15, 16] {
            let mut rng = Rng::new(1000 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = FsChallenger::new(b"flock-test-v0");
            let (proof, claim_p) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

            let mut ch_verify = FsChallenger::new(b"flock-test-v0");
            let result = verify(m, &proof, &mut ch_verify);
            let claim_v = result.unwrap_or_else(|e| panic!("verify rejected at m={m}: {e:?}"));

            assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");
        }
    }

    /// **A1′ combined masked zerocheck: prove→verify roundtrip.** With honest
    /// (a,b,c=a·b) and fresh random full-support (P,Q), the combined proof
    /// verifies under `verify_zk` (which checks the â(ρ)b̂(ρ)+γP(ρ)Q(ρ)
    /// equation). The mask never breaks completeness — the round messages
    /// carry `γ·M_j`, the initial claim carries `γ·σ_z`, and they telescope
    /// consistently.
    #[test]
    fn prove_verify_zk_roundtrip_honest() {
        for &m in &[13usize, 14, 15, 16] {
            let mut rng = Rng::new(2000 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
            let p = rng.bits(1 << m);
            let q = rng.bits(1 << m);
            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let (p_p, q_p, _) = pack_abc(&p, &q, &q);

            let mut ch_prove = FsChallenger::new(b"flock-zk-test-v0");
            let (proof, claim_p) =
                prove_packed_padded_zk(&a_p, &b_p, &c_p, &p_p, &q_p, m, &PaddingSpec::dense(m), &mut ch_prove);

            let mut ch_verify = FsChallenger::new(b"flock-zk-test-v0");
            let claim_v = verify_zk(m, &proof, &mut ch_verify)
                .unwrap_or_else(|e| panic!("verify_zk rejected honest proof at m={m}: {e:?}"));
            assert_eq!(claim_p, claim_v, "zk claim mismatch at m={m}");
        }
    }

    /// **A1′ soundness spot-checks.** Tampering the mask sum `σ_z`, either
    /// mask evaluation `P(ρ)`/`Q(ρ)`, or a combined round message must be
    /// rejected by `verify_zk`.
    #[test]
    fn verify_zk_rejects_mutations() {
        let m = 14;
        let mut rng = Rng::new(7070);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let p = rng.bits(1 << m);
        let q = rng.bits(1 << m);
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let (p_p, q_p, _) = pack_abc(&p, &q, &q);
        let mut ch_prove = FsChallenger::new(b"flock-zk-test-v0");
        let (proof, _) =
            prove_packed_padded_zk(&a_p, &b_p, &c_p, &p_p, &q_p, m, &PaddingSpec::dense(m), &mut ch_prove);

        let bump = F128 { lo: 0xABCD, hi: 0 };
        let mutate = |f: &dyn Fn(&mut ZkZerocheckProof)| {
            let mut bad = proof.clone();
            f(&mut bad);
            let mut ch = FsChallenger::new(b"flock-zk-test-v0");
            assert!(verify_zk(m, &bad, &mut ch).is_err());
        };
        mutate(&|pr| pr.mask_init += bump);
        mutate(&|pr| pr.final_p_eval += bump);
        mutate(&|pr| pr.final_q_eval += bump);
        mutate(&|pr| pr.multilinear_rounds[3].1 += bump);
        mutate(&|pr| pr.final_a_eval += bump);
        // Complete the matrix: every round pair, both components; round-1
        // entries on both vectors; the remaining finals; truncations.
        for i in 0..proof.multilinear_rounds.len() {
            mutate(&|pr| pr.multilinear_rounds[i].0 += bump);
            mutate(&|pr| pr.multilinear_rounds[i].1 += bump);
        }
        for k in [0usize, 1, 31, 63] {
            mutate(&|pr| pr.round1_ab[k] += bump);
            mutate(&|pr| pr.round1_c[k] += bump);
        }
        mutate(&|pr| pr.final_b_eval += bump);
        mutate(&|pr| pr.final_c_eval += bump);
        mutate(&|pr| {
            pr.multilinear_rounds.pop();
        });
        mutate(&|pr| {
            pr.round1_ab.pop();
        });
        mutate(&|pr| {
            pr.round1_c.truncate(1);
        });
    }

    /// **S1 — invalid witness rejected on the amended path.** The zk twin of
    /// `audit_false_statement_rejected`: one flipped `c` bit (so
    /// `a·b ⊕ c ≠ 0` somewhere) with an otherwise HONEST prover run and
    /// honest fresh masks must be rejected by `verify_zk`. The masked
    /// channel must not create an acceptance path for a false statement.
    #[test]
    fn zk_invalid_witness_rejected() {
        for &m in &[13usize, 14, 15] {
            let mut rng = Rng::new(0xA1_5000 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
            c[3] = !c[3];
            let p = rng.bits(1 << m);
            let q = rng.bits(1 << m);
            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let (p_p, q_p, _) = pack_abc(&p, &q, &q);

            let mut ch_prove = FsChallenger::new(b"flock-zk-test-v0");
            let (proof, _) = prove_packed_padded_zk(
                &a_p,
                &b_p,
                &c_p,
                &p_p,
                &q_p,
                m,
                &PaddingSpec::dense(m),
                &mut ch_prove,
            );
            let mut ch_verify = FsChallenger::new(b"flock-zk-test-v0");
            let res = verify_zk(m, &proof, &mut ch_verify);
            assert!(res.is_err(), "verify_zk ACCEPTED a false statement at m={m}: {res:?}");
        }
    }

    /// Replay `verify_zk`'s final-check residual for a given proof under
    /// `RandomChallenger(seed)`, with `mask_init` overridden. Uses the SAME
    /// in-crate primitives as `verify_zk` (interpolation + the fixed inner
    /// challenge schedule) — measurement instrumentation, not a parallel
    /// verifier. Returns `c_running + expected` (zero ⇔ final check passes).
    #[cfg(test)]
    fn zk_final_residual(m: usize, proof: &ZkZerocheckProof, seed: u64, mask_init: F128) -> F128 {
        use crate::challenger::RandomChallenger;
        let k_skip = K_SKIP;
        const N_INNER: usize = 7;
        let mut ch = RandomChallenger::new(seed);
        let _r_skip = ch.sample_f128_vec(k_skip);
        let r_outer = ch.sample_f128_vec(m - k_skip - N_INNER);
        let mut r = vec![F128::ZERO; m];
        for (i, val) in small_challenges_ghash().iter().enumerate() {
            r[k_skip + i] = *val;
        }
        for (i, val) in medium_challenges_ghash().iter().enumerate() {
            r[k_skip + 3 + i] = *val;
        }
        r[k_skip + N_INNER..].copy_from_slice(&r_outer);
        let z = ch.sample_f128();

        let combined_at_lambda: Vec<F128> = proof
            .round1_ab
            .iter()
            .zip(&proof.round1_c)
            .map(|(x, y)| *x + *y)
            .collect();
        let combined_at_z = interpolate_at_z_combined(&combined_at_lambda, k_skip, z);
        let p_c_at_z = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
        let ab_init = combined_at_z + p_c_at_z;
        let gamma = ch.sample_f128();
        let mut c_running = ab_init + gamma * mask_init;
        for (i, &(g1, g_inf)) in proof.multilinear_rounds.iter().enumerate() {
            let r_eq = r[k_skip + i];
            let one_plus_r_eq = F128::ONE + r_eq;
            let g0 = (c_running + r_eq * g1) * one_plus_r_eq.inv();
            let rho = ch.sample_f128();
            let one_plus_rho = F128::ONE + rho;
            c_running = g0 * one_plus_rho + g1 * rho + g_inf * rho * one_plus_rho;
        }
        let expected =
            proof.final_a_eval * proof.final_b_eval + gamma * proof.final_p_eval * proof.final_q_eval;
        c_running + expected
    }

    /// **S2 + S3 — γ-batching soundness, constructively, on the real code.**
    ///
    /// Lemma L6's content: for FIXED prover messages with zerocheck defect
    /// δ and mask-channel defect δ′, the verifier's final residual is an
    /// AFFINE function of `σ_z` with slope γ·Π(1+ρᵢ)/(1+r_eq,ᵢ) ≠ 0 —
    /// so for a prover who already knows γ there is EXACTLY ONE σ_z that
    /// cancels an invalid witness, and for a prover bound to send σ_z
    /// before γ (Fiat–Shamir) the cancellation succeeds with probability
    /// 2⁻¹²⁸. Demonstrated:
    ///  (a) an invalid-witness proof is rejected at its honest σ_z;
    ///  (b) the residual is affine in σ_z with nonzero slope — the solved
    ///      σ* is its unique root;
    ///  (c) under `RandomChallenger` (γ known in advance — the ordering
    ///      attack) the σ*-patched proof is ACCEPTED: choosing σ_z after γ
    ///      breaks soundness, so the transcript ordering is load-bearing;
    ///  (d) the SAME patched proof under `FsChallenger` is REJECTED — γ
    ///      re-derives from σ*, denying the prover the γ it solved against;
    ///  (e) at 100 fresh challenge tuples the patched proof is rejected
    ///      (the accepting tuple set is thin, as the 2⁻¹²⁸ bound predicts).
    #[test]
    fn zk_gamma_cancellation_unique_and_fs_ordering() {
        use crate::challenger::RandomChallenger;
        let m = 14;
        let seed = 0x6A77A_5EED;
        let mut rng = Rng::new(0xBAD_C0DE);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        c[7] = !c[7]; // invalid witness: nonzero zerocheck defect δ
        let p = rng.bits(1 << m);
        let q = rng.bits(1 << m);
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let (p_p, q_p, _) = pack_abc(&p, &q, &q);

        // Prove under the fixed (observation-independent) challenge tuple.
        let mut ch_prove = RandomChallenger::new(seed);
        let (proof, _) = prove_packed_padded_zk(
            &a_p,
            &b_p,
            &c_p,
            &p_p,
            &q_p,
            m,
            &PaddingSpec::dense(m),
            &mut ch_prove,
        );

        // (a) Rejected as-is.
        let mut ch = RandomChallenger::new(seed);
        assert!(
            verify_zk(m, &proof, &mut ch).is_err(),
            "invalid witness must be rejected at the honest σ_z"
        );

        // (b) Residual is affine in σ_z; solve for the unique root σ*.
        let r0 = zk_final_residual(m, &proof, seed, proof.mask_init);
        let r1 = zk_final_residual(m, &proof, seed, proof.mask_init + F128::ONE);
        let slope = r0 + r1; // affine over char 2: R(x+1) + R(x) = slope
        assert_ne!(r0, F128::ZERO, "defect must be visible in the residual");
        assert_ne!(slope, F128::ZERO, "σ_z slope γ·Π(1+ρ)/(1+r_eq) must be nonzero");
        let sigma_star = proof.mask_init + r0 * slope.inv();
        assert_eq!(
            zk_final_residual(m, &proof, seed, sigma_star),
            F128::ZERO,
            "σ* must be the root"
        );
        // Uniqueness: affine with nonzero slope ⇒ any other σ has nonzero
        // residual; spot-check a few.
        for k in 1..8u64 {
            let other = sigma_star + F128 { lo: k, hi: k.wrapping_mul(0x9E37) };
            assert_ne!(zk_final_residual(m, &proof, seed, other), F128::ZERO);
        }

        // (c) The ordering attack: with γ known in advance, the patched
        // proof is ACCEPTED by the real verifier.
        let mut cheat = proof.clone();
        cheat.mask_init = sigma_star;
        let mut ch = RandomChallenger::new(seed);
        assert!(
            verify_zk(m, &cheat, &mut ch).is_ok(),
            "σ_z chosen AFTER γ must cancel the invalid witness under a \
             fixed-challenge (ordering-violating) verifier — this is the \
             attack Fiat–Shamir ordering exists to prevent"
        );

        // (d) Under Fiat–Shamir the same proof is rejected: γ is derived
        // after σ_z is absorbed, so the solved-for γ never occurs.
        let mut ch_fs = FsChallenger::new(b"flock-zk-order-v0");
        assert!(
            verify_zk(m, &cheat, &mut ch_fs).is_err(),
            "FS-derived γ must deny the σ_z-after-γ cancellation"
        );

        // (e) Thin accepting set: 100 fresh challenge tuples all reject.
        for s in 0..100u64 {
            let mut ch = RandomChallenger::new(0x51DE_0000 + s);
            assert!(
                verify_zk(m, &cheat, &mut ch).is_err(),
                "patched proof accepted at unrelated challenge tuple {s}"
            );
        }
    }

    /// **Verify rejects byte-mutated proofs.** Walk each component of the
    /// proof and flip one F128 entry; the verifier must return an `Err`
    /// (rather than panicking or silently accepting).
    #[test]
    fn verify_rejects_mutations() {
        let m = 14;
        let mut rng = Rng::new(5050);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let _seed: u64 = 0xDEAD_BEEF;
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        // Each closure returns a mutated copy; verify must reject all of them.
        let mutations: Vec<(&str, Box<dyn Fn(&ZerocheckProof) -> ZerocheckProof>)> = vec![
            (
                "round1_ab[0] bit-flip",
                Box::new(|p| {
                    let mut q = p.clone();
                    q.round1_ab[0].lo ^= 1;
                    q
                }),
            ),
            (
                "round1_c[5] bit-flip",
                Box::new(|p| {
                    let mut q = p.clone();
                    q.round1_c[5].lo ^= 1;
                    q
                }),
            ),
            (
                "multilinear_rounds[0].0 bit-flip",
                Box::new(|p| {
                    let mut q = p.clone();
                    q.multilinear_rounds[0].0.lo ^= 1;
                    q
                }),
            ),
            (
                "multilinear_rounds[2].1 bit-flip",
                Box::new(|p| {
                    let mut q = p.clone();
                    let last = q.multilinear_rounds.len() / 2;
                    q.multilinear_rounds[last].1.hi ^= 1;
                    q
                }),
            ),
            (
                "final_a_eval bit-flip",
                Box::new(|p| {
                    let mut q = p.clone();
                    q.final_a_eval.lo ^= 1;
                    q
                }),
            ),
            (
                "final_c_eval bit-flip",
                Box::new(|p| {
                    let mut q = p.clone();
                    q.final_c_eval.hi ^= 1;
                    q
                }),
            ),
        ];

        for (label, mutate) in mutations {
            let bad = mutate(&proof);
            let mut ch = FsChallenger::new(b"flock-test-v0");
            let result = verify(m, &bad, &mut ch);
            assert!(
                result.is_err(),
                "verify accepted mutated proof ({label}) — should have rejected"
            );
        }
    }

    /// Shape rejections: too-short round1, wrong number of multilinear rounds.
    #[test]
    fn verify_rejects_shape_errors() {
        let m = 14;
        let mut rng = Rng::new(606);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        // Truncate round1_ab.
        let mut bad = proof.clone();
        bad.round1_ab.pop();
        let mut ch = FsChallenger::new(b"flock-test-v0");
        assert!(matches!(
            verify(m, &bad, &mut ch),
            Err(VerifyError::BadRound1Length { .. })
        ));

        // Truncate multilinear rounds.
        let mut bad = proof.clone();
        bad.multilinear_rounds.pop();
        let mut ch = FsChallenger::new(b"flock-test-v0");
        assert!(matches!(
            verify(m, &bad, &mut ch),
            Err(VerifyError::BadMultilinearRoundsLength { .. })
        ));

        // log_n too small.
        let mut ch = FsChallenger::new(b"flock-test-v0");
        assert!(matches!(
            verify(K_SKIP + 6, &proof, &mut ch),
            Err(VerifyError::LogNTooSmall { .. })
        ));
    }

    /// AUDIT: a FALSE statement (c ≠ a·b at some hypercube point) must be
    /// rejected, even though the prover follows the honest algorithm on its
    /// (dishonest) witness.
    #[test]
    fn audit_false_statement_rejected() {
        for &m in &[13usize, 14, 15] {
            let mut rng = Rng::new(7777 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            // Correct c, then corrupt ONE bit so a·b ⊕ c ≠ 0 somewhere.
            let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
            c[3] = !c[3];

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = FsChallenger::new(b"flock-test-v0");
            let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

            let mut ch_verify = FsChallenger::new(b"flock-test-v0");
            let res = verify(m, &proof, &mut ch_verify);
            assert!(
                res.is_err(),
                "verify ACCEPTED a false statement at m={m}: {res:?}"
            );
        }
    }

    /// AUDIT: flipping any round's `msg_inf` (the degree-2 / ∞ coefficient)
    /// must be rejected. `msg_inf` is observed into the transcript, so the
    /// tamper both reshuffles subsequent ρ challenges and breaks the
    /// running-claim chain — either way the final check fails.
    #[test]
    fn audit_round_msg_inf_tamper_rejected() {
        let m = 14;
        let mut rng = Rng::new(424242);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        // For each round, flip msg_inf to a different value. Because msg_inf
        // is observed into the transcript, this reshuffles subsequent rho's;
        // a sound verifier should reject (overwhelming probability).
        for idx in 0..proof.multilinear_rounds.len() {
            let mut bad = proof.clone();
            bad.multilinear_rounds[idx].1 += F128::ONE;
            let mut ch = FsChallenger::new(b"flock-test-v0");
            let res = verify(m, &bad, &mut ch);
            assert!(res.is_err(), "msg_inf tamper at round {idx} ACCEPTED");
        }
    }

    /// AUDIT: the LAST round's `msg_inf` must be constrained — a common
    /// off-by-one is to leave the final round's leading coefficient unchecked.
    /// Kept separate from the all-rounds loop above so a regression here points
    /// straight at the final-round binding.
    #[test]
    fn audit_last_round_inf_constrained() {
        let m = 13;
        let mut rng = Rng::new(98765);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        let last = proof.multilinear_rounds.len() - 1;
        let mut bad = proof.clone();
        bad.multilinear_rounds[last].1 += F128::ONE;
        let mut ch = FsChallenger::new(b"flock-test-v0");
        assert!(
            verify(m, &bad, &mut ch).is_err(),
            "last-round msg_inf unconstrained"
        );
    }

    /// AUDIT (Fiat–Shamir binding of the final â, b̂ claims). Regression test
    /// for the gap where `final_a_eval`/`final_b_eval` were not observed into
    /// the transcript.
    ///
    /// Downstream, lincheck reduces these two claims via a *single* random-
    /// linear-combination check (`target = α·v_a + v_b`). That batching is only
    /// sound if α is sampled *after* the claims are bound to the transcript —
    /// otherwise a prover that already knows α can pick (v_a, v_b) to satisfy
    /// the one batched equation while violating the individual ties.
    ///
    /// A *product-preserving* tamper `(â, b̂) → (â·t, b̂·t⁻¹)` leaves the
    /// zerocheck's own final check `c_running == â·b̂` satisfied, so `verify`
    /// still returns `Ok` — the zerocheck alone is blind to it. The defense is
    /// that both claims are now observed last in the transcript, so the next
    /// challenge (the slot lincheck draws α from) must diverge from the honest
    /// run. This assertion FAILS before the observe was added (identical
    /// post-state) and passes now.
    #[test]
    fn audit_final_ab_claims_bound_to_transcript() {
        let m = 14;
        let mut rng = Rng::new(0xF1A7_5A11);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

        // Honest verify, then capture the next challenge the transcript feeds
        // downstream — this is exactly the slot lincheck samples α from.
        let mut ch_honest = FsChallenger::new(b"flock-test-v0");
        assert!(
            verify(m, &proof, &mut ch_honest).is_ok(),
            "honest verify rejected"
        );
        let alpha_honest = ch_honest.sample_f128();

        // Product-preserving tamper: â' = â·t, b̂' = b̂·t⁻¹ ⇒ â'·b̂' = â·b̂, so the
        // zerocheck's `c_running == â·b̂` check still holds for the tampered pair.
        let t = F128 {
            lo: 0x0123_4567_89ab_cdef,
            hi: 0xfedc_ba98_7654_3210,
        };
        assert!(t != F128::ZERO && t != F128::ONE, "t must be nontrivial");
        let mut bad = proof.clone();
        bad.final_a_eval *= t;
        bad.final_b_eval *= t.inv();
        assert_ne!(bad.final_a_eval, proof.final_a_eval, "tamper must change â");
        assert_ne!(bad.final_b_eval, proof.final_b_eval, "tamper must change b̂");
        assert_eq!(
            bad.final_a_eval * bad.final_b_eval,
            proof.final_a_eval * proof.final_b_eval,
            "tamper must preserve the product",
        );

        // The zerocheck's own checks are blind to a product-preserving tamper:
        // verify still ACCEPTS. This is precisely the gap the FS binding closes —
        // the tamper is caught only because the claims now move the transcript.
        let mut ch_tampered = FsChallenger::new(b"flock-test-v0");
        assert!(
            verify(m, &bad, &mut ch_tampered).is_ok(),
            "product-preserving tamper rejected by zerocheck's own checks (unexpected)",
        );
        let alpha_tampered = ch_tampered.sample_f128();

        // The fix: observing â, b̂ makes the downstream challenge depend on them,
        // so lincheck's α (and everything after) diverges and rejects the
        // tampered pair. Before the fix these challenges were equal.
        assert_ne!(
            alpha_honest, alpha_tampered,
            "final â/b̂ claims are NOT bound into the transcript: a product-preserving \
             tamper leaves the downstream challenge unchanged, breaking lincheck's \
             α-batched reduction of (v_a, v_b)",
        );
    }

    /// AUDIT: many random false witnesses must all be rejected. Stronger than a
    /// single corruption — exercises the full prove→verify path on statements
    /// that are false at varying numbers of hypercube points.
    #[test]
    fn audit_many_false_statements_rejected() {
        let m = 13;
        for seed in 0..20u64 {
            let mut rng = Rng::new(0xBADC0DE ^ seed);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
            // Flip a random number of bits (1..=4).
            let nflip = 1 + (rng.next_u64() as usize % 4);
            for _ in 0..nflip {
                let idx = rng.next_u64() as usize % c.len();
                c[idx] = !c[idx];
            }
            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = FsChallenger::new(b"flock-test-v0");
            let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
            let mut ch_verify = FsChallenger::new(b"flock-test-v0");
            let res = verify(m, &proof, &mut ch_verify);
            assert!(
                res.is_err(),
                "false statement (seed={seed}) ACCEPTED: {res:?}"
            );
        }
    }

    /// AUDIT: tamper msg_1 in each round; must reject.
    #[test]
    fn audit_round_msg_1_tamper_rejected() {
        let m = 14;
        let mut rng = Rng::new(31415);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = FsChallenger::new(b"flock-test-v0");
        let (proof, _) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        for idx in 0..proof.multilinear_rounds.len() {
            let mut bad = proof.clone();
            bad.multilinear_rounds[idx].0 += F128::ONE;
            let mut ch = FsChallenger::new(b"flock-test-v0");
            assert!(
                verify(m, &bad, &mut ch).is_err(),
                "msg_1 tamper round {idx} ACCEPTED"
            );
        }
    }

    /// Determinism: same witness + same challenger seed → same proof.
    #[test]
    fn prove_deterministic() {
        let m = 14;
        let mut rng = Rng::new(99);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch1 = FsChallenger::new(b"flock-test-v0");
        let mut ch2 = FsChallenger::new(b"flock-test-v0");
        let (proof1, claim1) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch1);
        let (proof2, claim2) = prove_packed(&a_p, &b_p, &c_p, m, &mut ch2);

        assert_eq!(proof1.round1_ab, proof2.round1_ab);
        assert_eq!(proof1.round1_c, proof2.round1_c);
        assert_eq!(proof1.multilinear_rounds, proof2.multilinear_rounds);
        assert_eq!(proof1.final_a_eval, proof2.final_a_eval);
        assert_eq!(proof1.final_b_eval, proof2.final_b_eval);
        assert_eq!(proof1.final_c_eval, proof2.final_c_eval);
        assert_eq!(claim1.z, claim2.z);
        assert_eq!(claim1.mlv_challenges, claim2.mlv_challenges);
    }
}

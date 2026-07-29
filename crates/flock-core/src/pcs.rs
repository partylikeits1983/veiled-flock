//! Polynomial commitment scheme for the bit-MLE witness `ẑ` over GF(2).
//!
//! Construction: Binius-style PCS with F_{2^128} packing.
//!
//! - **Commit**: pack the 2^m Boolean witness into 2^(m−7) F_{2^128} elements
//!   (one bit per polynomial-basis coordinate of F_{2^128}), batch RS-encode
//!   via additive NTT, Merkle-commit the codeword.
//! - **Open**: at a QuirkyPoint (z_skip, x_outer) from the zerocheck/lincheck:
//!   1. [`ring_switch::prove`] sends 128 partial-evaluations `s_hat_v` and
//!      produces a sumcheck target `(rs_eq_ind, sumcheck_claim)`.
//!   2. [`ligerito::recursive_prover_with_basis`] discharges the combined
//!      claim `⟨packed_witness, b_combined⟩ = target_combined` via the
//!      recursive Ligerito argument, reusing the commit-time codeword and
//!      Merkle tree as Ligerito's L0 commitment.
//! - **Verify**: the verifier replays ring-switching succinctly, then drives
//!   the succinct recursive Ligerito verifier, evaluating the combined basis
//!   at the residual point (see [`verify_opening_batch_ligerito_mixed`]).
//!
//! See [DP24](https://eprint.iacr.org/2024/504) (ring-switching) and the
//! ligerito module docs for the recursion.

pub mod commit;
pub mod jagged;
pub mod ligerito;
pub mod pack;
pub mod ring_switch;
#[cfg(feature = "symbolic")]
pub mod symbolic_opening;
pub mod tensor_algebra;
#[cfg(all(test, feature = "zk"))]
mod zk_audit;

#[cfg(feature = "zk")]
pub use commit::commit_zk_with_ro;
pub use commit::{
    Commitment, PcsParams, ProverData, commit, commit_into, commit_into_with_ro, commit_with_ro,
    prefault_codeword_during,
};
pub use pack::{LOG_PACKING, pack_witness, unpack_witness};
pub use ring_switch::{RingSwitchProof, SparseEqTensor};

use crate::challenger::Challenger;
use crate::field::F128;
use crate::zerocheck::PaddingSpec;
use serde::{Deserialize, Serialize};

/// Batched opening proof: ring-switching frontend + Ligerito backend.
/// The combined `b_combined` + target_combined feed
/// [`ligerito::recursive_prover_with_basis`] (see ligerito module docs).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchOpeningProofLigerito {
    pub ring_switches: Vec<RingSwitchProof>,
    pub ligerito: ligerito::LigeritoProof,
    /// zk mode only: the blinder-combination opening. `y_g = ⟨g_top,
    /// b_combined⟩` is observed BEFORE the combination challenge `c` is
    /// sampled (soundness-critical: `y_g` shifts the combined target), with a
    /// PoW grind pricing the extra fold round. `None` for non-zk proofs
    /// (serde-default keeps old proofs readable).
    #[serde(default)]
    pub zk_blind: Option<ZkBlindOpening>,
}

/// The zk blinder opening data (see [`BatchOpeningProofLigerito::zk_blind`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZkBlindOpening {
    pub y_g: F128,
    pub c_grind_nonce: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    RingSwitch(ring_switch::VerifyError),
    /// The Ligerito recursive verifier rejected the proof.
    Ligerito,
}

/// `eq_ind` representation for a packed-direct claim. The contributed value at
/// scattered index `j` is the tensor entry — for the dense variant the index
/// is the array offset; for the sparse variant it's reconstructed via
/// [`SparseEqTensor::scatter_idx`].
#[derive(Clone, Debug)]
pub enum DirectEqInd {
    /// Fully-materialized `eq_ind(point)` of length `2^L`.
    Dense(Vec<F128>),
    /// Sparse representation — non-zero entries at scattered indices.
    /// Built from a claim point with one or more exactly-zero coords via
    /// [`ring_switch::build_eq_sparse`].
    Sparse(SparseEqTensor),
}

/// A packed-MLE evaluation claim: `ẑ_packed(point) = value`. Unlike a
/// ring-switched claim, this is opened directly without going through the
/// bit-MLE ↔ packed-MLE bridge (no `s_hat_v`, no φ_8 weighting).
///
/// Use case: protocols whose sumcheck output is naturally a packed-MLE
/// evaluation (e.g. the chain shift sumcheck operating on packed columns
/// instead of bit-folded scalars). Skips the ring-switch step for this claim,
/// saving the `fold_1b_rows` + per-opening-tail work at the prover and the
/// ring-switch verify + φ_8 reconstruction at the verifier.
///
/// The claim-combine step adds `γ_k · eq_ind(point)` to `b_combined` and
/// `γ_k · value` to the target; the verifier's residual check contributes
/// `γ_k · eq_eval(point, residual_challenges)`.
#[derive(Clone, Debug)]
pub struct PackedDirectClaim {
    /// Multilinear point of length `L = m − 7`.
    pub point: Vec<F128>,
    /// Claimed `ẑ_packed(point)` value.
    pub value: F128,
    /// `eq_ind(point)` in dense or sparse form. Caller responsibility to
    /// match the claim's `point` — the contribution to `b_combined` is read
    /// directly from this tensor.
    pub eq_ind: DirectEqInd,
}

/// A claim against an arbitrary public linear functional of the packed
/// message. This is the general form of [`PackedDirectClaim`]: `basis` has
/// exactly the packed-message length and the claim asserts
/// `dot(packed_witness, basis) = value`.
#[derive(Clone, Debug)]
pub struct PackedLinearClaim {
    pub basis: Vec<F128>,
    pub value: F128,
}

/// Mixed-claim batched open: supports both **ring-switched** claims (bit-MLE
/// openings reduced via `ring_switch::prove_batched`, with optional per-claim
/// precomputed `s_hat_v`) and **packed-direct** claims (packed-MLE openings
/// that skip ring-switch). Runs the ring_switch + b_combined computation, then
/// routes to [`ligerito::recursive_prover_with_basis`] using the existing
/// `prover_data`'s codeword + tree as Ligerito's L0 commit (no L0 re-commit).
///
/// `lig_config.initial_k` must equal `commitment.params.log_batch_size` so that
/// `prover_data`'s codeword/tree shape matches what Ligerito expects for L0.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed_ligerito_with_precomputed_s_hat_v<Ch: Challenger>(
    packed_witness: Vec<F128>,
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[PackedDirectClaim],
    padding: &PaddingSpec,
    lig_config: &ligerito::ProverConfig,
    challenger: &mut Ch,
) -> BatchOpeningProofLigerito {
    let ro = crate::ro::RoContext::plain();
    open_batch_mixed_ligerito_with_precomputed_s_hat_v_ro(
        packed_witness,
        prover_data,
        commitment,
        x_outers,
        precomputed_s_hat_v,
        packed_direct,
        padding,
        lig_config,
        &ro,
        crate::ro::RoChannel::Witness,
        challenger,
    )
}

/// Mixed batch opening with an explicit point-oracle context and channel.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed_ligerito_with_precomputed_s_hat_v_ro<Ch: Challenger>(
    packed_witness: Vec<F128>,
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[PackedDirectClaim],
    padding: &PaddingSpec,
    lig_config: &ligerito::ProverConfig,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> BatchOpeningProofLigerito {
    open_batch_mixed_ligerito_with_precomputed_s_hat_v_linear_ro(
        packed_witness,
        prover_data,
        commitment,
        x_outers,
        precomputed_s_hat_v,
        packed_direct,
        &[],
        padding,
        lig_config,
        ro,
        channel,
        challenger,
    )
}

/// Mixed batch opening with additional arbitrary public linear claims.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed_ligerito_with_precomputed_s_hat_v_linear_ro<Ch: Challenger>(
    packed_witness: Vec<F128>,
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[PackedDirectClaim],
    packed_linear: &[PackedLinearClaim],
    padding: &PaddingSpec,
    lig_config: &ligerito::ProverConfig,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> BatchOpeningProofLigerito {
    let trace = std::env::var("PCS_TRACE").is_ok();
    let t_total = std::time::Instant::now();

    assert_eq!(
        lig_config.initial_k, commitment.params.log_batch_size,
        "ligerito initial_k ({}) must match PcsParams.log_batch_size ({}) for L0 reuse",
        lig_config.initial_k, commitment.params.log_batch_size,
    );
    assert_eq!(
        lig_config.log_inv_rates[0], commitment.params.log_inv_rate,
        "ligerito log_inv_rates[0] ({}) must match PcsParams.log_inv_rate ({}) for L0 reuse",
        lig_config.log_inv_rates[0], commitment.params.log_inv_rate,
    );

    let combined = compute_combined_basis_and_target(
        &packed_witness,
        x_outers,
        precomputed_s_hat_v,
        packed_direct,
        packed_linear,
        padding,
        challenger,
        trace,
    );

    let CombinedClaim {
        ring_switches,
        b_combined,
        target_combined,
        round0_prime,
    } = combined;

    let t = std::time::Instant::now();
    let (ligerito_proof, zk_blind) = if commitment.params.zk {
        #[cfg(feature = "zk")]
        {
            let (p, b) = open_zk_blinded(
                packed_witness,
                prover_data,
                b_combined,
                target_combined,
                round0_prime,
                lig_config,
                ro,
                channel,
                challenger,
            );
            (p, Some(b))
        }
        #[cfg(not(feature = "zk"))]
        unreachable!("PcsParams.zk requires the `zk` cargo feature")
    } else {
        let p = ligerito::recursive_prover_with_basis_precomputed_round0_with_ro(
            lig_config,
            packed_witness,
            b_combined,
            target_combined,
            &prover_data.codeword,
            &prover_data.merkle_tree,
            round0_prime,
            ro,
            channel,
            challenger,
        );
        (p, None)
    };
    if trace {
        eprintln!(
            "  [open_batch] ligerito::recursive_prover_with_basis: {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
        eprintln!(
            "  [open_batch] TOTAL: {:6.2} ms",
            t_total.elapsed().as_secs_f64() * 1e3
        );
    }

    BatchOpeningProofLigerito {
        ring_switches,
        ligerito: ligerito_proof,
        zk_blind,
    }
}

/// zk open path: combine the blinder `g` into the folded vector.
///
/// Steps (transcript-order is soundness-critical):
/// 1. `y_g = ⟨g_top, b_combined⟩` (+ its round-0 prime terms) — one pass.
/// 2. Observe `y_g`; PoW-grind `fold_grinding_bits[0]+1` bits (the `c`
///    combination is one extra interleave-fold round); sample `c`.
/// 3. Materialize `F = [mask + c·g_lo ‖ z_packed + c·g_top]` and
///    `b′ = [0 ‖ b_combined]`; shift target and round-0 prime by `c·(…)`.
/// 4. Run the unchanged Ligerito recursion on `(F, b′)` with wide-leaf L0.
#[cfg(feature = "zk")]
fn open_zk_blinded<Ch: Challenger>(
    packed_witness: Vec<F128>,
    prover_data: &ProverData,
    b_combined: Vec<F128>,
    target_combined: F128,
    round0_prime: (F128, F128),
    lig_config: &ligerito::ProverConfig,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> (ligerito::LigeritoProof, ZkBlindOpening) {
    use rayon::prelude::*;
    let w = packed_witness.len();
    assert_eq!(prover_data.zk_mask.len(), w, "commit_zk mask missing");
    assert_eq!(
        prover_data.zk_blind.len(),
        2 * w,
        "commit_zk blinder missing"
    );
    let g = &prover_data.zk_blind;
    let g_top = &g[w..];

    // (1) y_g and the blinder's round-0 prime contribution, one fused pass.
    //     Pairing is the wide LSB pairing restricted to the top half, which
    //     coincides with the witness-space pairing (w is even).
    let (u0g, u2g, y_g) = g_top
        .par_chunks(2)
        .zip(b_combined.par_chunks(2))
        .map(|(gp, bp)| {
            let u0 = gp[0] * bp[0];
            let u2 = (gp[0] + gp[1]) * (bp[0] + bp[1]);
            (u0, u2, u0 + gp[1] * bp[1])
        })
        .reduce(
            || (F128::ZERO, F128::ZERO, F128::ZERO),
            |(a0, a2, ay), (b0, b2, by)| (a0 + b0, a2 + b2, ay + by),
        );

    // (2) y_g before c — a prover that could pick y_g after seeing c could
    //     shift the combined target to prove a false claim.
    challenger.observe_label(b"flock-pcs-zk-blind-v0");
    challenger.observe_f128(y_g);
    let c_bits = lig_config.fold_grinding_bits.first().copied().unwrap_or(0) as u32 + 1;
    let c_grind_nonce = challenger.grind_pow(c_bits);
    let c = challenger.sample_f128();

    // (3) F = message′ + c·g and the offset-embedded basis b′ = [0 ‖ b].
    let mut f_blinded = crate::scratch::take_f128(2 * w);
    {
        let (lo, hi) = f_blinded.split_at_mut(w);
        lo.par_iter_mut().enumerate().for_each(|(i, s)| {
            *s = prover_data.zk_mask[i] + c * g[i];
        });
        hi.par_iter_mut().enumerate().for_each(|(i, s)| {
            *s = packed_witness[i] + c * g_top[i];
        });
    }
    let mut b_wide = crate::scratch::take_f128(2 * w);
    {
        let (lo, hi) = b_wide.split_at_mut(w);
        lo.par_iter_mut().for_each(|s| *s = F128::ZERO);
        hi.copy_from_slice(&b_combined);
    }
    crate::scratch::give_f128(b_combined);
    crate::scratch::give_f128(packed_witness);

    let target_prime = target_combined + c * y_g;
    let prime_wide = (round0_prime.0 + c * u0g, round0_prime.1 + c * u2g);

    let proof = ligerito::recursive_prover_with_basis_precomputed_round0_zk_with_ro(
        lig_config,
        f_blinded,
        b_wide,
        target_prime,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        prime_wide,
        ligerito::ZkL0 { c },
        ro,
        channel,
        challenger,
    );
    (proof, ZkBlindOpening { y_g, c_grind_nonce })
}

/// What ring_switch + claim-combination produces, fed to the Ligerito backend.
struct CombinedClaim {
    ring_switches: Vec<RingSwitchProof>,
    b_combined: Vec<F128>,
    target_combined: F128,
    /// Round-0 sumcheck `(u_0, u_2)` prime over `packed_witness · b_combined`,
    /// consumed by `recursive_prover_with_basis_precomputed_round0`.
    round0_prime: (F128, F128),
}

/// Runs ring_switch over RS claims, observes packed-direct claim values +
/// samples their gammas, then builds `b_combined` (the γ-weighted linear
/// combination of all `rs_eq_ind`s and `eq_ind`s) and `target_combined`.
/// Also computes the round-0 prime as a side effect (cheap since it shares
/// the b_combined pass).
#[allow(clippy::too_many_arguments)]
fn compute_combined_basis_and_target<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[PackedDirectClaim],
    packed_linear: &[PackedLinearClaim],
    padding: &PaddingSpec,
    challenger: &mut Ch,
    trace: bool,
) -> CombinedClaim {
    let n_rs = x_outers.len();
    let n_pd = packed_direct.len();
    let n_pl = packed_linear.len();
    assert!(
        n_rs + n_pd + n_pl > 0,
        "open_batch_mixed: need at least one claim"
    );
    assert!(
        precomputed_s_hat_v.is_empty() || precomputed_s_hat_v.len() == n_rs,
        "precomputed_s_hat_v: must be empty or length {n_rs}, got {}",
        precomputed_s_hat_v.len(),
    );

    challenger.observe_label(b"flock-pcs-open-batch-v0");

    // 1. Ring-switching for all x_outers.
    let t = std::time::Instant::now();
    let (rs_results, gammas_rs): (
        Vec<(RingSwitchProof, ring_switch::RingSwitchBatchOutput)>,
        Vec<F128>,
    ) = if n_rs > 0 {
        ring_switch::prove_batched_padded_with_precomputed(
            packed_witness,
            x_outers,
            precomputed_s_hat_v,
            padding,
            challenger,
        )
    } else {
        (Vec::new(), Vec::new())
    };
    if trace {
        eprintln!(
            "  [open_batch] ring_switch::prove_batched ×{}: {:6.2} ms",
            n_rs,
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    // 2. Observe packed-direct claim values + sample γ_pd.
    for pd in packed_direct {
        challenger.observe_label(b"flock-pcs-packed-direct-v0");
        challenger.observe_f128(pd.value);
    }
    for pl in packed_linear {
        challenger.observe_label(b"flock-pcs-packed-linear-v0");
        challenger.observe_f128(pl.value);
    }
    let gammas_pd: Vec<F128> = (0..n_pd).map(|_| challenger.sample_f128()).collect();
    let gammas_pl: Vec<F128> = (0..n_pl).map(|_| challenger.sample_f128()).collect();

    let t = std::time::Instant::now();
    use rayon::prelude::*;

    let l = if let Some((_, out)) = rs_results.first() {
        out.rs_eq_ind.len()
    } else if let Some(pd) = packed_direct.first() {
        1usize << pd.point.len()
    } else {
        packed_linear[0].basis.len()
    };
    debug_assert!(rs_results.iter().all(|(_, o)| o.rs_eq_ind.len() == l));
    debug_assert!(
        packed_direct.iter().all(|pd| 1usize << pd.point.len() == l),
        "all packed-direct claims must share L (= packed witness length)"
    );
    debug_assert!(
        packed_linear.iter().all(|pl| pl.basis.len() == l),
        "all packed-linear claims must share L (= packed witness length)"
    );

    let mut target_combined = F128::ZERO;
    for ((_, output), g) in rs_results.iter().zip(gammas_rs.iter()) {
        target_combined += *g * output.sumcheck_claim;
    }
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        target_combined += *g * pd.value;
    }
    for (pl, g) in packed_linear.iter().zip(gammas_pl.iter()) {
        target_combined += *g * pl.value;
    }

    let rs_baked: Vec<&[F128]> = rs_results
        .iter()
        .filter_map(|(_, o)| match &o.rs_eq_ind {
            ring_switch::RsEqInd::Dense(v) => Some(v.as_slice()),
            _ => None,
        })
        .collect();
    // Deferred-dense claims (fused fast path): the per-claim `γ_k·B_k` buffer
    // was never materialized — fold each slot on the fly below and accumulate
    // straight into `b_combined`, saving a 2^(m-7) materialize + readback per
    // claim. Carries (eq_lo, eq_hi, γ-baked table, log₂ B).
    let rs_deferred: Vec<(&[F128], &[F128], &[F128], usize)> = rs_results
        .iter()
        .filter_map(|(_, o)| match &o.rs_eq_ind {
            ring_switch::RsEqInd::DeferredDense {
                eq_lo,
                eq_hi,
                table,
            } => Some((
                eq_lo.as_slice(),
                eq_hi.as_slice(),
                table.as_slice(),
                eq_lo.len().trailing_zeros() as usize,
            )),
            _ => None,
        })
        .collect();
    let pd_dense: Vec<(&[F128], F128)> = packed_direct
        .iter()
        .zip(gammas_pd.iter())
        .filter_map(|(pd, g)| match &pd.eq_ind {
            DirectEqInd::Dense(v) => Some((v.as_slice(), *g)),
            _ => None,
        })
        .collect();
    let pl_dense: Vec<(&[F128], F128)> = packed_linear
        .iter()
        .zip(gammas_pl.iter())
        .map(|(pl, g)| (pl.basis.as_slice(), *g))
        .collect();

    // ---- Build b_combined (γ-weighted sum of all rs_eq_ind + eq_ind) and the
    //      round-0 prime (u_0, u_2 over packed_witness · b_combined).
    let mut b_combined: Vec<F128> = crate::scratch::take_f128(l);

    // Fast path (compression-proof open: claims ab, c; also chain/merkle): every
    // RS claim is a fused DeferredDense fold and no DENSE packed-direct claim
    // needs the per-element combine. Fold all claims block-by-block straight into
    // b_combined — each claim's `e_hi` hoisted once per block, exactly as in
    // `fold_b128_elems_split` — and fuse the round-0 prime in the same pass.
    // Neither the per-claim `γ_k·B_k` buffer nor a combine readback is ever
    // materialized (saves ~2·L writes + 2·L reads of the 2^(m-7) basis).
    //
    // SPARSE packed-direct claims (the chain/merkle I/O claim) do NOT disable
    // this path: they're scatter-added onto b_combined after the fold (with an
    // incremental round-0 prime adjustment), so they only require
    // `pd_dense.is_empty()`, not `packed_direct.is_empty()`. This keeps the two
    // big ab/c claims on the fused fold instead of materializing them.
    let use_fast = !rs_deferred.is_empty()
        && rs_deferred.len() == rs_results.len()
        && pd_dense.is_empty()
        && pl_dense.is_empty();

    let (mut round0_u0, mut round0_u2) = if use_fast {
        let b = rs_deferred[0].0.len(); // eq_lo.len(); shared across claims (same split)
        debug_assert!(b >= 2 && b.is_multiple_of(2));
        debug_assert!(rs_deferred.iter().all(|d| d.0.len() == b));
        b_combined
            .par_chunks_mut(b)
            .enumerate()
            .map(|(hi, out_block)| {
                // Accumulate each claim's block: first claim writes, rest add.
                // `e_hi` is read once per claim per block, then swept over eq_lo.
                for (ci, (eq_lo, eq_hi, table, _)) in rs_deferred.iter().enumerate() {
                    let e_hi = eq_hi[hi];
                    if ci == 0 {
                        for (slot, &lo) in out_block.iter_mut().zip(eq_lo.iter()) {
                            *slot = ring_switch::fold_one_slot(lo * e_hi, table);
                        }
                    } else {
                        for (slot, &lo) in out_block.iter_mut().zip(eq_lo.iter()) {
                            *slot += ring_switch::fold_one_slot(lo * e_hi, table);
                        }
                    }
                }
                // Round-0 prime over this block's pairs (b is even, base is even).
                let base = hi * b;
                let mut u0 = F128::ZERO;
                let mut u2 = F128::ZERO;
                for t in 0..(b / 2) {
                    let s0 = out_block[2 * t];
                    let s1 = out_block[2 * t + 1];
                    let a0 = packed_witness[base + 2 * t];
                    let a1 = packed_witness[base + 2 * t + 1];
                    u0 += a0 * s0;
                    u2 += (a0 + a1) * (s0 + s1);
                }
                (u0, u2)
            })
            .reduce(
                || (F128::ZERO, F128::ZERO),
                |(x0, x2), (y0, y2)| (x0 + y0, x2 + y2),
            )
    } else {
        // General path (mixed / sparse / packed-direct): materialize any
        // deferred-dense claims (parallel block fold), then the per-element
        // combine over all dense buffers + packed-direct, matching the
        // original behavior.
        let materialized: Vec<Vec<F128>> = rs_results
            .iter()
            .filter_map(|(_, o)| match &o.rs_eq_ind {
                ring_switch::RsEqInd::DeferredDense {
                    eq_lo,
                    eq_hi,
                    table,
                } => Some(ring_switch::fold_b128_from_table(eq_lo, eq_hi, table)),
                _ => None,
            })
            .collect();
        let mut rs_dense_all: Vec<&[F128]> = rs_baked.clone();
        rs_dense_all.extend(materialized.iter().map(|v| v.as_slice()));
        let prime = b_combined
            .par_chunks_mut(2)
            .enumerate()
            .map(|(i, chunk)| {
                let mut b0 = F128::ZERO;
                let mut b1 = F128::ZERO;
                for v in rs_dense_all.iter() {
                    b0 += v[2 * i];
                    b1 += v[2 * i + 1];
                }
                for (v, g) in pd_dense.iter() {
                    b0 += *g * v[2 * i];
                    b1 += *g * v[2 * i + 1];
                }
                for (v, g) in pl_dense.iter() {
                    b0 += *g * v[2 * i];
                    b1 += *g * v[2 * i + 1];
                }
                chunk[0] = b0;
                chunk[1] = b1;
                let a0 = packed_witness[2 * i];
                let a1 = packed_witness[2 * i + 1];
                (a0 * b0, (a0 + a1) * (b0 + b1))
            })
            .reduce(
                || (F128::ZERO, F128::ZERO),
                |(x0, x2), (y0, y2)| (x0 + y0, x2 + y2),
            );
        for v in materialized {
            crate::scratch::give_f128(v);
        }
        prime
    };
    let mut adjust_prime_for_delta = |idx: usize, delta: F128| {
        let pair = idx / 2;
        let a0 = packed_witness[2 * pair];
        let a1 = packed_witness[2 * pair + 1];
        if idx & 1 == 0 {
            round0_u0 += a0 * delta;
        }
        round0_u2 += (a0 + a1) * delta;
    };
    for (_, output) in rs_results.iter() {
        if let ring_switch::RsEqInd::Sparse { entries, .. } = &output.rs_eq_ind {
            for &(idx, val) in entries {
                b_combined[idx] += val;
                adjust_prime_for_delta(idx, val);
            }
        }
    }
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        if let DirectEqInd::Sparse(eq) = &pd.eq_ind {
            // Scatter-add the sparse claim and fold its round-0 prime
            // contribution in the SAME pass (O(live positions)), instead of a
            // full O(L) re-pass over b_combined. The prime is linear in
            // b_combined, so the delta from scattering `g·eq` equals
            // Σ adjust_prime_for_delta(idx, g·val) over the live positions.
            let (du0, du2) = sparse_scatter_add_parallel(&mut b_combined, packed_witness, eq, *g);
            round0_u0 += du0;
            round0_u2 += du2;
        }
    }
    if trace {
        eprintln!(
            "  [open_batch] combine rs_eq_ind (L={}, rs×{}, pd×{}, pl×{}): {:6.2} ms",
            l,
            n_rs,
            n_pd,
            n_pl,
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    CombinedClaim {
        ring_switches: rs_results
            .into_iter()
            .map(|(p, o)| {
                // The per-claim rs_eq_ind (L F128s) dies here — recycle it.
                if let ring_switch::RsEqInd::Dense(v) = o.rs_eq_ind {
                    crate::scratch::give_f128(v);
                }
                p
            })
            .collect(),
        b_combined,
        target_combined,
        round0_prime: (round0_u0, round0_u2),
    }
}

/// Parallel sparse scatter-add: `b_combined[scatter_idx(c)] += gamma * eq.live_tensor[c]`
/// for every `c`. Partitions `c`-space across rayon threads; since
/// [`SparseEqTensor::scatter_idx`] is monotonic in `c` (live_positions sorted
/// ascending), each thread's scattered indices fall in a contiguous, disjoint
/// range of `b_combined`. Splits `b_combined` at the chunk boundaries via
/// `split_at_mut`, then writes scatter-adds into the disjoint mutable slices —
/// safe rust, no atomics.
/// Scatter-add `gamma · eq` into `b_combined` and return the resulting
/// round-0 prime delta `(Δu0, Δu2)`. Because the prime is linear in
/// `b_combined`, adding `delta = gamma·val` at index `idx` changes the prime by
/// `Δu0 += a0·delta` (if `idx` even) and `Δu2 += (a0+a1)·delta`, where
/// `a0 = packed_witness[2·pair]`, `a1 = packed_witness[2·pair+1]`,
/// `pair = idx/2`. Computing it here (O(live positions)) avoids a full O(L)
/// re-pass over `b_combined` at the call site.
fn sparse_scatter_add_parallel(
    b_combined: &mut [F128],
    packed_witness: &[F128],
    eq: &SparseEqTensor,
    gamma: F128,
) -> (F128, F128) {
    use rayon::prelude::*;

    let c_total = eq.live_tensor.len();
    if c_total == 0 {
        return (F128::ZERO, F128::ZERO);
    }
    let n_threads = rayon::current_num_threads().max(1);
    let c_per_chunk = c_total.div_ceil(n_threads).max(1);
    let actual_n_chunks = c_total.div_ceil(c_per_chunk);

    // Boundaries in `b_combined` index space. `b_boundaries[i]` is where chunk
    // `i` starts. `b_boundaries[i+1] − b_boundaries[i]` is chunk `i`'s slice
    // length. The last chunk extends to `b_combined.len()` to absorb any tail
    // positions beyond the maximum scatter idx (those contain only dense
    // contributions from the parallel pass).
    let b_boundaries: Vec<usize> = (0..=actual_n_chunks)
        .map(|i| {
            if i == 0 {
                0
            } else if i == actual_n_chunks {
                b_combined.len()
            } else {
                eq.scatter_idx(i * c_per_chunk)
            }
        })
        .collect();
    debug_assert!(b_boundaries.windows(2).all(|w| w[0] <= w[1]));

    // Disjoint mutable slices via repeated split_at_mut.
    let mut remaining: &mut [F128] = b_combined;
    let mut slices: Vec<&mut [F128]> = Vec::with_capacity(actual_n_chunks);
    for i in 1..actual_n_chunks {
        let split_at = b_boundaries[i] - b_boundaries[i - 1];
        let (left, right) = remaining.split_at_mut(split_at);
        slices.push(left);
        remaining = right;
    }
    slices.push(remaining);
    debug_assert_eq!(slices.len(), actual_n_chunks);

    slices
        .into_par_iter()
        .enumerate()
        .map(|(t, slice)| {
            let c_lo = t * c_per_chunk;
            let c_hi = ((t + 1) * c_per_chunk).min(c_total);
            let b_lo = b_boundaries[t];
            let mut du0 = F128::ZERO;
            let mut du2 = F128::ZERO;
            for c in c_lo..c_hi {
                let val = eq.live_tensor[c];
                let idx = eq.scatter_idx(c);
                let delta = gamma * val;
                slice[idx - b_lo] += delta;
                // Round-0 prime delta for this scattered position.
                let pair = idx / 2;
                let a0 = packed_witness[2 * pair];
                let a1 = packed_witness[2 * pair + 1];
                if idx & 1 == 0 {
                    du0 += a0 * delta;
                }
                du2 += (a0 + a1) * delta;
            }
            (du0, du2)
        })
        .reduce(
            || (F128::ZERO, F128::ZERO),
            |(x0, x2), (y0, y2)| (x0 + y0, x2 + y2),
        )
}

/// Verifier reference to a packed-direct claim: the multilinear point at
/// which `ẑ_packed` was claimed equal to `value`. The verifier owns the data
/// (it appears in the public statement of whatever produced the claim, e.g.
/// the chain shift sumcheck output).
#[derive(Clone, Copy, Debug)]
pub struct PackedDirectClaimRef<'a> {
    pub point: &'a [F128],
    pub value: F128,
}

#[derive(Clone, Copy, Debug)]
pub struct PackedLinearClaimRef<'a> {
    pub basis: &'a [F128],
    pub value: F128,
}

/// Verify a mixed-claim batched opening (mirror of
/// [`open_batch_mixed_ligerito_with_precomputed_s_hat_v`]). Uses
/// `ring_switch::verify_succinct` per claim (no dense `rs_eq_ind`
/// materialization), then drives the succinct recursive Ligerito verifier,
/// evaluating the combined basis only at the residual point.
#[allow(clippy::too_many_arguments)]
pub fn verify_opening_batch_ligerito_mixed<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    packed_direct: &[PackedDirectClaimRef<'_>],
    proof: &BatchOpeningProofLigerito,
    lig_config: &ligerito::VerifierConfig,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    let ro = crate::ro::RoContext::plain();
    verify_opening_batch_ligerito_mixed_ro(
        commitment,
        claims,
        z_skips,
        x_outers,
        packed_direct,
        proof,
        lig_config,
        &ro,
        crate::ro::RoChannel::Witness,
        challenger,
    )
}

/// Mixed batch-opening verifier with an explicit point-oracle context and channel.
#[allow(clippy::too_many_arguments)]
pub fn verify_opening_batch_ligerito_mixed_ro<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    packed_direct: &[PackedDirectClaimRef<'_>],
    proof: &BatchOpeningProofLigerito,
    lig_config: &ligerito::VerifierConfig,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    verify_opening_batch_ligerito_mixed_linear_ro(
        commitment,
        claims,
        z_skips,
        x_outers,
        packed_direct,
        &[],
        proof,
        lig_config,
        ro,
        channel,
        challenger,
    )
}

/// Verify a mixed opening with additional arbitrary public linear claims.
#[allow(clippy::too_many_arguments)]
pub fn verify_opening_batch_ligerito_mixed_linear_ro<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    packed_direct: &[PackedDirectClaimRef<'_>],
    packed_linear: &[PackedLinearClaimRef<'_>],
    proof: &BatchOpeningProofLigerito,
    lig_config: &ligerito::VerifierConfig,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    let n_rs = claims.len();
    let n_pd = packed_direct.len();
    let n_pl = packed_linear.len();
    if z_skips.len() != n_rs
        || x_outers.len() != n_rs
        || proof.ring_switches.len() != n_rs
        || n_rs + n_pd + n_pl == 0
    {
        return Err(VerifyError::Ligerito);
    }

    challenger.observe_label(b"flock-pcs-open-batch-v0");

    // 1. Ring-switch SUCCINCT verify per claim — gets sumcheck_claim and a
    //    length-128 `eq_r_dprime` instead of the dense `rs_eq_ind`. Saves
    //    ~16 MB allocation at m=29.
    let mut rs_outputs = Vec::with_capacity(n_rs);
    for i in 0..n_rs {
        let out = ring_switch::verify_succinct(
            claims[i],
            z_skips[i],
            x_outers[i],
            &proof.ring_switches[i],
            challenger,
        )
        .map_err(VerifyError::RingSwitch)?;
        rs_outputs.push(out);
    }
    let gammas_rs: Vec<F128> = (0..n_rs).map(|_| challenger.sample_f128()).collect();

    // 2. PD claim values + γ_pd.
    for pd in packed_direct {
        challenger.observe_label(b"flock-pcs-packed-direct-v0");
        challenger.observe_f128(pd.value);
    }
    for pl in packed_linear {
        challenger.observe_label(b"flock-pcs-packed-linear-v0");
        challenger.observe_f128(pl.value);
    }
    let gammas_pd: Vec<F128> = (0..n_pd).map(|_| challenger.sample_f128()).collect();
    let gammas_pl: Vec<F128> = (0..n_pl).map(|_| challenger.sample_f128()).collect();

    // 3. target_combined from succinct rs claims + PD values.
    let mut target_combined = F128::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target_combined += *g * out.sumcheck_claim;
    }
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        target_combined += *g * pd.value;
    }
    for (pl, g) in packed_linear.iter().zip(gammas_pl.iter()) {
        target_combined += *g * pl.value;
    }

    // 3b. zk: mirror the blinder combination — observe y_g, check its PoW,
    //     sample c, shift the target. Reject a zk/non-zk mode mismatch
    //     between params and proof either way.
    let zk_l0 = if commitment.params.zk {
        let Some(zkb) = &proof.zk_blind else {
            return Err(VerifyError::Ligerito);
        };
        challenger.observe_label(b"flock-pcs-zk-blind-v0");
        challenger.observe_f128(zkb.y_g);
        let c_bits = lig_config.fold_grinding_bits.first().copied().unwrap_or(0) as u32 + 1;
        if !challenger.verify_pow(zkb.c_grind_nonce, c_bits) {
            return Err(VerifyError::Ligerito);
        }
        let c = challenger.sample_f128();
        target_combined += c * zkb.y_g;
        Some(ligerito::ZkL0 { c })
    } else {
        if proof.zk_blind.is_some() {
            return Err(VerifyError::Ligerito);
        }
        None
    };

    // 4. Batch evaluator: returns b_combined at all yr positions in one call.
    //    For RS claims, precompute the ring_switch tensor PREFIX once (over
    //    the ris part) and only re-do the yr_log_n-step suffix per y.
    //    For PD claims, precompute eq prefix factors over ris and finish per y.
    //    For BLAKE3 m=30: ris is 19 dims, yr is 4 dims → 19× prefix reuse.
    let log_n = commitment.params.log_msg_len();
    let eval_b_witness = |ris: &[F128], yr_log_n: usize| -> Vec<F128> {
        use crate::zerocheck::multilinear::eq_eval;
        let yr_len = 1usize << yr_log_n;
        let prefix_len = ris.len();

        // ---- RS claim prefixes ----
        let rs_prefixes: Vec<crate::pcs::tensor_algebra::TensorAlgebra> = rs_outputs
            .iter()
            .zip(x_outers.iter())
            .map(|(_out, x_outer)| {
                // x_outer[1..] has length log_n; we feed only the ris prefix.
                ring_switch::eval_rs_eq_prefix(&x_outer[1..1 + prefix_len], ris)
            })
            .collect();

        // ---- PD claim prefix scalars ----
        // eq(pd.point, point) factors over coordinates; precompute the prefix product.
        let pd_prefix_scalars: Vec<F128> = packed_direct
            .iter()
            .map(|pd| eq_eval(&pd.point[..prefix_len], ris))
            .collect();

        // Arbitrary bases are folded over the residual prefix once. The
        // remaining suffix is queried only at Boolean points, so entry `y`
        // is exactly the required multilinear evaluation.
        let pl_prefixes: Vec<Vec<F128>> = packed_linear
            .iter()
            .map(|pl| {
                assert_eq!(
                    pl.basis.len(),
                    1usize << commitment.params.witness_log_msg_len()
                );
                let mut folded = pl.basis.to_vec();
                for challenge in ris {
                    let half = folded.len() / 2;
                    for i in 0..half {
                        folded[i] = folded[2 * i] * (F128::ONE + *challenge)
                            + folded[2 * i + 1] * *challenge;
                    }
                    folded.truncate(half);
                }
                debug_assert_eq!(folded.len(), yr_len);
                folded
            })
            .collect();

        // ---- Per-y assembly (parallel over yr positions; each y is independent).
        //      y_suffix is binary (bits of y), so we use the binary-query
        //      specializations of eval_rs_eq_finish / eq_eval — each suffix
        //      step collapses to a single scale_vertical / scalar product.
        use rayon::prelude::*;
        debug_assert!(yr_log_n <= 32, "yr_log_n > 32 not supported by binary path");
        (0..yr_len)
            .into_par_iter()
            .map(|y| {
                let y_bits = y as u32;
                let mut sum = F128::ZERO;
                for (((out, g), x_outer), prefix) in rs_outputs
                    .iter()
                    .zip(gammas_rs.iter())
                    .zip(x_outers.iter())
                    .zip(rs_prefixes.iter())
                {
                    sum += *g
                        * ring_switch::eval_rs_eq_finish_from_prefix_binary_q(
                            prefix,
                            &x_outer[1 + prefix_len..],
                            y_bits,
                            &out.eq_r_dprime,
                        );
                }
                for ((pd, g), prefix_scalar) in packed_direct
                    .iter()
                    .zip(gammas_pd.iter())
                    .zip(pd_prefix_scalars.iter())
                {
                    sum += *g
                        * *prefix_scalar
                        * crate::zerocheck::multilinear::eq_eval_binary_x(
                            &pd.point[prefix_len..],
                            y_bits,
                        );
                }
                for ((_, g), prefix) in packed_linear
                    .iter()
                    .zip(gammas_pl.iter())
                    .zip(pl_prefixes.iter())
                {
                    sum += *g * prefix[y];
                }
                sum
            })
            .collect()
    };

    // zk: the committed message is `[mask ‖ z_packed]`, so the combined
    // basis is `b′ = [0 ‖ b_combined]` — as a multilinear, the top (MSB)
    // residual variable gates the witness-space evaluation. The residual
    // suffix y therefore contributes 0 when its top bit is 0, and the
    // witness formula on the remaining bits when it is 1. The ris prefix
    // length is identical in both modes (log_n−yr_log_n = log_n_wit−(yr−1)),
    // so the inner closure is reused unchanged.
    let eval_b_residual = |ris: &[F128], yr_log_n: usize| -> Vec<F128> {
        if zk_l0.is_some() {
            debug_assert!(yr_log_n >= 1);
            let inner = eval_b_witness(ris, yr_log_n - 1);
            let half = 1usize << (yr_log_n - 1);
            let mut out = vec![F128::ZERO; 1usize << yr_log_n];
            out[half..].copy_from_slice(&inner);
            out
        } else {
            eval_b_witness(ris, yr_log_n)
        }
    };

    // 5. Drive ligerito SUCCINCT verifier — eval_b_residual is called ONCE
    //    at the residual check (returns all yr_len values in one batch).
    let ok = ligerito::recursive_verifier_with_basis_succinct_with_ro(
        lig_config,
        &proof.ligerito,
        log_n,
        target_combined,
        &commitment.root,
        eval_b_residual,
        zk_l0,
        ro,
        channel,
        challenger,
    );
    if !ok {
        return Err(VerifyError::Ligerito);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsChallenger;
    use crate::zerocheck::multilinear::lagrange_weights_naive;
    use crate::zerocheck::univariate_skip::build_eq;

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
        fn f128(&mut self) -> F128 {
            F128 {
                lo: self.next_u64(),
                hi: self.next_u64(),
            }
        }
    }

    fn zhat_skip_reference(z: &[bool], m: usize, z_skip: F128, x_outer: &[F128]) -> F128 {
        const K_SKIP: usize = 6;
        let ell = 1usize << K_SKIP;
        let lambda = lagrange_weights_naive(K_SKIP, z_skip);
        let eq_outer = build_eq(x_outer);
        let mut acc = F128::ZERO;
        for i_outer in 0..(1usize << (m - K_SKIP)) {
            let base = i_outer * ell;
            let mut inner = F128::ZERO;
            for i_skip in 0..ell {
                if z[base + i_skip] {
                    inner += lambda[i_skip];
                }
            }
            acc += eq_outer[i_outer] * inner;
        }
        acc
    }

    /// Small hand-built Ligerito config pair for the zk roundtrip at m=13
    /// (wide log_n = 7): initial_k=2, two recursive steps, small query counts.
    #[cfg(feature = "zk")]
    fn tiny_zk_configs() -> (
        crate::pcs::ligerito::ProverConfig,
        crate::pcs::ligerito::VerifierConfig,
    ) {
        let recursive_ks = vec![2usize, 2];
        let log_inv_rates = vec![1usize, 2, 3];
        let queries = vec![6usize, 4, 4];
        let n_levels = log_inv_rates.len();
        let p = crate::pcs::ligerito::ProverConfig {
            log_inv_rates: log_inv_rates.clone(),
            recursive_steps: recursive_ks.len(),
            initial_log_msg_cols: 7 - 2,
            initial_log_num_interleaved: 2,
            initial_k: 2,
            recursive_log_msg_cols: vec![3, 1],
            recursive_ks: recursive_ks.clone(),
            queries: queries.clone(),
            grinding_bits: vec![0; n_levels],
            fold_grinding_bits: vec![0; n_levels],
            ood_samples: vec![0; n_levels],
        };
        let v = crate::pcs::ligerito::VerifierConfig {
            log_inv_rates,
            recursive_steps: recursive_ks.len(),
            initial_log_msg_cols: 7 - 2,
            initial_log_num_interleaved: 2,
            initial_k: 2,
            recursive_log_msg_cols: vec![3, 1],
            recursive_ks,
            queries,
            grinding_bits: vec![0; n_levels],
            fold_grinding_bits: vec![0; n_levels],
            ood_samples: vec![0; n_levels],
        };
        (p, v)
    }

    /// zk PCS roundtrip at m=13: hiding commit, blinded open (RS claim + one
    /// packed-direct claim), succinct verify; then tamper/negative cases.
    #[cfg(feature = "zk")]
    #[test]
    fn pcs_zk_roundtrip_and_negatives() {
        use std::sync::Arc;

        use crate::ro::{RecordingOracle, RoChannel, RoContext};
        use crate::zerocheck::univariate_skip::build_eq;
        use crate::zk::ZkRng;
        let m = 13usize;
        let mut rng = Rng::new(0x2CF0);
        let z = rng.bits(1 << m);
        let z_skip = rng.f128();
        let x_outer: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        let rs_claim = zhat_skip_reference(&z, m, z_skip, &x_outer);

        let params = PcsParams {
            m,
            log_inv_rate: 1,
            log_batch_size: 2,
            profile: Default::default(),
            zk: true,
        };
        let z_packed = pack_witness(&z, m);

        // Packed-direct claim at a random point.
        let pd_point: Vec<F128> = (0..(m - 7)).map(|_| rng.f128()).collect();
        let pd_eq = build_eq(&pd_point);
        let pd_value: F128 = pd_eq
            .iter()
            .zip(z_packed.iter())
            .map(|(e, z)| *e * *z)
            .fold(F128::ZERO, |a, b| a + b);

        let (lig_p_cfg, lig_v_cfg) = tiny_zk_configs();
        let recorder = Arc::new(RecordingOracle::new());
        let ro = RoContext::external([0x42; 32], recorder.clone());

        let prove = |mask_seed: [u8; 32], tamper_mask: bool, tamper_y_g: bool| {
            let mut zk_rng = ZkRng::from_seed(mask_seed);
            let (commitment, mut prover_data) =
                commit::commit_zk_with_ro(&z_packed, &params, &mut zk_rng, &ro, RoChannel::Witness);
            if tamper_mask {
                prover_data.zk_mask[0] += F128::ONE;
            }
            let mut ch_p = FsChallenger::new(b"flock-test-lig-zk-v0");
            let mut proof = open_batch_mixed_ligerito_with_precomputed_s_hat_v_ro(
                z_packed.clone(),
                &prover_data,
                &commitment,
                &[x_outer.as_slice()],
                &[],
                &[PackedDirectClaim {
                    point: pd_point.clone(),
                    value: pd_value,
                    eq_ind: DirectEqInd::Dense(pd_eq.clone()),
                }],
                &PaddingSpec::dense(m),
                &lig_p_cfg,
                &ro,
                RoChannel::Witness,
                &mut ch_p,
            );
            if tamper_y_g {
                let zkb = proof.zk_blind.as_mut().unwrap();
                zkb.y_g += F128::ONE;
            }
            (commitment, proof)
        };
        let verify = |commitment: &Commitment, proof: &BatchOpeningProofLigerito| {
            let mut ch_v = FsChallenger::new(b"flock-test-lig-zk-v0");
            verify_opening_batch_ligerito_mixed_ro(
                commitment,
                &[rs_claim],
                &[z_skip],
                &[x_outer.as_slice()],
                &[PackedDirectClaimRef {
                    point: &pd_point,
                    value: pd_value,
                }],
                proof,
                &lig_v_cfg,
                &ro,
                RoChannel::Witness,
                &mut ch_v,
            )
        };

        // Honest roundtrip.
        let (commitment, proof) = prove([5u8; 32], false, false);
        verify(&commitment, &proof)
            .unwrap_or_else(|e| panic!("zk verify rejected honest proof: {e:?}"));
        assert!(proof.zk_blind.is_some());
        assert!(!recorder.leaf_payloads(RoChannel::Witness).is_empty());
        // L0 opened rows must be wide (f′ + g lanes).
        assert!(
            proof.ligerito.initial_proof.opened_rows[0].len() == 2 * (1 << 2),
            "expected wide L0 rows"
        );

        // Different mask seed ⇒ different transcript, still verifies.
        let (c2, p2) = prove([6u8; 32], false, false);
        verify(&c2, &p2).expect("fresh-seed zk proof must verify");
        assert_ne!(commitment.root, c2.root);
        assert_ne!(
            proof.zk_blind.unwrap().y_g,
            p2.zk_blind.unwrap().y_g,
            "y_g must depend on the blinder"
        );

        // Tampered mask (commit/open inconsistency) ⇒ reject.
        let (c3, p3) = prove([5u8; 32], true, false);
        assert!(verify(&c3, &p3).is_err(), "tampered mask must be rejected");

        // Tampered y_g ⇒ reject.
        let (c4, p4) = prove([5u8; 32], false, true);
        assert!(verify(&c4, &p4).is_err(), "tampered y_g must be rejected");

        // Proof stripped of its zk_blind ⇒ mode mismatch ⇒ reject.
        let (c5, mut p5) = prove([5u8; 32], false, false);
        p5.zk_blind = None;
        assert!(
            verify(&c5, &p5).is_err(),
            "missing zk_blind must be rejected"
        );
    }

    /// Field-valued P commitment + general-linear opening at the zerocheck
    /// terminal point. The diagonal support is not an ordinary subcube MLE,
    /// so the PCS binds `P(rho)` through its public coefficient vector.
    #[cfg(feature = "zk")]
    #[test]
    fn zk_field_mask_hiding_open_roundtrip() {
        use crate::zerocheck::univariate_skip::pack_bits;
        use crate::zerocheck::{SmallMaskSpec, univariate_skip::build_eq};
        use crate::zk::ZkRng;
        let m = 13usize;
        let mut rng = Rng::new(0x9A2B);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let spec = SmallMaskSpec::default();
        let p_small = (0..spec.d(m)).map(|_| rng.f128()).collect::<Vec<_>>();

        let params = PcsParams {
            m,
            log_inv_rate: 1,
            log_batch_size: 2,
            profile: Default::default(),
            zk: true,
        };
        let p_packed = p_small.clone();
        let (lig_p, lig_v) = tiny_zk_configs();
        let pad = PaddingSpec::dense(m);
        let (ap, bp, cp) = (pack_bits(&a), pack_bits(&b), pack_bits(&c));
        let ro = crate::ro::RoContext::plain();

        let run = |tamper_pr: bool| {
            let mut zk_p = ZkRng::from_seed([3u8; 32]);
            let (comm_p, pd_p) = commit::commit_zk_with_ro(
                &p_packed,
                &params,
                &mut zk_p,
                &ro,
                crate::ro::RoChannel::MaskP,
            );
            let mut ch = FsChallenger::new(b"flock-z2-v0");
            ch.observe_bytes(&comm_p.root);
            let (mut zkproof, claim) =
                crate::zerocheck::prove_packed_padded_zk(&ap, &bp, &cp, &p_small, m, &pad, &mut ch);
            if tamper_pr {
                zkproof.final_p_eval += F128::ONE;
            }
            let eq_terminal = build_eq(&claim.mlv_challenges);
            let mut basis = vec![F128::ZERO; p_packed.len()];
            for (i, value) in basis.iter_mut().enumerate().take(spec.d(m)) {
                *value = eq_terminal[spec.support_index(i, m)];
            }
            if !tamper_pr {
                assert_eq!(
                    p_packed
                        .iter()
                        .zip(&basis)
                        .fold(F128::ZERO, |acc, (p, b)| acc + *p * *b),
                    zkproof.final_p_eval,
                    "general-linear basis must encode P(rho)"
                );
            }
            let mut ch_p = ch.clone();
            ch_p.observe_label(b"flock-p-open-P");
            let proof_p = open_batch_mixed_ligerito_with_precomputed_s_hat_v_linear_ro(
                p_packed.clone(),
                &pd_p,
                &comm_p,
                &[],
                &[],
                &[],
                &[PackedLinearClaim {
                    basis,
                    value: zkproof.final_p_eval,
                }],
                &pad,
                &lig_p,
                &ro,
                crate::ro::RoChannel::MaskP,
                &mut ch_p,
            );
            (comm_p, zkproof, proof_p)
        };

        let verify = |comm_p: &Commitment,
                      zkproof: &crate::zerocheck::ZkZerocheckProof,
                      proof_p: &BatchOpeningProofLigerito|
         -> bool {
            let mut ch = FsChallenger::new(b"flock-z2-v0");
            ch.observe_bytes(&comm_p.root);
            let claim = match crate::zerocheck::verify_zk(m, zkproof, &mut ch) {
                Ok(c) => c,
                Err(_) => return false,
            };
            let eq_terminal = build_eq(&claim.mlv_challenges);
            let mut basis = vec![F128::ZERO; p_packed.len()];
            for (i, value) in basis.iter_mut().enumerate().take(spec.d(m)) {
                *value = eq_terminal[spec.support_index(i, m)];
            }
            let mut ch_p = ch.clone();
            ch_p.observe_label(b"flock-p-open-P");
            verify_opening_batch_ligerito_mixed_linear_ro(
                comm_p,
                &[],
                &[],
                &[],
                &[],
                &[PackedLinearClaimRef {
                    basis: &basis,
                    value: zkproof.final_p_eval,
                }],
                proof_p,
                &lig_v,
                &ro,
                crate::ro::RoChannel::MaskP,
                &mut ch_p,
            )
            .is_ok()
        };

        let (cp_, pf, pp) = run(false);
        assert!(
            verify(&cp_, &pf, &pp),
            "honest field-mask hiding opening must verify"
        );
        let (cp2, pf2, pp2) = run(true);
        assert!(!verify(&cp2, &pf2, &pp2), "tampered P(ρ) must be rejected");
    }

    /// End-to-end Ligerito backend roundtrip through pcs::open_batch_mixed_ligerito
    /// and verify_opening_batch_ligerito_mixed. Single ring-switched claim
    /// (no PD — PD path is task #11).
    #[test]
    #[ignore] // Heavier — ~50-100 ms; run with `cargo test pcs_ligerito_roundtrip -- --ignored --nocapture`
    fn pcs_ligerito_backend_roundtrip() {
        let m = 22usize;
        let mut rng = Rng::new(0x11_6E_2170);
        let z = rng.bits(1 << m);
        let z_skip = rng.f128();
        let x_outer: Vec<F128> = (0..(m - 6)).map(|_| rng.f128()).collect();
        let rs_claim = zhat_skip_reference(&z, m, z_skip, &x_outer);

        // PcsParams MUST set log_batch_size = ligerito_initial_k for L0 reuse.
        let initial_k = 6;
        let params = PcsParams {
            m,
            log_inv_rate: 1,
            log_batch_size: initial_k,
            profile: Default::default(),
            zk: false,
        };
        let z_packed = pack_witness(&z, m);
        let (commitment, prover_data) = commit(&z_packed, &params);

        let recursive_ks = vec![3usize, 3, 3];
        // Last level: msg_cols = 0 ⇒ block_len = 2^rate, which must fit the
        // UDR query count (udr_queries(7) = 102 ≤ 128; rate 6 gave 103 > 64
        // and tripped sample_distinct_queries — pre-existing stale config).
        let log_inv_rates = vec![1usize, 3, 4, 7];
        let queries: Vec<usize> = log_inv_rates
            .iter()
            .map(|&r| crate::pcs::ligerito::udr_queries(r))
            .collect();
        let grinding_bits = vec![0usize; log_inv_rates.len()];
        let n_levels = log_inv_rates.len();
        let lig_p_cfg = crate::pcs::ligerito::ProverConfig {
            log_inv_rates: log_inv_rates.clone(),
            recursive_steps: recursive_ks.len(),
            initial_log_msg_cols: (m - LOG_PACKING) - initial_k,
            initial_log_num_interleaved: initial_k,
            initial_k,
            recursive_log_msg_cols: vec![6, 3, 0],
            recursive_ks: recursive_ks.clone(),
            queries: queries.clone(),
            grinding_bits: grinding_bits.clone(),
            fold_grinding_bits: vec![0; n_levels],
            ood_samples: vec![0; n_levels],
        };
        let lig_v_cfg = crate::pcs::ligerito::VerifierConfig {
            log_inv_rates,
            recursive_steps: recursive_ks.len(),
            initial_log_msg_cols: (m - LOG_PACKING) - initial_k,
            initial_log_num_interleaved: initial_k,
            initial_k,
            recursive_log_msg_cols: vec![6, 3, 0],
            recursive_ks,
            queries,
            grinding_bits,
            fold_grinding_bits: vec![0; n_levels],
            ood_samples: vec![0; n_levels],
        };

        let mut ch_p = FsChallenger::new(b"flock-test-lig-v0");
        let proof = open_batch_mixed_ligerito_with_precomputed_s_hat_v(
            z_packed.clone(),
            &prover_data,
            &commitment,
            &[x_outer.as_slice()],
            &[],
            &[],
            &PaddingSpec::dense(m),
            &lig_p_cfg,
            &mut ch_p,
        );

        let mut ch_v = FsChallenger::new(b"flock-test-lig-v0");
        verify_opening_batch_ligerito_mixed(
            &commitment,
            &[rs_claim],
            &[z_skip],
            &[x_outer.as_slice()],
            &[],
            &proof,
            &lig_v_cfg,
            &mut ch_v,
        )
        .unwrap_or_else(|e| panic!("ligerito verify rejected honest proof: {e:?}"));
    }
}

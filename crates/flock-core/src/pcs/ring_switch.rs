// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The verifier's polylog `eval_rs_eq` helper is ported from binius64's
// `crates/verifier/src/ring_switch.rs`
// (https://github.com/binius-zk/binius64). The rest of this module (the
// prover-side reduction adapted for the φ_8 LCH basis) is original to Flock.

//! Ring-switching reduction (DP24-style, adapted for the φ_8 LCH basis).
//!
//! Converts the zerocheck's claim `ẑ_skip(z_skip, x_outer) = v` into a BaseFold
//! sumcheck claim over the packed multilinear `f_packed` with a transparent
//! multilinear `rs_eq_ind`.
//!
//! ## Non-novelty basis: only affects the claim-check step
//!
//! Binius's DP24 ring-switching uses tensor-product (`eq_ind`) weights for the
//! verifier's claim check. That requires the prefix's LCH-Lagrange to factor
//! as `eq(x_skip, i_skip)`, which holds only for the *novelty basis* of the
//! subspace.
//!
//! Our zerocheck uses the φ_8 image of {1,2,4,…,32} as the 6-dim LCH basis.
//! That basis is **not** a novelty basis (verified at k=2: the ratio of
//! Lagrange values doesn't satisfy the tensor identity), so the 64 weights
//! `ν_φ8(i_skip)(z_skip)` are not tensor-factorizable.
//!
//! Resolution: replace the verifier's claim check with **direct** Lagrange
//! weights (computed via
//! [`lagrange_weights_naive`](crate::zerocheck::multilinear::lagrange_weights_naive)); every other component of
//! the reduction (`s_hat_v`, `s_hat_u`, BaseFold target `T`, `rs_eq_ind`) is
//! independent of the prefix and stays identical to Binius.
//!
//! ## Prover vs. verifier paths for `rs_eq_ind`
//!
//! - **Prover side** (used by [`prove`], [`prove_batched`]): materializes
//!   `rs_eq_ind` densely (or sparsely) via [`fold_b128_elems`] / [`RsEqInd`].
//!   The dense vector becomes the BaseFold target witness, so the prover does
//!   need the full `2^(m-7)` entries.
//! - **Verifier side** (used by [`verify_succinct`] + [`eval_rs_eq`]): never
//!   materializes `rs_eq_ind`. Instead, evaluates `MLE(rs_eq_ind)(c)` at the
//!   BaseFold final challenge point in `O((m-7) · 128²)` field ops via the
//!   DP24 tensor-algebra iterative algorithm ([DP24] §1.3, Figure 3). This is
//!   polylog in the witness size.
//!
//! [DP24]: <https://eprint.iacr.org/2024/504>
//!
//! ## Layout (for m-bit witness, F_{2^128} packing with LOG_PACKING = 7)
//!
//! Zerocheck output: `(z_skip ∈ F, x_outer ∈ F^{m−6})` with claim `v`.
//!
//! After translation:
//! - **prefix bits 0..6**: weighted by `ν_φ8(·)(z_skip)` (the 64 Lagrange weights).
//! - **prefix bit 6**: weighted by `eq(x_outer[0], ·)`.
//! - **suffix coords**: `x_outer[1..]`, length `m − 7`.
//!
//! The packed witness has `2^(m−7)` F_{2^128} elements indexed by the suffix.
//! `s_hat_v` has 128 entries indexed by the 7-bit prefix.

mod fold;
mod sparse;

pub use fold::*;
pub(crate) use fold::{deferred_dense_value, fold_b128_from_table, fold_one_slot};
pub use sparse::*;

use crate::challenger::Challenger;
use crate::field::F128;
use crate::pcs::tensor_algebra::TensorAlgebra;
use crate::zerocheck::PaddingSpec;
use crate::zerocheck::univariate_skip::build_eq;
use fold::{build_eq_parallel, build_fold_byte_table};
use serde::{Deserialize, Serialize};
use sparse::SPARSE_ZERO_THRESHOLD;

use super::pack::LOG_PACKING;

// ---------------------------------------------------------------------------
// Prover / verifier of the ring-switching reduction.
// ---------------------------------------------------------------------------

/// The prover message: the 128 slice-MLEs at the suffix point.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RingSwitchProof {
    pub s_hat_v: Vec<F128>,
}

/// What both prover and verifier compute as a result of the reduction:
/// the transparent multilinear and the BaseFold sumcheck target.
#[derive(Clone, Debug)]
pub struct RingSwitchOutput {
    pub rs_eq_ind: Vec<F128>,
    pub sumcheck_claim: F128,
}

/// Per-claim output of [`prove_batched`]. Mirrors [`RingSwitchOutput`] but lets
/// the prover skip the dense `2^(m-7)` `rs_eq_ind` allocation for claims whose
/// suffix tensor is sparse (e.g. the hash-chain claim). Verifier-side
/// (`ring_switch::verify` + `pcs::verify_opening_batch`) still consumes the
/// dense [`RingSwitchOutput`].
#[derive(Clone, Debug)]
pub struct RingSwitchBatchOutput {
    /// For dense claims this is `γ_k · B_k` — γ is baked into the byte
    /// table during the fold inside `prove_batched_padded_with_precomputed`,
    /// so pcs's combine just adds it without per-slot γ-mul. For sparse
    /// claims `γ_k · entries` are baked similarly.
    pub rs_eq_ind: RsEqInd,
    pub sumcheck_claim: F128,
}

/// Sparse-or-dense representation of `rs_eq_ind`. All variants here have γ_k
/// pre-multiplied in (see `RingSwitchBatchOutput`).
#[derive(Clone, Debug)]
pub enum RsEqInd {
    Dense(Vec<F128>),
    /// Deferred dense: the `γ_k·B_k` buffer is **not** materialized. Instead the
    /// fold ingredients (`build_eq_split` factors + the γ-baked byte table) are
    /// carried so pcs's combine can fold each slot on the fly and accumulate it
    /// straight into `b_combined` — avoiding a 2^(m-7) materialize + readback
    /// per claim. `value(j) = deferred_dense_value(eq_lo, eq_hi, table, log2(B), j)`,
    /// `B = eq_lo.len()`; byte-identical to `Dense(fold_b128_elems_split(..))`.
    DeferredDense {
        eq_lo: Vec<F128>,
        eq_hi: Vec<F128>,
        table: Vec<F128>,
    },
    Sparse {
        len: usize,
        entries: Vec<(usize, F128)>,
    },
}

impl RsEqInd {
    /// Logical length of the underlying vector.
    pub fn len(&self) -> usize {
        match self {
            Self::Dense(v) => v.len(),
            Self::DeferredDense { eq_lo, eq_hi, .. } => eq_lo.len() * eq_hi.len(),
            Self::Sparse { len, .. } => *len,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Accumulate `gamma * self[j]` into `out[j]` for all `j`. Sparse variants
    /// touch only their support; dense variants iterate `out` in lockstep.
    pub fn add_scaled_into(&self, gamma: F128, out: &mut [F128]) {
        debug_assert_eq!(out.len(), self.len());
        match self {
            Self::Dense(v) => {
                for (o, &x) in out.iter_mut().zip(v.iter()) {
                    *o += gamma * x;
                }
            }
            Self::DeferredDense {
                eq_lo,
                eq_hi,
                table,
            } => {
                let log_b = eq_lo.len().trailing_zeros() as usize;
                for (j, o) in out.iter_mut().enumerate() {
                    *o += gamma * deferred_dense_value(eq_lo, eq_hi, table, log_b, j);
                }
            }
            Self::Sparse { entries, .. } => {
                for &(idx, val) in entries {
                    out[idx] += gamma * val;
                }
            }
        }
    }

    /// Materialize the dense view. O(L) regardless of variant; use sparingly.
    pub fn to_dense(&self) -> Vec<F128> {
        match self {
            Self::Dense(v) => v.clone(),
            Self::DeferredDense {
                eq_lo,
                eq_hi,
                table,
            } => {
                let log_b = eq_lo.len().trailing_zeros() as usize;
                let l = eq_lo.len() * eq_hi.len();
                (0..l)
                    .map(|j| deferred_dense_value(eq_lo, eq_hi, table, log_b, j))
                    .collect()
            }
            Self::Sparse { len, entries } => {
                let mut out = vec![F128::ZERO; *len];
                for &(idx, val) in entries {
                    out[idx] = val;
                }
                out
            }
        }
    }

    /// Consume into a dense `Vec<F128>`. Returns the inner vector directly when
    /// already `Dense` (no copy).
    pub fn into_dense(self) -> Vec<F128> {
        match self {
            Self::Dense(v) => v,
            Self::DeferredDense { .. } => self.to_dense(),
            Self::Sparse { len, entries } => {
                let mut out = vec![F128::ZERO; len];
                for (idx, val) in entries {
                    out[idx] = val;
                }
                out
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    ClaimMismatch,
}

/// Prover side of the ring-switching reduction.
///
/// Inputs:
/// - `packed_witness` (length `2^L`, L = m − 7), the F_{2^128}-packed witness.
/// - `x_outer` (length m − 6), the multilinear coords from the zerocheck.
/// - `challenger` for sampling row-batching `r''`.
///
/// Output: the proof message `s_hat_v` (128 F_{2^128} values to send) plus the
/// BaseFold inputs `(rs_eq_ind, sumcheck_claim)`.
pub fn prove<Ch: Challenger>(
    packed_witness: &[F128],
    x_outer: &[F128],
    challenger: &mut Ch,
) -> (RingSwitchProof, RingSwitchOutput) {
    assert!(
        !x_outer.is_empty(),
        "x_outer must contain at least 1 coord (the 7th-bit factor)"
    );
    let l = packed_witness.len();
    assert_eq!(l, 1 << (x_outer.len() - 1).saturating_add(0)); // sanity (placeholder)
    // Actually: packed_witness.len() = 2^L where L = m - 7. And x_outer.len() = m - 6.
    // So packed_witness.len() = 2^(x_outer.len() - 1). Enforce that.
    assert_eq!(l, 1 << (x_outer.len() - 1));

    let trace = std::env::var("PCS_TRACE").is_ok();

    challenger.observe_label(b"flock-ring-switch");

    // Suffix is x_outer[1..] (length m-7); first coord becomes the 7th-bit factor.
    let suffix = &x_outer[1..];
    let t = std::time::Instant::now();
    let suffix_tensor = build_eq_parallel(suffix);
    if trace {
        eprintln!(
            "    [rs::prove] build_eq(suffix L={}): {:6.2} ms",
            suffix.len(),
            t.elapsed().as_secs_f64() * 1e3
        );
    }
    debug_assert_eq!(suffix_tensor.len(), l);

    // Compute and send s_hat_v.
    let t = std::time::Instant::now();
    let s_hat_v = fold_1b_rows_naive(packed_witness, &suffix_tensor);
    if trace {
        eprintln!(
            "    [rs::prove] fold_1b_rows:          {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
    }
    challenger.observe_f128_slice(&s_hat_v);

    // Sample row-batching r''.
    let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
    let eq_r_dprime = build_eq(&r_dprime);

    // Compute BaseFold target: T = ⟨transpose(s_hat_v), eq(r'')⟩.
    let s_hat_u = tensor_algebra_transpose(&s_hat_v);
    let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

    // Compute transparent multilinear rs_eq_ind.
    let t = std::time::Instant::now();
    let rs_eq_ind = fold_b128_elems(&suffix_tensor, &eq_r_dprime);
    if trace {
        eprintln!(
            "    [rs::prove] fold_b128_elems:       {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    (
        RingSwitchProof { s_hat_v },
        RingSwitchOutput {
            rs_eq_ind,
            sumcheck_claim,
        },
    )
}

/// Batched prover: produce ring-switching proofs for `x_outers.len()` opening
/// points in one pass. Shares a single fused `fold_1b_rows` bit-scan over
/// `packed_witness`. Challenger interaction is byte-identical to calling
/// [`prove`] sequentially for each `x_outer`.
pub fn prove_batched<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    challenger: &mut Ch,
) -> (Vec<(RingSwitchProof, RingSwitchBatchOutput)>, Vec<F128>) {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    prove_batched_padded(packed_witness, x_outers, &PaddingSpec::dense(m), challenger)
}

/// Padding-aware variant of [`prove_batched`]. Threads `padding` into
/// `fold_1b_rows_multi_padded` so dense suffix folds skip chunks that fall
/// entirely in the per-block zero padding.
///
/// Returns `(results, gammas_rs)` — γ_rs is sampled internally after all
/// claims are observed (Schwartz-Zippel-sound), and is **baked into each
/// `RingSwitchBatchOutput::rs_eq_ind`** so the pcs combine doesn't need a
/// per-slot γ-mul. The returned `gammas_rs` is for pcs to compute the
/// γ-weighted `target_combined` (Σ γ_rs[k] · sumcheck_claim_k).
pub fn prove_batched_padded<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> (Vec<(RingSwitchProof, RingSwitchBatchOutput)>, Vec<F128>) {
    prove_batched_padded_with_precomputed(packed_witness, x_outers, &[], padding, challenger)
}

/// Variant of [`prove_batched_padded`] that accepts an optional precomputed
/// `s_hat_v` per claim. When `precomputed_s_hat_v[i] = Some(v)` for claim `i`,
/// the prover skips that claim's `fold_1b_rows` work and uses `v` directly as
/// `s_hat_v` for the per-opening tail (sumcheck_claim, rs_eq_ind, transcript
/// observe). The eq tensor (`eq_lo`/`eq_hi` or sparse support) is still built
/// because `fold_b128_elems_split` needs it for `rs_eq_ind`.
///
/// Use case: AB-claim opening when lincheck's pre-sumcheck `z_vec` is
/// available — see [`s_hat_v_from_z_vec`] and `prover::open_claims`.
///
/// `precomputed_s_hat_v` must be `&[]` (no precomputes) or have length equal
/// to `x_outers.len()`. Each precomputed slice must be length `2^LOG_PACKING`.
///
/// Output is **byte-identical** to [`prove_batched_padded`] when the precomputed
/// `s_hat_v` is honest (matches what `fold_1b_rows` would produce). Transcript
/// observes the same bytes in the same order.
pub fn prove_batched_padded_with_precomputed<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> (Vec<(RingSwitchProof, RingSwitchBatchOutput)>, Vec<F128>) {
    assert!(!x_outers.is_empty());
    let trace = std::env::var("PCS_TRACE").is_ok();
    let n = x_outers.len();
    let l = packed_witness.len();
    for x in x_outers {
        assert!(!x.is_empty());
        assert_eq!(l, 1 << (x.len() - 1));
    }
    assert!(
        precomputed_s_hat_v.is_empty() || precomputed_s_hat_v.len() == n,
        "precomputed_s_hat_v: must be empty or length {n}, got {}",
        precomputed_s_hat_v.len(),
    );
    let n_packed = 1usize << LOG_PACKING;
    for p in precomputed_s_hat_v.iter().flatten() {
        assert_eq!(
            p.len(),
            n_packed,
            "precomputed_s_hat_v entry must have length 2^LOG_PACKING"
        );
    }

    // Per-orig-claim "precomputed?" predicate. Empty precomputed slice → all
    // claims need fold (matches the existing behavior bit-for-bit).
    let has_precomputed =
        |orig: usize| -> bool { precomputed_s_hat_v.get(orig).copied().flatten().is_some() };

    // 1. Classify each claim. Claims whose suffix `x_outer[1..]` has at least
    //    `SPARSE_ZERO_THRESHOLD` exactly-zero coords (e.g. the hash-chain
    //    ẑ-claim) skip the dense kernels entirely; the rest fuse through the
    //    existing MFR/8-wide multi-fold. Pulling sparse claims out also
    //    restores k==2 (the MFR fast-path threshold in `fold_1b_rows_multi`)
    //    when there are exactly two dense claims — the common case.
    #[derive(Clone, Copy)]
    enum Kind {
        Dense(usize),
        Sparse(usize),
    }
    let mut kinds: Vec<Kind> = Vec::with_capacity(n);
    let mut dense_suffixes: Vec<&[F128]> = Vec::new();
    let mut sparse_suffixes: Vec<&[F128]> = Vec::new();
    // Map dense/sparse claim index back to the original `x_outers` index — used
    // to look up precomputed slots without recomputing the classification.
    let mut dense_to_orig: Vec<usize> = Vec::new();
    let mut sparse_to_orig: Vec<usize> = Vec::new();
    for (orig, x) in x_outers.iter().enumerate() {
        let suffix = &x[1..];
        let n_zeros = suffix.iter().filter(|&&c| c == F128::ZERO).count();
        if n_zeros >= SPARSE_ZERO_THRESHOLD {
            kinds.push(Kind::Sparse(sparse_suffixes.len()));
            sparse_to_orig.push(orig);
            sparse_suffixes.push(suffix);
        } else {
            kinds.push(Kind::Dense(dense_suffixes.len()));
            dense_to_orig.push(orig);
            dense_suffixes.push(suffix);
        }
    }

    // 2. Build suffix representations. Dense claims use the tensor-split
    //    factorization (two ~2^(n/2) factors instead of the full 2^n tensor)
    //    whenever `len` is a whole number of 16-wide MFR chunks — i.e. all
    //    real workloads. The split keeps `build_eq` off the critical path and
    //    lets the fold skip streaming the multi-MB tensor (see
    //    `fold_1b_rows_split`). Tiny test sizes (len not divisible by 16) fall
    //    back to the materialized tensor + the legacy multi-fold.
    let use_split = l.is_multiple_of(16);
    let t = std::time::Instant::now();
    let dense_splits: Vec<(Vec<F128>, Vec<F128>)> = if use_split {
        dense_suffixes
            .iter()
            .map(|s| build_eq_split(s, split_n_lo(s.len())))
            .collect()
    } else {
        Vec::new()
    };
    let dense_tensors: Vec<Vec<F128>> = if use_split {
        Vec::new()
    } else {
        dense_suffixes
            .iter()
            .map(|s| build_eq_parallel(s))
            .collect()
    };
    let sparse_supports: Vec<SparseEqTensor> =
        sparse_suffixes.iter().map(|s| build_eq_sparse(s)).collect();
    if trace {
        eprintln!(
            "    [rs::prove_batched] build_eq dense×{} ({}) + sparse×{}: {:6.2} ms",
            dense_suffixes.len(),
            if use_split { "split" } else { "full" },
            sparse_supports.len(),
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    // 3. fold_1b_rows: split inner-then-outer fold per dense claim (or the
    //    legacy fused MFR multi-fold for tiny non-split sizes); per-claim
    //    sparse scan for the rest.
    //
    //    Precomputed claims skip fold_1b_rows entirely — their s_hat_v is
    //    supplied by the caller. dense_s_hat_v/sparse_s_hat_v are still
    //    indexed by classify-time index `d` / `s`; we splice precomputed
    //    values in at those slots and run the kernel only on the others.
    let dense_needs_fold: Vec<usize> = (0..dense_suffixes.len())
        .filter(|&d| !has_precomputed(dense_to_orig[d]))
        .collect();
    let sparse_needs_fold: Vec<usize> = (0..sparse_suffixes.len())
        .filter(|&s| !has_precomputed(sparse_to_orig[s]))
        .collect();
    let t = std::time::Instant::now();
    let mut dense_s_hat_v: Vec<Vec<F128>> = vec![Vec::new(); dense_suffixes.len()];
    let mut sparse_s_hat_v: Vec<Vec<F128>> = vec![Vec::new(); sparse_suffixes.len()];
    // Fill precomputed slots first.
    for d in 0..dense_suffixes.len() {
        if let Some(p) = precomputed_s_hat_v.get(dense_to_orig[d]).copied().flatten() {
            dense_s_hat_v[d] = p.to_vec();
        }
    }
    for s in 0..sparse_suffixes.len() {
        if let Some(p) = precomputed_s_hat_v
            .get(sparse_to_orig[s])
            .copied()
            .flatten()
        {
            sparse_s_hat_v[s] = p.to_vec();
        }
    }
    // Run the kernel only on claims that genuinely need fold_1b_rows.
    if use_split {
        match dense_needs_fold.len() {
            0 => {}
            2 => {
                // K=2 specialization with stack-allocated inner accumulators —
                // one packed_witness streaming pass, shared transposes.
                let d0 = dense_needs_fold[0];
                let d1 = dense_needs_fold[1];
                let (lo0, hi0) = (dense_splits[d0].0.as_slice(), dense_splits[d0].1.as_slice());
                let (lo1, hi1) = (dense_splits[d1].0.as_slice(), dense_splits[d1].1.as_slice());
                let (a, b) = fold_1b_rows_split_2way(packed_witness, lo0, hi0, lo1, hi1, padding);
                dense_s_hat_v[d0] = a;
                dense_s_hat_v[d1] = b;
            }
            _ => {
                for &d in &dense_needs_fold {
                    let (eq_lo, eq_hi) = (&dense_splits[d].0, &dense_splits[d].1);
                    dense_s_hat_v[d] = fold_1b_rows_split(packed_witness, eq_lo, eq_hi, padding);
                }
            }
        }
    } else if !dense_needs_fold.is_empty() {
        let dense_refs: Vec<&[F128]> = dense_needs_fold
            .iter()
            .map(|&d| dense_tensors[d].as_slice())
            .collect();
        let out = fold_1b_rows_multi_padded(packed_witness, &dense_refs, padding);
        for (i, &d) in dense_needs_fold.iter().enumerate() {
            dense_s_hat_v[d] = out[i].clone();
        }
    }
    for &s in &sparse_needs_fold {
        sparse_s_hat_v[s] = fold_1b_rows_sparse(packed_witness, &sparse_supports[s]);
    }
    if trace {
        eprintln!(
            "    [rs::prove_batched] fold_1b_rows dense(k={})+sparse(k={}): {:6.2} ms",
            dense_s_hat_v.len(),
            sparse_s_hat_v.len(),
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    // 4. Per-opening tail. Two phases:
    //    (a) Per claim: observe(label, s_hat_v), sample r''_i, compute
    //        sumcheck_claim. Stash factors needed for fold.
    //    (b) Sample γ_rs after all observations (Schwartz-Zippel-sound).
    //    (c) Per claim: bake γ_k into eq_r_dprime, fold. Output rs_eq_ind
    //        already has γ_k baked in — pcs combine just adds.
    let t = std::time::Instant::now();

    struct ClaimWork {
        s_hat_v: Vec<F128>,
        sumcheck_claim: F128,
        eq_r_dprime: Vec<F128>,
    }
    let mut work: Vec<ClaimWork> = Vec::with_capacity(n);
    for i in 0..n {
        challenger.observe_label(b"flock-ring-switch");
        let s_hat_v: Vec<F128> = match kinds[i] {
            Kind::Dense(d) => dense_s_hat_v[d].clone(),
            Kind::Sparse(s) => sparse_s_hat_v[s].clone(),
        };
        challenger.observe_f128_slice(&s_hat_v);
        let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
        let eq_r_dprime = build_eq(&r_dprime);

        let s_hat_u = tensor_algebra_transpose(&s_hat_v);
        let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

        work.push(ClaimWork {
            s_hat_v,
            sumcheck_claim,
            eq_r_dprime,
        });
    }

    // γ_rs sampled after all RS observations — sound. Each γ_rs[k] is then
    // baked into eq_r_dprime[k] before building the Φ byte table, so the
    // fold output is γ_k · B_k directly. pcs combine just adds.
    let gammas_rs: Vec<F128> = (0..n).map(|_| challenger.sample_f128()).collect();

    let results: Vec<(RingSwitchProof, RingSwitchBatchOutput)> = work
        .into_iter()
        .zip(gammas_rs.iter())
        .enumerate()
        .map(|(i, (w, &g))| {
            let scaled_eq_r_dprime: Vec<F128> = w.eq_r_dprime.iter().map(|x| g * *x).collect();
            let rs_eq_ind = match kinds[i] {
                Kind::Dense(d) => {
                    if use_split {
                        // Defer the fold: carry the split factors + γ-baked byte
                        // table so pcs's combine folds each slot directly into
                        // `b_combined` (no 2^(m-7) materialize + readback). The
                        // table build is the only work done here (16·256 adds).
                        let (eq_lo, eq_hi) = &dense_splits[d];
                        RsEqInd::DeferredDense {
                            eq_lo: eq_lo.clone(),
                            eq_hi: eq_hi.clone(),
                            table: build_fold_byte_table(&scaled_eq_r_dprime),
                        }
                    } else {
                        RsEqInd::Dense(fold_b128_elems(&dense_tensors[d], &scaled_eq_r_dprime))
                    }
                }
                Kind::Sparse(s) => RsEqInd::Sparse {
                    len: l,
                    entries: fold_b128_elems_sparse_pairs(&sparse_supports[s], &scaled_eq_r_dprime),
                },
            };
            (
                RingSwitchProof { s_hat_v: w.s_hat_v },
                RingSwitchBatchOutput {
                    rs_eq_ind,
                    sumcheck_claim: w.sumcheck_claim,
                },
            )
        })
        .collect();

    if trace {
        eprintln!(
            "    [rs::prove_batched] per-opening tail ×{}: {:6.2} ms",
            n,
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    (results, gammas_rs)
}

/// Verifier side of the ring-switching reduction.
///
/// Inputs:
/// - `claim`: the zerocheck's claim value `ẑ_skip(z_skip, x_outer)`.
/// - `z_skip` ∈ F_{2^128}: the univariate-skip coord.
/// - `x_outer` (length m − 6): the multilinear coords.
/// - `proof`: the prover's `s_hat_v` message.
/// - `challenger` for sampling `r''` in lockstep with the prover.
///
/// Output: the matching BaseFold inputs `(rs_eq_ind, sumcheck_claim)`, or a
/// `ClaimMismatch` error if `weights · s_hat_v ≠ claim`.
pub fn verify<Ch: Challenger>(
    claim: F128,
    z_skip: F128,
    x_outer: &[F128],
    proof: &RingSwitchProof,
    challenger: &mut Ch,
) -> Result<RingSwitchOutput, VerifyError> {
    assert!(!x_outer.is_empty());
    let l = 1usize << (x_outer.len() - 1);
    assert_eq!(proof.s_hat_v.len(), 1 << LOG_PACKING);

    challenger.observe_label(b"flock-ring-switch");

    // Verifier observes s_hat_v.
    challenger.observe_f128_slice(&proof.s_hat_v);

    // Check the claim against ν_φ8 ⊗ eq weights.
    let weights = build_claim_weights(z_skip, x_outer[0]);
    if claim_check(&weights, &proof.s_hat_v) != claim {
        return Err(VerifyError::ClaimMismatch);
    }

    // Sample r''.
    let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
    let eq_r_dprime = build_eq(&r_dprime);

    // Compute BaseFold target.
    let s_hat_u = tensor_algebra_transpose(&proof.s_hat_v);
    let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

    // Compute rs_eq_ind (verifier needs it to check BaseFold; reconstructs it
    // from x_outer and r''). The suffix tensor is rebuilt from x_outer[1..].
    let suffix = &x_outer[1..];
    let suffix_tensor = build_eq(suffix);
    debug_assert_eq!(suffix_tensor.len(), l);
    let rs_eq_ind = fold_b128_elems(&suffix_tensor, &eq_r_dprime);

    Ok(RingSwitchOutput {
        rs_eq_ind,
        sumcheck_claim,
    })
}

/// Verifier-side output of [`verify_succinct`]: contains everything the caller
/// needs to drive the BaseFold consistency check, *without* materializing the
/// dense `rs_eq_ind` vector of length `2^(m-7)`.
#[derive(Clone, Debug)]
pub struct RingSwitchVerifierOutput {
    pub sumcheck_claim: F128,
    /// `eq` tensor of length `2^LOG_PACKING = 128` derived from the verifier's
    /// sampled `r''`. Used by [`eval_rs_eq`] at the BaseFold final point.
    pub eq_r_dprime: Vec<F128>,
}

/// Polylog-cost ring-switching verifier.
///
/// Same FS interface as [`verify`] but **does not** build the dense
/// `rs_eq_ind` vector. Pair with [`eval_rs_eq`] at the BaseFold final point to
/// evaluate `MLE(rs_eq_ind)(challenges)` in `O((m − 7) · 128²)` field ops
/// instead of `O(2^(m−7))`.
pub fn verify_succinct<Ch: Challenger>(
    claim: F128,
    z_skip: F128,
    x_outer: &[F128],
    proof: &RingSwitchProof,
    challenger: &mut Ch,
) -> Result<RingSwitchVerifierOutput, VerifyError> {
    assert!(!x_outer.is_empty());
    assert_eq!(proof.s_hat_v.len(), 1 << LOG_PACKING);

    challenger.observe_label(b"flock-ring-switch");
    challenger.observe_f128_slice(&proof.s_hat_v);

    let weights = build_claim_weights(z_skip, x_outer[0]);
    if claim_check(&weights, &proof.s_hat_v) != claim {
        return Err(VerifyError::ClaimMismatch);
    }

    let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
    let eq_r_dprime = build_eq(&r_dprime);

    let s_hat_u = tensor_algebra_transpose(&proof.s_hat_v);
    let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

    Ok(RingSwitchVerifierOutput {
        sumcheck_claim,
        eq_r_dprime,
    })
}

/// Polylog-cost evaluation of `MLE(rs_eq_ind)(query)` at the BaseFold final
/// challenge point, following [DP24] §1.3 Figure 3.
///
/// The dense alternative — `mle_eval(&fold_b128_elems(build_eq(z_vals),
/// eq_r_dprime), query)` — costs `O(2^|z_vals|)` field operations. This
/// function costs `O(|z_vals| · 2^{2·LOG_PACKING}) = O(|z_vals| · 16384)`
/// field operations: a length-128 `TensorAlgebra` element is iteratively
/// updated by `scale_vertical` / `scale_horizontal` over `|z_vals|`
/// iterations, then folded against `eq_r_dprime` (length 128).
///
/// Ports binius64's `crates/verifier/src/ring_switch.rs::eval_rs_eq`.
///
/// ## Arguments
///
/// * `z_vals` — the suffix-side coords, i.e. `x_outer[1..]` from
///   [`verify_succinct`]. Length `ℓ' = m − 7`.
/// * `query` — the BaseFold sumcheck final challenges, length `ℓ'`.
/// * `eq_r_dprime` — the `eq` tensor over the sampled `r''`, length 128.
///
/// [DP24]: <https://eprint.iacr.org/2024/504>
pub fn eval_rs_eq(z_vals: &[F128], query: &[F128], eq_r_dprime: &[F128]) -> F128 {
    assert_eq!(
        z_vals.len(),
        query.len(),
        "eval_rs_eq: z_vals and query must have equal length"
    );
    assert_eq!(
        eq_r_dprime.len(),
        1 << LOG_PACKING,
        "eval_rs_eq: eq_r_dprime length must be 128"
    );

    let mut eval = TensorAlgebra::from_vertical(F128::ONE);
    for (&z_i, &q_i) in z_vals.iter().zip(query.iter()) {
        // In characteristic 2: eq(z, q) = 1 + z + q + 2·z·q = 1 + z + q.
        // So updating eval ← eval + z·eval + q·eval (with vertical = z-axis,
        // horizontal = q-axis) yields the correct per-step eq tensor update.
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval.fold_vertical(eq_r_dprime)
}

/// **Prefix-only** variant of [`eval_rs_eq`]: walks `prefix_len` of the
/// (z_vals, query) pairs and returns the partially-evolved `TensorAlgebra`.
/// Pair with [`eval_rs_eq_finish_from_prefix`] to share the prefix across
/// many query points (e.g. residual `y_bits` positions).
pub fn eval_rs_eq_prefix(z_vals: &[F128], query_prefix: &[F128]) -> TensorAlgebra {
    assert!(query_prefix.len() <= z_vals.len());
    let mut eval = TensorAlgebra::from_vertical(F128::ONE);
    for (&z_i, &q_i) in z_vals.iter().zip(query_prefix.iter()) {
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval
}

/// Finish [`eval_rs_eq`] given a precomputed prefix tensor + the remaining
/// (z, query) suffix. `z_vals_suffix` and `query_suffix` are the parts of
/// the original `z_vals`/`query` past the prefix length.
pub fn eval_rs_eq_finish_from_prefix(
    prefix: &TensorAlgebra,
    z_vals_suffix: &[F128],
    query_suffix: &[F128],
    eq_r_dprime: &[F128],
) -> F128 {
    assert_eq!(z_vals_suffix.len(), query_suffix.len());
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    let mut eval = prefix.clone();
    for (&z_i, &q_i) in z_vals_suffix.iter().zip(query_suffix.iter()) {
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval.fold_vertical(eq_r_dprime)
}

/// Specialized variant of [`eval_rs_eq_finish_from_prefix`] for the case where
/// `query_suffix` is known to be **binary** (each coord is `F128::ZERO` or
/// `F128::ONE`). Used by Ligerito's succinct verifier where the suffix is the
/// bit-decomposition of a residual position `y`.
///
/// When `q_i ∈ {0, 1}`, the general recurrence
/// `new_eval = eval + z·eval + q·eval` collapses (in char 2) to:
/// - `q_i = 0`: `new_eval = (1 + z_i) · eval`
/// - `q_i = 1`: `new_eval = z_i · eval`
///
/// Both reduce to a single in-place `scale_vertical`, eliminating all the
/// per-step clones, transposes, and additions of the general path. Each suffix
/// step becomes one 128-mult instead of ~8 passes.
///
/// `y_bits` encodes the suffix as a bitmask: bit `j` is the j-th suffix coord.
pub fn eval_rs_eq_finish_from_prefix_binary_q(
    prefix: &TensorAlgebra,
    z_vals_suffix: &[F128],
    y_bits: u32,
    eq_r_dprime: &[F128],
) -> F128 {
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    debug_assert!(
        z_vals_suffix.len() <= 32,
        "y_bits is u32; suffix > 32 not supported"
    );
    let mut eval = prefix.clone();
    for (j, &z_i) in z_vals_suffix.iter().enumerate() {
        let scalar = if (y_bits >> j) & 1 == 1 {
            z_i
        } else {
            F128::ONE + z_i
        };
        for e in eval.elems.iter_mut() {
            *e *= scalar;
        }
    }
    eval.fold_vertical(eq_r_dprime)
}

#[cfg(test)]
use fold::subset_sums_4;
#[cfg(test)]
mod tests;

//! PCS leakage-rank audit — the machine-checked ZK certificate for the
//! hiding commitment + blinded opening (test-only).
//!
//! With a fixed challenger (`RandomChallenger` ignores observations, so every
//! challenge, query set, and fold coefficient is constant across runs), every
//! value the PCS reveals — opened rows at every level, the internal sumcheck
//! messages `(u_0, u_2)`, the final residual `yr`, and `y_g` — is an **affine
//! function** of `(mask, g, z_packed)` over F₂₁₂₈.
//!
//! Write the revealed vector as `revealed = A·masks + B·witness + const`.
//! Honest transcripts satisfy the verifier's linear consistency equations, so
//! `A` can never have full row rank; the correct simulatability criterion is
//!
//! ```text
//!     Image(B) ⊆ Image(A)
//! ```
//!
//! — witness variation adds no direction that the (uniform, prover-secret)
//! masks don't already randomize. Then the revealed distribution is a fixed
//! translate of the uniform distribution on Image(A), independent of the
//! witness, and a simulator samples it from the public data alone.
//!
//! **Conditioning on public inputs.** The claim value `v = ẑ_packed(point)`
//! is a public input to the PCS verification, and the opening's consistency
//! equation genuinely determines it from the revealed values (that is the
//! point of the PCS) — so an unrestricted witness probe escapes the mask
//! image in exactly the public-claim direction (measured: rank gap exactly 1
//! per claim). HVZK conditions on public inputs: the criterion is
//! `B(ker p) ⊆ Image(A)` where `p` maps the witness to the public claim
//! values. The audit therefore probes witness directions in `ker p` — char-2
//! pairs `eq_j⁻¹·e_j + eq_0⁻¹·e_0`, which leave the claim value unchanged —
//! and checks image inclusion by F₂₁₂₈ Gaussian elimination.
//!
//! A negative control re-runs the audit with the blinder `g` withheld from
//! the mask side and must FAIL (this is precisely the leak class that made
//! `g` necessary: pre-glue sumcheck messages and the `yr` top half).
//!
//! Witness bit-flips live in the F₂-span of the packed-slot columns
//! (multiplication by x^r is F₂₁₂₈-linear), so checking the F₂₁₂₈ span of the
//! 64 packed columns covers all bit-level witness variations.

use super::commit::{PcsParams, commit_zk};
use super::ligerito::ProverConfig;
use super::{DirectEqInd, PackedDirectClaim, open_batch_mixed_ligerito_with_precomputed_s_hat_v};
use crate::challenger::RandomChallenger;
use crate::field::F128;
use crate::zerocheck::PaddingSpec;
use crate::zerocheck::univariate_skip::build_eq;
use crate::zk::PlaybackSampler;

const M: usize = 13; // witness 2^13 bits = 64 packed F128
const W: usize = 1 << (M - 7); // 64
const MASK_SLOTS: usize = W; // low-half mask
const G_SLOTS: usize = 2 * W; // blinder
const CH_SEED: u64 = 0xA0D17;

fn tiny_params() -> PcsParams {
    PcsParams {
        m: M,
        log_inv_rate: 1,
        log_batch_size: 2,
        profile: Default::default(),
        zk: true,
    }
}

fn tiny_config() -> ProverConfig {
    let recursive_ks = vec![2usize, 2];
    let log_inv_rates = vec![1usize, 2, 3];
    let queries = vec![6usize, 4, 4];
    let n_levels = log_inv_rates.len();
    ProverConfig {
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
    }
}

/// Run one blinded opening and return the flattened revealed vector
/// (everything the proof exposes at the PCS layer). Claim values and
/// `s_hat_v` are the PIOP layer's masking responsibility (witness
/// randomizers) and are deliberately NOT part of this audit's revealed set —
/// this run uses a packed-direct claim only, so no `s_hat_v` exists at all.
fn revealed_vector(mask: &[F128], g: &[F128], z_packed: &[F128]) -> Vec<F128> {
    assert_eq!(mask.len(), MASK_SLOTS);
    assert_eq!(g.len(), G_SLOTS);
    assert_eq!(z_packed.len(), W);
    let params = tiny_params();
    // `commit_zk` consumes two field elements for each 256-bit initial-leaf
    // salt after the algebraic mask and blinder. The Merkle salts are not
    // part of this algebraic rank audit, so fix them to zero while preserving
    // the production sampler schedule.
    let playback: Vec<F128> = mask
        .iter()
        .chain(g.iter())
        .copied()
        .chain(std::iter::repeat_n(F128::ZERO, 2 * params.n_leaves()))
        .collect();
    let mut sampler = PlaybackSampler {
        data: &playback,
        pos: 0,
    };
    let (commitment, prover_data) = commit_zk(z_packed, &params, &mut sampler);

    // One packed-direct claim at a fixed point (value moves with the witness;
    // it is a PIOP-layer/public quantity, not part of this audit's output).
    let pd_point = audit_pd_point();
    let pd_eq = build_eq(&pd_point);
    let pd_value: F128 = pd_eq
        .iter()
        .zip(z_packed.iter())
        .map(|(e, z)| *e * *z)
        .fold(F128::ZERO, |a, b| a + b);

    let mut ch = RandomChallenger::new(CH_SEED);
    let proof = open_batch_mixed_ligerito_with_precomputed_s_hat_v(
        z_packed.to_vec(),
        &prover_data,
        &commitment,
        &[],
        &[],
        &[PackedDirectClaim {
            point: pd_point,
            value: pd_value,
            eq_ind: DirectEqInd::Dense(pd_eq),
        }],
        &PaddingSpec::dense(M),
        &tiny_config(),
        &mut ch,
    );

    let lp = &proof.ligerito;
    let mut out: Vec<F128> = Vec::new();
    for row in &lp.initial_proof.opened_rows {
        out.extend_from_slice(row);
    }
    for rp in &lp.recursive_proofs {
        for row in &rp.opened_rows {
            out.extend_from_slice(row);
        }
    }
    for row in &lp.final_proof.opened_rows {
        out.extend_from_slice(row);
    }
    out.extend_from_slice(&lp.final_proof.yr);
    for msg in &lp.sumcheck_transcript {
        out.push(msg.u_0);
        out.push(msg.u_2);
    }
    out.extend_from_slice(&lp.ood_values);
    out.push(proof.zk_blind.expect("zk proof").y_g);
    out
}

/// In-place F₂₁₂₈ row reduction; returns the rank. Rows are consumed.
fn rank_f128(mut rows: Vec<Vec<F128>>) -> usize {
    let width = rows.first().map(|r| r.len()).unwrap_or(0);
    let mut rank = 0usize;
    for col in 0..width {
        // Find a pivot row with a nonzero entry in `col`.
        let Some(p) = (rank..rows.len()).find(|&r| rows[r][col] != F128::ZERO) else {
            continue;
        };
        rows.swap(rank, p);
        let inv = rows[rank][col].inv();
        for j in col..width {
            let v = rows[rank][j];
            rows[rank][j] = v * inv;
        }
        let pivot_row = rows[rank].clone();
        for (r, row) in rows.iter_mut().enumerate() {
            if r != rank && row[col] != F128::ZERO {
                let factor = row[col];
                for j in col..width {
                    let sub = factor * pivot_row[j];
                    row[j] += sub;
                }
            }
        }
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    rank
}

/// The audit's fixed claim point (shared by `revealed_vector` and the
/// kernel-probe construction).
fn audit_pd_point() -> Vec<F128> {
    (0..(M - 7))
        .map(|i| F128 {
            lo: 0x9E37 + i as u64,
            hi: 0xC2B2 * (i as u64 + 1),
        })
        .collect()
}

/// Extract the probe matrices A (mask columns) and B (claim-preserving
/// witness columns) by affine differencing. `use_g`: whether the blinder-g
/// slots participate on the mask side (false = negative control).
fn probe_matrices(use_g: bool) -> (Vec<Vec<F128>>, Vec<Vec<F128>>) {
    let mask0 = vec![F128::ZERO; MASK_SLOTS];
    let g0 = vec![F128::ZERO; G_SLOTS];
    // Fixed nonzero witness so constants don't hide structural terms.
    let w0: Vec<F128> = (0..W)
        .map(|i| F128 {
            lo: 0xD1B5_4A32 + 3 * i as u64,
            hi: 0x9E51_7A1B * (i as u64 + 7),
        })
        .collect();
    let base = revealed_vector(&mask0, &g0, &w0);

    let mut a_cols: Vec<Vec<F128>> = Vec::new();
    for i in 0..MASK_SLOTS {
        let mut m = mask0.clone();
        m[i] = F128::ONE;
        let v = revealed_vector(&m, &g0, &w0);
        a_cols.push(v.iter().zip(base.iter()).map(|(x, b)| *x + *b).collect());
    }
    if use_g {
        for i in 0..G_SLOTS {
            let mut g = g0.clone();
            g[i] = F128::ONE;
            let v = revealed_vector(&mask0, &g, &w0);
            a_cols.push(v.iter().zip(base.iter()).map(|(x, b)| *x + *b).collect());
        }
    }
    // Witness probes restricted to ker(claim functional): the direction
    // eq_j⁻¹·e_j + eq_0⁻¹·e_0 shifts ẑ(point) by 1 + 1 = 0 (char 2). These
    // 63 directions span the kernel.
    let pd_eq = build_eq(&audit_pd_point());
    assert!(
        pd_eq.iter().all(|e| *e != F128::ZERO),
        "audit point hits a zero eq coordinate — pick another point"
    );
    let mut b_cols: Vec<Vec<F128>> = Vec::new();
    for j in 1..W {
        let mut w = w0.clone();
        w[j] += pd_eq[j].inv();
        w[0] += pd_eq[0].inv();
        let v = revealed_vector(&mask0, &g0, &w);
        b_cols.push(v.iter().zip(base.iter()).map(|(x, b)| *x + *b).collect());
    }
    (a_cols, b_cols)
}

#[test]
fn pcs_rank_audit_witness_image_covered() {
    let (a_cols, b_cols) = probe_matrices(true);
    let rank_a = rank_f128(a_cols.clone());
    let mut all = a_cols;
    let n_a = all.len();
    all.extend(b_cols);
    let rank_ab = rank_f128(all);
    assert!(rank_a > 0);
    assert_eq!(
        rank_a, rank_ab,
        "witness variation escapes the mask image: rank(A)={rank_a} (of {n_a} probes), \
         rank([A|B])={rank_ab} — the PCS leaks a witness functional"
    );
}

#[test]
fn pcs_rank_audit_negative_control_without_g() {
    // Withhold the blinder g from the mask side: the low-half mask alone must
    // NOT cover the witness image (pre-glue sumcheck messages + yr top half
    // are then clear witness functionals). This validates the auditor.
    let (a_cols, b_cols) = probe_matrices(false);
    let rank_a = rank_f128(a_cols.clone());
    let mut all = a_cols;
    all.extend(b_cols);
    let rank_ab = rank_f128(all);
    assert!(
        rank_ab > rank_a,
        "negative control failed: mask-only image unexpectedly covers the witness \
         (rank {rank_a} = {rank_ab}) — the auditor would not catch a missing blinder"
    );
}

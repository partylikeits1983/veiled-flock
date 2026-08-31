//! Exact L0 replacement translator for the blinded PCS opening.
//!
//! Hashes are the boundary. This module works on the linear codeword rows
//! before hashing and checks the closed-form translation against the actual
//! additive-NTT encoding used by `commit_zk`.

use crate::field::F128;
use crate::linalg::F128Mat;
use crate::ntt::AdditiveNttF128;

use super::commit::PcsParams;
use super::ligerito::{FinalProof, LigeritoProof, RecursiveProof};
use super::ring_switch::RingSwitchProof;
use super::{BatchOpeningProofLigerito, ZkBlindOpening};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcsMaskTranslation {
    pub delta_mu: Vec<F128>,
    pub delta_g_lo: Vec<F128>,
    pub delta_g_top: Vec<F128>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PcsMaskTranslationError {
    ZeroChallenge,
    InvalidQuerySet,
    InvalidWitnessDeltaLength,
    SingularMaskSystem,
    OpenedRowsNotPreserved,
    InvalidPublicFunctionalLength,
    PublicFunctionalNotInKernel,
    PublicFunctionalNotPreserved,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L0EntropyBound {
    pub opened_positions: usize,
    pub mask_symbols_per_lane: usize,
    pub leaf_f128_symbols: usize,
    pub conditional_bits_per_fresh_leaf: usize,
}

/// Structural certificate for the initial low-mask encoding system.
///
/// The first `mask_symbols_per_lane` LCH novel-basis elements have degrees
/// `0, ..., mask_symbols_per_lane - 1` and therefore span all polynomials
/// below that degree bound. Evaluation at `q` distinct field points is
/// surjective whenever `q <= mask_symbols_per_lane`, by interpolation. Thus
/// these purely combinatorial checks certify full row rank for every query set
/// satisfying them; no challenge-specific matrix rank computation is needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L0QueryRankCertificate {
    pub domain_positions: usize,
    pub opened_positions: usize,
    pub mask_symbols_per_lane: usize,
}

/// Exhaustive destructuring makes proof-schema additions fail compilation
/// until their replacement behavior is reviewed here.
pub fn assert_proof_fields_classified(proof: &BatchOpeningProofLigerito) {
    let BatchOpeningProofLigerito {
        ring_switches,
        ligerito,
        zk_blind,
    } = proof;
    for ring_switch in ring_switches {
        let RingSwitchProof { s_hat_v: _ } = ring_switch;
    }
    let LigeritoProof {
        initial_root: _,
        initial_proof,
        recursive_roots: _,
        recursive_proofs,
        final_proof,
        sumcheck_transcript: _,
        grinding_nonces: _,
        ood_values: _,
        fold_grinding_nonces: _,
    } = ligerito;
    let RecursiveProof {
        opened_rows: _,
        leaf_salts: _,
        merkle_proof: _,
    } = initial_proof;
    for recursive in recursive_proofs {
        let RecursiveProof {
            opened_rows: _,
            leaf_salts: _,
            merkle_proof: _,
        } = recursive;
    }
    let FinalProof {
        yr: _,
        opened_rows: _,
        merkle_proof: _,
    } = final_proof;
    if let Some(blind) = zk_blind {
        let ZkBlindOpening {
            y_g: _,
            c_grind_nonce: _,
        } = blind;
    }
}

/// Encode `(mu, z, g)` using the exact wide interleaving and additive NTT of
/// the hiding commitment, without constructing a Merkle tree.
pub fn encode_zk_linear(params: &PcsParams, mu: &[F128], z: &[F128], g: &[F128]) -> Vec<F128> {
    assert!(params.zk);
    assert_eq!(mu.len(), z.len());
    assert_eq!(g.len(), 2 * z.len());
    assert_eq!(z.len(), 1usize << params.witness_log_msg_len());
    let num_ntts = params.num_ntts();
    let wide = 2 * num_ntts;
    let message_positions = g.len() / num_ntts;
    let mask_positions = mu.len() / num_ntts;
    let mut codeword = vec![F128::ZERO; params.codeword_len_f128()];
    for (position, row) in codeword.chunks_mut(wide).enumerate() {
        let source_position = position % message_positions;
        let f_source = if source_position < mask_positions {
            &mu[source_position * num_ntts..(source_position + 1) * num_ntts]
        } else {
            let witness_position = source_position - mask_positions;
            &z[witness_position * num_ntts..(witness_position + 1) * num_ntts]
        };
        row[..num_ntts].copy_from_slice(f_source);
        row[num_ntts..]
            .copy_from_slice(&g[source_position * num_ntts..(source_position + 1) * num_ntts]);
    }
    AdditiveNttF128::standard(params.k_code()).forward_transform_interleaved_from_layer(
        &mut codeword,
        wide,
        params.log_inv_rate,
    );
    codeword
}

fn selected_f_rows(params: &PcsParams, codeword: &[F128], queries: &[usize]) -> Vec<F128> {
    let wide = 2 * params.num_ntts();
    queries
        .iter()
        .flat_map(|&query| {
            assert!(query < params.n_positions());
            codeword[query * wide..query * wide + params.num_ntts()]
                .iter()
                .copied()
        })
        .collect()
}

/// Translate a claim-preserving witness-message delta into PCS mask deltas.
/// The returned translation makes every selected raw L0 row invariant and
/// makes the combined recursive vector `F = [mu || z] + c*g` invariant
/// globally.
pub fn translate_mask_for_queries(
    params: &PcsParams,
    c: F128,
    queries: &[usize],
    witness_delta: &[F128],
) -> Result<PcsMaskTranslation, PcsMaskTranslationError> {
    if c == F128::ZERO {
        return Err(PcsMaskTranslationError::ZeroChallenge);
    }
    certify_l0_query_rank(params, queries).ok_or(PcsMaskTranslationError::InvalidQuerySet)?;
    let w = 1usize << params.witness_log_msg_len();
    if witness_delta.len() != w {
        return Err(PcsMaskTranslationError::InvalidWitnessDeltaLength);
    }
    let zero_w = vec![F128::ZERO; w];
    let zero_g = vec![F128::ZERO; 2 * w];

    let witness_codeword = encode_zk_linear(params, &zero_w, witness_delta, &zero_g);
    let rhs = selected_f_rows(params, &witness_codeword, queries);
    let equation_count = rhs.len();
    let mut matrix_data = vec![F128::ZERO; equation_count * w];
    for column in 0..w {
        let mut basis = vec![F128::ZERO; w];
        basis[column] = F128::ONE;
        let encoded = encode_zk_linear(params, &basis, &zero_w, &zero_g);
        for (row, value) in selected_f_rows(params, &encoded, queries)
            .into_iter()
            .enumerate()
        {
            matrix_data[row * w + column] = value;
        }
    }
    let delta_mu = F128Mat::new(equation_count, w, matrix_data)
        .solve(&rhs)
        .ok_or(PcsMaskTranslationError::SingularMaskSystem)?;
    let c_inv = c.inv();
    let delta_g_lo = delta_mu.iter().map(|value| c_inv * *value).collect();
    let delta_g_top = witness_delta.iter().map(|value| c_inv * *value).collect();
    let translation = PcsMaskTranslation {
        delta_mu,
        delta_g_lo,
        delta_g_top,
    };

    let delta_g = translation
        .delta_g_lo
        .iter()
        .chain(&translation.delta_g_top)
        .copied()
        .collect::<Vec<_>>();
    let delta_codeword = encode_zk_linear(params, &translation.delta_mu, witness_delta, &delta_g);
    let wide = 2 * params.num_ntts();
    if queries.iter().any(|query| {
        delta_codeword[query * wide..(query + 1) * wide]
            .iter()
            .any(|value| *value != F128::ZERO)
    }) {
        return Err(PcsMaskTranslationError::OpenedRowsNotPreserved);
    }
    Ok(translation)
}

/// Joint VEIL coupling for the exact initial PCS view. In addition to the
/// opened L0 rows and global blinded vector `F`, require every exposed direct
/// functional to be public-statement-derived: its basis must annihilate the
/// witness difference. The returned affine mask translation then preserves
/// those blinder evaluations as well because
/// `delta_g_top = c^-1 * witness_delta`.
pub fn translate_joint_view_for_queries(
    params: &PcsParams,
    c: F128,
    queries: &[usize],
    witness_delta: &[F128],
    public_functional_bases: &[&[F128]],
) -> Result<PcsMaskTranslation, PcsMaskTranslationError> {
    for basis in public_functional_bases {
        if basis.len() != witness_delta.len() {
            return Err(PcsMaskTranslationError::InvalidPublicFunctionalLength);
        }
        let delta_value = basis
            .iter()
            .zip(witness_delta)
            .fold(F128::ZERO, |acc, (weight, value)| acc + *weight * *value);
        if delta_value != F128::ZERO {
            return Err(PcsMaskTranslationError::PublicFunctionalNotInKernel);
        }
    }
    let translation = translate_mask_for_queries(params, c, queries, witness_delta)?;
    if public_functional_bases.iter().any(|basis| {
        basis
            .iter()
            .zip(&translation.delta_g_top)
            .fold(F128::ZERO, |acc, (weight, value)| acc + *weight * *value)
            != F128::ZERO
    }) {
        return Err(PcsMaskTranslationError::PublicFunctionalNotPreserved);
    }
    Ok(translation)
}

/// Certify full row rank of the low-mask evaluation system for an arbitrary
/// L0 query set. The registered verifier's sampler returns distinct positions,
/// so every set it can generate passes whenever its configured query count is
/// at most the per-lane mask dimension.
pub fn certify_l0_query_rank(
    params: &PcsParams,
    queries: &[usize],
) -> Option<L0QueryRankCertificate> {
    if !params.zk {
        return None;
    }
    let domain_positions = params.n_positions();
    let mask_symbols_per_lane = (1usize << params.witness_log_msg_len()) / params.num_ntts();
    if queries.len() > mask_symbols_per_lane
        || queries.iter().any(|&query| query >= domain_positions)
    {
        return None;
    }
    let distinct = queries
        .iter()
        .copied()
        .collect::<std::collections::HashSet<_>>();
    if distinct.len() != queries.len() {
        return None;
    }
    Some(L0QueryRankCertificate {
        domain_positions,
        opened_positions: queries.len(),
        mask_symbols_per_lane,
    })
}

/// Structural RS-subcode counting gate used by the L0 replacement theorem.
/// When the number of distinct opened positions is strictly below the mask
/// coefficient dimension per lane, every additional leaf retains all of its
/// `f'` and `g` lane symbols as field entropy.
pub fn l0_entropy_bound(params: &PcsParams, opened_positions: usize) -> Option<L0EntropyBound> {
    assert!(params.zk);
    let witness_slots = 1usize << params.witness_log_msg_len();
    let mask_symbols_per_lane = witness_slots / params.num_ntts();
    if opened_positions >= mask_symbols_per_lane {
        return None;
    }
    let leaf_f128_symbols = 2 * params.num_ntts();
    Some(L0EntropyBound {
        opened_positions,
        mask_symbols_per_lane,
        leaf_f128_symbols,
        conditional_bits_per_fresh_leaf: 128 * leaf_f128_symbols,
    })
}

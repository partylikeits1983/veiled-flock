//! Single-column commitment and masked lane reduction. The enclosing ZK
//! circuit must bind the masked reduction to its evaluation claims.

use super::commit::{PcsParams, ProverData, commit_encoded_rows, commit_encoded_rows_at};
use super::ligerito::{
    self, LigeritoProof, ProverConfig, SumcheckMessage, SumcheckProver, VerifierConfig,
};
use super::query_padding::PaddingCode;
use super::ring_switch::inner_product;
use crate::challenger::Challenger;
use crate::field::F128;
use crate::merkle::Hash;
use crate::ntt::AdditiveNttF128;
use crate::ro::{RoChannel, RoContext};
use crate::zerocheck::univariate_skip::build_eq;
use crate::zk::MaskSampler;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ColumnCommitment {
    pub root: Hash,
    pub params: PcsParams,
}

pub struct ColumnProverData {
    data: ProverData,
    padding_code: Option<PaddingCode>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ColumnOpening {
    pub masked_rounds: Vec<SumcheckMessage>,
    pub masked_blind_value: F128,
    pub fold_nonces: Vec<u64>,
    pub blind_nonce: u64,
    pub target: F128,
    pub padding: Vec<F128>,
    pub ligerito: LigeritoProof,
}

#[derive(Clone, Copy)]
pub struct ColumnReductionView<'a> {
    pub masked_rounds: &'a [SumcheckMessage],
    pub masked_blind_value: F128,
    pub fold_nonces: &'a [u64],
    pub blind_nonce: u64,
    pub target: F128,
}

impl ColumnOpening {
    pub fn reduction_view(&self) -> ColumnReductionView<'_> {
        ColumnReductionView {
            masked_rounds: &self.masked_rounds,
            masked_blind_value: self.masked_blind_value,
            fold_nonces: &self.fold_nonces,
            blind_nonce: self.blind_nonce,
            target: self.target,
        }
    }
}

pub struct ColumnReduction {
    pub lane_challenges: Vec<F128>,
    pub blind_challenge: F128,
}

pub fn mask_count(params: &PcsParams) -> usize {
    2 * params.log_batch_size + 1
}

pub fn codeword_len(params: &PcsParams) -> usize {
    params.n_positions() * (params.num_ntts() + 1)
}

pub fn commit<R: MaskSampler + ?Sized>(
    witness: &[F128],
    params: &PcsParams,
    rng: &mut R,
    ro: &RoContext,
    channel: RoChannel,
) -> (ColumnCommitment, ColumnProverData) {
    params.validate().expect("invalid PCS parameters");
    assert!(params.zk);
    assert_eq!(witness.len(), 1 << params.witness_log_msg_len());
    let lanes = params.num_ntts();
    let mask_positions = witness.len() / lanes;
    let mut mask = crate::scratch::take_f128(witness.len());
    rng.fill_f128(&mut mask);
    let mut blind = crate::scratch::take_f128(2 * mask_positions);
    rng.fill_f128(&mut blind);
    let mut salt_fields = vec![F128::ZERO; 2 * params.n_positions()];
    rng.fill_f128(&mut salt_fields);
    let salts: Vec<[u8; 32]> = salt_fields
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let mut salt = [0u8; 32];
            for (dst, limb) in salt
                .as_chunks_mut::<8>()
                .0
                .iter_mut()
                .zip([pair[0].lo, pair[0].hi, pair[1].lo, pair[1].hi])
            {
                dst.copy_from_slice(&limb.to_le_bytes());
            }
            salt
        })
        .collect();
    let mut codeword = crate::scratch::take_f128(codeword_len(params));
    AdditiveNttF128::standard(params.k_code()).rs_encode_interleaved_from_rows(
        &mut codeword,
        lanes + 1,
        params.log_inv_rate,
        |position| {
            let (source, offset) = if position < mask_positions {
                (&mask[..], position)
            } else {
                (witness, position - mask_positions)
            };
            [
                &source[offset * lanes..(offset + 1) * lanes],
                &blind[position..position + 1],
            ]
        },
    );
    let (commitment, mut data) = commit_encoded_rows(codeword, params, salts, ro, channel);
    data.zk_mask = mask;
    data.zk_blind = blind;
    (
        ColumnCommitment {
            root: commitment.root,
            params: commitment.params,
        },
        ColumnProverData {
            data,
            padding_code: None,
        },
    )
}

pub fn commit_with_query_padding<R: MaskSampler + ?Sized>(
    witness: &[F128],
    params: &PcsParams,
    queries: usize,
    rng: &mut R,
    ro: &RoContext,
    channel: RoChannel,
) -> (ColumnCommitment, ColumnProverData) {
    params.validate().expect("invalid PCS parameters");
    assert!(params.zk);
    assert_eq!(witness.len(), 1 << params.witness_log_msg_len());
    let lanes = params.num_ntts();
    let height = witness.len() / lanes;
    assert!(queries > 0 && queries <= height);
    let code = PaddingCode::new(params.log_dim() - 1, params.k_code() - 1);
    let mut mask = vec![F128::ZERO; queries * lanes];
    rng.fill_f128(&mut mask);
    let mut blind = vec![F128::ZERO; height + queries];
    rng.fill_f128(&mut blind);
    let mut message = crate::scratch::take_f128(height * (lanes + 1));
    for (position, row) in message.chunks_exact_mut(lanes + 1).enumerate() {
        row[..lanes].copy_from_slice(&witness[position * lanes..(position + 1) * lanes]);
        row[lanes] = blind[position];
    }
    let mut pads = vec![F128::ZERO; queries * (lanes + 1)];
    for (position, row) in pads.chunks_exact_mut(lanes + 1).enumerate() {
        row[..lanes].copy_from_slice(&mask[position * lanes..(position + 1) * lanes]);
        row[lanes] = blind[height + position];
    }
    let codeword = code.encode(&message, &pads, lanes + 1);
    crate::scratch::give_f128(message);
    let mut salt_fields = vec![F128::ZERO; 2 * code.code_len()];
    rng.fill_f128(&mut salt_fields);
    let salts = salt_fields
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let mut salt = [0u8; 32];
            for (bytes, limb) in salt
                .as_chunks_mut::<8>()
                .0
                .iter_mut()
                .zip([pair[0].lo, pair[0].hi, pair[1].lo, pair[1].hi])
            {
                bytes.copy_from_slice(&limb.to_le_bytes());
            }
            salt
        })
        .collect();
    let (commitment, mut data) =
        commit_encoded_rows_at(codeword, params, code.code_len(), salts, ro, channel);
    data.zk_mask = mask;
    data.zk_blind = blind;
    (
        ColumnCommitment {
            root: commitment.root,
            params: commitment.params,
        },
        ColumnProverData {
            data,
            padding_code: Some(code),
        },
    )
}

fn next_nonzero<Ch: Challenger>(challenger: &mut Ch) -> F128 {
    loop {
        let value = challenger.sample_f128();
        if !value.is_zero() {
            return value;
        }
    }
}

fn backend_prover(config: &ProverConfig) -> ProverConfig {
    let mut config = config.clone();
    config.initial_k = 0;
    config.initial_log_num_interleaved = 0;
    config
}

fn backend_verifier(config: &VerifierConfig) -> VerifierConfig {
    let mut config = config.clone();
    config.initial_k = 0;
    config.initial_log_num_interleaved = 0;
    config
}

#[allow(clippy::too_many_arguments)]
pub fn open<Ch: Challenger + Send>(
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    data: &ColumnProverData,
    config: &ProverConfig,
    masks: &[F128],
    ro: &RoContext,
    channel: RoChannel,
    challenger: &mut Ch,
) -> (ColumnOpening, ColumnReduction) {
    let (opening, reduction, ()) = open_with(
        witness,
        basis,
        target,
        data,
        config,
        masks,
        ro,
        channel,
        challenger,
        None,
        |_, _| (),
    );
    (opening, reduction)
}

/// Run an independent proof after the reduction, alongside the native PCS backend.
#[allow(clippy::too_many_arguments)]
pub fn open_with<Ch: Challenger + Send, T: Send>(
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    data: &ColumnProverData,
    config: &ProverConfig,
    masks: &[F128],
    ro: &RoContext,
    channel: RoChannel,
    challenger: &mut Ch,
    initial_message: Option<SumcheckMessage>,
    companion: impl FnOnce(ColumnReductionView<'_>, &ColumnReduction) -> T + Send,
) -> (ColumnOpening, ColumnReduction, T) {
    assert_eq!(masks.len(), 2 * config.initial_k + 1);
    assert!(!config.fold_grinding_taper.iter().any(|v| *v));
    assert_eq!(witness.len(), basis.len());
    let (message, padded_basis) = if let Some(code) = &data.padding_code {
        assert_eq!(witness.len(), code.message_len() << config.initial_k);
        assert_eq!(
            data.data.zk_mask.len(),
            config.queries[0] << config.initial_k
        );
        assert_eq!(1 << config.initial_log_msg_cols, code.message_len());
        (witness, basis)
    } else {
        assert_eq!(witness.len(), data.data.zk_mask.len());
        let mut message = data.data.zk_mask.clone();
        message.extend(witness);
        let mut padded_basis = vec![F128::ZERO; basis.len()];
        padded_basis.extend(basis);
        (message, padded_basis)
    };
    let (mut sumcheck, mut msg) = if let Some(first) = initial_message {
        assert!(data.padding_code.is_some());
        SumcheckProver::new_with_first_msg(message, padded_basis, target, first)
    } else {
        SumcheckProver::new(message, padded_basis, target)
    };
    challenger.observe_label(if data.padding_code.is_some() {
        b"flock-query-padded-column-reduction"
    } else {
        b"flock-single-column-reduction"
    });
    let mut masked_rounds = Vec::new();
    let mut lane_challenges = Vec::new();
    let mut fold_nonces = Vec::new();
    for round in 0..config.initial_k {
        let masked = SumcheckMessage {
            u_0: msg.u_0 + masks[2 * round],
            u_2: msg.u_2 + masks[2 * round + 1],
        };
        challenger.observe_f128(masked.u_0);
        challenger.observe_f128(masked.u_2);
        let bits = config.fold_grinding_bits[0];
        fold_nonces.push(challenger.grind_pow(bits as u32));
        let r = challenger.sample_f128();
        msg = sumcheck.fold(r);
        lane_challenges.push(r);
        masked_rounds.push(masked);
    }
    let blind_value = inner_product(
        &data.data.zk_blind[..sumcheck.basis().len()],
        sumcheck.basis(),
    );
    let masked_blind_value = blind_value + masks[2 * config.initial_k];
    challenger.observe_f128(masked_blind_value);
    let blind_nonce =
        challenger.grind_pow(ligerito::l0_derived_grind_bits(&config.fold_grinding_bits));
    let c = next_nonzero(challenger);
    let mut folded = sumcheck.f().to_vec();
    folded
        .par_iter_mut()
        .zip(&data.data.zk_blind)
        .for_each(|(f, g)| *f += c * *g);
    let basis = sumcheck.basis().to_vec();
    let target = inner_product(&folded, &basis);
    challenger.observe_f128(target);
    let mut weights = build_eq(&lane_challenges);
    let padding = if let Some(code) = &data.padding_code {
        data.data
            .zk_mask
            .chunks_exact(weights.len())
            .zip(&data.data.zk_blind[code.message_len()..])
            .map(|(row, blind)| inner_product(row, &weights) + c * *blind)
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    for value in &padding {
        challenger.observe_f128(*value);
    }
    weights.push(c);
    let reduction = ColumnReduction {
        lane_challenges,
        blind_challenge: c,
    };
    let view = ColumnReductionView {
        masked_rounds: &masked_rounds,
        masked_blind_value,
        fold_nonces: &fold_nonces,
        blind_nonce,
        target,
    };
    let backend = || {
        ligerito::recursive_prover_combined_columns(
            &backend_prover(config),
            folded,
            basis,
            target,
            &data.data,
            &weights,
            data.padding_code
                .as_ref()
                .map(|code| (code, padding.as_slice())),
            ro,
            channel,
            challenger,
        )
    };
    let auxiliary = || companion(view, &reduction);
    let (ligerito, auxiliary) = if ro.is_native() {
        rayon::join(backend, auxiliary)
    } else {
        (backend(), auxiliary())
    };
    (
        ColumnOpening {
            masked_rounds,
            masked_blind_value,
            fold_nonces,
            blind_nonce,
            target,
            padding,
            ligerito,
        },
        reduction,
        auxiliary,
    )
}

/// Verify authenticated rows and the folded PCS. The caller must separately
/// check the masked lane reduction in its ZK circuit.
#[allow(clippy::too_many_arguments)]
pub fn verify_backend<Ch, F>(
    commitment: &ColumnCommitment,
    proof: &ColumnOpening,
    config: &VerifierConfig,
    eval_basis: F,
    ro: &RoContext,
    channel: RoChannel,
    challenger: &mut Ch,
) -> Option<ColumnReduction>
where
    Ch: Challenger,
    F: Fn(&[F128], &[F128], usize) -> Vec<F128>,
{
    let params = &commitment.params;
    if !params.zk
        || params.validate().is_err()
        || config.initial_k != params.log_batch_size
        || config.log_inv_rates.first() != Some(&params.log_inv_rate)
        || proof.masked_rounds.len() != config.initial_k
        || proof.fold_nonces.len() != config.initial_k
        || config.fold_grinding_bits.is_empty()
        || config.fold_grinding_taper.iter().any(|v| *v)
    {
        return None;
    }
    let padding_code = if config.initial_log_msg_cols.checked_add(1) == Some(params.log_dim()) {
        let code = PaddingCode::new(params.log_dim() - 1, params.k_code() - 1);
        let queries = *config.queries.first()?;
        if queries == 0 || queries > code.message_len() || proof.padding.len() != queries {
            return None;
        }
        Some(code)
    } else if config.initial_log_msg_cols == params.log_dim() && proof.padding.is_empty() {
        None
    } else {
        return None;
    };
    challenger.observe_label(if padding_code.is_some() {
        b"flock-query-padded-column-reduction"
    } else {
        b"flock-single-column-reduction"
    });
    let mut lane_challenges = Vec::new();
    for (msg, nonce) in proof.masked_rounds.iter().zip(&proof.fold_nonces) {
        challenger.observe_f128(msg.u_0);
        challenger.observe_f128(msg.u_2);
        if !challenger.verify_pow(*nonce, config.fold_grinding_bits[0] as u32) {
            return None;
        }
        lane_challenges.push(challenger.sample_f128());
    }
    challenger.observe_f128(proof.masked_blind_value);
    if !challenger.verify_pow(
        proof.blind_nonce,
        ligerito::l0_derived_grind_bits(&config.fold_grinding_bits),
    ) {
        return None;
    }
    let c = next_nonzero(challenger);
    challenger.observe_f128(proof.target);
    for value in &proof.padding {
        challenger.observe_f128(*value);
    }
    let mut weights = build_eq(&lane_challenges);
    weights.push(c);
    let valid = ligerito::recursive_verifier_combined_columns(
        &backend_verifier(config),
        &proof.ligerito,
        config.initial_log_msg_cols,
        proof.target,
        &commitment.root,
        |ris, log_yr| eval_basis(&lane_challenges, ris, log_yr),
        &weights,
        padding_code
            .as_ref()
            .map(|code| (code, proof.padding.as_slice())),
        ro,
        channel,
        challenger,
    );
    valid.then_some(ColumnReduction {
        lane_challenges,
        blind_challenge: c,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsChallenger;
    use crate::zk::ZkRng;

    fn configs() -> (ProverConfig, VerifierConfig) {
        let p = ProverConfig {
            initial_k: 2,
            initial_log_msg_cols: 5,
            initial_log_num_interleaved: 2,
            recursive_steps: 2,
            recursive_ks: vec![2, 2],
            recursive_log_msg_cols: vec![3, 1],
            log_inv_rates: vec![1, 2, 3],
            queries: vec![6, 4, 4],
            grinding_bits: vec![0; 3],
            fold_grinding_bits: vec![0; 3],
            fold_grinding_taper: vec![false; 3],
            ood_samples: vec![0; 3],
        };
        let v = VerifierConfig {
            initial_k: p.initial_k,
            initial_log_msg_cols: p.initial_log_msg_cols,
            initial_log_num_interleaved: p.initial_log_num_interleaved,
            recursive_steps: p.recursive_steps,
            recursive_ks: p.recursive_ks.clone(),
            recursive_log_msg_cols: p.recursive_log_msg_cols.clone(),
            log_inv_rates: p.log_inv_rates.clone(),
            queries: p.queries.clone(),
            grinding_bits: p.grinding_bits.clone(),
            fold_grinding_bits: p.fold_grinding_bits.clone(),
            fold_grinding_taper: p.fold_grinding_taper.clone(),
            ood_samples: p.ood_samples.clone(),
        };
        (p, v)
    }

    fn eval(mut values: Vec<F128>, point: &[F128]) -> F128 {
        for r in point {
            values = values
                .as_chunks::<2>()
                .0
                .iter()
                .map(|v| v[0] + *r * (v[0] + v[1]))
                .collect();
        }
        assert_eq!(values.len(), 1);
        values[0]
    }

    #[test]
    fn query_padded_column_roundtrip_and_tampering() {
        let params = PcsParams::new(13, 2, Default::default(), true).unwrap();
        let (mut p, mut v) = configs();
        p.initial_log_msg_cols = 4;
        p.recursive_ks = vec![2, 1];
        p.recursive_log_msg_cols = vec![2, 1];
        v.initial_log_msg_cols = p.initial_log_msg_cols;
        v.recursive_ks = p.recursive_ks.clone();
        v.recursive_log_msg_cols = p.recursive_log_msg_cols.clone();
        let mut rng = ZkRng::from_seed([97; 32]);
        let mut witness = vec![F128::ZERO; 64];
        let mut basis = witness.clone();
        rng.fill_f128(&mut witness);
        rng.fill_f128(&mut basis);
        let target = inner_product(&witness, &basis);
        let ro = RoContext::plain();
        let (commitment, data) = commit_with_query_padding(
            &witness,
            &params,
            p.queries[0],
            &mut rng,
            &ro,
            RoChannel::Witness,
        );
        assert_eq!(data.data.codeword.len(), 32 * 5);
        assert_eq!(data.data.zk_mask.len(), 6 * 4);
        assert_eq!(data.data.zk_blind.len(), 16 + 6);
        let mut masks = vec![F128::ZERO; mask_count(&params)];
        rng.fill_f128(&mut masks);
        let (proof, _) = open(
            witness,
            basis.clone(),
            target,
            &data,
            &p,
            &masks,
            &ro,
            RoChannel::Witness,
            &mut FsChallenger::new(b"query-padded-column-test"),
        );
        let verify = |proof: &ColumnOpening| {
            verify_backend(
                &commitment,
                proof,
                &v,
                |lanes, ris, log_yr| {
                    (0..1 << log_yr)
                        .map(|y| {
                            let mut point = lanes.to_vec();
                            point.extend_from_slice(ris);
                            point.extend(
                                (0..log_yr).map(|bit| F128::new(((y >> bit) & 1) as u64, 0)),
                            );
                            eval(basis.clone(), &point)
                        })
                        .collect()
                },
                &ro,
                RoChannel::Witness,
                &mut FsChallenger::new(b"query-padded-column-test"),
            )
        };
        let reduction = verify(&proof).expect("valid query-padded opening");
        let mut running = target;
        for (i, (message, r)) in proof
            .masked_rounds
            .iter()
            .zip(&reduction.lane_challenges)
            .enumerate()
        {
            let u0 = message.u_0 + masks[2 * i];
            let u2 = message.u_2 + masks[2 * i + 1];
            running = u0 + running * *r + u2 * (*r * *r + *r);
        }
        assert_eq!(
            running + reduction.blind_challenge * (proof.masked_blind_value + masks[4]),
            proof.target
        );
        for field in 0..5 {
            let mut bad = proof.clone();
            match field {
                0 => bad.padding[0] += F128::ONE,
                1 => {
                    bad.padding.pop();
                }
                2 => bad.target += F128::ONE,
                3 => bad.ligerito.initial_proof.opened_rows[0][0] += F128::ONE,
                _ => bad.ligerito.initial_proof.opened_rows[0][4] += F128::ONE,
            }
            assert!(verify(&bad).is_none(), "accepted mutation {field}");
        }
    }

    #[test]
    fn single_column_roundtrip_and_tampering() {
        let params = PcsParams::new(13, 2, Default::default(), true).unwrap();
        let (p, v) = configs();
        let mut rng = ZkRng::from_seed([17; 32]);
        let mut witness = vec![F128::ZERO; 64];
        let mut basis = witness.clone();
        rng.fill_f128(&mut witness);
        rng.fill_f128(&mut basis);
        let target = inner_product(&witness, &basis);
        let ro = RoContext::plain();
        let (commitment, data) = commit(&witness, &params, &mut rng, &ro, RoChannel::Witness);
        assert_eq!(data.data.zk_blind.len(), 32);
        assert_eq!(data.data.codeword.len(), params.n_positions() * 5);
        let mut masks = vec![F128::ZERO; mask_count(&params)];
        rng.fill_f128(&mut masks);
        let (proof, reduction) = open(
            witness,
            basis.clone(),
            target,
            &data,
            &p,
            &masks,
            &ro,
            RoChannel::Witness,
            &mut FsChallenger::new(b"single-column-test"),
        );
        let mut padded_basis = vec![F128::ZERO; basis.len()];
        padded_basis.extend(basis);
        let verify = |proof: &ColumnOpening| {
            verify_backend(
                &commitment,
                proof,
                &v,
                |lanes, ris, log_yr| {
                    (0..1 << log_yr)
                        .map(|y| {
                            let mut point = lanes.to_vec();
                            point.extend_from_slice(ris);
                            point.extend(
                                (0..log_yr).map(|bit| F128::new(((y >> bit) & 1) as u64, 0)),
                            );
                            eval(padded_basis.clone(), &point)
                        })
                        .collect()
                },
                &ro,
                RoChannel::Witness,
                &mut FsChallenger::new(b"single-column-test"),
            )
        };
        let checked = verify(&proof).expect("valid backend");
        assert_eq!(checked.lane_challenges, reduction.lane_challenges);
        assert_eq!(checked.blind_challenge, reduction.blind_challenge);
        let mut running = target;
        for (i, (msg, r)) in proof
            .masked_rounds
            .iter()
            .zip(&checked.lane_challenges)
            .enumerate()
        {
            let u0 = msg.u_0 + masks[2 * i];
            let u2 = msg.u_2 + masks[2 * i + 1];
            running = u0 + running * *r + u2 * (*r * *r + *r);
        }
        let blind = proof.masked_blind_value + masks[2 * p.initial_k];
        assert_eq!(running + checked.blind_challenge * blind, proof.target);
        for field in 0..6 {
            let mut bad = proof.clone();
            match field {
                0 => bad.target += F128::ONE,
                1 => bad.masked_rounds[0].u_0 += F128::ONE,
                2 => bad.masked_blind_value += F128::ONE,
                3 => bad.ligerito.initial_proof.opened_rows[0][0] += F128::ONE,
                4 => bad.ligerito.initial_proof.opened_rows[0][4] += F128::ONE,
                _ => {
                    bad.ligerito.initial_proof.opened_rows[0].pop();
                }
            }
            assert!(verify(&bad).is_none(), "accepted mutation {field}");
        }
    }
    #[test]
    fn single_column_translation_preserves_the_joint_algebraic_view() {
        use crate::challenger::RandomChallenger;
        use crate::linalg::F128Mat;
        use crate::zk::PlaybackSampler;
        let params = PcsParams::new(13, 2, Default::default(), true).unwrap();
        for query_padding in [false, true] {
            let (mut config, _) = configs();
            if query_padding {
                config.initial_log_msg_cols = 4;
                config.recursive_ks = vec![2, 1];
                config.recursive_log_msg_cols = vec![2, 1];
            }
            let lanes = params.num_ntts();
            let height = (1 << params.witness_log_msg_len()) / lanes;
            let padding_height = if query_padding {
                config.queries[0]
            } else {
                height
            };
            let log_code = params.k_code() - usize::from(query_padding);
            let positions = 1 << log_code;
            let ro = RoContext::plain();
            let commit_layout = |witness: &[F128], rng: &mut dyn MaskSampler| {
                if query_padding {
                    commit_with_query_padding(
                        witness,
                        &params,
                        config.queries[0],
                        rng,
                        &ro,
                        RoChannel::Witness,
                    )
                } else {
                    commit(witness, &params, rng, &ro, RoChannel::Witness)
                }
            };
            for (seed, preserve_target) in [(71, true), (72, false), (73, false)] {
                let mut rng = ZkRng::from_seed([seed as u8; 32]);
                let mut witness = vec![F128::ZERO; height * lanes];
                let mut basis = witness.clone();
                let mut delta = witness.clone();
                let mut masks = vec![F128::ZERO; mask_count(&params)];
                rng.fill_f128(&mut witness);
                rng.fill_f128(&mut basis);
                rng.fill_f128(&mut delta);
                rng.fill_f128(&mut masks);
                assert!(!basis[0].is_zero());
                if preserve_target {
                    let correction = inner_product(&delta, &basis) * basis[0].inv();
                    delta[0] += correction;
                    assert_eq!(inner_product(&delta, &basis), F128::ZERO);
                } else {
                    assert!(!inner_product(&delta, &basis).is_zero());
                }
                let target = inner_product(&witness, &basis);
                let (_, data) = commit_layout(&witness, &mut rng);
                let (proof, reduction) = open(
                    witness.clone(),
                    basis.clone(),
                    target,
                    &data,
                    &config,
                    &masks,
                    &ro,
                    RoChannel::Witness,
                    &mut RandomChallenger::new(seed),
                );
                let queries: Vec<_> = proof
                    .ligerito
                    .initial_proof
                    .opened_rows
                    .iter()
                    .map(|row| {
                        data.data
                            .codeword
                            .chunks_exact(lanes + 1)
                            .position(|r| r == row)
                            .unwrap()
                    })
                    .collect();
                let ntt = AdditiveNttF128::standard(log_code);
                let mut matrix = vec![F128::ZERO; queries.len() * padding_height];
                for column in 0..padding_height {
                    let mut encoded = vec![F128::ZERO; positions];
                    if let Some(code) = &data.padding_code {
                        encoded[column] = code.padding_factor(0);
                        encoded[height + column] = F128::ONE;
                    } else {
                        encoded[column] = F128::ONE;
                    }
                    ntt.forward_transform_scalar(&mut encoded);
                    for (row, q) in queries.iter().enumerate() {
                        matrix[row * padding_height + column] = encoded[*q];
                    }
                }
                let matrix = F128Mat::new(queries.len(), padding_height, matrix);
                let mut padding_delta = vec![F128::ZERO; padding_height * lanes];
                for lane in 0..lanes {
                    let mut encoded = vec![F128::ZERO; positions];
                    for row in 0..height {
                        let offset = if query_padding { 0 } else { height };
                        encoded[offset + row] = delta[row * lanes + lane];
                    }
                    ntt.forward_transform_scalar(&mut encoded);
                    let rhs: Vec<_> = queries.iter().map(|q| encoded[*q]).collect();
                    let solution = matrix
                        .solve(&rhs)
                        .expect("query padding spans the opened rows");
                    for row in 0..padding_height {
                        padding_delta[row * lanes + lane] = solution[row];
                    }
                }
                let mut changed_witness = witness;
                for (w, d) in changed_witness.iter_mut().zip(&delta) {
                    *w += *d;
                }
                let mut changed_mask = data.data.zk_mask.clone();
                for (m, d) in changed_mask.iter_mut().zip(&padding_delta) {
                    *m += *d;
                }
                let mut full_delta = if query_padding {
                    delta.clone()
                } else {
                    padding_delta.clone()
                };
                if query_padding {
                    full_delta.extend(padding_delta);
                } else {
                    full_delta.extend(delta);
                }
                let weights = build_eq(&reduction.lane_challenges);
                let inverse = reduction.blind_challenge.inv();
                let mut changed_blind = data.data.zk_blind.clone();
                for (g, row) in changed_blind.iter_mut().zip(full_delta.chunks_exact(lanes)) {
                    *g += inverse * inner_product(row, &weights);
                }
                let mut playback = changed_mask;
                playback.extend(changed_blind);
                for salt in &data.data.initial_leaf_salts {
                    for pair in salt.as_chunks::<16>().0 {
                        playback.push(F128::new(
                            u64::from_le_bytes(pair[..8].try_into().unwrap()),
                            u64::from_le_bytes(pair[8..].try_into().unwrap()),
                        ));
                    }
                }
                let (_, changed_data) = commit_layout(
                    &changed_witness,
                    &mut PlaybackSampler {
                        data: &playback,
                        pos: 0,
                    },
                );
                let changed_target = inner_product(&changed_witness, &basis);
                let zeros = vec![F128::ZERO; masks.len()];
                let (raw, _) = open(
                    changed_witness.clone(),
                    basis.clone(),
                    changed_target,
                    &changed_data,
                    &config,
                    &zeros,
                    &ro,
                    RoChannel::Witness,
                    &mut RandomChallenger::new(seed),
                );
                let mut changed_masks = Vec::new();
                for (old, new) in proof.masked_rounds.iter().zip(&raw.masked_rounds) {
                    changed_masks.extend([old.u_0 + new.u_0, old.u_2 + new.u_2]);
                }
                changed_masks.push(proof.masked_blind_value + raw.masked_blind_value);
                let (changed, _) = open(
                    changed_witness,
                    basis,
                    changed_target,
                    &changed_data,
                    &config,
                    &changed_masks,
                    &ro,
                    RoChannel::Witness,
                    &mut RandomChallenger::new(seed),
                );
                assert_eq!(proof.masked_rounds, changed.masked_rounds);
                assert_eq!(proof.masked_blind_value, changed.masked_blind_value);
                assert_eq!(proof.target, changed.target);
                assert_eq!(proof.padding, changed.padding);
                assert_eq!(
                    proof.ligerito.initial_proof.opened_rows,
                    changed.ligerito.initial_proof.opened_rows
                );
                assert_eq!(
                    proof.ligerito.sumcheck_transcript,
                    changed.ligerito.sumcheck_transcript
                );
                assert_eq!(
                    proof.ligerito.recursive_roots,
                    changed.ligerito.recursive_roots
                );
                assert_eq!(
                    proof.ligerito.recursive_proofs,
                    changed.ligerito.recursive_proofs
                );
                assert_eq!(proof.ligerito.final_proof, changed.ligerito.final_proof);
            }
        }
    }
}

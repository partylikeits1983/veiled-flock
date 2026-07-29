//! Straightline full-codeword decoder used by the recording-oracle extractor.
//!
//! The inverse additive NTT recovers a candidate coefficient vector. The
//! candidate is truncated to the declared message dimension, re-encoded, and
//! accepted only when it lies inside the code's unique-decoding radius.

use flock_core::field::F128;
use flock_core::ntt::AdditiveNttF128;
use flock_core::pcs::PcsParams;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedZkCodeword {
    pub mask: Vec<F128>,
    pub witness: Vec<F128>,
    pub blinder: Vec<F128>,
    pub row_distance: usize,
    pub unique_radius: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    BadShape { expected: usize, got: usize },
    OutsideUniqueRadius { distance: usize, radius: usize },
}

fn forward_columns(coefficients: &[F128], positions: usize, lanes: usize) -> Vec<F128> {
    let ntt = AdditiveNttF128::standard(positions.trailing_zeros() as usize);
    let mut encoded = vec![F128::ZERO; coefficients.len()];
    for lane in 0..lanes {
        let mut column = (0..positions)
            .map(|position| coefficients[position * lanes + lane])
            .collect::<Vec<_>>();
        ntt.forward_transform(&mut column);
        for (position, value) in column.into_iter().enumerate() {
            encoded[position * lanes + lane] = value;
        }
    }
    encoded
}

pub fn decode_zk_codeword(
    codeword: &[F128],
    params: &PcsParams,
) -> Result<DecodedZkCodeword, DecodeError> {
    let expected = params.codeword_len_f128();
    if !params.zk || codeword.len() != expected {
        return Err(DecodeError::BadShape {
            expected,
            got: codeword.len(),
        });
    }
    let positions = params.n_positions();
    let lanes = 1usize << params.log_lanes_committed();
    let f_lanes = params.num_ntts();
    let witness_words = 1usize << params.witness_log_msg_len();
    let mask_positions = witness_words / f_lanes;
    let message_positions = 2 * mask_positions;
    let ntt = AdditiveNttF128::standard(params.k_code());

    let mut coefficients = vec![F128::ZERO; codeword.len()];
    for lane in 0..lanes {
        let mut column = (0..positions)
            .map(|position| codeword[position * lanes + lane])
            .collect::<Vec<_>>();
        ntt.inverse_transform(&mut column);
        for (position, value) in column.into_iter().enumerate() {
            coefficients[position * lanes + lane] = value;
        }
    }

    let mut candidate_coefficients = coefficients.clone();
    for position in message_positions..positions {
        candidate_coefficients[position * lanes..(position + 1) * lanes].fill(F128::ZERO);
    }
    let candidate = forward_columns(&candidate_coefficients, positions, lanes);
    let row_distance = codeword
        .chunks_exact(lanes)
        .zip(candidate.chunks_exact(lanes))
        .filter(|(received, encoded)| received != encoded)
        .count();
    let unique_radius = (positions - message_positions) / 2;
    if row_distance > unique_radius {
        return Err(DecodeError::OutsideUniqueRadius {
            distance: row_distance,
            radius: unique_radius,
        });
    }

    let mut mask = Vec::with_capacity(witness_words);
    let mut witness = Vec::with_capacity(witness_words);
    let mut blinder = Vec::with_capacity(2 * witness_words);
    for position in 0..message_positions {
        if position < mask_positions {
            mask.extend_from_slice(
                &candidate_coefficients[position * lanes..position * lanes + f_lanes],
            );
        } else {
            witness.extend_from_slice(
                &candidate_coefficients[position * lanes..position * lanes + f_lanes],
            );
        }
        blinder.extend_from_slice(
            &candidate_coefficients[position * lanes + f_lanes..position * lanes + 2 * f_lanes],
        );
    }
    Ok(DecodedZkCodeword {
        mask,
        witness,
        blinder,
        row_distance,
        unique_radius,
    })
}

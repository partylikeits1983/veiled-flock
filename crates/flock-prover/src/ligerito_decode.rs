//! Straightline full-codeword decoder used by the recording-oracle extractor.
//!
//! The inverse additive NTT recovers a coefficient vector. The declared
//! message portion is re-encoded and
//! accepted only when it lies inside the code's unique-decoding radius.

use flock_core::field::F128;
use flock_core::ntt::AdditiveNttF128;
use flock_core::pcs::{LOG_PACKING, PcsParams};

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
    InvalidParams(&'static str),
    BadShape { expected: usize, got: usize },
    OutsideUniqueRadius { distance: usize, radius: usize },
}

struct ZkCodewordShape {
    expected: usize,
    positions: usize,
    lanes: usize,
    f_lanes: usize,
    witness_words: usize,
    mask_positions: usize,
    message_positions: usize,
    k_code: usize,
}

fn checked_pow2(log: usize, what: &'static str) -> Result<usize, DecodeError> {
    let shift = u32::try_from(log).map_err(|_| DecodeError::InvalidParams(what))?;
    1usize
        .checked_shl(shift)
        .ok_or(DecodeError::InvalidParams(what))
}

fn checked_zk_codeword_shape(params: &PcsParams) -> Result<ZkCodewordShape, DecodeError> {
    if !params.zk {
        return Err(DecodeError::InvalidParams("zk mode required"));
    }
    if params.log_inv_rate == 0 {
        return Err(DecodeError::InvalidParams("log_inv_rate must be nonzero"));
    }
    let witness_log_msg_len = params
        .m
        .checked_sub(LOG_PACKING)
        .ok_or(DecodeError::InvalidParams("m below packing width"))?;
    if witness_log_msg_len < params.log_batch_size {
        return Err(DecodeError::InvalidParams(
            "log_batch_size exceeds witness dimension",
        ));
    }
    let log_msg_len = witness_log_msg_len
        .checked_add(1)
        .ok_or(DecodeError::InvalidParams("message dimension overflow"))?;
    let log_dim =
        log_msg_len
            .checked_sub(params.log_batch_size)
            .ok_or(DecodeError::InvalidParams(
                "log_batch_size exceeds message dimension",
            ))?;
    let k_code = log_dim
        .checked_add(params.log_inv_rate)
        .ok_or(DecodeError::InvalidParams("code dimension overflow"))?;
    let log_lanes_committed = params
        .log_batch_size
        .checked_add(1)
        .ok_or(DecodeError::InvalidParams("lane dimension overflow"))?;
    let positions = checked_pow2(k_code, "codeword position count overflow")?;
    let lanes = checked_pow2(log_lanes_committed, "lane count overflow")?;
    let f_lanes = checked_pow2(params.log_batch_size, "f-lane count overflow")?;
    let witness_words = checked_pow2(witness_log_msg_len, "witness length overflow")?;
    let mask_positions = witness_words
        .checked_div(f_lanes)
        .ok_or(DecodeError::InvalidParams("invalid f-lane count"))?;
    let message_positions = mask_positions
        .checked_mul(2)
        .ok_or(DecodeError::InvalidParams(
            "message position count overflow",
        ))?;
    if message_positions > positions {
        return Err(DecodeError::InvalidParams(
            "message positions exceed codeword positions",
        ));
    }
    if f_lanes
        .checked_mul(2)
        .ok_or(DecodeError::InvalidParams("blinder lane count overflow"))?
        > lanes
    {
        return Err(DecodeError::InvalidParams(
            "committed lanes do not cover witness and blinder lanes",
        ));
    }
    let expected = positions
        .checked_mul(lanes)
        .ok_or(DecodeError::InvalidParams("codeword length overflow"))?;
    Ok(ZkCodewordShape {
        expected,
        positions,
        lanes,
        f_lanes,
        witness_words,
        mask_positions,
        message_positions,
        k_code,
    })
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
    let shape = checked_zk_codeword_shape(params)?;
    if codeword.len() != shape.expected {
        return Err(DecodeError::BadShape {
            expected: shape.expected,
            got: codeword.len(),
        });
    }
    let positions = shape.positions;
    let lanes = shape.lanes;
    let f_lanes = shape.f_lanes;
    let witness_words = shape.witness_words;
    let mask_positions = shape.mask_positions;
    let message_positions = shape.message_positions;
    let ntt = AdditiveNttF128::standard(shape.k_code);

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

    let mut message_coefficients = coefficients.clone();
    for position in message_positions..positions {
        message_coefficients[position * lanes..(position + 1) * lanes].fill(F128::ZERO);
    }
    let reencoded = forward_columns(&message_coefficients, positions, lanes);
    let row_distance = codeword
        .chunks_exact(lanes)
        .zip(reencoded.chunks_exact(lanes))
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
                &message_coefficients[position * lanes..position * lanes + f_lanes],
            );
        } else {
            witness.extend_from_slice(
                &message_coefficients[position * lanes..position * lanes + f_lanes],
            );
        }
        blinder.extend_from_slice(
            &message_coefficients[position * lanes + f_lanes..position * lanes + 2 * f_lanes],
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

#[cfg(test)]
mod tests {
    use super::*;
    use flock_core::pcs::ligerito::LigeritoProfile;

    fn zk_params(m: usize, log_inv_rate: usize, log_batch_size: usize) -> PcsParams {
        PcsParams {
            m,
            log_inv_rate,
            log_batch_size,
            profile: LigeritoProfile::Secure,
            zk: true,
        }
    }

    #[test]
    fn decode_zk_codeword_accepts_small_valid_zero_word() {
        let params = zk_params(LOG_PACKING + 2, 1, 1);
        let shape = checked_zk_codeword_shape(&params).expect("valid shape");
        let decoded = decode_zk_codeword(&vec![F128::ZERO; shape.expected], &params)
            .expect("zero codeword is within the unique radius");
        assert_eq!(decoded.mask.len(), shape.witness_words);
        assert_eq!(decoded.witness.len(), shape.witness_words);
        assert_eq!(decoded.blinder.len(), 2 * shape.witness_words);
        assert_eq!(decoded.row_distance, 0);
        assert_eq!(decoded.unique_radius, 2);
    }

    #[test]
    fn decode_zk_codeword_rejects_malformed_params_before_geometry() {
        let zero_rate = zk_params(LOG_PACKING + 2, 0, 1);
        assert!(matches!(
            decode_zk_codeword(&[], &zero_rate),
            Err(DecodeError::InvalidParams(reason)) if reason.contains("log_inv_rate")
        ));

        let oversized_shift = zk_params(usize::MAX, 1, 1);
        assert!(matches!(
            decode_zk_codeword(&[], &oversized_shift),
            Err(DecodeError::InvalidParams(_))
        ));

        let oversized_batch = zk_params(LOG_PACKING + 1, 1, usize::MAX);
        assert!(matches!(
            decode_zk_codeword(&[], &oversized_batch),
            Err(DecodeError::InvalidParams(_))
        ));
    }

    #[test]
    fn decode_zk_codeword_reports_checked_expected_length() {
        let params = zk_params(LOG_PACKING + 2, 1, 1);
        let shape = checked_zk_codeword_shape(&params).expect("valid shape");
        assert_eq!(
            decode_zk_codeword(&[], &params),
            Err(DecodeError::BadShape {
                expected: shape.expected,
                got: 0,
            })
        );
    }
}

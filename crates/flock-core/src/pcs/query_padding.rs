use crate::field::F128;
use crate::ntt::AdditiveNttF128;
use rayon::prelude::*;

/// RS padding that preserves the unpadded code and hides every query row.
pub struct PaddingCode {
    log_message: usize,
    log_code: usize,
    shift: F128,
    ntt: AdditiveNttF128,
}

impl PaddingCode {
    pub fn new(log_message: usize, log_code: usize) -> Self {
        assert!(log_message < log_code && log_code < usize::BITS as usize - 1);
        let extended = AdditiveNttF128::standard(log_code + 1);
        let shift = extended.normalized_subspace_at(log_message, 1usize << log_code);
        Self {
            log_message,
            log_code,
            shift,
            ntt: AdditiveNttF128::standard(log_code),
        }
    }

    pub fn message_len(&self) -> usize {
        1 << self.log_message
    }

    pub fn code_len(&self) -> usize {
        1 << self.log_code
    }

    pub fn padding_factor(&self, position: usize) -> F128 {
        self.shift + self.ntt.normalized_subspace_at(self.log_message, position)
    }

    /// Encode `w + (X_n + shift) p` in the novel polynomial basis.
    pub fn encode(&self, message: &[F128], padding: &[F128], lanes: usize) -> Vec<F128> {
        assert!(lanes > 0);
        assert_eq!(message.len(), self.message_len() * lanes);
        assert_eq!(padding.len() % lanes, 0);
        assert!(padding.len() <= message.len());
        let mut code = crate::scratch::take_f128(self.code_len() * lanes);
        let rows_per_chunk = self.message_len().min(256);
        code.par_chunks_mut(rows_per_chunk * lanes)
            .enumerate()
            .for_each(|(chunk, values)| {
                let position = chunk * rows_per_chunk;
                let offset = (position % self.message_len()) * lanes;
                values.copy_from_slice(&message[offset..offset + values.len()]);
                if offset < padding.len() {
                    let block_start = position - position % self.message_len();
                    let factor = self.padding_factor(block_start);
                    for (value, pad) in values.iter_mut().zip(&padding[offset..]) {
                        *value += factor * *pad;
                    }
                }
            });
        self.ntt.forward_transform_interleaved_from_layer(
            &mut code,
            lanes,
            self.log_code - self.log_message,
        );
        code
    }

    pub fn evaluate_padding(&self, padding: &[F128], position: usize) -> F128 {
        assert!(padding.len() <= self.message_len());
        assert!(position < self.code_len());
        if padding.is_empty() {
            return F128::ZERO;
        }
        let mut basis = vec![F128::ONE; padding.len()];
        let mut start = 1;
        let mut degree = 0;
        while start < basis.len() {
            let scale = self.ntt.normalized_subspace_at(degree, position);
            for i in start..(2 * start).min(basis.len()) {
                basis[i] = basis[i - start] * scale;
            }
            start *= 2;
            degree += 1;
        }
        self.padding_factor(position)
            * padding
                .iter()
                .zip(basis)
                .fold(F128::ZERO, |sum, (coefficient, value)| {
                    sum + *coefficient * value
                })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::linalg::F128Mat;
    use crate::zk::{MaskSampler, ZkRng};

    #[test]
    fn padding_encoding_matches_dense_ntt_and_virtual_oracle() {
        let mut rng = ZkRng::from_seed([93; 32]);
        for log_message in [2, 4, 7, 9] {
            for log_rate in [1, 2, 3] {
                let code = PaddingCode::new(log_message, log_message + log_rate);
                for lanes in [1, 3, 33, 65] {
                    let mut message = vec![F128::ZERO; code.message_len() * lanes];
                    rng.fill_f128(&mut message);
                    for queries in [1, code.message_len() / 2 - 1, code.message_len()] {
                        let mut padding = vec![F128::ZERO; queries * lanes];
                        rng.fill_f128(&mut padding);
                        let encoded = code.encode(&message, &padding, lanes);
                        let mut dense = vec![F128::ZERO; code.code_len() * lanes];
                        dense[..message.len()].copy_from_slice(&message);
                        for (i, pad) in padding.iter().enumerate() {
                            dense[i] += code.shift * *pad;
                            dense[message.len() + i] = *pad;
                        }
                        code.ntt
                            .forward_transform_interleaved_scalar(&mut dense, lanes);
                        assert_eq!(encoded, dense);
                        let unpadded = code.encode(&message, &[], lanes);
                        for lane in [0, lanes - 1] {
                            let pads: Vec<_> =
                                padding.chunks_exact(lanes).map(|row| row[lane]).collect();
                            for position in 0..code.code_len() {
                                assert_eq!(
                                    encoded[position * lanes + lane]
                                        + code.evaluate_padding(&pads, position),
                                    unpadded[position * lanes + lane],
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn query_padding_matches_scalar_with_cache_blocking() {
        let code = PaddingCode::new(12, 13);
        let lanes = 33;
        let mut rng = ZkRng::from_seed([94; 32]);
        let mut message = vec![F128::ZERO; code.message_len() * lanes];
        let mut padding = vec![F128::ZERO; 252 * lanes];
        rng.fill_f128(&mut message);
        rng.fill_f128(&mut padding);
        let encoded = code.encode(&message, &padding, lanes);
        let mut expected = vec![F128::ZERO; code.code_len() * lanes];
        expected[..message.len()].copy_from_slice(&message);
        for (i, pad) in padding.iter().enumerate() {
            expected[i] += code.shift * *pad;
            expected[message.len() + i] = *pad;
        }
        code.ntt
            .forward_transform_interleaved_scalar(&mut expected, lanes);
        assert_eq!(encoded, expected);
    }

    #[test]
    fn padding_has_full_query_rank_including_the_base_domain() {
        for log_rate in [1, 2, 3] {
            let code = PaddingCode::new(3, 3 + log_rate);
            for position in 0..code.code_len() {
                assert_ne!(code.padding_factor(position), F128::ZERO);
            }
            for queries in [vec![0, 1, 7, 8, code.code_len() - 1], vec![0, 1, 2, 3, 4]] {
                let q = queries.len();
                let mut matrix = vec![F128::ZERO; q * q];
                let mut unshifted = matrix.clone();
                for column in 0..q {
                    let mut unit = vec![F128::ZERO; q];
                    unit[column] = F128::ONE;
                    let mut dense = vec![F128::ZERO; code.code_len()];
                    dense[code.message_len() + column] = F128::ONE;
                    code.ntt.forward_transform_scalar(&mut dense);
                    for (row, position) in queries.iter().enumerate() {
                        matrix[row * q + column] = code.evaluate_padding(&unit, *position);
                        unshifted[row * q + column] = dense[*position];
                    }
                }
                assert_eq!(F128Mat::new(q, q, matrix).rank(), q);
                assert!(F128Mat::new(q, q, unshifted).rank() < q);
            }
        }
    }
}

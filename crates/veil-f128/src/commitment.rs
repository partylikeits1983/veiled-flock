//! Merkle commitment to a row-major matrix of `F128` codeword evaluations.

use flock_core::{
    field::F128,
    merkle::{
        Hash, merkle_multi_proof, merkle_tree_framed_salted, verify_merkle_multi_proof_framed,
    },
    ro::{RoChannel, RoContext},
    zk::MaskSampler,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug)]
pub struct MerkleMatrix {
    rows: usize,
    columns: usize,
    values: Vec<F128>,
    salts: Vec<[u8; 32]>,
    tree: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleMatrixOpening {
    pub positions: Vec<usize>,
    pub rows: Vec<F128>,
    pub salts: Vec<[u8; 32]>,
    pub siblings: Vec<Hash>,
}

impl MerkleMatrix {
    pub fn new<R: MaskSampler + ?Sized>(
        columns: &[Vec<F128>],
        rng: &mut R,
        ctx: &RoContext,
        channel: RoChannel,
    ) -> Self {
        assert!(
            !columns.is_empty(),
            "commitment must contain at least one column"
        );
        let rows = columns[0].len();
        assert!(
            rows.is_power_of_two(),
            "codeword row count must be a power of two"
        );
        assert!(columns.iter().all(|column| column.len() == rows));

        let column_count = columns.len();
        let mut values = Vec::with_capacity(rows * column_count);
        for row in 0..rows {
            values.extend(columns.iter().map(|column| column[row]));
        }
        let salts = sample_leaf_salts(rows, rng);
        let bytes = matrix_bytes(&values);
        let tree = merkle_tree_framed_salted(&bytes, rows, &salts, ctx, channel, 0);
        Self {
            rows,
            columns: column_count,
            values,
            salts,
            tree,
        }
    }

    pub fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
    }

    pub fn num_rows(&self) -> usize {
        self.rows
    }

    pub fn num_columns(&self) -> usize {
        self.columns
    }

    pub fn row(&self, position: usize) -> &[F128] {
        let start = position * self.columns;
        &self.values[start..start + self.columns]
    }

    pub fn open(&self, positions: &[usize]) -> MerkleMatrixOpening {
        let mut positions = positions.to_vec();
        positions.sort_unstable();
        positions.dedup();
        assert!(positions.iter().all(|position| *position < self.rows));

        let mut rows = Vec::with_capacity(positions.len() * self.columns);
        for &position in &positions {
            rows.extend_from_slice(self.row(position));
        }
        let siblings = merkle_multi_proof(&self.tree, self.rows, &positions);
        let salts = positions
            .iter()
            .map(|&position| self.salts[position])
            .collect();
        MerkleMatrixOpening {
            positions,
            rows,
            salts,
            siblings,
        }
    }
}

impl MerkleMatrixOpening {
    pub fn verify(
        &self,
        root: &Hash,
        num_rows: usize,
        num_columns: usize,
        ctx: &RoContext,
        channel: RoChannel,
    ) -> bool {
        if !num_rows.is_power_of_two()
            || self.rows.len() != self.positions.len().saturating_mul(num_columns)
            || self.salts.len() != self.positions.len()
        {
            return false;
        }
        let bytes = self
            .rows
            .chunks(num_columns)
            .zip(&self.salts)
            .map(|(row, salt)| {
                let mut payload = Vec::with_capacity(32 + 16 * num_columns);
                payload.extend_from_slice(salt);
                payload.extend_from_slice(&matrix_bytes(row));
                payload
            })
            .collect::<Vec<_>>();
        let leaves = bytes.iter().map(Vec::as_slice).collect::<Vec<_>>();
        verify_merkle_multi_proof_framed(
            root,
            num_rows,
            &self.positions,
            &leaves,
            &self.siblings,
            ctx,
            channel,
            0,
        )
    }

    pub fn row(&self, position: usize, num_columns: usize) -> Option<&[F128]> {
        let index = self.positions.binary_search(&position).ok()?;
        let start = index * num_columns;
        self.rows.get(start..start + num_columns)
    }
}

pub(crate) fn sample_leaf_salts<R: MaskSampler + ?Sized>(
    rows: usize,
    rng: &mut R,
) -> Vec<[u8; 32]> {
    let mut fields = vec![F128::ZERO; 2 * rows];
    rng.fill_f128(&mut fields);
    fields
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let mut salt = [0u8; 32];
            salt[..8].copy_from_slice(&pair[0].lo.to_le_bytes());
            salt[8..16].copy_from_slice(&pair[0].hi.to_le_bytes());
            salt[16..24].copy_from_slice(&pair[1].lo.to_le_bytes());
            salt[24..].copy_from_slice(&pair[1].hi.to_le_bytes());
            salt
        })
        .collect()
}

fn matrix_bytes(values: &[F128]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(values.len() * 16);
    for value in values {
        bytes.extend_from_slice(&value.lo.to_le_bytes());
        bytes.extend_from_slice(&value.hi.to_le_bytes());
    }
    bytes
}

#[cfg(test)]
mod tests {
    use flock_core::zk::ZkRng;

    use super::*;

    #[test]
    fn multi_opening_roundtrip_and_mutation_rejection() {
        let columns = vec![
            (0..16).map(|i| F128::new(i, 0)).collect(),
            (0..16).map(|i| F128::new(100 + i, 1)).collect(),
        ];
        let ctx = RoContext::native([7; 32]);
        let mut rng = ZkRng::from_seed([7; 32]);
        let matrix = MerkleMatrix::new(&columns, &mut rng, &ctx, RoChannel::Witness);
        let opening = matrix.open(&[1, 2, 2, 11]);
        assert!(opening.verify(&matrix.root(), 16, 2, &ctx, RoChannel::Witness));
        assert_eq!(opening.positions, vec![1, 2, 11]);

        let mut bad = opening.clone();
        bad.rows[0] += F128::ONE;
        assert!(!bad.verify(&matrix.root(), 16, 2, &ctx, RoChannel::Witness));

        let mut bad_salt = opening.clone();
        bad_salt.salts[0][0] ^= 1;
        assert!(!bad_salt.verify(&matrix.root(), 16, 2, &ctx, RoChannel::Witness));

        let mut fresh_rng = ZkRng::from_seed([8; 32]);
        let fresh = MerkleMatrix::new(&columns, &mut fresh_rng, &ctx, RoChannel::Witness);
        assert_ne!(matrix.root(), fresh.root());
    }
}

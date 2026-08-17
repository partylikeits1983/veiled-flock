//! Merkle commitment to a row-major matrix of `F128` codeword evaluations.

use flock_core::{
    field::F128,
    merkle::{
        Hash, hash_leaf, merkle_multi_proof, merkle_tree, merkle_tree_framed,
        verify_merkle_multi_proof, verify_merkle_multi_proof_framed,
    },
    ro::{RoChannel, RoContext},
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug)]
pub struct MerkleMatrix {
    rows: usize,
    columns: usize,
    values: Vec<F128>,
    tree: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleMatrixOpening {
    pub positions: Vec<usize>,
    pub rows: Vec<F128>,
    pub siblings: Vec<Hash>,
}

impl MerkleMatrix {
    pub fn new(columns: &[Vec<F128>]) -> Self {
        Self::build(columns, None)
    }

    pub fn new_framed(columns: &[Vec<F128>], ctx: &RoContext, channel: RoChannel) -> Self {
        Self::build(columns, Some((ctx, channel)))
    }

    fn build(columns: &[Vec<F128>], framed: Option<(&RoContext, RoChannel)>) -> Self {
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
        let bytes = matrix_bytes(&values);
        let tree = match framed {
            Some((ctx, channel)) => merkle_tree_framed(&bytes, rows, ctx, channel, 0),
            None => merkle_tree(&bytes, rows),
        };
        Self {
            rows,
            columns: column_count,
            values,
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
        MerkleMatrixOpening {
            positions,
            rows,
            siblings,
        }
    }
}

impl MerkleMatrixOpening {
    pub fn verify(&self, root: &Hash, num_rows: usize, num_columns: usize) -> bool {
        if !num_rows.is_power_of_two()
            || self.rows.len() != self.positions.len().saturating_mul(num_columns)
        {
            return false;
        }
        let leaf_hashes: Vec<Hash> = self
            .rows
            .chunks(num_columns)
            .map(|row| hash_leaf(&matrix_bytes(row)))
            .collect();
        verify_merkle_multi_proof(
            root,
            num_rows,
            &self.positions,
            &leaf_hashes,
            &self.siblings,
        )
    }

    pub fn verify_framed(
        &self,
        root: &Hash,
        num_rows: usize,
        num_columns: usize,
        ctx: &RoContext,
        channel: RoChannel,
    ) -> bool {
        if !num_rows.is_power_of_two()
            || self.rows.len() != self.positions.len().saturating_mul(num_columns)
        {
            return false;
        }
        let bytes = self
            .rows
            .chunks(num_columns)
            .map(matrix_bytes)
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
    use super::*;

    #[test]
    fn multi_opening_roundtrip_and_mutation_rejection() {
        let columns = vec![
            (0..16).map(|i| F128::new(i, 0)).collect(),
            (0..16).map(|i| F128::new(100 + i, 1)).collect(),
        ];
        let matrix = MerkleMatrix::new(&columns);
        let opening = matrix.open(&[1, 2, 2, 11]);
        assert!(opening.verify(&matrix.root(), 16, 2));
        assert_eq!(opening.positions, vec![1, 2, 11]);

        let mut bad = opening.clone();
        bad.rows[0] += F128::ONE;
        assert!(!bad.verify(&matrix.root(), 16, 2));
    }
}

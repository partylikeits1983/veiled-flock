//! Small exact linear-algebra utilities used by the ZK coverage, symbolic,
//! replacement, and extractor certificates.

use crate::field::F128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128Mat {
    pub rows: usize,
    pub cols: usize,
    pub data: Vec<F128>,
}

impl F128Mat {
    pub fn new(rows: usize, cols: usize, data: Vec<F128>) -> Self {
        assert_eq!(data.len(), rows * cols);
        Self { rows, cols, data }
    }

    pub fn from_rows(rows: &[Vec<F128>]) -> Self {
        let cols = rows.first().map_or(0, Vec::len);
        assert!(rows.iter().all(|row| row.len() == cols));
        Self::new(rows.len(), cols, rows.iter().flatten().copied().collect())
    }

    #[inline]
    pub fn get(&self, row: usize, col: usize) -> F128 {
        self.data[row * self.cols + col]
    }

    #[inline]
    pub fn set(&mut self, row: usize, col: usize, value: F128) {
        self.data[row * self.cols + col] = value;
    }

    fn swap_rows(&mut self, a: usize, b: usize) {
        if a == b {
            return;
        }
        for col in 0..self.cols {
            self.data.swap(a * self.cols + col, b * self.cols + col);
        }
    }

    /// Reduced row echelon form and pivot columns.
    pub fn rref(&self) -> (Self, Vec<usize>) {
        let mut out = self.clone();
        let mut pivots = Vec::new();
        let mut pivot_row = 0usize;
        for col in 0..out.cols {
            let Some(found) = (pivot_row..out.rows).find(|&row| out.get(row, col) != F128::ZERO)
            else {
                continue;
            };
            out.swap_rows(pivot_row, found);
            let inv = out.get(pivot_row, col).inv();
            for j in col..out.cols {
                out.set(pivot_row, j, out.get(pivot_row, j) * inv);
            }
            for row in 0..out.rows {
                if row == pivot_row {
                    continue;
                }
                let factor = out.get(row, col);
                if factor == F128::ZERO {
                    continue;
                }
                for j in col..out.cols {
                    out.set(row, j, out.get(row, j) + factor * out.get(pivot_row, j));
                }
            }
            pivots.push(col);
            pivot_row += 1;
            if pivot_row == out.rows {
                break;
            }
        }
        (out, pivots)
    }

    pub fn rank(&self) -> usize {
        self.rref().1.len()
    }

    pub fn det(&self) -> F128 {
        assert_eq!(self.rows, self.cols);
        let mut a = self.clone();
        let mut det = F128::ONE;
        for col in 0..a.cols {
            let Some(pivot) = (col..a.rows).find(|&row| a.get(row, col) != F128::ZERO) else {
                return F128::ZERO;
            };
            a.swap_rows(col, pivot);
            let pivot_value = a.get(col, col);
            det *= pivot_value;
            let inv = pivot_value.inv();
            for row in col + 1..a.rows {
                let factor = a.get(row, col) * inv;
                if factor == F128::ZERO {
                    continue;
                }
                for j in col..a.cols {
                    a.set(row, j, a.get(row, j) + factor * a.get(col, j));
                }
            }
        }
        // Row swaps have sign +1 in characteristic two.
        det
    }

    pub fn transpose(&self) -> Self {
        let mut data = vec![F128::ZERO; self.data.len()];
        for row in 0..self.rows {
            for col in 0..self.cols {
                data[col * self.rows + row] = self.get(row, col);
            }
        }
        Self::new(self.cols, self.rows, data)
    }

    pub fn mul(&self, other: &Self) -> Self {
        assert_eq!(self.cols, other.rows);
        let mut data = vec![F128::ZERO; self.rows * other.cols];
        for row in 0..self.rows {
            for inner in 0..self.cols {
                let left = self.get(row, inner);
                if left == F128::ZERO {
                    continue;
                }
                for col in 0..other.cols {
                    data[row * other.cols + col] += left * other.get(inner, col);
                }
            }
        }
        Self::new(self.rows, other.cols, data)
    }

    pub fn identity(size: usize) -> Self {
        let mut data = vec![F128::ZERO; size * size];
        for index in 0..size {
            data[index * size + index] = F128::ONE;
        }
        Self::new(size, size, data)
    }

    pub fn inverse(&self) -> Option<Self> {
        assert_eq!(self.rows, self.cols);
        let size = self.rows;
        let mut augmented = Vec::with_capacity(size * 2 * size);
        for row in 0..size {
            augmented.extend_from_slice(&self.data[row * size..(row + 1) * size]);
            for col in 0..size {
                augmented.push(if row == col { F128::ONE } else { F128::ZERO });
            }
        }
        let (rref, pivots) = Self::new(size, 2 * size, augmented).rref();
        if pivots.len() < size || pivots[..size] != (0..size).collect::<Vec<_>>() {
            return None;
        }
        let mut data = Vec::with_capacity(size * size);
        for row in 0..size {
            for col in 0..size {
                data.push(rref.get(row, size + col));
            }
        }
        Some(Self::new(size, size, data))
    }

    /// Solve `self * x = rhs`, returning one solution with free variables set
    /// to zero. Returns `None` when the system is inconsistent.
    pub fn solve(&self, rhs: &[F128]) -> Option<Vec<F128>> {
        assert_eq!(rhs.len(), self.rows);
        let mut aug = Vec::with_capacity(self.rows * (self.cols + 1));
        for (row, value) in rhs.iter().enumerate() {
            aug.extend_from_slice(&self.data[row * self.cols..(row + 1) * self.cols]);
            aug.push(*value);
        }
        let (rref, pivots) = Self::new(self.rows, self.cols + 1, aug).rref();
        for row in 0..rref.rows {
            let zero_left = (0..self.cols).all(|col| rref.get(row, col) == F128::ZERO);
            if zero_left && rref.get(row, self.cols) != F128::ZERO {
                return None;
            }
        }
        let mut solution = vec![F128::ZERO; self.cols];
        for (row, &pivot) in pivots.iter().enumerate() {
            if pivot < self.cols {
                solution[pivot] = rref.get(row, self.cols);
            }
        }
        Some(solution)
    }

    pub fn kernel_basis(&self) -> Vec<Vec<F128>> {
        let (rref, pivots) = self.rref();
        let mut is_pivot = vec![false; self.cols];
        for &pivot in &pivots {
            is_pivot[pivot] = true;
        }
        let mut basis = Vec::new();
        for free in (0..self.cols).filter(|&col| !is_pivot[col]) {
            let mut vector = vec![F128::ZERO; self.cols];
            vector[free] = F128::ONE;
            for (row, &pivot) in pivots.iter().enumerate() {
                vector[pivot] = rref.get(row, free);
            }
            basis.push(vector);
        }
        basis
    }

    /// Select pivot rows and columns forming a nonsingular minor.
    pub fn minor_select(&self, target_rank: usize) -> Minor {
        let mut work = self.clone();
        let mut row_ids = (0..self.rows).collect::<Vec<_>>();
        let mut selected_rows = Vec::new();
        let mut selected_cols = Vec::new();
        let mut pivot_row = 0usize;
        for col in 0..work.cols {
            let Some(found) = (pivot_row..work.rows).find(|&row| work.get(row, col) != F128::ZERO)
            else {
                continue;
            };
            work.swap_rows(pivot_row, found);
            row_ids.swap(pivot_row, found);
            selected_rows.push(row_ids[pivot_row]);
            selected_cols.push(col);
            let inv = work.get(pivot_row, col).inv();
            for row in pivot_row + 1..work.rows {
                let factor = work.get(row, col) * inv;
                for j in col..work.cols {
                    work.set(row, j, work.get(row, j) + factor * work.get(pivot_row, j));
                }
            }
            pivot_row += 1;
            if pivot_row == target_rank {
                break;
            }
        }
        assert_eq!(selected_cols.len(), target_rank, "matrix rank below target");
        let data = selected_rows
            .iter()
            .flat_map(|&row| selected_cols.iter().map(move |&col| self.get(row, col)))
            .collect();
        let det = Self::new(target_rank, target_rank, data).det();
        Minor {
            row_ids: selected_rows,
            col_ids: selected_cols,
            det,
        }
    }

    /// Select a full-rank minor and return its inverse together with the
    /// selected original row and column indices. This is the compact Cramer
    /// data used to rederive an explicit right inverse on the matrix image.
    pub fn right_inverse_on_image(&self) -> (Self, Vec<usize>, Vec<usize>) {
        let rank = self.rank();
        let minor = self.minor_select(rank);
        let data = minor
            .row_ids
            .iter()
            .flat_map(|&row| minor.col_ids.iter().map(move |&col| self.get(row, col)))
            .collect();
        let inverse = Self::new(rank, rank, data)
            .inverse()
            .expect("selected minor must be nonsingular");
        (inverse, minor.row_ids, minor.col_ids)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Minor {
    pub row_ids: Vec<usize>,
    pub col_ids: Vec<usize>,
    pub det: F128,
}

/// Montgomery batch inversion. Zero entries remain zero.
pub fn batch_inv(values: &mut [F128]) {
    let nonzero = values
        .iter()
        .enumerate()
        .filter(|(_, value)| **value != F128::ZERO)
        .map(|(index, value)| (index, *value))
        .collect::<Vec<_>>();
    if nonzero.is_empty() {
        return;
    }
    let mut prefix = Vec::with_capacity(nonzero.len());
    let mut product = F128::ONE;
    for (_, value) in &nonzero {
        prefix.push(product);
        product *= *value;
    }
    let mut inverse = product.inv();
    for ((index, value), before) in nonzero.into_iter().zip(prefix).rev() {
        values[index] = inverse * before;
        inverse *= value;
    }
}

/// Matrix for `R(ker L)`. `R` and `L` are row-functional matrices over the
/// same input coordinates; output columns are the images under `R` of a
/// basis of `ker L`.
pub fn conditioned_image(r: &F128Mat, l: &F128Mat) -> F128Mat {
    assert_eq!(r.cols, l.cols);
    let kernel = l.kernel_basis();
    if kernel.is_empty() {
        return F128Mat::new(r.rows, 0, Vec::new());
    }
    let kernel_columns = F128Mat::new(
        l.cols,
        kernel.len(),
        (0..l.cols)
            .flat_map(|row| kernel.iter().map(move |vector| vector[row]))
            .collect(),
    );
    r.mul(&kernel_columns)
}

#[derive(Default)]
pub struct F128Span {
    rows: Vec<Vec<F128>>,
    pivots: Vec<usize>,
}

impl F128Span {
    pub fn insert(&mut self, mut vector: Vec<F128>) -> bool {
        for (row, &pivot) in self.rows.iter().zip(&self.pivots) {
            if vector[pivot] != F128::ZERO {
                let factor = vector[pivot];
                for (dst, src) in vector.iter_mut().zip(row) {
                    *dst += factor * *src;
                }
            }
        }
        let Some(pivot) = vector.iter().position(|value| *value != F128::ZERO) else {
            return false;
        };
        let inv = vector[pivot].inv();
        for value in &mut vector {
            *value *= inv;
        }
        self.rows.push(vector);
        self.pivots.push(pivot);
        true
    }

    pub fn rank(&self) -> usize {
        self.rows.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rank_det_solve_and_kernel_agree() {
        let a = F128Mat::from_rows(&[
            vec![F128::ONE, F128::ONE, F128::ZERO],
            vec![F128::ZERO, F128::ONE, F128::ONE],
        ]);
        assert_eq!(a.rank(), 2);
        let rhs = [F128::ONE, F128::ZERO];
        let x = a.solve(&rhs).unwrap();
        for (row, expected) in rhs.iter().enumerate() {
            let got = (0..a.cols)
                .map(|col| a.get(row, col) * x[col])
                .fold(F128::ZERO, |acc, value| acc + value);
            assert_eq!(got, *expected);
        }
        for vector in a.kernel_basis() {
            for row in 0..a.rows {
                let got = (0..a.cols)
                    .map(|col| a.get(row, col) * vector[col])
                    .fold(F128::ZERO, |acc, value| acc + value);
                assert_eq!(got, F128::ZERO);
            }
        }
        let minor = a.minor_select(2);
        assert_ne!(minor.det, F128::ZERO);
        let (inverse, rows, cols) = a.right_inverse_on_image();
        let mut selected_data = Vec::with_capacity(rows.len() * cols.len());
        for &row in &rows {
            for &col in &cols {
                selected_data.push(a.get(row, col));
            }
        }
        let selected = F128Mat::new(rows.len(), cols.len(), selected_data);
        assert_eq!(selected.mul(&inverse), F128Mat::identity(2));
    }

    #[test]
    fn batch_inverse_preserves_zeroes() {
        let mut values = [F128::new(2, 0), F128::ZERO, F128::new(7, 0)];
        let original = values;
        batch_inv(&mut values);
        assert_eq!(values[1], F128::ZERO);
        assert_eq!(values[0] * original[0], F128::ONE);
        assert_eq!(values[2] * original[2], F128::ONE);
    }

    #[test]
    fn conditioned_image_applies_r_to_kernel_of_l() {
        let r = F128Mat::identity(3);
        let l = F128Mat::from_rows(&[vec![F128::ONE, F128::ONE, F128::ZERO]]);
        let image = conditioned_image(&r, &l);
        assert_eq!(image.rows, 3);
        assert_eq!(image.cols, 2);
        assert_eq!(image.rank(), 2);
        for col in 0..image.cols {
            assert_eq!(image.get(0, col) + image.get(1, col), F128::ZERO);
        }
    }
}

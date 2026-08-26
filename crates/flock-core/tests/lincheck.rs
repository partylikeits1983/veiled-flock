//! Integration tests for the lincheck layer: kernel equivalences, the
//! prove/verify round trip, the masked (A2) round trip, the rejection paths,
//! and the zk randomizer-row decorator.
//!
//! Kernel tests that need `lincheck`'s private surface stay in
//! `crates/flock-core/src/lincheck/tests.rs`.

use flock_core::challenger::FsChallenger;
use flock_core::field::F128;
use flock_core::lincheck::*;
use flock_core::r1cs::SparseBinaryMatrix;
use flock_core::zerocheck::multilinear::lagrange_weights_naive;
use flock_core::zk::{ZkBlockLayout, ZkConfig};

use flock_test_util::Rng;

/// Field-element helpers over the shared [`Rng`]. They live here because a
/// foreign trait cannot be implemented for a foreign type, and `flock-test-util`
/// depends on nothing (see that crate's docs).
trait RngF128 {
    fn f128(&mut self) -> F128;
    fn f128_vec(&mut self, n: usize) -> Vec<F128>;
}

impl RngF128 for Rng {
    fn f128(&mut self) -> F128 {
        F128 {
            lo: self.next_u64(),
            hi: self.next_u64(),
        }
    }
    fn f128_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.f128()).collect()
    }
}
/// Naive MLE evaluation: `f̂(point) = Σ_i eq(point, i) · f[i]` where i ∈
/// {0,1}^d and f[i] is given as a bool slice.
fn mle_eval_bool(f: &[bool], point: &[F128]) -> F128 {
    let d = point.len();
    assert_eq!(f.len(), 1 << d);
    let eq = build_eq_table(point);
    let mut acc = F128::ZERO;
    for (i, &b) in f.iter().enumerate() {
        if b {
            acc += eq[i];
        }
    }
    acc
}

/// Sample a random `QuirkyPoint` for testing: z_skip ∈ F₁₂₈,
/// x_inner_rest of length `k_log − k_skip`, x_outer of length `n_log`.
fn random_quirky_point(m: usize, k_log: usize, k_skip: usize, rng: &mut Rng) -> QuirkyPoint {
    QuirkyPoint {
        z_skip: rng.f128(),
        x_inner_rest: rng.f128_vec(k_log - k_skip),
        x_outer: rng.f128_vec(m - k_log),
    }
}

/// "Quirky MLE evaluation" of a Boolean vector `f` at a quirky point.
///
/// `ã(z_skip, x_inner_rest, x_outer) = Σ_i  f[i] · L_{i_skip}(z_skip)
///                                          · eq(x_inner_rest, i_inner_rest)
///                                          · eq(x_outer, i_outer)`
///
/// where `i = i_skip + 2^k_skip · i_inner_rest + 2^k_log · i_outer` (matches
/// the linear-LSB indexing of `f`).
fn mle_eval_bool_quirky(
    f: &[bool],
    m: usize,
    k_log: usize,
    k_skip: usize,
    point: &QuirkyPoint,
) -> F128 {
    let k_skip_dim = 1usize << k_skip;
    let inner_rest_len = k_log - k_skip;
    let inner_rest_dim = 1usize << inner_rest_len;
    let k = 1usize << k_log;
    let n_outer = 1usize << (m - k_log);
    assert_eq!(f.len(), 1 << m);

    let lambda = lagrange_weights_naive(k_skip, point.z_skip);
    let eq_rest = build_eq_table(&point.x_inner_rest);
    let eq_outer = build_eq_table(&point.x_outer);
    debug_assert_eq!(lambda.len(), k_skip_dim);
    debug_assert_eq!(eq_rest.len(), inner_rest_dim);
    debug_assert_eq!(eq_outer.len(), n_outer);

    let mut acc = F128::ZERO;
    for i in 0..(1 << m) {
        if !f[i] {
            continue;
        }
        let i_skip = i & (k_skip_dim - 1);
        let i_inner_rest = (i >> k_skip) & (inner_rest_dim - 1);
        let i_outer = i / k;
        acc += lambda[i_skip] * eq_rest[i_inner_rest] * eq_outer[i_outer];
    }
    acc
}

/// Naive sparse matrix · bool-vector product: `out[i] = ⊕_{j: M[i,j]=1} z[j]`.
fn matrix_vector_product(m: &SparseBinaryMatrix, z: &[bool]) -> Vec<bool> {
    assert_eq!(z.len(), m.num_cols);
    m.rows
        .iter()
        .map(|row| {
            let mut acc = false;
            for &col in row {
                acc ^= z[col];
            }
            acc
        })
        .collect()
}

/// Build a block-diagonal full witness vector from a base matrix and the
/// outer dimension: full[i_inner + i_outer · k] for the i_outer-th block.
/// Used to construct `a = (I_{2^n_log} ⊗ A_0) · z` directly for tests.
fn apply_block_diag(m_0: &SparseBinaryMatrix, z: &[bool], k_log: usize) -> Vec<bool> {
    let k = 1usize << k_log;
    assert_eq!(m_0.num_rows, k);
    assert_eq!(m_0.num_cols, k);
    assert_eq!(z.len() % k, 0);
    let n_outer = z.len() / k;
    let mut out = vec![false; z.len()];
    for i_outer in 0..n_outer {
        let z_block = &z[i_outer * k..(i_outer + 1) * k];
        let a_block = matrix_vector_product(m_0, z_block);
        out[i_outer * k..(i_outer + 1) * k].copy_from_slice(&a_block);
    }
    out
}

/// Build a sparse boolean matrix with `nnz` random nonzero entries among
/// `k × k` slots. Used for tests.
fn random_sparse_matrix(k: usize, nnz: usize, rng: &mut Rng) -> SparseBinaryMatrix {
    let mut rows: Vec<Vec<usize>> = vec![Vec::new(); k];
    let mut seen = std::collections::HashSet::new();
    let mut count = 0;
    while count < nnz {
        let r = (rng.next_u64() as usize) % k;
        let c = (rng.next_u64() as usize) % k;
        if seen.insert((r, c)) {
            rows[r].push(c);
            count += 1;
        }
    }
    for row in &mut rows {
        row.sort();
    }
    SparseBinaryMatrix {
        num_rows: k,
        num_cols: k,
        rows,
    }
}

// ---- Unit tests for the kernels ----

/// `build_eq_table` produces eq(point, i) for all boolean i.
#[test]
fn eq_table_matches_direct_formula() {
    for &d in &[1usize, 2, 3, 5, 8] {
        let mut rng = Rng::new(11 + d as u64);
        let point = rng.f128_vec(d);
        let table = build_eq_table(&point);
        assert_eq!(table.len(), 1 << d);
        for i in 0..(1 << d) {
            let mut expected = F128::ONE;
            for j in 0..d {
                let bit = ((i >> j) & 1) as u64;
                // eq(r, bit) = (1 + r) if bit = 0 else r
                let factor = if bit == 0 {
                    F128::ONE + point[j]
                } else {
                    point[j]
                };
                expected *= factor;
            }
            assert_eq!(table[i], expected, "mismatch at d={d}, i={i}");
        }
    }
}

/// `sparse_row_fold` matches a brute-force dense implementation.
#[test]
fn sparse_row_fold_matches_dense() {
    let mut rng = Rng::new(22);
    let k = 16;
    let nnz = 40;
    let matrix = random_sparse_matrix(k, nnz, &mut rng);
    let eq_table: Vec<F128> = rng.f128_vec(k);

    let got = sparse_row_fold(&matrix, &eq_table);

    // Brute force: for each col j, sum eq[i] over rows i where M[i,j] = 1.
    let mut expected = vec![F128::ZERO; k];
    for (i, row) in matrix.rows.iter().enumerate() {
        for &j in row {
            expected[j] += eq_table[i];
        }
    }
    assert_eq!(got, expected);
}

/// `partial_fold_packed_z` matches the direct sum.
#[test]
fn partial_fold_matches_direct() {
    for &(m, k_log) in &[(10usize, 3), (12, 4), (14, 5), (16, 8)] {
        let mut rng = Rng::new(33 + m as u64);
        let z = rng.bits(1 << m);
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let n_log = m - k_log;
        let outer_point = rng.f128_vec(n_log);
        let eq_outer = build_eq_table(&outer_point);

        let got = partial_fold_packed_z(&z_packed, m, k_log, &eq_outer);

        let k = 1usize << k_log;
        assert_eq!(got.len(), k);
        for i_inner in 0..k {
            let mut acc = F128::ZERO;
            for i_outer in 0..(1usize << n_log) {
                let i = i_inner + i_outer * k;
                if z[i] {
                    acc += eq_outer[i_outer];
                }
            }
            assert_eq!(got[i_inner], acc, "mismatch at m={m}, i_inner={i_inner}");
        }
    }
}

/// `partial_fold_packed_z_fast` (parallel lookup-table) matches the scalar
/// reference `partial_fold_packed_z`.
#[test]
fn partial_fold_fast_matches_serial() {
    for &(m, k_log) in &[(10usize, 3), (12, 4), (14, 5), (16, 8), (18, 10)] {
        let mut rng = Rng::new(800 + m as u64);
        let z = rng.bits(1 << m);
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let n_log = m - k_log;
        let p = rng.f128_vec(n_log);
        let eq = build_eq_table(&p);

        let serial = partial_fold_packed_z(&z_packed, m, k_log, &eq);
        let fast = partial_fold_packed_z_fast(&z_packed, m, k_log, &eq);
        assert_eq!(serial, fast, "at m={m}, k_log={k_log}");
    }
}

/// `partial_fold_packed_z(eq_outer) ↦ ẑ(·, x_outer)` matches direct MLE
/// evaluation of z at `(i_inner, x_outer)` for boolean i_inner.
#[test]
fn partial_fold_is_mle_at_outer_point() {
    let m = 14;
    let k_log = 5;
    let k = 1 << k_log;
    let mut rng = Rng::new(44);
    let z = rng.bits(1 << m);
    let z_packed = pack_z_lincheck(&z, m, k_log);
    let x_outer = rng.f128_vec(m - k_log);
    let eq_outer = build_eq_table(&x_outer);

    let z_partial = partial_fold_packed_z(&z_packed, m, k_log, &eq_outer);

    // For each boolean i_inner ∈ {0,1}^k_log, the partial fold should
    // equal ẑ(i_inner, x_outer).
    for i_inner in 0..k {
        // Construct the m-dim point: first k_log coords from i_inner (boolean lifted),
        // then m-k_log coords from x_outer.
        let mut point = Vec::with_capacity(m);
        for j in 0..k_log {
            point.push(if (i_inner >> j) & 1 == 1 {
                F128::ONE
            } else {
                F128::ZERO
            });
        }
        point.extend_from_slice(&x_outer);
        let z_eval = mle_eval_bool(&z, &point);
        assert_eq!(z_partial[i_inner], z_eval, "i_inner={i_inner}");
    }
}

// ---- End-to-end prove/verify roundtrip on honest data ----

/// Build a small honest instance: random sparse A_0/B_0/C_0, random z;
/// compute a, b, c via apply_block_diag; pick three points; compute true
/// MLE evals as v, v', v''. Roundtrip prove/verify, check claim matches
/// what the verifier would re-derive from the (now-known-honest) z.
#[test]
fn prove_verify_roundtrip_honest() {
    // Exercise a range of k_skip values:
    //   k_skip = 0 (no skip)     — reduces to multilinear lincheck
    //   k_skip = k_log (max)     — only univariate inner
    //   k_skip < k_log (typical) — protocol-realistic case
    for &(m, k_log, k_skip) in &[
        (10usize, 4, 0),
        (10, 4, 2),
        (10, 4, 4),
        (12, 5, 3),
        (14, 7, 6),
        (14, 7, 0),
    ] {
        let k = 1usize << k_log;
        let mut rng = Rng::new(55 + (m * 100 + k_log * 10 + k_skip) as u64);

        // Random sparse base matrices A_0, B_0 (no C since C = I in our use case).
        let nnz_per_mat = k * 2;
        let a_0 = random_sparse_matrix(k, nnz_per_mat, &mut rng);
        let b_0 = random_sparse_matrix(k, nnz_per_mat, &mut rng);

        // Random witness z, then a = A·z, b = B·z.
        let z = rng.bits(1 << m);
        let a = apply_block_diag(&a_0, &z, k_log);
        let b = apply_block_diag(&b_0, &z, k_log);
        let z_packed = pack_z_lincheck(&z, m, k_log);

        // **One shared quirky point** (since zerocheck gives a, b claims at
        // the same point).
        let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);

        // True quirky-MLE eval claims at the shared point.
        let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
        let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);

        // Prove and verify with matched challengers.
        let circuit = SparseMatrixCircuit::new(&a_0, &b_0);
        let mut ch_p = FsChallenger::new(b"flock-test-v0");
        let (proof, claim_p) = prove(&z_packed, m, k_log, k_skip, &circuit, &x_ab, &mut ch_p);

        let mut ch_v = FsChallenger::new(b"flock-test-v0");
        let claim_v = verify(
            m, k_log, k_skip, &circuit, &x_ab, v_a, v_b, &proof, &mut ch_v,
        )
        .unwrap_or_else(|e| {
            panic!("verify rejected honest proof at m={m},k_log={k_log},k_skip={k_skip}: {e:?}")
        });

        assert_eq!(
            claim_p, claim_v,
            "claim mismatch at m={m}, k_log={k_log}, k_skip={k_skip}"
        );

        // The single `w` value must match the true z quirky evaluation
        // at ((r_inner_skip, r_inner_rest), x_ab.x_outer).
        let pt = QuirkyPoint {
            z_skip: claim_v.r_inner_skip,
            x_inner_rest: claim_v.r_inner_rest.clone(),
            x_outer: x_ab.x_outer.clone(),
        };
        assert_eq!(
            claim_v.w,
            mle_eval_bool_quirky(&z, m, k_log, k_skip, &pt),
            "w wrong at m={m}, k_log={k_log}, k_skip={k_skip}"
        );
    }
}

/// Amendment A2 round-trip. The masked prover runs the sumcheck on
/// `z + γ_lc·S`, so every message of the layer belongs to the *shifted*
/// witness — but the output claim it hands on must still be the real
/// `ẑ(ρ)`, or the downstream PCS binding to `ẑ` breaks. This pins:
///
/// 1. prover and verifier agree on the whole claim;
/// 2. the recovered `w` is the true quirky-MLE of the **unmasked** `z`;
/// 3. `s_eval` is the true quirky-MLE of `S` at the *same* point — the
///    exact statement the PCS opening of `S`'s commitment will check;
/// 4. the mask is not vacuous: `z_partial` actually moved.
#[test]
fn masked_roundtrip_recovers_the_unmasked_claim() {
    for &(m, k_log, k_skip) in &[(10usize, 4, 0), (10, 4, 2), (12, 5, 3), (14, 7, 6)] {
        let k = 1usize << k_log;
        let mut rng = Rng::new(9090 + (m * 100 + k_log * 10 + k_skip) as u64);

        let a_0 = random_sparse_matrix(k, k * 2, &mut rng);
        let b_0 = random_sparse_matrix(k, k * 2, &mut rng);
        let z = rng.bits(1 << m);
        let a = apply_block_diag(&a_0, &z, k_log);
        let b = apply_block_diag(&b_0, &z, k_log);
        let z_packed = pack_z_lincheck(&z, m, k_log);

        // The A2 mask: a witness-free cube of the same shape as z.
        let s_bits = rng.bits(1 << m);
        let s_packed = pack_z_lincheck(&s_bits, m, k_log);

        let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);
        let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
        let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);
        let circuit = SparseMatrixCircuit::new(&a_0, &b_0);

        let mut ch_p = FsChallenger::new(b"flock-test-v0");
        let (proof, claim_p, _z_vec, mt) = prove_padded_masked_capture_z_vec(
            &z_packed,
            m,
            k_log,
            k_skip,
            k,
            &circuit,
            &x_ab,
            LincheckMask {
                s_packed: &s_packed,
            },
            &mut ch_p,
        );

        let mut ch_v = FsChallenger::new(b"flock-test-v0");
        let claim_v = verify_masked(
            m,
            k_log,
            k_skip,
            &circuit,
            &x_ab,
            v_a,
            v_b,
            &proof,
            Some((mt.sigma_lc, mt.s_eval)),
            &mut ch_v,
        )
        .unwrap_or_else(|e| panic!("masked verify rejected honest proof at m={m}: {e:?}"));

        assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");

        let pt = QuirkyPoint {
            z_skip: claim_v.r_inner_skip,
            x_inner_rest: claim_v.r_inner_rest.clone(),
            x_outer: x_ab.x_outer.clone(),
        };
        assert_eq!(
            claim_v.w,
            mle_eval_bool_quirky(&z, m, k_log, k_skip, &pt),
            "masked run must still claim the UNMASKED ẑ(ρ) at m={m}"
        );
        assert_eq!(
            mt.s_eval,
            mle_eval_bool_quirky(&s_bits, m, k_log, k_skip, &pt),
            "s_eval must be Ŝ(ρ) in the PCS's sense at m={m}"
        );

        // Non-vacuity: the same statement proved without the channel must
        // produce a different z_partial. (Challenges diverge once σ_lc is
        // absorbed, so this only asserts the transcripts are not equal.)
        let mut ch_u = FsChallenger::new(b"flock-test-v0");
        let (plain, _) = prove(&z_packed, m, k_log, k_skip, &circuit, &x_ab, &mut ch_u);
        assert_ne!(
            plain.z_partial, proof.z_partial,
            "mask channel left z_partial untouched at m={m}"
        );
    }
}

/// σ_lc is bound before γ_lc is drawn, so a prover that misreports it
/// shifts the initial claim by `γ_lc·δ'` and the sumcheck's final check
/// fails. (The γ-batching argument, at the lincheck layer.)
#[test]
fn masked_verify_rejects_sigma_tamper() {
    let (m, k_log, k_skip) = (12usize, 5, 3);
    let k = 1usize << k_log;
    let mut rng = Rng::new(4242);

    let a_0 = random_sparse_matrix(k, k * 2, &mut rng);
    let b_0 = random_sparse_matrix(k, k * 2, &mut rng);
    let z = rng.bits(1 << m);
    let a = apply_block_diag(&a_0, &z, k_log);
    let b = apply_block_diag(&b_0, &z, k_log);
    let z_packed = pack_z_lincheck(&z, m, k_log);
    let s_packed = pack_z_lincheck(&rng.bits(1 << m), m, k_log);

    let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);
    let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
    let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);
    let circuit = SparseMatrixCircuit::new(&a_0, &b_0);

    let mut ch_p = FsChallenger::new(b"flock-test-v0");
    let (proof, _claim, _z, mt) = prove_padded_masked_capture_z_vec(
        &z_packed,
        m,
        k_log,
        k_skip,
        k,
        &circuit,
        &x_ab,
        LincheckMask {
            s_packed: &s_packed,
        },
        &mut ch_p,
    );

    for delta in [1u64, 2, 7, 1 << 33] {
        let bad = mt.sigma_lc + F128::new(delta, 0);
        let mut ch_v = FsChallenger::new(b"flock-test-v0");
        let got = verify_masked(
            m,
            k_log,
            k_skip,
            &circuit,
            &x_ab,
            v_a,
            v_b,
            &proof,
            Some((bad, mt.s_eval)),
            &mut ch_v,
        );
        assert!(
            got.is_err(),
            "verifier accepted a tampered σ_lc (δ={delta})"
        );
    }
}

/// Verify must reject byte-mutated proofs. Mutation positions are picked
/// where the corresponding matrix row-vector entry is **nonzero** —
/// otherwise the inner-product delta vanishes and the mutation is
/// undetectable (a property of the random sparse matrix, not a verifier
/// bug). The verifier's consistency check is sound for *any* mutation in
/// a nonzero-weighted slot.
#[test]
fn verify_rejects_mutations() {
    let m = 12;
    let k_log = 4;
    let k_skip = 2;
    let k = 1 << k_log;
    let mut rng = Rng::new(66);
    let a_0 = random_sparse_matrix(k, k * 5, &mut rng);
    let b_0 = random_sparse_matrix(k, k * 5, &mut rng);
    let z = rng.bits(1 << m);
    let a = apply_block_diag(&a_0, &z, k_log);
    let b = apply_block_diag(&b_0, &z, k_log);
    let z_packed = pack_z_lincheck(&z, m, k_log);
    let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);
    let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
    let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);

    let _seed: u64 = 0xFEEDFACE;
    let circuit = SparseMatrixCircuit::new(&a_0, &b_0);
    let mut ch_p = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove(&z_packed, m, k_log, k_skip, &circuit, &x_ab, &mut ch_p);

    // Pick a mutation position where BOTH row vectors are nonzero so the
    // mutation guarantees both checks would diverge.
    let eq_inner = build_quirky_eq_table(x_ab.z_skip, &x_ab.x_inner_rest, k_skip);
    let row_a = sparse_row_fold(&a_0, &eq_inner);
    let row_b = sparse_row_fold(&b_0, &eq_inner);
    let idx = (0..k)
        .find(|&i| row_a[i] != F128::ZERO || row_b[i] != F128::ZERO)
        .expect("no row-vector slot is nonzero in either A or B — test degenerate");

    // Mutations now target `z_partial` (the post-sumcheck length-2^k_skip
    // vector). Bit-flipping any entry must cause the sumcheck-final check
    // to fail (running_claim ≠ Σ comb_partial · z_partial).
    let n_skip = 1usize << k_skip;
    let skip_idx = idx % n_skip;
    let mutations: Vec<(String, Box<dyn Fn(&LincheckProof) -> LincheckProof>)> = vec![
        (
            format!("z_partial[{skip_idx}].lo bit-flip"),
            Box::new(move |p| {
                let mut q = p.clone();
                q.z_partial[skip_idx].lo ^= 1;
                q
            }),
        ),
        (
            format!("z_partial[{skip_idx}].hi bit-flip"),
            Box::new(move |p| {
                let mut q = p.clone();
                q.z_partial[skip_idx].hi ^= 1;
                q
            }),
        ),
    ];
    for (label, mutate) in mutations {
        let bad = mutate(&proof);
        let mut ch = FsChallenger::new(b"flock-test-v0");
        let res = verify(m, k_log, k_skip, &circuit, &x_ab, v_a, v_b, &bad, &mut ch);
        assert!(
            matches!(res, Err(VerifyError::ConsistencyFailed { .. })),
            "verify did not reject {label}: got {res:?}"
        );
    }
}

/// Verify must reject shape errors.
#[test]
fn verify_rejects_shape_errors() {
    let m = 10;
    let k_log = 3;
    let k_skip = 1;
    let k = 1 << k_log;
    let mut rng = Rng::new(77);
    let a_0 = random_sparse_matrix(k, k, &mut rng);
    let b_0 = random_sparse_matrix(k, k, &mut rng);
    let z = rng.bits(1 << m);
    let a = apply_block_diag(&a_0, &z, k_log);
    let b = apply_block_diag(&b_0, &z, k_log);
    let z_packed = pack_z_lincheck(&z, m, k_log);
    let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);
    let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
    let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);

    let circuit = SparseMatrixCircuit::new(&a_0, &b_0);
    let mut ch_p = FsChallenger::new(b"flock-test-v0");
    let (proof, _) = prove(&z_packed, m, k_log, k_skip, &circuit, &x_ab, &mut ch_p);

    // Truncate z_partial.
    let mut bad = proof.clone();
    bad.z_partial.pop();
    let mut ch = FsChallenger::new(b"flock-test-v0");
    assert!(matches!(
        verify(m, k_log, k_skip, &circuit, &x_ab, v_a, v_b, &bad, &mut ch),
        Err(VerifyError::BadVectorLength { .. })
    ));

    // Wrong x_inner_rest length.
    let mut ch = FsChallenger::new(b"flock-test-v0");
    let bad_x_ab = QuirkyPoint {
        z_skip: x_ab.z_skip,
        x_inner_rest: x_ab.x_inner_rest[..x_ab.x_inner_rest.len() - 1].to_vec(),
        x_outer: x_ab.x_outer.clone(),
    };
    assert!(matches!(
        verify(
            m, k_log, k_skip, &circuit, &bad_x_ab, v_a, v_b, &proof, &mut ch
        ),
        Err(VerifyError::BadInnerRestLength { .. })
    ));

    // k_skip > k_log.
    let mut ch = FsChallenger::new(b"flock-test-v0");
    assert!(matches!(
        verify(
            m,
            k_log,
            k_log + 1,
            &circuit,
            &x_ab,
            v_a,
            v_b,
            &proof,
            &mut ch,
        ),
        Err(VerifyError::KSkipExceedsKLog { .. })
    ));
}

/// Inner stub whose fold contributes nothing: isolates the decorator's
/// own contributions for the matrix-convention equivalence check.
struct ZeroFold {
    k: usize,
}

impl LincheckCircuit for ZeroFold {
    fn n_cols(&self) -> usize {
        self.k
    }
    fn fold_alpha_batched(&self, _alpha: F128, _eq_inner: &[F128]) -> Vec<F128> {
        vec![F128::ZERO; self.k]
    }
    fn const_pin_col(&self) -> Option<usize> {
        Some(0)
    }
}

#[test]
fn zk_decorator_matches_sparse_matrix_convention() {
    // k_log = 10, useful_bits = 512: A rows [512, 640), B rows [640, 768),
    // chain-mask pair [768, 1024). SparseMatrixCircuit folds over every row.
    let cfg = ZkConfig {
        rand_chunks_a: 1,
        rand_chunks_b: 1,
        chain_mask: true,
    };
    let layout = ZkBlockLayout::new(10, 512, Some(7), &cfg);
    let k = 1usize << 10;
    let mut a_rows = vec![Vec::new(); k];
    let mut b_rows = vec![Vec::new(); k];
    for s in layout.a_bits() {
        a_rows[s] = vec![s];
        b_rows[s] = vec![0];
    }
    for s in layout.b_bits() {
        a_rows[s] = vec![0];
        b_rows[s] = vec![s];
    }
    let a_0 = SparseBinaryMatrix {
        num_rows: k,
        num_cols: k,
        rows: a_rows,
    };
    let b_0 = SparseBinaryMatrix {
        num_rows: k,
        num_cols: k,
        rows: b_rows,
    };
    let oracle = SparseMatrixCircuit::new(&a_0, &b_0);
    let stub = ZeroFold { k };
    let decorated = ZkLincheckCircuit::new(&stub, &layout);

    let mut rng = Rng::new(0x5EED_CAFE);
    let alpha = rng.f128();
    let eq_inner: Vec<F128> = (0..k).map(|_| rng.f128()).collect();
    assert_eq!(
        decorated.fold_alpha_batched(alpha, &eq_inner),
        oracle.fold_alpha_batched(alpha, &eq_inner),
    );
}

/// Inner stub with no constant-one wire.
struct NoPin;

impl LincheckCircuit for NoPin {
    fn n_cols(&self) -> usize {
        1 << 10
    }
    fn fold_alpha_batched(&self, _alpha: F128, _eq_inner: &[F128]) -> Vec<F128> {
        vec![F128::ZERO; 1 << 10]
    }
}

#[test]
#[should_panic(expected = "constant-one wire")]
fn zk_decorator_rejects_inner_without_pin() {
    let cfg = ZkConfig {
        rand_chunks_a: 1,
        rand_chunks_b: 1,
        chain_mask: false,
    };
    let layout = ZkBlockLayout::new(10, 512, None, &cfg);
    let _ = ZkLincheckCircuit::new(&NoPin, &layout);
}

#[test]
fn zk_decorator_forwards_inner_surface() {
    let cfg = ZkConfig {
        rand_chunks_a: 1,
        rand_chunks_b: 1,
        chain_mask: false,
    };
    let layout = ZkBlockLayout::new(10, 512, None, &cfg);
    let stub = ZeroFold { k: 1 << 10 };
    let decorated = ZkLincheckCircuit::new(&stub, &layout);
    assert_eq!(decorated.const_pin_col(), Some(0));
    assert_eq!(decorated.n_cols(), 1 << 10);
}

//! Example: zero-knowledge proof of which valid root of a public polynomial over
//! `GF(2^8)` was selected, as a complete FLOCK argument.
//!
//! The relation is a Boolean R1CS with `C = I`, the circuit convention of
//! this repository. One block holds one instance:
//!
//! - wire 0 is the constant one, pinned by the lincheck;
//! - wires 1..=8 hold the selected root;
//! - each Horner step `acc = acc * root + coefficient` spends 64 product
//!   rows (`t_ij = acc_i * root_j`) and 8 reduction rows (linear XOR through
//!   the constant wire, with the public coefficient bits folded in);
//! - an OR chain reduces the final accumulator to one bit, and the row of the
//!   constant wire forces that bit to zero, so `p(root) = 0`.
//!
//! The public polynomial has multiple public roots; because `GF(2^8)` is tiny,
//! the proof hides which valid root was selected, not the root set itself. The
//! batch tiles `2^(M - K_LOG)` copies of the block, each with fresh private
//! randomizer rows. The proof is the full FLOCK pipeline under VEIL: hiding
//! commitment of the packed witness, masked zerocheck with univariate skip,
//! masked lincheck, and two ring-switched openings (`ab` and `c`) with masked
//! slices.
//!
//! Two functions encode the protocol:
//!
//! - `root_prove`: prover-only — commit + native zerocheck + native lincheck.
//! - `root_verify`: reads-and-constrains in one pass; a port of the
//!   production shifted verifier circuit for this R1CS. Runs on the mask
//!   counter, on the verifier, and on the prover replay.

use flock_core::{
    lincheck::{LincheckCircuit, pack_z_lincheck},
    pcs::pack_witness,
    r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout},
    zerocheck::K_SKIP,
};
use veil_examples::{
    BitPcs, MaskSampler, ReadingCtx, SendingCtx, VeilError, ZkProof, ZkRng, bits_to_bytes,
    check_block_shape, initialize_prover_for, lincheck_prove, lincheck_verify, run_example,
    verify_with_body, zerocheck_prove, zerocheck_verify,
};

const DOMAIN: &[u8] = b"veil-examples-root";
/// `2^22` witness bits: the production floor of the hiding PCS.
const M: usize = 22;
/// One instance per `2^K_LOG`-bit block.
const K_LOG: usize = 12;
const DEGREE: usize = 50;
/// Public root set for the demo statement. The proof hides which valid root is
/// used as the witness; the small field makes the set itself enumerable.
const PUBLIC_ROOTS: [u8; 8] = [0x13, 0x57, 0x9b, 0xce, 0x22, 0x84, 0xf1, 0x6d];
/// Extra private rows that are copied through free constraints and do not
/// affect the public polynomial relation.
const RANDOMIZER_ROWS: usize = 256;
/// `x^8 + x^4 + x^3 + x + 1`, the AES field polynomial.
const MODULUS: u16 = 0x11b;

// ============================================================================
// GF(2^8) helpers
// ============================================================================

/// `x^k mod MODULUS` as a byte, for `k < 16`.
const REDUCTION: [u8; 16] = reduction_table();

const fn reduction_table() -> [u8; 16] {
    let mut table = [0u8; 16];
    let mut value: u16 = 1;
    let mut index = 0;
    while index < table.len() {
        table[index] = value as u8;
        value <<= 1;
        if value & 0x100 != 0 {
            value ^= MODULUS;
        }
        index += 1;
    }
    table
}

fn gf8_mul(a: u8, b: u8) -> u8 {
    let mut acc = 0u8;
    for i in 0..8 {
        for j in 0..8 {
            if (a >> i) & 1 == 1 && (b >> j) & 1 == 1 {
                acc ^= REDUCTION[i + j];
            }
        }
    }
    acc
}

fn horner(coeffs: &[u8], x: u8) -> u8 {
    coeffs.iter().rev().fold(0u8, |acc, &c| gf8_mul(acc, x) ^ c)
}

fn poly_mul(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut result = vec![0u8; a.len() + b.len() - 1];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b.iter().enumerate() {
            result[i + j] ^= gf8_mul(ai, bj);
        }
    }
    result
}

/// `p(x) = q(x) * prod_i (x + roots[i])`, where
/// `q(x) = 1 + x + ... + x^(degree - roots.len())`.
fn make_polynomial_with_roots(roots: &[u8], degree: usize) -> Vec<u8> {
    assert!(!roots.is_empty(), "the statement needs at least one root");
    assert!(roots.len() <= degree, "too many roots for the degree");
    let mut product = vec![1u8];
    for &root in roots {
        product = poly_mul(&product, &[root, 1]);
    }
    let cofactor = vec![1u8; degree - roots.len() + 1];
    let result = poly_mul(&product, &cofactor);
    assert_eq!(result.len(), degree + 1);
    result
}

fn public_polynomial() -> Vec<u8> {
    make_polynomial_with_roots(&PUBLIC_ROOTS, DEGREE)
}

fn choose_public_root<R: MaskSampler + ?Sized>(rng: &mut R) -> u8 {
    let mut word = [0u64; 1];
    rng.fill_u64s(&mut word);
    PUBLIC_ROOTS[word[0] as usize % PUBLIC_ROOTS.len()]
}

fn randomizer_bits<R: MaskSampler + ?Sized>(rng: &mut R, count: usize) -> Vec<bool> {
    let mut words = vec![0u64; count.div_ceil(64)];
    rng.fill_u64s(&mut words);
    (0..count)
        .map(|index| (words[index / 64] >> (index % 64)) & 1 == 1)
        .collect()
}

// ============================================================================
// The root relation as a block R1CS with C = I
// ============================================================================

/// Wire indices of one block.
struct Layout {
    const_wire: usize,
    root: [usize; 8],
    /// Per step: 64 product wires, then 8 accumulator wires.
    steps: Vec<([usize; 64], [usize; 8])>,
    /// OR chain: `(product, or)` pairs, `or = x + y + product`.
    ors: Vec<(usize, usize)>,
    /// Free private rows included in the committed witness.
    randomizers: Vec<usize>,
    useful_bits: usize,
}

impl Layout {
    fn new(degree: usize) -> Self {
        let mut next = 0usize;
        let mut alloc = || {
            let wire = next;
            next += 1;
            wire
        };
        let const_wire = alloc();
        let root = std::array::from_fn(|_| alloc());
        let steps = (0..degree)
            .map(|_| {
                let products = std::array::from_fn(|_| alloc());
                let acc = std::array::from_fn(|_| alloc());
                (products, acc)
            })
            .collect();
        let ors = (0..7).map(|_| (alloc(), alloc())).collect();
        let randomizers = (0..RANDOMIZER_ROWS).map(|_| alloc()).collect();
        Self {
            const_wire,
            root,
            steps,
            ors,
            randomizers,
            useful_bits: next,
        }
    }

    /// The accumulator bits before step `step`: public constant bits of the
    /// leading coefficient for step 0, otherwise the previous step's wires.
    fn acc_before(&self, step: usize) -> Option<[usize; 8]> {
        (step > 0).then(|| self.steps[step - 1].1)
    }

    /// The final accumulator wires and the OR chain output.
    fn final_acc(&self) -> [usize; 8] {
        self.steps[self.steps.len() - 1].1
    }

    fn nonzero_flag(&self) -> usize {
        self.ors[self.ors.len() - 1].1
    }
}

/// Build the R1CS for `p(root) = 0`. Row `w` defines wire `w` as
/// `(A_w z) * (B_w z)`; rows past `useful_bits` are empty and pin zero.
fn build_r1cs(layout: &Layout, coeffs: &[u8]) -> BlockR1cs {
    let k = 1usize << K_LOG;
    assert!(layout.useful_bits <= k, "block too small for the relation");
    let mut a_rows: Vec<Vec<usize>> = vec![Vec::new(); k];
    let mut b_rows: Vec<Vec<usize>> = vec![Vec::new(); k];
    let one = layout.const_wire;

    // Free wires: the root bits are `u * 1 = u`.
    for &wire in &layout.root {
        a_rows[wire] = vec![wire];
        b_rows[wire] = vec![one];
    }

    for (step, (products, acc)) in layout.steps.iter().enumerate() {
        let coefficient = coeffs[DEGREE - 1 - step];
        let leading = coeffs[DEGREE];
        for i in 0..8 {
            for j in 0..8 {
                let wire = products[8 * i + j];
                let acc_bit: Vec<usize> = match layout.acc_before(step) {
                    Some(previous) => vec![previous[i]],
                    None if (leading >> i) & 1 == 1 => vec![one],
                    None => Vec::new(),
                };
                a_rows[wire] = acc_bit;
                b_rows[wire] = vec![layout.root[j]];
            }
        }
        for (bit, &wire) in acc.iter().enumerate() {
            let mut terms: Vec<usize> = (0..8)
                .flat_map(|i| (0..8).map(move |j| (i, j)))
                .filter(|&(i, j)| (REDUCTION[i + j] >> bit) & 1 == 1)
                .map(|(i, j)| products[8 * i + j])
                .collect();
            if (coefficient >> bit) & 1 == 1 {
                terms.push(one);
            }
            a_rows[wire] = terms;
            b_rows[wire] = vec![one];
        }
    }

    // OR chain over the final accumulator: or = x + y + x*y.
    let final_acc = layout.final_acc();
    let mut running = final_acc[0];
    for (index, &(product, or)) in layout.ors.iter().enumerate() {
        let other = final_acc[index + 1];
        a_rows[product] = vec![running];
        b_rows[product] = vec![other];
        a_rows[or] = vec![running, other, product];
        b_rows[or] = vec![one];
        running = or;
    }

    // The constant wire: `1 = (1 + nonzero) * 1` forces `nonzero = 0`.
    a_rows[one] = vec![one, layout.nonzero_flag()];
    b_rows[one] = vec![one];

    // Free randomizer rows: `u = u * 1`.
    for &wire in &layout.randomizers {
        a_rows[wire] = vec![wire];
        b_rows[wire] = vec![one];
    }

    BlockR1cs {
        m: M,
        k_log: K_LOG,
        k_skip: K_SKIP,
        useful_bits: layout.useful_bits,
        a_0: SparseBinaryMatrix {
            num_rows: k,
            num_cols: k,
            rows: a_rows,
        },
        b_0: SparseBinaryMatrix {
            num_rows: k,
            num_cols: k,
            rows: b_rows,
        },
        c_0: SparseBinaryMatrix {
            num_rows: k,
            num_cols: k,
            rows: (0..k).map(|i| vec![i]).collect(),
        },
        layout: WitnessLayout::RowMajor,
        const_pin: Some(one),
        zk: None,
        digest_cache: std::sync::OnceLock::new(),
        csc_cache: std::sync::OnceLock::new(),
    }
}

/// One block of the witness for `root`; every non-randomizer wire follows its
/// R1CS row, and the randomizer rows are caller-supplied private bits.
fn block_witness(layout: &Layout, coeffs: &[u8], root: u8, randomizers: &[bool]) -> Vec<bool> {
    assert_eq!(randomizers.len(), layout.randomizers.len());
    let mut z = vec![false; 1usize << K_LOG];
    z[layout.const_wire] = true;
    for (bit, &wire) in layout.root.iter().enumerate() {
        z[wire] = (root >> bit) & 1 == 1;
    }
    for (&wire, &bit) in layout.randomizers.iter().zip(randomizers) {
        z[wire] = bit;
    }
    let mut acc = coeffs[DEGREE];
    for (step, (products, acc_wires)) in layout.steps.iter().enumerate() {
        let coefficient = coeffs[DEGREE - 1 - step];
        for i in 0..8 {
            for j in 0..8 {
                z[products[8 * i + j]] = (acc >> i) & 1 == 1 && (root >> j) & 1 == 1;
            }
        }
        let mut next = coefficient;
        for i in 0..8 {
            for j in 0..8 {
                if z[products[8 * i + j]] {
                    next ^= REDUCTION[i + j];
                }
            }
        }
        for (bit, &wire) in acc_wires.iter().enumerate() {
            z[wire] = (next >> bit) & 1 == 1;
        }
        acc = next;
    }
    let final_acc = layout.final_acc();
    let mut running = z[final_acc[0]];
    for (index, &(product, or)) in layout.ors.iter().enumerate() {
        let other = z[final_acc[index + 1]];
        z[product] = running && other;
        z[or] = running ^ other ^ z[product];
        running = z[or];
    }
    z
}

/// Tile the relation over the batch, refreshing randomizer rows per block.
fn full_witness<R: MaskSampler + ?Sized>(
    layout: &Layout,
    coeffs: &[u8],
    root: u8,
    rng: &mut R,
) -> Vec<bool> {
    let instances = 1usize << (M - K_LOG);
    let mut witness = Vec::with_capacity(1usize << M);
    for _ in 0..instances {
        let randomizers = randomizer_bits(rng, layout.randomizers.len());
        witness.extend(block_witness(layout, coeffs, root, &randomizers));
    }
    witness
}

// ============================================================================
// Generic protocol code
// ============================================================================

/// Prover-only entry point: commit the packed witness, then run the native
/// FLOCK zerocheck and lincheck provers through the masking context.
fn root_prove<C: SendingCtx>(ctx: &mut C, r1cs: &BlockR1cs, z: &[bool]) {
    let z_packed = pack_witness(z, M);
    ctx.commit_bits(z_packed)
        .expect("failed to commit the witness");
    ctx.observe_label(b"veil-examples-root-statement");
    ctx.observe_bytes(&r1cs.statement_digest());

    let a = bits_to_bytes(&r1cs.apply_a(z));
    let b = bits_to_bytes(&r1cs.apply_b(z));
    let c = bits_to_bytes(z);
    let claim =
        zerocheck_prove(ctx, &a, &b, &c, M, &r1cs.padding_spec()).expect("zerocheck prover failed");

    let x_ab = r1cs.x_ab_from_mlv(claim.z, &claim.mlv_challenges);
    let z_lincheck = pack_z_lincheck(z, M, K_LOG);
    lincheck_prove(ctx, r1cs, r1cs.csc_lincheck_circuit(), &z_lincheck, &x_ab);
}

/// Unified read+constrain pass: the shifted FLOCK verifier for this R1CS.
/// Every read returns an error on a malformed proof, so the verifier never
/// panics on untrusted input.
fn root_verify<C: ReadingCtx>(r1cs: &BlockR1cs, ctx: &mut C) -> Result<(), VeilError> {
    check_block_shape(r1cs)?;
    let oracle = ctx.read_oracle(M)?;
    ctx.absorb_label(b"veil-examples-root-statement");
    ctx.absorb_bytes(&r1cs.statement_digest());

    let zc = zerocheck_verify(M, ctx)?;
    let x_ab = r1cs.x_ab_from_mlv(zc.z, &zc.mlv_challenges);
    let circuit: &dyn LincheckCircuit = r1cs.csc_lincheck_circuit();
    let lc = lincheck_verify(r1cs, circuit, &x_ab, zc.a_eval, zc.b_eval, ctx)?;

    let ab_point = r1cs.ab_claim_point(lc.r_inner_skip, &lc.r_inner_rest, &x_ab.x_outer);
    let c_point = r1cs.c_claim_point(zc.z, &zc.r_rest);
    ctx.assert_bit_mle_eval(oracle, ab_point, lc.w);
    ctx.assert_bit_mle_eval(oracle, c_point, zc.c_eval);
    Ok(())
}

// ============================================================================
// Driver
// ============================================================================

fn prove(
    pcs: &BitPcs,
    r1cs: &BlockR1cs,
    z: &[bool],
    rng: ZkRng,
) -> Result<(ZkProof, usize), VeilError> {
    let (mut pctx, mask_length) =
        initialize_prover_for(DOMAIN, pcs, rng, |ctx| root_verify(r1cs, ctx))?;
    root_prove(&mut pctx, r1cs, z);
    // The prover replays the SAME verify body to build the constraints.
    root_verify(r1cs, &mut pctx)?;
    Ok((pctx.prove()?, mask_length))
}

fn verify(pcs: &BitPcs, r1cs: &BlockR1cs, proof: ZkProof) -> Result<(), VeilError> {
    verify_with_body(DOMAIN, pcs, proof, |ctx| root_verify(r1cs, ctx))
}

fn main() {
    flock_core::init_perf_thread_pool();
    let mut rng = ZkRng::from_entropy();
    let coeffs = public_polynomial();
    let selected_root = choose_public_root(&mut rng.fork(b"veil-examples-root-choice"));
    assert_eq!(
        horner(&coeffs, selected_root),
        0,
        "polynomial should vanish at the selected root"
    );
    eprintln!(
        "Public polynomial over GF(2^8), degree {DEGREE}, {} valid public roots",
        PUBLIC_ROOTS.len()
    );

    let layout = Layout::new(DEGREE);
    let r1cs = build_r1cs(&layout, &coeffs);
    let z = full_witness(
        &layout,
        &coeffs,
        selected_root,
        &mut rng.fork(b"veil-examples-root-randomizers"),
    );
    assert!(r1cs.satisfies(&z), "witness should satisfy the R1CS");
    eprintln!(
        "R1CS: 2^{K_LOG}-bit blocks, {} useful wires, 2^{} instances",
        r1cs.useful_bits,
        M - K_LOG
    );
    let pcs = BitPcs::new(M).expect("registered hiding PCS shape");
    run_example(
        || prove(&pcs, &r1cs, &z, rng),
        |proof| verify(&pcs, &r1cs, proof),
    );
}

#[cfg(test)]
mod tests {
    use veil_examples::{
        F128, RING_WIDTH, ZkVerifierCtx, assert_no_unmasked_f128_values, bit_mle_eval,
        compute_mask_length, ring_slices,
    };
    use veil_f128::ConstraintError;

    use super::*;

    const ROOT_A: u8 = PUBLIC_ROOTS[0];
    const ROOT_B: u8 = PUBLIC_ROOTS[1];

    fn witness_for(root: u8, seed: u8) -> Vec<bool> {
        let coeffs = public_polynomial();
        full_witness(
            &Layout::new(DEGREE),
            &coeffs,
            root,
            &mut ZkRng::from_seed([seed; 32]),
        )
    }

    fn fixture() -> (BitPcs, BlockR1cs, Vec<bool>) {
        let coeffs = public_polynomial();
        let r1cs = build_r1cs(&Layout::new(DEGREE), &coeffs);
        (BitPcs::new(M).unwrap(), r1cs, witness_for(ROOT_A, 0xA0))
    }

    fn first_non_root(coeffs: &[u8]) -> u8 {
        (0u16..=u8::MAX as u16)
            .map(|value| value as u8)
            .find(|&root| horner(coeffs, root) != 0)
            .expect("not every field element is a root")
    }

    /// Zerocheck, lincheck, and two ring claims.
    fn expected_masks() -> usize {
        2 * (1 << K_SKIP)
            + 2 * (M - K_SKIP)
            + 2
            + 2 * (K_LOG - K_SKIP)
            + (1 << K_SKIP)
            + 2 * 2 * RING_WIDTH
    }

    #[test]
    fn gf8_arithmetic_is_consistent() {
        let coeffs = public_polynomial();
        assert_eq!(coeffs.len(), DEGREE + 1);
        assert_eq!(coeffs[DEGREE], 1);
        let mut public_roots = PUBLIC_ROOTS.to_vec();
        public_roots.sort_unstable();
        let actual_roots = (0u16..=u8::MAX as u16)
            .map(|value| value as u8)
            .filter(|&root| horner(&coeffs, root) == 0)
            .collect::<Vec<_>>();
        assert_eq!(actual_roots, public_roots);
        for root in PUBLIC_ROOTS {
            assert_eq!(horner(&coeffs, root), 0, "root {root:#x}");
            assert_ne!(coeffs[0], root, "the constant coefficient leaked a root");
        }
        // Commutativity and the AES identity 0x53 * 0xca = 1.
        assert_eq!(gf8_mul(0x53, 0xca), 1);
        assert_eq!(gf8_mul(0x57, 0x83), gf8_mul(0x83, 0x57));
        assert_eq!(gf8_mul(0x57, 0x83), 0xc1);
    }

    #[test]
    fn witness_satisfies_the_r1cs_and_wrong_root_does_not() {
        let (_, r1cs, z) = fixture();
        assert!(r1cs.satisfies(&z));
        let non_root = first_non_root(&public_polynomial());
        assert!(!r1cs.satisfies(&witness_for(non_root, 0xA1)));
    }

    #[test]
    fn same_public_statement_accepts_multiple_roots() {
        let coeffs = public_polynomial();
        let layout = Layout::new(DEGREE);
        let r1cs = build_r1cs(&layout, &coeffs);
        let a = full_witness(&layout, &coeffs, ROOT_A, &mut ZkRng::from_seed([0xA2; 32]));
        let b = full_witness(&layout, &coeffs, ROOT_B, &mut ZkRng::from_seed([0xA3; 32]));
        assert_eq!(
            r1cs.statement_digest(),
            build_r1cs(&layout, &coeffs).statement_digest()
        );
        assert!(r1cs.satisfies(&a));
        assert!(r1cs.satisfies(&b));
        assert_ne!(a, b);

        let pcs = BitPcs::new(M).unwrap();
        let (proof_a, _) = prove(&pcs, &r1cs, &a, ZkRng::from_seed([0xA6; 32])).unwrap();
        let (proof_b, _) = prove(&pcs, &r1cs, &b, ZkRng::from_seed([0xA7; 32])).unwrap();
        verify(&pcs, &r1cs, proof_a.clone()).unwrap();
        verify(&pcs, &r1cs, proof_b.clone()).unwrap();
        assert_ne!(proof_a.masked_transcript, proof_b.masked_transcript);
    }

    #[test]
    fn randomizer_rows_are_private_and_non_fixed() {
        let coeffs = public_polynomial();
        let layout = Layout::new(DEGREE);
        let witness = full_witness(&layout, &coeffs, ROOT_A, &mut ZkRng::from_seed([0xA4; 32]));
        let block_size = 1usize << K_LOG;
        let first = layout
            .randomizers
            .iter()
            .map(|&wire| witness[wire])
            .collect::<Vec<_>>();
        let second = layout
            .randomizers
            .iter()
            .map(|&wire| witness[block_size + wire])
            .collect::<Vec<_>>();
        assert!(first.iter().any(|bit| *bit));
        assert_ne!(first, second);
    }

    #[test]
    fn mask_count_matches_the_transcript() {
        let (pcs, r1cs, _) = fixture();
        assert_eq!(
            compute_mask_length(Some(&pcs), |ctx| root_verify(&r1cs, ctx)).unwrap(),
            expected_masks()
        );
    }

    #[test]
    fn root_proof_roundtrip() {
        let (pcs, r1cs, z) = fixture();
        let (proof, _) = prove(&pcs, &r1cs, &z, ZkRng::from_seed([1; 32])).unwrap();
        assert_eq!(proof.masked_transcript.len(), expected_masks());
        assert_eq!(proof.commitments.len(), 1);
        assert_eq!(proof.pcs_openings.len(), 1);
        verify(&pcs, &r1cs, proof).unwrap();
    }

    #[test]
    fn proof_surface_omits_unmasked_terminal_data() {
        let (pcs, r1cs, z) = fixture();
        let (proof, _) = prove(&pcs, &r1cs, &z, ZkRng::from_seed([0xA8; 32])).unwrap();

        let mut replay = ZkVerifierCtx::init(DOMAIN, proof.clone(), Some(pcs.clone())).unwrap();
        replay.read_oracle(M).unwrap();
        replay.absorb_label(b"veil-examples-root-statement");
        replay.absorb_bytes(&r1cs.statement_digest());
        let zc = zerocheck_verify(M, &mut replay).unwrap();
        let z_skip = zc.z;
        let mlv_challenges = zc.mlv_challenges.clone();
        let r_rest = zc.r_rest.clone();
        let circuit: &dyn LincheckCircuit = r1cs.csc_lincheck_circuit();
        let lc = lincheck_verify(
            &r1cs,
            circuit,
            &r1cs.x_ab_from_mlv(z_skip, &mlv_challenges),
            zc.a_eval,
            zc.b_eval,
            &mut replay,
        )
        .unwrap();

        let x_ab = r1cs.x_ab_from_mlv(z_skip, &mlv_challenges);
        let ab_point = r1cs.ab_claim_point(lc.r_inner_skip, &lc.r_inner_rest, &x_ab.x_outer);
        let c_point = r1cs.c_claim_point(z_skip, &r_rest);
        let packed = pack_witness(&z, M);
        let mut sensitive = vec![
            bit_mle_eval(&packed, &ab_point),
            bit_mle_eval(&packed, &c_point),
        ];
        sensitive.extend(ring_slices(&packed, &ab_point));
        sensitive.extend(ring_slices(&packed, &c_point));
        assert_no_unmasked_f128_values(&proof, sensitive);
    }

    #[test]
    fn wrong_root_is_not_provable() {
        let (pcs, r1cs, _) = fixture();
        let bad = witness_for(first_non_root(&public_polynomial()), 0xA5);
        let error = prove(&pcs, &r1cs, &bad, ZkRng::from_seed([2; 32])).unwrap_err();
        assert_eq!(
            error,
            VeilError::Constraint(ConstraintError::UnsatisfiedCircuit)
        );
    }

    #[test]
    fn mutations_are_rejected() {
        let (pcs, r1cs, z) = fixture();
        let (proof, _) = prove(&pcs, &r1cs, &z, ZkRng::from_seed([3; 32])).unwrap();

        let mut bad_zerocheck = proof.clone();
        bad_zerocheck.masked_transcript[0] += F128::ONE;
        assert!(verify(&pcs, &r1cs, bad_zerocheck).is_err());

        let mut bad_lincheck = proof.clone();
        let lincheck_start = 2 * (1 << K_SKIP) + 2 * (M - K_SKIP) + 2;
        bad_lincheck.masked_transcript[lincheck_start] += F128::ONE;
        assert!(verify(&pcs, &r1cs, bad_lincheck).is_err());

        let mut bad_slice = proof;
        bad_slice.blinded_slices[0][0] += F128::ONE;
        assert!(verify(&pcs, &r1cs, bad_slice).is_err());
    }

    #[test]
    fn malformed_block_shape_is_an_error() {
        let (pcs, mut r1cs, _) = fixture();
        r1cs.k_skip = K_LOG + 1;
        assert_eq!(
            compute_mask_length(Some(&pcs), |ctx| root_verify(&r1cs, ctx)).unwrap_err(),
            VeilError::ProofShape("block shape")
        );
    }

    #[test]
    fn wrong_statement_is_rejected() {
        let (pcs, r1cs, z) = fixture();
        let (proof, _) = prove(&pcs, &r1cs, &z, ZkRng::from_seed([4; 32])).unwrap();
        let other_roots = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80];
        let other = build_r1cs(
            &Layout::new(DEGREE),
            &make_polynomial_with_roots(&other_roots, DEGREE),
        );
        assert!(verify(&pcs, &other, proof).is_err());
    }
}

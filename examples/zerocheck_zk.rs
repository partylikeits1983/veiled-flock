//! Example: zero-knowledge FLOCK zerocheck over three committed bit vectors.
//!
//! Protocol:
//! 1. Generate random Boolean vectors `a`, `b` of `2^22` bits and compute
//!    `c = a AND b`.
//! 2. Commit `a`, `b`, `c` with the hiding PCS.
//! 3. Run FLOCK's zerocheck with univariate skip on `a * b + c = 0` over the
//!    hypercube. The prover context masks every round message.
//! 4. The verify body replays the univariate-skip interpolation, the
//!    multilinear fold recurrences, and the terminal product as VEIL
//!    constraints.
//! 5. Tie the terminal evaluations to `a`, `b` at `(z, rho)` and to `c` at
//!    `(z, r_rest)` via ring-switched openings with masked slices.
//!
//! Two functions encode the protocol:
//!
//! - `zerocheck_prove`: prover-only — commit + native zerocheck prover.
//! - `zerocheck_verify`: reads-and-constrains in one pass. Generic over any
//!   `ReadingCtx`, so it runs on the mask counter, on the verifier, and on
//!   the prover replay.

use flock_core::{
    pcs::{pack_witness, unpack_witness},
    zerocheck::PaddingSpec,
};
use veil_examples::{
    BitPcs, F128, QuirkyPoint, ReadingCtx, SendingCtx, VeilError, ZkProof, ZkRng, bits_to_bytes,
    initialize_prover_for, random_packed_bits, run_example, verify_with_body, zerocheck_prove,
    zerocheck_verify,
};

const DOMAIN: &[u8] = b"veil-examples-zerocheck";
/// `2^22` bits per vector: the production floor of the hiding PCS.
const M: usize = 22;

/// A bit vector in the two layouts the protocol consumes.
struct BitVector {
    bytes: Vec<u8>,
    packed: Vec<F128>,
}

impl BitVector {
    fn new(bits: &[bool]) -> Self {
        Self {
            bytes: bits_to_bytes(bits),
            packed: pack_witness(bits, M),
        }
    }
}

/// Random `a`, `b`, and `c = a AND b`.
fn random_instance(rng: &mut ZkRng, pcs: &BitPcs) -> (Vec<bool>, Vec<bool>, Vec<bool>) {
    let a = unpack_witness(&random_packed_bits(rng, pcs), M);
    let b = unpack_witness(&random_packed_bits(rng, pcs), M);
    let c = a.iter().zip(&b).map(|(x, y)| *x && *y).collect();
    (a, b, c)
}

// ============================================================================
// Generic protocol code
// ============================================================================

/// Prover-only entry point: commit `a`, `b`, `c`, then run the native FLOCK
/// zerocheck prover through the masking context.
fn zerocheck_prove_all<C: SendingCtx>(ctx: &mut C, a: &BitVector, b: &BitVector, c: &BitVector) {
    for vector in [a, b, c] {
        ctx.commit_bits(vector.packed.clone())
            .expect("failed to commit a vector");
    }
    zerocheck_prove(ctx, &a.bytes, &b.bytes, &c.bytes, M, &PaddingSpec::dense(M))
        .expect("zerocheck prover failed");
}

/// The zerocheck claim points as quirky points with no inner-rest block:
/// `a`, `b` at `(z, rho)` and `c` at `(z, r_rest)`.
fn quirky(z_skip: F128, rest: &[F128]) -> QuirkyPoint {
    QuirkyPoint {
        z_skip,
        x_inner_rest: Vec::new(),
        x_outer: rest.to_vec(),
    }
}

/// Unified read+constrain pass. Every read returns an error on a malformed
/// proof, so the verifier never panics on untrusted input.
fn zerocheck_verify_all<C: ReadingCtx>(ctx: &mut C) -> Result<(), VeilError> {
    let a_oracle = ctx.read_oracle(M)?;
    let b_oracle = ctx.read_oracle(M)?;
    let c_oracle = ctx.read_oracle(M)?;

    let out = zerocheck_verify(M, ctx)?;

    let ab_point = quirky(out.z, &out.mlv_challenges);
    ctx.assert_bit_mle_eval(a_oracle, ab_point.clone(), out.a_eval);
    ctx.assert_bit_mle_eval(b_oracle, ab_point, out.b_eval);
    ctx.assert_bit_mle_eval(c_oracle, quirky(out.z, &out.r_rest), out.c_eval);
    Ok(())
}

// ============================================================================
// Driver
// ============================================================================

fn prove(
    pcs: &BitPcs,
    a: &BitVector,
    b: &BitVector,
    c: &BitVector,
    rng: ZkRng,
) -> Result<(ZkProof, usize), VeilError> {
    let (mut pctx, mask_length) = initialize_prover_for(DOMAIN, pcs, rng, zerocheck_verify_all)?;
    zerocheck_prove_all(&mut pctx, a, b, c);
    // The prover replays the SAME verify body to build the constraints.
    zerocheck_verify_all(&mut pctx)?;
    Ok((pctx.prove()?, mask_length))
}

fn verify(pcs: &BitPcs, proof: ZkProof) -> Result<(), VeilError> {
    verify_with_body(DOMAIN, pcs, proof, zerocheck_verify_all)
}

fn main() {
    flock_core::init_perf_thread_pool();
    let mut rng = ZkRng::from_entropy();
    let pcs = BitPcs::new(M).expect("registered hiding PCS shape");
    eprintln!("Generating random bit vectors (2^{M} bits)...");
    let (a, b, c) = random_instance(&mut rng.fork(b"veil-examples-zerocheck-data"), &pcs);
    let (a, b, c) = (BitVector::new(&a), BitVector::new(&b), BitVector::new(&c));
    run_example(|| prove(&pcs, &a, &b, &c, rng), |proof| verify(&pcs, proof));
}

#[cfg(test)]
mod tests {
    use flock_core::zerocheck::K_SKIP;
    use veil_examples::{
        RING_WIDTH, ZkVerifierCtx, assert_no_unmasked_f128_values, bit_mle_eval,
        compute_mask_length, ring_slices,
    };
    use veil_f128::ConstraintError;

    use super::*;

    fn fixture(seed: u8) -> (BitPcs, Vec<bool>, Vec<bool>, Vec<bool>, ZkRng) {
        let mut rng = ZkRng::from_seed([seed; 32]);
        let pcs = BitPcs::new(M).unwrap();
        let (a, b, c) = random_instance(&mut rng.fork(b"test-data"), &pcs);
        (pcs, a, b, c, rng)
    }

    /// Zerocheck masks: two round-one vectors, `M - K_SKIP` round pairs, two
    /// terminal evaluations. Ring masks: two slices per claim.
    fn expected_masks() -> usize {
        2 * (1 << K_SKIP) + 2 * (M - K_SKIP) + 2 + 3 * 2 * RING_WIDTH
    }

    #[test]
    fn mask_count_matches_the_transcript() {
        let (pcs, ..) = fixture(1);
        assert_eq!(
            compute_mask_length(Some(&pcs), zerocheck_verify_all).unwrap(),
            expected_masks()
        );
    }

    #[test]
    fn zerocheck_proof_roundtrip() {
        let (pcs, a, b, c, rng) = fixture(2);
        let (a, b, c) = (BitVector::new(&a), BitVector::new(&b), BitVector::new(&c));
        let (proof, _) = prove(&pcs, &a, &b, &c, rng).unwrap();
        assert_eq!(proof.masked_transcript.len(), expected_masks());
        assert_eq!(proof.commitments.len(), 3);
        assert_eq!(proof.pcs_openings.len(), 3);
        verify(&pcs, proof).unwrap();
    }

    #[test]
    fn simulator_style_independent_view_verifies() {
        let (pcs, a, b, c, rng) = fixture(8);
        let (a, b, c) = (BitVector::new(&a), BitVector::new(&b), BitVector::new(&c));
        let (proof, _) = prove(&pcs, &a, &b, &c, rng).unwrap();

        let mut simulated_rng = ZkRng::from_seed([0x61; 32]);
        let (sa, sb, sc) = random_instance(&mut simulated_rng.fork(b"simulated-data"), &pcs);
        let (sa, sb, sc) = (
            BitVector::new(&sa),
            BitVector::new(&sb),
            BitVector::new(&sc),
        );
        let (simulated, _) = prove(&pcs, &sa, &sb, &sc, ZkRng::from_seed([0x62; 32])).unwrap();

        verify(&pcs, proof.clone()).unwrap();
        verify(&pcs, simulated.clone()).unwrap();
        assert_ne!(proof.masked_transcript, simulated.masked_transcript);
    }

    #[test]
    fn proof_surface_omits_unmasked_evals_and_slices() {
        let (pcs, a, b, c, rng) = fixture(9);
        let (a, b, c) = (BitVector::new(&a), BitVector::new(&b), BitVector::new(&c));
        let (proof, _) = prove(&pcs, &a, &b, &c, rng).unwrap();

        let mut replay = ZkVerifierCtx::init(DOMAIN, proof.clone(), Some(pcs.clone())).unwrap();
        replay.read_oracle(M).unwrap();
        replay.read_oracle(M).unwrap();
        replay.read_oracle(M).unwrap();
        let out = zerocheck_verify(M, &mut replay).unwrap();
        let ab_point = quirky(out.z, &out.mlv_challenges);
        let c_point = quirky(out.z, &out.r_rest);

        let mut sensitive = vec![
            bit_mle_eval(&a.packed, &ab_point),
            bit_mle_eval(&b.packed, &ab_point),
            bit_mle_eval(&c.packed, &c_point),
        ];
        sensitive.extend(ring_slices(&a.packed, &ab_point));
        sensitive.extend(ring_slices(&b.packed, &ab_point));
        sensitive.extend(ring_slices(&c.packed, &c_point));
        assert_no_unmasked_f128_values(&proof, sensitive);
    }

    #[test]
    fn false_product_is_not_provable() {
        let (pcs, a, b, mut c, rng) = fixture(3);
        c[7] = !c[7];
        let (a, b, c) = (BitVector::new(&a), BitVector::new(&b), BitVector::new(&c));
        let error = prove(&pcs, &a, &b, &c, rng).unwrap_err();
        assert_eq!(
            error,
            VeilError::Constraint(ConstraintError::UnsatisfiedCircuit)
        );
    }

    #[test]
    fn mutations_are_rejected() {
        let (pcs, a, b, c, rng) = fixture(4);
        let (a, b, c) = (BitVector::new(&a), BitVector::new(&b), BitVector::new(&c));
        let (proof, _) = prove(&pcs, &a, &b, &c, rng).unwrap();

        let mut bad_round = proof.clone();
        bad_round.masked_transcript[5] += F128::ONE;
        assert!(verify(&pcs, bad_round).is_err());

        let mut bad_final = proof.clone();
        let final_a = 2 * (1 << K_SKIP) + 2 * (M - K_SKIP);
        bad_final.masked_transcript[final_a] += F128::ONE;
        assert!(verify(&pcs, bad_final).is_err());

        let mut bad_slice = proof;
        bad_slice.blinded_slices[1][3] += F128::ONE;
        assert!(verify(&pcs, bad_slice).is_err());
    }
}

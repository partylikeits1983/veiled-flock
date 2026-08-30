//! Example: zero-knowledge opening of a committed FLOCK bit witness.
//!
//! This is the degenerate terminal case of a FLOCK protocol: commit a
//! Boolean witness of `2^22` bits with the hiding PCS, sample a quirky point,
//! send the evaluation of its multilinear extension, and discharge the claim
//! with a ring-switched opening. Effectively a hiding-PCS smoke test.
//!
//! The opening never reveals the witness slices: the prover sends the 128
//! witness slices and the 128 blinder slices one-time padded, the shifted
//! circuit links them to the public blinded slices `s(z) + c * s(g)`, and the
//! PCS opens `z + c * g` for a challenge `c` sampled after the masked slices
//! are bound.
//!
//! Two functions encode the protocol:
//!
//! - `mle_eval_prove`: prover-only — commit + sample + send.
//! - `mle_eval_verify`: reads the oracle, samples the point, reads the claimed
//!   eval, and registers the ring-switched claim in one `ReadingCtx`-generic
//!   pass. Runs on the mask counter, on the verifier, and (via the prover's
//!   replay `ReadingCtx`) on the prover.

use veil_examples::{
    BitPcs, F128, ReadingCtx, SendingCtx, VeilError, ZkProof, ZkProverCtx, ZkRng, ZkVerifierCtx,
    bit_mle_eval, compute_mask_length, random_packed_bits, run_example, sample_quirky_point,
    sample_quirky_point_sending,
};

const DOMAIN: &[u8] = b"veil-examples-mle-eval";
/// `2^22` committed bits: the production floor of the hiding PCS.
const M: usize = 22;
/// Inner block size of the quirky point; only the univariate-skip block.
const K_LOG: usize = 6;

// ============================================================================
// Generic protocol code
// ============================================================================

/// Prover-only entry point: commit the packed bits, sample the opening
/// point, and send the evaluation on the transcript.
fn mle_eval_prove<C: SendingCtx>(ctx: &mut C, packed: Vec<F128>) {
    let witness = packed.clone();
    ctx.commit_bits(packed)
        .expect("failed to commit the witness");
    let point = sample_quirky_point_sending(ctx, M, K_LOG).expect("addressable point");
    ctx.send_value(bit_mle_eval(&witness, &point));
}

/// Unified read+constrain pass. Every read returns an error on a malformed
/// proof, so the verifier never panics on untrusted input.
fn mle_eval_verify<C: ReadingCtx>(ctx: &mut C) -> Result<(), VeilError> {
    let oracle = ctx.read_oracle(M)?;
    let point = sample_quirky_point(ctx, M, K_LOG)?;
    let claimed_eval = ctx.read_one()?;
    ctx.assert_bit_mle_eval(oracle, point, claimed_eval);
    Ok(())
}

// ============================================================================
// Driver
// ============================================================================

fn prove(pcs: &BitPcs, packed: Vec<F128>, rng: ZkRng) -> Result<(ZkProof, usize), VeilError> {
    let mask_length = compute_mask_length(Some(pcs), mle_eval_verify)?;
    let mut pctx = ZkProverCtx::initialize_with_rng(DOMAIN, mask_length, Some(pcs.clone()), rng)?;
    mle_eval_prove(&mut pctx, packed);
    mle_eval_verify(&mut pctx)?;
    Ok((pctx.prove()?, mask_length))
}

fn verify(pcs: &BitPcs, proof: ZkProof) -> Result<(), VeilError> {
    let mut vctx = ZkVerifierCtx::init(DOMAIN, proof, Some(pcs.clone()))?;
    mle_eval_verify(&mut vctx)?;
    vctx.verify()
}

fn main() {
    flock_core::init_perf_thread_pool();
    let mut rng = ZkRng::from_entropy();
    let pcs = BitPcs::new(M).expect("registered hiding PCS shape");
    let packed = random_packed_bits(&mut rng.fork(b"veil-examples-mle-data"), &pcs);
    eprintln!("Committed witness: 2^{M} bits, PCS m = {}", pcs.m());
    run_example(|| prove(&pcs, packed, rng), |proof| verify(&pcs, proof));
}

#[cfg(test)]
mod tests {
    use veil_examples::RING_WIDTH;

    use super::*;

    fn fixture(seed: u8) -> (BitPcs, Vec<F128>, ZkRng) {
        let mut rng = ZkRng::from_seed([seed; 32]);
        let pcs = BitPcs::new(M).unwrap();
        let packed = random_packed_bits(&mut rng.fork(b"test-data"), &pcs);
        (pcs, packed, rng)
    }

    #[test]
    fn mask_count_matches_the_transcript() {
        let (pcs, _, _) = fixture(1);
        assert_eq!(
            compute_mask_length(Some(&pcs), mle_eval_verify).unwrap(),
            1 + 2 * RING_WIDTH
        );
        assert_eq!(pcs.blind_grinding_bits().unwrap(), 2);
    }

    #[test]
    fn mle_eval_proof_roundtrip() {
        let (pcs, packed, rng) = fixture(2);
        let (proof, _) = prove(&pcs, packed, rng).unwrap();
        assert_eq!(proof.masked_transcript.len(), 1 + 2 * RING_WIDTH);
        assert_eq!(proof.commitments.len(), 1);
        assert_eq!(proof.pcs_openings.len(), 1);
        verify(&pcs, proof).unwrap();
    }

    #[test]
    fn mutations_are_rejected() {
        let (pcs, packed, rng) = fixture(3);
        let (proof, _) = prove(&pcs, packed, rng).unwrap();

        let mut bad_eval = proof.clone();
        bad_eval.masked_transcript[0] += F128::ONE;
        assert!(verify(&pcs, bad_eval).is_err());

        let mut bad_slice = proof.clone();
        bad_slice.masked_transcript[1] += F128::ONE;
        assert!(verify(&pcs, bad_slice).is_err());

        let mut bad_blinded = proof.clone();
        bad_blinded.blinded_slices[0][0] += F128::ONE;
        assert!(verify(&pcs, bad_blinded).is_err());

        let mut bad_root = proof.clone();
        bad_root.commitments[0].root[0] ^= 1;
        assert!(verify(&pcs, bad_root).is_err());

        // A proof without commitments is an error, not a panic.
        let mut no_oracle = proof.clone();
        no_oracle.commitments.clear();
        no_oracle.oracle_nonces.clear();
        no_oracle.pcs_openings.clear();
        assert_eq!(
            verify(&pcs, no_oracle).unwrap_err(),
            VeilError::OracleExhausted
        );

        let mut short = proof;
        short.masked_transcript.truncate(1);
        assert_eq!(
            verify(&pcs, short).unwrap_err(),
            VeilError::TranscriptNotConsumed
        );
    }
}

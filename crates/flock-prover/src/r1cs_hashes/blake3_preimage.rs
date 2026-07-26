//! **The fixed-digest BLAKE3 preimage statement.**
//!
//! ```text
//!   public:  y_1 … y_n           (BLAKE3 digests)
//!   private: x_1 … x_n           (64-byte messages)
//!   claim:   BLAKE3(x_i) = y_i   for every i
//! ```
//!
//! This is the statement applications ask for, and it is a strictly stronger
//! object than the batch statement this crate started with. The batch
//! statement binds nothing — its digest covers the matrices and layout only,
//! so "there exist `2^n` valid compressions" is all it asserts, and a prover
//! who knows no preimage at all can satisfy it by hashing messages of its own
//! choosing. Here the digests are public inputs: they are enforced by the
//! relation, bound into the transcript before any challenge, and checked by
//! the verifier against the committed witness.
//!
//! ## What makes one compression a whole hash
//!
//! BLAKE3 of a message that fits in a single 64-byte block is one compression
//! with `cv = IV`, `counter = 0`, `block_len = 64` and
//! `flags = CHUNK_START|CHUNK_END|ROOT`. [`ParamPinning::RootHash64`] pins
//! exactly those wires in the R1CS, so the circuit no longer accepts *some*
//! compression — it accepts the hash. The message words stay free: they are
//! the witness. Longer messages need chunk/tree chaining and are future work
//! (`docs/memos/fixed-digest-relation.md`); the statement encoding records the
//! length policy so a proof for this relation can never be read as a proof for
//! another.
//!
//! ## How the digests are bound
//!
//! One public-target packed-direct claim in the existing batched opening
//! ([`crate::digest_bind`]). The verifier computes the target itself from the
//! public digest list, so there is no prover-supplied value to attack, and the
//! claim rides the opening that already exists rather than adding a second
//! commitment or sumcheck.
//!
//! ## Zero-knowledge status
//!
//! The prove entry points here are the **non-zk** ones: they prove knowledge
//! of preimages, they do not hide them. The zk mode for this statement needs a
//! simulator that receives only `y` and produces an accepting transcript — a
//! different object from the batch mode's simulator, which is the honest
//! prover on a self-chosen witness and is valid *only* because that statement
//! binds nothing. See `docs/memos/` for the construction and its open
//! obligations; until it is built and certified, no zero-knowledge claim
//! attaches to this statement.

use flock_core::challenger::Challenger;
use flock_core::pcs::{Commitment, PcsParams};
use flock_core::proof::R1csProofLigerito;
use flock_core::r1cs::BlockR1cs;

use crate::digest_bind::{
    DigestChallenges, DigestLayout, DigestStatement, PaddingDigest, digest_claim,
    digest_claim_point, digest_claim_value,
};
use crate::r1cs_hashes::blake3::{
    BLAKE3_IV, Compression, FLAGS_ROOT_HASH, K_LOG, ParamPinning, ROOT_HASH_BLOCK_LEN,
    build_block_r1cs_pinned, generate_witness_with_ab_packed_and_lincheck_pinned, min_n_blocks_log,
};

/// Bytes of message covered by one instance of this relation.
pub const MESSAGE_BYTES: usize = 64;
/// Bytes of digest produced per instance.
pub const DIGEST_BYTES: usize = 32;

/// The digest region's geometry in a BLAKE3 witness block: `out_lo` is the
/// 256-bit aligned slot 1 (see the encoder's I/O-aligned layout).
pub fn digest_layout() -> DigestLayout {
    DigestLayout {
        k_log: K_LOG,
        region_log: 8,
        region_bits: 256,
        output_byte_off: 32,
    }
}

/// Convert a 32-byte digest to the physical within-slot bit order the witness
/// stores (word `w`, bit `b` ↦ slot bit `32w + b`, LSB-first within a word).
pub fn digest_to_bits(digest: &[u8; DIGEST_BYTES]) -> Vec<bool> {
    let mut bits = vec![false; 256];
    for w in 0..8 {
        let word = u32::from_le_bytes(digest[w * 4..w * 4 + 4].try_into().unwrap());
        for b in 0..32 {
            bits[w * 32 + b] = (word >> b) & 1 == 1;
        }
    }
    bits
}

/// The compression that hashes a 64-byte message under the pinned parameters.
pub fn message_compression(msg: &[u8; MESSAGE_BYTES]) -> Compression {
    let m: [u32; 16] =
        std::array::from_fn(|i| u32::from_le_bytes(msg[i * 4..i * 4 + 4].try_into().unwrap()));
    (BLAKE3_IV, m, 0u64, ROOT_HASH_BLOCK_LEN, FLAGS_ROOT_HASH)
}

/// Setup for the fixed-digest preimage relation over `n_blocks` instances.
#[derive(Clone, Debug)]
pub struct Blake3PreimageSetup {
    pub n_blocks: usize,
    pub r1cs: BlockR1cs,
    pub pcs_params: PcsParams,
}

/// Why a preimage proof was refused before any cryptography ran.
#[derive(Debug, PartialEq, Eq)]
pub enum PreimageError {
    /// The supplied preimages do not hash to the stated digests. Caught by the
    /// prover so a caller learns it has the wrong witness, rather than
    /// producing a proof that silently fails to verify.
    DigestMismatch { index: usize },
    /// The statement's digest count does not match the setup's batch size.
    BatchSizeMismatch { expected: usize, got: usize },
}

impl std::fmt::Display for PreimageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DigestMismatch { index } => write!(
                f,
                "preimage {index} does not hash to the stated digest — wrong witness"
            ),
            Self::BatchSizeMismatch { expected, got } => {
                write!(f, "statement has {got} digests, setup expects {expected}")
            }
        }
    }
}

impl std::error::Error for PreimageError {}

impl Blake3PreimageSetup {
    /// Build a setup for `n_blocks` preimage instances.
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        let n_log = min_n_blocks_log(n_blocks);
        let r1cs = build_block_r1cs_pinned(n_log, ParamPinning::RootHash64);
        r1cs.csc_lincheck_circuit();
        flock_core::scratch::prewarm_prover(r1cs.m);
        let pcs_params = PcsParams {
            m: r1cs.m,
            log_inv_rate: 1,
            log_batch_size: 6,
            profile: flock_core::pcs::ligerito::LigeritoProfile::Fast,
            zk: false,
        };
        Self {
            n_blocks,
            r1cs,
            pcs_params,
        }
    }

    pub fn n_blocks_log(&self) -> usize {
        min_n_blocks_log(self.n_blocks)
    }

    /// The public statement for a digest list. The padding rule is fixed by
    /// the pinning: padding slots carry the hash of the all-zero message.
    pub fn statement(&self, digests: &[[u8; DIGEST_BYTES]]) -> DigestStatement {
        let pad_words = ParamPinning::RootHash64.padding_digest_words();
        let mut pad = [0u8; DIGEST_BYTES];
        for w in 0..8 {
            pad[w * 4..w * 4 + 4].copy_from_slice(&pad_words[w].to_le_bytes());
        }
        DigestStatement {
            layout: digest_layout(),
            n_log: self.n_blocks_log(),
            digests: digests.iter().map(digest_to_bits).collect(),
            padding: PaddingDigest::Constant,
            padding_bits: digest_to_bits(&pad),
        }
    }

    /// Compute the digests of a preimage list — the honest public statement
    /// for that witness.
    pub fn digests_of(msgs: &[[u8; MESSAGE_BYTES]]) -> Vec<[u8; DIGEST_BYTES]> {
        msgs.iter().map(|m| *::blake3::hash(m).as_bytes()).collect()
    }

    /// Prove knowledge of `msgs` with `BLAKE3(msgs[i]) == stmt digest i`.
    ///
    /// The prover checks the witness against the statement first: a mismatch
    /// is a caller error, not a proof that fails downstream for opaque
    /// reasons.
    pub fn prove<Ch: Challenger>(
        &self,
        msgs: &[[u8; MESSAGE_BYTES]],
        digests: &[[u8; DIGEST_BYTES]],
        challenger: &mut Ch,
    ) -> Result<(R1csProofLigerito, Commitment), PreimageError> {
        if digests.len() != self.n_blocks {
            return Err(PreimageError::BatchSizeMismatch {
                expected: self.n_blocks,
                got: digests.len(),
            });
        }
        if msgs.len() != self.n_blocks {
            return Err(PreimageError::BatchSizeMismatch {
                expected: self.n_blocks,
                got: msgs.len(),
            });
        }
        for (i, (m, d)) in msgs.iter().zip(digests).enumerate() {
            if ::blake3::hash(m).as_bytes() != d {
                return Err(PreimageError::DigestMismatch { index: i });
            }
        }
        let stmt = self.statement(digests);
        stmt.validate();

        let blocks: Vec<Compression> = msgs.iter().map(message_compression).collect();
        let (z_packed, a_packed, b_packed, z_lincheck) =
            generate_witness_with_ab_packed_and_lincheck_pinned(
                &blocks,
                self.n_blocks_log(),
                ParamPinning::RootHash64,
            );
        let lc_circuit = self.r1cs.csc_lincheck_circuit();
        let log_n = self.pcs_params.log_msg_len();
        let lig_config = flock_core::pcs::ligerito::prover_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        )
        .expect("Ligerito prover config");

        // The public digests enter the transcript BEFORE anything else, so
        // every challenge in the proof — and therefore the proof itself — is
        // specific to this list, in this order, with this padding rule.
        absorb_statement(challenger, &stmt);

        let core = crate::prover::prove_fast_core(
            &self.r1cs,
            &self.pcs_params,
            z_packed,
            a_packed,
            b_packed,
            z_lincheck,
            lc_circuit,
            challenger,
        );

        let dch = DigestChallenges::sample(&stmt, challenger);
        let pd = digest_claim(&stmt, self.r1cs.layout, &dch);

        let padding = self.r1cs.padding_spec();
        let ab_x_outer = crate::prover::quirky_x_outer_full(&core.ab.point);
        let c_x_outer = crate::prover::quirky_x_outer_full(&core.c.point);
        let crate::prover::ProveCore {
            zc_proof,
            lc_proof,
            commitment,
            prover_data,
            z_packed,
            s_hat_v_ab,
            s_hat_v_c,
            ..
        } = core;
        let pcs_open = flock_core::pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v(
            z_packed,
            &prover_data,
            &commitment,
            &[ab_x_outer.as_slice(), c_x_outer.as_slice()],
            &[s_hat_v_ab.as_deref(), Some(s_hat_v_c.as_slice())],
            std::slice::from_ref(&pd),
            &padding,
            &lig_config,
            challenger,
        );
        Ok((
            R1csProofLigerito {
                zerocheck: zc_proof,
                lincheck: lc_proof,
                pcs_open,
            },
            commitment,
        ))
    }

    /// Verify a preimage proof against the public digest list.
    pub fn verify<Ch: Challenger>(
        &self,
        commitment: &Commitment,
        proof: &R1csProofLigerito,
        digests: &[[u8; DIGEST_BYTES]],
        challenger: &mut Ch,
    ) -> Result<(), flock_core::verifier::VerifyError> {
        let stmt = self.statement(digests);
        stmt.validate();
        let log_n = self.pcs_params.log_msg_len();
        let lig_v = flock_core::pcs::ligerito::verifier_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        )
        .expect("Ligerito verifier config");

        absorb_statement(challenger, &stmt);

        let (ab, c) = flock_core::verifier::verify_core(
            &self.r1cs,
            &proof.zerocheck,
            &proof.lincheck,
            commitment,
            self.r1cs.csc_lincheck_circuit(),
            challenger,
        )?;

        let dch = DigestChallenges::sample(&stmt, challenger);
        let point = digest_claim_point(&stmt, self.r1cs.layout, &dch);
        let value = digest_claim_value(&stmt, &dch);

        flock_core::verifier::verify_claims_ligerito_with_config_pd(
            commitment,
            &[ab, c],
            &[flock_core::pcs::PackedDirectClaimRef {
                point: &point,
                value,
            }],
            &proof.pcs_open,
            &self.pcs_params,
            &lig_v,
            challenger,
        )
        .map_err(flock_core::verifier::VerifyError::PcsAb)
    }
}

/// Absorb the public digest statement into the transcript.
///
/// This must happen before any challenge is drawn: it is what makes every
/// subsequent challenge — and therefore the whole proof — specific to this
/// digest list, in this order, with this padding rule. Without it a proof
/// could be replayed against a permuted or truncated list.
fn absorb_statement<Ch: Challenger>(challenger: &mut Ch, stmt: &DigestStatement) {
    challenger.observe_label(b"flock-blake3-preimage-v1");
    challenger.observe_bytes(&stmt.public_digest());
}

#[cfg(test)]
mod tests {
    use super::*;
    use flock_core::challenger::FsChallenger;

    /// The smallest batch with a registered Ligerito config: m = k_log +
    /// n_log = 14 + 8 = 22, the production shape.
    const N_TEST: usize = 256;

    fn msgs_of(seed: u64, n: usize) -> Vec<[u8; MESSAGE_BYTES]> {
        let mut s = seed | 1;
        (0..n)
            .map(|_| {
                std::array::from_fn(|_| {
                    s ^= s << 13;
                    s ^= s >> 7;
                    s ^= s << 17;
                    (s & 0xFF) as u8
                })
            })
            .collect()
    }

    /// End to end: prove knowledge of preimages of real BLAKE3 digests, and
    /// verify against the digests alone.
    #[test]
    fn preimage_roundtrip() {
        let n = N_TEST;
        let setup = Blake3PreimageSetup::new(n);
        let msgs = msgs_of(0xC0FFEE, n);
        let digests = Blake3PreimageSetup::digests_of(&msgs);
        // The digests really are BLAKE3 of the messages.
        for (m, d) in msgs.iter().zip(&digests) {
            assert_eq!(::blake3::hash(m).as_bytes(), d);
        }

        let mut ch = FsChallenger::new(b"b3-preimage");
        let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");
        let mut chv = FsChallenger::new(b"b3-preimage");
        setup
            .verify(&comm, &proof, &digests, &mut chv)
            .expect("honest preimage proof must verify");
    }

    /// A proof is bound to its digest list: flipping one bit of one public
    /// digest must make verification fail.
    #[test]
    fn wrong_digest_rejected() {
        let n = N_TEST;
        let setup = Blake3PreimageSetup::new(n);
        let msgs = msgs_of(0xBEEF, n);
        let digests = Blake3PreimageSetup::digests_of(&msgs);
        let mut ch = FsChallenger::new(b"b3-preimage");
        let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");

        let mut tampered = digests.clone();
        tampered[2][7] ^= 1;
        let mut chv = FsChallenger::new(b"b3-preimage");
        assert!(
            setup.verify(&comm, &proof, &tampered, &mut chv).is_err(),
            "a proof must not verify against a different digest list"
        );
    }

    /// Reordering the public digests is a different statement.
    #[test]
    fn reordered_digests_rejected() {
        let n = N_TEST;
        let setup = Blake3PreimageSetup::new(n);
        let msgs = msgs_of(0xFEED, n);
        let digests = Blake3PreimageSetup::digests_of(&msgs);
        let mut ch = FsChallenger::new(b"b3-preimage");
        let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");

        let mut swapped = digests.clone();
        swapped.swap(0, 3);
        let mut chv = FsChallenger::new(b"b3-preimage");
        assert!(
            setup.verify(&comm, &proof, &swapped, &mut chv).is_err(),
            "a proof must not verify against a permuted digest list"
        );
    }

    /// The prover refuses a witness that does not hash to the statement,
    /// rather than emitting a proof that cannot verify.
    #[test]
    fn wrong_preimage_refused_by_prover() {
        let n = N_TEST;
        let setup = Blake3PreimageSetup::new(n);
        let msgs = msgs_of(0x1234, n);
        let mut digests = Blake3PreimageSetup::digests_of(&msgs);
        digests[1][0] ^= 0xFF;
        let mut ch = FsChallenger::new(b"b3-preimage");
        match setup.prove(&msgs, &digests, &mut ch) {
            Err(PreimageError::DigestMismatch { index }) => assert_eq!(index, 1),
            Err(e) => panic!("wrong error: {e}"),
            Ok(_) => panic!("prover accepted a witness that does not hash to the statement"),
        }
    }

    /// A prover who knows preimages of OTHER digests cannot pass off its
    /// proof as one for this statement — the transcript binds the list.
    #[test]
    fn proof_for_other_digests_does_not_transfer() {
        let n = N_TEST;
        let setup = Blake3PreimageSetup::new(n);
        let mine = msgs_of(0xAAAA, n);
        let theirs = msgs_of(0xBBBB, n);
        let my_digests = Blake3PreimageSetup::digests_of(&mine);
        let their_digests = Blake3PreimageSetup::digests_of(&theirs);

        let mut ch = FsChallenger::new(b"b3-preimage");
        let (proof, comm) = setup
            .prove(&theirs, &their_digests, &mut ch)
            .expect("prove");
        let mut chv = FsChallenger::new(b"b3-preimage");
        assert!(
            setup.verify(&comm, &proof, &my_digests, &mut chv).is_err(),
            "a proof of other preimages must not verify against my digests"
        );
    }
}

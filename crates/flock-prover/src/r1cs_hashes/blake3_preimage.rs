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
//! [`Blake3PreimageSetup`] is the non-zk prover. [`Blake3PreimageZkSetup`]
//! uses the certified field-mask protocol and is gated to the exact production
//! shape. Its simulator accepts only a sealed public statement, and the
//! unmodified verifier checks the resulting proof through the same framed
//! random oracle. The precise computational-ZK and knowledge-security scopes
//! are recorded in `docs/paper/zk-flock.tex`.

use flock_core::challenger::Challenger;
use flock_core::pcs::{Commitment, PcsParams};
use flock_core::proof::R1csProofLigerito;
use flock_core::r1cs::BlockR1cs;

use crate::digest_bind::{
    DigestChallenges, DigestLayout, DigestStatement, PaddingDigest, digest_claim,
    digest_claim_point, digest_claim_value,
};
#[cfg(feature = "zk")]
use crate::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk_pinned;
use crate::r1cs_hashes::blake3::{
    BLAKE3_IV, Compression, FLAGS_ROOT_HASH, K_LOG, ParamPinning, ROOT_HASH_BLOCK_LEN,
    build_block_r1cs_pinned, build_block_r1cs_zk_pinned,
    generate_witness_with_ab_packed_and_lincheck_pinned, min_n_blocks_log,
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
    /// The caller selected a zk shape that is not in the fail-closed
    /// certificate registry.
    Uncertified,
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
            Self::Uncertified => write!(f, "fixed-digest zk configuration is not certified"),
        }
    }
}

impl std::error::Error for PreimageError {}

#[cfg(feature = "veil")]
#[derive(Debug, PartialEq, Eq)]
pub enum SuccinctPreimageError {
    Statement(PreimageError),
    Protocol(crate::succinct_veil::SuccinctVeilError),
}

#[cfg(feature = "veil")]
pub struct SimulatedSuccinctPreimage {
    pub proof: crate::succinct_veil::SuccinctVeilProof,
    pub commitment: Commitment,
    pub programmed_points: usize,
}

#[cfg(feature = "veil")]
impl From<PreimageError> for SuccinctPreimageError {
    fn from(value: PreimageError) -> Self {
        Self::Statement(value)
    }
}

#[cfg(feature = "veil")]
impl From<crate::succinct_veil::SuccinctVeilError> for SuccinctPreimageError {
    fn from(value: crate::succinct_veil::SuccinctVeilError) -> Self {
        Self::Protocol(value)
    }
}

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
            // Small direct-preimage batches fall below the registered m=22
            // profile floor. Keep at least seven message-column bits so the
            // ad-hoc UDR query schedule remains feasible.
            log_batch_size: 6.min((r1cs.m - flock_core::pcs::LOG_PACKING) - 7),
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
        let lig_config = self.ligerito_prover_config(log_n);

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
        let lig_v = self.ligerito_verifier_config(log_n);

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

    fn ligerito_prover_config(&self, log_n: usize) -> flock_core::pcs::ligerito::ProverConfig {
        match flock_core::pcs::ligerito::prover_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        ) {
            Ok(config) => config,
            Err(_) if self.pcs_params.m < 22 => {
                // Explicitly limited to the below-registry benchmark/test
                // range. Missing production-sized profiles still fail closed.
                #[allow(deprecated)]
                flock_core::pcs::ligerito::default_config(
                    log_n,
                    self.pcs_params.log_batch_size,
                    self.pcs_params.profile.log_inv_rate(),
                )
                .expect("small-batch ad-hoc Ligerito prover config")
            }
            Err(error) => panic!("Ligerito prover config: {error}"),
        }
    }

    fn ligerito_verifier_config(&self, log_n: usize) -> flock_core::pcs::ligerito::VerifierConfig {
        match flock_core::pcs::ligerito::verifier_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        ) {
            Ok(config) => config,
            Err(_) if self.pcs_params.m < 22 =>
            {
                #[allow(deprecated)]
                flock_core::pcs::ligerito::default_verifier_config(
                    log_n,
                    self.pcs_params.log_batch_size,
                    self.pcs_params.profile.log_inv_rate(),
                )
                .expect("small-batch ad-hoc Ligerito verifier config")
            }
            Err(error) => panic!("Ligerito verifier config: {error}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Zero-knowledge mode
// ---------------------------------------------------------------------------

/// The zk-mode fixed-digest setup: the same relation, proved through the
/// amended (masked) A1′ pipeline with a hiding commitment.
///
/// The proving path is fail-closed: it runs only for a circuit digest and PCS
/// shape registered as [`crate::zk_certificate::StatementFamily::Blake3Preimage`].
/// Its computational-ZK claim is separate from the standalone knowledge
/// label; see the paper for the exact bounds and assumptions.
#[derive(Clone, Debug)]
pub struct Blake3PreimageZkSetup {
    pub n_blocks: usize,
    pub r1cs: BlockR1cs,
    pub pcs_params: PcsParams,
}

impl Blake3PreimageZkSetup {
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        let n_log = min_n_blocks_log(n_blocks);
        Self::with_outer_log(n_blocks, n_log)
    }

    /// Succinct VEIL setup padded to the hiding-Ligerito production floor.
    /// This lets applications prove a short list while the public statement
    /// deterministically fills the remaining slots with the fixed padding
    /// digest.
    #[cfg(feature = "veil")]
    pub fn new_succinct(n_blocks: usize) -> Self {
        assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
        Self::with_outer_log(n_blocks, min_n_blocks_log(n_blocks).max(8))
    }

    fn with_outer_log(n_blocks: usize, n_log: usize) -> Self {
        let r1cs = build_block_r1cs_zk_pinned(n_log, ParamPinning::RootHash64);
        r1cs.csc_lincheck_circuit();
        flock_core::scratch::prewarm_prover(r1cs.m);
        let pcs_params = PcsParams {
            m: r1cs.m,
            log_inv_rate: 1,
            log_batch_size: 6,
            profile: flock_core::pcs::ligerito::LigeritoProfile::Fast,
            zk: true,
        };
        Self {
            n_blocks,
            r1cs,
            pcs_params,
        }
    }

    pub fn n_blocks_log(&self) -> usize {
        self.r1cs.n_log()
    }

    pub fn n_block_slots(&self) -> usize {
        1usize << self.n_blocks_log()
    }

    #[cfg(feature = "veil")]
    fn succinct_ligerito_prover_config(&self) -> flock_core::pcs::ligerito::ProverConfig {
        let log_n = self.pcs_params.log_msg_len();
        match flock_core::pcs::ligerito::prover_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        ) {
            Ok(config) => config,
            Err(_) if self.pcs_params.m < 22 =>
            {
                #[allow(deprecated)]
                flock_core::pcs::ligerito::default_config(
                    log_n,
                    self.pcs_params.log_batch_size,
                    self.pcs_params.profile.log_inv_rate(),
                )
                .expect("small-batch succinct-VEIL Ligerito prover config")
            }
            Err(error) => panic!("Ligerito prover config: {error}"),
        }
    }

    #[cfg(feature = "veil")]
    fn succinct_ligerito_verifier_config(&self) -> flock_core::pcs::ligerito::VerifierConfig {
        let log_n = self.pcs_params.log_msg_len();
        match flock_core::pcs::ligerito::verifier_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        ) {
            Ok(config) => config,
            Err(_) if self.pcs_params.m < 22 =>
            {
                #[allow(deprecated)]
                flock_core::pcs::ligerito::default_verifier_config(
                    log_n,
                    self.pcs_params.log_batch_size,
                    self.pcs_params.profile.log_inv_rate(),
                )
                .expect("small-batch succinct-VEIL Ligerito verifier config")
            }
            Err(error) => panic!("Ligerito verifier config: {error}"),
        }
    }

    /// The public statement for a digest list (same rule as the non-zk path).
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

    /// Experimental succinct VEIL mode. Unlike the older A1 reference path,
    /// this makes one hiding witness opening and proves only FLOCK's small
    /// algebraic verifier transcript inside VEIL.
    #[cfg(feature = "veil")]
    pub fn prove_succinct<Ch: Challenger + Clone>(
        &self,
        msgs: &[[u8; MESSAGE_BYTES]],
        digests: &[[u8; DIGEST_BYTES]],
        rng: &mut flock_core::zk::ZkRng,
        challenger: &mut Ch,
    ) -> Result<(crate::succinct_veil::SuccinctVeilProof, Commitment), SuccinctPreimageError> {
        use flock_core::zk::MaskSampler;

        if digests.len() != self.n_blocks || msgs.len() != self.n_blocks {
            return Err(PreimageError::BatchSizeMismatch {
                expected: self.n_blocks,
                got: digests.len().max(msgs.len()),
            }
            .into());
        }
        for (index, (message, digest)) in msgs.iter().zip(digests).enumerate() {
            if ::blake3::hash(message).as_bytes() != digest {
                return Err(PreimageError::DigestMismatch { index }.into());
            }
        }
        let statement = self.statement(digests);
        statement.validate();
        let layout = self
            .r1cs
            .zk
            .expect("succinct setup carries randomizer rows");
        let mut witness_rng = rng.fork(b"succinct-preimage-witness-randomizers");
        let mut random_words =
            vec![
                0u64;
                self.n_block_slots() * crate::r1cs_hashes::common::zk_rand_words_per_block(&layout)
            ];
        witness_rng.fill_u64s(&mut random_words);
        let blocks = msgs.iter().map(message_compression).collect::<Vec<_>>();
        let (z, a, b, z_lincheck) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
            &blocks,
            self.n_blocks_log(),
            &layout,
            &random_words,
            ParamPinning::RootHash64,
        );
        let lig_config = self.succinct_ligerito_prover_config();
        absorb_statement(challenger, &statement);
        let statement_for_claim = statement.clone();
        Ok(crate::succinct_veil::prove_succinct_veil_r1cs(
            &self.r1cs,
            &self.pcs_params,
            z,
            a,
            b,
            z_lincheck,
            self.r1cs.csc_lincheck_circuit(),
            &lig_config,
            rng,
            &mut |ch: &mut Ch| {
                let digest_challenges = DigestChallenges::sample(&statement_for_claim, ch);
                vec![digest_claim(
                    &statement_for_claim,
                    self.r1cs.layout,
                    &digest_challenges,
                )]
            },
            None,
            challenger,
        )?)
    }

    #[cfg(feature = "veil")]
    pub fn verify_succinct<Ch: Challenger + Clone>(
        &self,
        commitment: &Commitment,
        proof: &crate::succinct_veil::SuccinctVeilProof,
        digests: &[[u8; DIGEST_BYTES]],
        challenger: &mut Ch,
    ) -> Result<(), SuccinctPreimageError> {
        if digests.len() != self.n_blocks {
            return Err(PreimageError::BatchSizeMismatch {
                expected: self.n_blocks,
                got: digests.len(),
            }
            .into());
        }
        let statement = self.statement(digests);
        statement.validate();
        let lig_config = self.succinct_ligerito_verifier_config();
        absorb_statement(challenger, &statement);
        let layout = self.r1cs.layout;
        crate::succinct_veil::verify_succinct_veil_r1cs(
            &self.r1cs,
            &self.pcs_params,
            proof,
            commitment,
            self.r1cs.csc_lincheck_circuit(),
            &lig_config,
            &mut |ch: &mut Ch| {
                let digest_challenges = DigestChallenges::sample(&statement, ch);
                vec![(
                    digest_claim_point(&statement, layout, &digest_challenges),
                    digest_claim_value(&statement, &digest_challenges),
                )]
            },
            challenger,
        )?;
        Ok(())
    }

    /// Programmable-ROM simulator for the succinct composition. The API has
    /// no preimage parameter: it builds an unrelated pseudo-witness, patches
    /// only its public digest cells, and simulates the zerocheck that would
    /// otherwise reject that vector. Lincheck, the hiding PCS opening, and
    /// the VEIL shifted-verifier proof all run through their production code.
    #[cfg(feature = "veil")]
    pub fn simulate_succinct(
        &self,
        digests: &[[u8; DIGEST_BYTES]],
        seed: [u8; 32],
        oracle: crate::sim_oracle::SharedOracle,
        domain: &[u8],
    ) -> Result<SimulatedSuccinctPreimage, SuccinctPreimageError> {
        use flock_core::zk::MaskSampler;

        if digests.len() != self.n_blocks {
            return Err(PreimageError::BatchSizeMismatch {
                expected: self.n_blocks,
                got: digests.len(),
            }
            .into());
        }
        let statement = self.statement(digests);
        statement.validate();
        let mut rng = flock_core::zk::ZkRng::from_seed(seed);
        let mut message_rng = rng.fork(b"succinct-simulator-pseudo-messages");
        let mut message_words = vec![0u64; self.n_blocks * MESSAGE_BYTES / 8];
        message_rng.fill_u64s(&mut message_words);
        let own_messages = message_words
            .chunks_exact(MESSAGE_BYTES / 8)
            .map(|words| {
                let mut message = [0u8; MESSAGE_BYTES];
                for (chunk, word) in message.chunks_exact_mut(8).zip(words) {
                    chunk.copy_from_slice(&word.to_le_bytes());
                }
                message
            })
            .collect::<Vec<_>>();
        let blocks = own_messages
            .iter()
            .map(message_compression)
            .collect::<Vec<_>>();
        let layout = self
            .r1cs
            .zk
            .expect("succinct simulator needs randomizer rows");
        let mut randomizer_rng = rng.fork(b"succinct-simulator-randomizer-rows");
        let mut randomizer_words =
            vec![
                0u64;
                self.n_block_slots() * crate::r1cs_hashes::common::zk_rand_words_per_block(&layout)
            ];
        randomizer_rng.fill_u64s(&mut randomizer_words);
        let (mut z, _, _, _) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
            &blocks,
            self.n_blocks_log(),
            &layout,
            &randomizer_words,
            ParamPinning::RootHash64,
        );

        // The BLAKE3 layout stores the two packed digest halves in aligned
        // words 2 and 3 of every witness block (the same public region used by
        // `digest_claim`).
        let words_per_block = (1usize << self.r1cs.k_log) / 128;
        for (instance, digest) in digests.iter().enumerate() {
            for half in 0..2usize {
                let mut packed = flock_core::field::F128::ZERO;
                for bit_in_half in 0..128usize {
                    let bit = half * 128 + bit_in_half;
                    if (digest[bit / 8] >> (bit % 8)) & 1 == 1 {
                        if bit_in_half < 64 {
                            packed.lo |= 1u64 << bit_in_half;
                        } else {
                            packed.hi |= 1u64 << (bit_in_half - 64);
                        }
                    }
                }
                z[instance * words_per_block + 2 + half] = packed;
            }
        }
        let a = self.r1cs.apply_a_packed(&z);
        let b = self.r1cs.apply_b_packed(&z);
        let z_lincheck =
            flock_core::lincheck::pack_z_lincheck_from_packed(&z, self.r1cs.m, self.r1cs.k_log);
        let lig_config = self.succinct_ligerito_prover_config();
        let mut challenger = crate::sim_oracle::OracleChallenger::new(domain, oracle.clone());
        absorb_statement(&mut challenger, &statement);
        let source_seed = *::blake3::keyed_hash(&seed, b"succinct-veil-zc-simulator").as_bytes();
        let mut source = crate::succinct_veil::RomZerocheckSimulator::new(self.r1cs.m, source_seed);
        let statement_for_claim = statement.clone();
        let (proof, commitment) = crate::succinct_veil::prove_succinct_veil_r1cs(
            &self.r1cs,
            &self.pcs_params,
            z,
            a,
            b,
            z_lincheck,
            self.r1cs.csc_lincheck_circuit(),
            &lig_config,
            &mut rng,
            &mut |ch: &mut crate::sim_oracle::OracleChallenger| {
                let digest_challenges = DigestChallenges::sample(&statement_for_claim, ch);
                vec![digest_claim(
                    &statement_for_claim,
                    self.r1cs.layout,
                    &digest_challenges,
                )]
            },
            Some(&mut source),
            &mut challenger,
        )?;
        let programmed_points = oracle.lock().expect("oracle poisoned").programmed_len();
        Ok(SimulatedSuccinctPreimage {
            proof,
            commitment,
            programmed_points,
        })
    }

    /// Prove, with masking, that the committed messages hash to `digests`.
    #[cfg(feature = "zk")]
    pub fn prove<Ch: Challenger + Clone>(
        &self,
        msgs: &[[u8; MESSAGE_BYTES]],
        digests: &[[u8; DIGEST_BYTES]],
        rng: &mut flock_core::zk::ZkRng,
        challenger: &mut Ch,
    ) -> Result<(crate::prover::R1csProofZkA1, Commitment), PreimageError> {
        use flock_core::zk::MaskSampler;

        crate::zk_certificate::require_certified(
            crate::zk_certificate::StatementFamily::Blake3Preimage,
            self.n_blocks,
            &self.r1cs,
            &self.pcs_params,
        )
        .map_err(|_| PreimageError::Uncertified)?;

        if digests.len() != self.n_blocks || msgs.len() != self.n_blocks {
            return Err(PreimageError::BatchSizeMismatch {
                expected: self.n_blocks,
                got: digests.len().max(msgs.len()),
            });
        }
        for (i, (m, d)) in msgs.iter().zip(digests).enumerate() {
            if ::blake3::hash(m).as_bytes() != d {
                return Err(PreimageError::DigestMismatch { index: i });
            }
        }
        let stmt = self.statement(digests);
        stmt.validate();
        let layout = self.r1cs.zk.expect("zk setup carries a layout");

        let mut wit_rng = rng.fork(b"preimage-witness-rand");
        let mut mask_rng = rng.fork(b"preimage-masks");
        let n_total = self.n_block_slots();
        let mut rand_words =
            vec![0u64; n_total * crate::r1cs_hashes::common::zk_rand_words_per_block(&layout)];
        wit_rng.fill_u64s(&mut rand_words);

        let blocks: Vec<Compression> = msgs.iter().map(message_compression).collect();
        let (z_packed, a_packed, b_packed, z_lincheck) =
            generate_witness_with_ab_packed_and_lincheck_zk_pinned(
                &blocks,
                self.n_blocks_log(),
                &layout,
                &rand_words,
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

        absorb_statement(challenger, &stmt);

        let mut forks = crate::prover::A1MaskForks::from_rng(&mut mask_rng);
        let proof_nonce = forks.proof_nonce;
        let layout_kind = self.r1cs.layout;
        let stmt_for_claim = stmt.clone();
        let (proof, comm, _) = crate::prover::prove_r1cs_zk_a1_with_masks_pd_nonce(
            &self.r1cs,
            &self.pcs_params,
            z_packed,
            a_packed,
            b_packed,
            z_lincheck,
            lc_circuit,
            &lig_config,
            forks.sources(),
            &mut |ch: &mut Ch| {
                let dch = DigestChallenges::sample(&stmt_for_claim, ch);
                vec![digest_claim(&stmt_for_claim, layout_kind, &dch)]
            },
            None,
            None,
            proof_nonce,
            challenger,
        );
        Ok((proof, comm))
    }

    /// Verify a masked preimage proof against the public digests.
    #[cfg(feature = "zk")]
    pub fn verify<Ch: Challenger + Clone>(
        &self,
        commitment: &Commitment,
        proof: &crate::prover::R1csProofZkA1,
        digests: &[[u8; DIGEST_BYTES]],
        challenger: &mut Ch,
    ) -> Result<(), flock_core::verifier::VerifyError> {
        let ro = flock_core::ro::RoContext::native(proof.proof_nonce);
        self.verify_with_ro(commitment, proof, digests, &ro, challenger)
    }

    /// Verify with an explicit point-oracle backend. The ROM simulator uses
    /// this to give the unmodified verification logic the same oracle object
    /// as its challenger and Merkle commitments.
    #[cfg(feature = "zk")]
    pub fn verify_with_ro<Ch: Challenger + Clone>(
        &self,
        commitment: &Commitment,
        proof: &crate::prover::R1csProofZkA1,
        digests: &[[u8; DIGEST_BYTES]],
        ro: &flock_core::ro::RoContext,
        challenger: &mut Ch,
    ) -> Result<(), flock_core::verifier::VerifyError> {
        let stmt = self.statement(digests);
        stmt.validate();
        absorb_statement(challenger, &stmt);
        let layout_kind = self.r1cs.layout;
        crate::prover::verify_r1cs_zk_a1_pd_ro(
            &self.r1cs,
            &self.pcs_params,
            proof,
            commitment,
            self.r1cs.csc_lincheck_circuit(),
            ro,
            &mut |ch: &mut Ch| {
                let dch = DigestChallenges::sample(&stmt, ch);
                vec![(
                    digest_claim_point(&stmt, layout_kind, &dch),
                    digest_claim_value(&stmt, &dch),
                )]
            },
            challenger,
        )
    }
}

/// Absorb the public digest statement into the transcript.
///
/// This must happen before any challenge is drawn: it is what makes every
/// subsequent challenge — and therefore the whole proof — specific to this
/// digest list, in this order, with this padding rule. Without it a proof
/// could be replayed against a permuted or truncated list.
pub(crate) fn absorb_statement<Ch: Challenger>(challenger: &mut Ch, stmt: &DigestStatement) {
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

    #[cfg(feature = "veil")]
    #[test]
    fn succinct_veil_preimage_roundtrip_and_mutations() {
        // The hiding Ligerito layer's registered production geometry starts
        // at m=22, i.e. 256 BLAKE3 blocks.
        let n = N_TEST;
        let setup = Blake3PreimageZkSetup::new(n);
        let messages = msgs_of(0x51_CC_1C_7, n);
        let digests = Blake3PreimageSetup::digests_of(&messages);
        let mut rng = flock_core::zk::ZkRng::from_seed([0x51; 32]);
        let mut prover_challenger = FsChallenger::new(b"succinct-veil-preimage-test");
        let (proof, commitment) = setup
            .prove_succinct(&messages, &digests, &mut rng, &mut prover_challenger)
            .expect("prove succinct VEIL");

        let mut verifier_challenger = FsChallenger::new(b"succinct-veil-preimage-test");
        setup
            .verify_succinct(&commitment, &proof, &digests, &mut verifier_challenger)
            .expect("verify succinct VEIL");

        let rejects = |candidate: &crate::succinct_veil::SuccinctVeilProof,
                       candidate_commitment: &Commitment,
                       candidate_digests: &[[u8; DIGEST_BYTES]]| {
            let mut challenger = FsChallenger::new(b"succinct-veil-preimage-test");
            assert!(
                setup
                    .verify_succinct(
                        candidate_commitment,
                        candidate,
                        candidate_digests,
                        &mut challenger,
                    )
                    .is_err()
            );
        };

        let mut changed_message = proof.clone();
        changed_message.masked_zerocheck.round1_ab[0] += flock_core::field::F128::ONE;
        rejects(&changed_message, &commitment, &digests);

        let mut changed_lincheck = proof.clone();
        changed_lincheck.masked_lincheck.z_partial[0] += flock_core::field::F128::ONE;
        rejects(&changed_lincheck, &commitment, &digests);

        let mut changed_claim = proof.clone();
        changed_claim.ab_value += flock_core::field::F128::ONE;
        rejects(&changed_claim, &commitment, &digests);

        let mut changed_veil = proof.clone();
        changed_veil.veil.linear.rlc_vector[0] += flock_core::field::F128::ONE;
        rejects(&changed_veil, &commitment, &digests);

        let mut changed_hadamard = proof.clone();
        changed_hadamard
            .veil
            .hadamard
            .as_mut()
            .expect("padding always creates Hadamard rows")
            .phi[0] += flock_core::field::F128::ONE;
        rejects(&changed_hadamard, &commitment, &digests);

        let mut changed_pcs = proof.clone();
        changed_pcs.pcs_open.ligerito.initial_proof.opened_rows[0][0] +=
            flock_core::field::F128::ONE;
        rejects(&changed_pcs, &commitment, &digests);

        let mut changed_nonce = proof.clone();
        changed_nonce.proof_nonce[0] ^= 1;
        rejects(&changed_nonce, &commitment, &digests);

        let mut changed_commitment = commitment.clone();
        changed_commitment.root[0] ^= 1;
        rejects(&proof, &changed_commitment, &digests);

        let mut wrong_digests = digests.clone();
        wrong_digests[0][0] ^= 1;
        rejects(&proof, &commitment, &wrong_digests);
    }

    #[cfg(feature = "veil")]
    #[test]
    fn succinct_output_claims_move_with_fresh_randomizers() {
        let setup = Blake3PreimageZkSetup::new_succinct(2);
        let messages = msgs_of(0x5A17, 2);
        let digests = Blake3PreimageSetup::digests_of(&messages);
        let prove = |seed: u8| {
            let mut rng = flock_core::zk::ZkRng::from_seed([seed; 32]);
            let mut challenger = FsChallenger::new(b"succinct-veil-claim-mask-test");
            setup
                .prove_succinct(&messages, &digests, &mut rng, &mut challenger)
                .expect("prove")
                .0
        };
        let first = prove(0x31);
        let second = prove(0x32);
        assert_ne!(first.ab_value, second.ab_value);
        assert_ne!(first.c_value, second.c_value);
    }

    #[cfg(feature = "veil")]
    #[test]
    fn succinct_veil_public_only_simulator_is_accepted() {
        const DOMAIN: &[u8] = b"succinct-veil-public-only-simulator-test";
        let setup = Blake3PreimageZkSetup::new_succinct(2);
        // Arbitrary public targets; the simulator API receives no messages
        // and makes no attempt to invert them.
        let digests = vec![[0x42; DIGEST_BYTES], [0xA7; DIGEST_BYTES]];
        let oracle = crate::sim_oracle::shared_oracle();
        let simulated = setup
            .simulate_succinct(&digests, [0x93; 32], oracle.clone(), DOMAIN)
            .expect("simulate without a preimage");
        assert_eq!(
            simulated.programmed_points,
            1 + setup.r1cs.m - flock_core::zerocheck::K_SKIP
        );

        let mut verifier = crate::sim_oracle::OracleChallenger::new(DOMAIN, oracle.clone());
        setup
            .verify_succinct(
                &simulated.commitment,
                &simulated.proof,
                &digests,
                &mut verifier,
            )
            .expect("the production verifier accepts the simulated proof");
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

    #[test]
    fn small_preimage_roundtrip_uses_explicit_ad_hoc_config() {
        let setup = Blake3PreimageSetup::new(1);
        assert_eq!(setup.pcs_params.log_batch_size, 3);
        let msgs = msgs_of(0x51_4d_41_4c_4c, 1);
        let digests = Blake3PreimageSetup::digests_of(&msgs);
        let mut prover = FsChallenger::new(b"b3-preimage-small");
        let (proof, commitment) = setup.prove(&msgs, &digests, &mut prover).unwrap();
        let mut verifier = FsChallenger::new(b"b3-preimage-small");
        setup
            .verify(&commitment, &proof, &digests, &mut verifier)
            .unwrap();
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

    /// The masked (zk-mode) path proves and verifies the same statement.
    #[test]
    fn zk_preimage_roundtrip() {
        let setup = Blake3PreimageZkSetup::new(N_TEST);
        let msgs = msgs_of(0x2222_3333, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&msgs);
        let mut rng = flock_core::zk::ZkRng::from_seed([7u8; 32]);
        let mut ch = FsChallenger::new(b"b3-preimage-zk");
        let (proof, comm) = setup
            .prove(&msgs, &digests, &mut rng, &mut ch)
            .expect("zk prove");
        let mut chv = FsChallenger::new(b"b3-preimage-zk");
        setup
            .verify(&comm, &proof, &digests, &mut chv)
            .expect("honest masked preimage proof must verify");
    }

    /// Masking is live on the zk path: two proofs of the SAME statement and
    /// witness under different mask draws differ in their commitment and in
    /// witness-dependent transcript values. (This is a freshness check, not a
    /// zero-knowledge claim — see the type's docs.)
    #[test]
    fn zk_preimage_masks_are_fresh() {
        let setup = Blake3PreimageZkSetup::new(N_TEST);
        let msgs = msgs_of(0x4444_5555, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&msgs);

        let go = |seed: u8| {
            let mut rng = flock_core::zk::ZkRng::from_seed([seed; 32]);
            let mut ch = FsChallenger::new(b"b3-preimage-zk");
            setup
                .prove(&msgs, &digests, &mut rng, &mut ch)
                .expect("prove")
        };
        let (p1, c1) = go(1);
        let (p2, c2) = go(2);
        assert_ne!(c1.root, c2.root, "fresh masks must move the commitment");
        assert_ne!(
            p1.zerocheck.final_a_eval, p2.zerocheck.final_a_eval,
            "fresh masks must move the witness-dependent evaluations"
        );
        // Both still verify against the same public digests.
        for (p, c) in [(&p1, &c1), (&p2, &c2)] {
            let mut chv = FsChallenger::new(b"b3-preimage-zk");
            setup.verify(c, p, &digests, &mut chv).expect("verify");
        }
    }

    /// The zk path is bound to its digest list too.
    #[test]
    fn zk_wrong_digest_rejected() {
        let setup = Blake3PreimageZkSetup::new(N_TEST);
        let msgs = msgs_of(0x6666_7777, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&msgs);
        let mut rng = flock_core::zk::ZkRng::from_seed([9u8; 32]);
        let mut ch = FsChallenger::new(b"b3-preimage-zk");
        let (proof, comm) = setup
            .prove(&msgs, &digests, &mut rng, &mut ch)
            .expect("prove");
        let mut tampered = digests.clone();
        tampered[0][31] ^= 0x80;
        let mut chv = FsChallenger::new(b"b3-preimage-zk");
        assert!(
            setup.verify(&comm, &proof, &tampered, &mut chv).is_err(),
            "masked proof must not verify against a different digest list"
        );
    }

    /// **The harness-faithfulness control.** A real proof, produced and
    /// verified through the programmable-oracle challenger with NOTHING
    /// programmed, must behave exactly as under plain Fiat–Shamir. Without
    /// this, any later "the simulator's output verifies" result would be
    /// meaningless — it could hold because the harness is a different
    /// protocol rather than because the simulation works.
    #[test]
    fn oracle_harness_accepts_a_real_proof_unprogrammed() {
        use crate::sim_oracle::{OracleChallenger, shared_oracle};

        let setup = Blake3PreimageSetup::new(N_TEST);
        let msgs = msgs_of(0x0AC1E_5EED, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&msgs);

        let oracle = shared_oracle();
        let mut ch = OracleChallenger::new(b"b3-preimage", oracle.clone());
        let (proof, comm) = setup.prove(&msgs, &digests, &mut ch).expect("prove");
        assert!(
            oracle.lock().unwrap().is_empty(),
            "the control must run with an unprogrammed oracle"
        );

        let mut chv = OracleChallenger::new(b"b3-preimage", oracle.clone());
        setup
            .verify(&comm, &proof, &digests, &mut chv)
            .expect("a real proof must verify through the oracle harness");

        // And the same proof verifies under plain Fiat–Shamir, so the harness
        // is not merely self-consistent.
        let mut chf = FsChallenger::new(b"b3-preimage");
        setup
            .verify(&comm, &proof, &digests, &mut chf)
            .expect("the same proof must verify under plain Fiat-Shamir");

        // The oracle recorded a query transcript — the object a straightline
        // extractor reads.
        assert!(oracle.lock().unwrap().query_count() > 0);
    }

    /// **The zero-knowledge result: a proof with no preimage behind it.**
    ///
    /// The simulator receives only the public digests. It never sees — and
    /// never computes — a message hashing to any of them; the vector it
    /// commits is an honest trace for messages of its own choosing whose
    /// output region has been overwritten with the public digests, which is
    /// not a satisfying assignment at all. The unmodified verifier accepts.
    #[test]
    fn simulator_produces_an_accepting_proof_without_any_preimage() {
        use crate::preimage_simulator::simulate;
        use crate::sim_oracle::{OracleChallenger, shared_oracle};
        use crate::sim_seal::{SealedStatement, SimCoins};

        let setup = Blake3PreimageZkSetup::new(N_TEST);
        // The statement: digests of messages the simulator will never see.
        let secret = msgs_of(0x5EC1_5EC1, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&secret);
        let sealed = SealedStatement::new(&setup, &digests).expect("public statement");
        let oracle = shared_oracle();
        let sim = simulate(&sealed, SimCoins::new(0xC0FFEE), &oracle, b"b3-preimage-zk")
            .expect("simulation must succeed");

        println!("simulator programmed {} oracle points", sim.programmed);

        let mut chv = OracleChallenger::new(b"b3-preimage-zk", oracle.clone());
        let ro = crate::sim_oracle::ro_context(sim.proof.proof_nonce, oracle.clone());
        setup
            .verify_with_ro(&sim.commitment, &sim.proof, &digests, &ro, &mut chv)
            .expect("the UNMODIFIED verifier must accept the simulated proof");
    }

    /// Record every production-shape oracle call made by the simulator and
    /// verifier. The artifact pins deterministic non-grinding counts; the
    /// security ledger replaces the observed geometric PoW attempts with an
    /// analytical 128-bit-tail budget.
    #[test]
    fn production_random_oracle_ledger_matches_artifact() {
        use crate::preimage_simulator::simulate;
        use crate::sim_game::{
            OracleQueryCounts, SimGameLedger, production_grinding_candidate_bound,
        };
        use crate::sim_oracle::{OracleChallenger, shared_oracle};
        use crate::sim_seal::{SealedStatement, SimCoins};

        let setup = Blake3PreimageZkSetup::new(N_TEST);
        let secret = msgs_of(0xA11C_E5E5, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&secret);
        let sealed = SealedStatement::new(&setup, &digests).expect("public statement");
        let oracle = shared_oracle();
        let sim = simulate(
            &sealed,
            SimCoins::new(0x51A7_E001),
            &oracle,
            b"b3-preimage-zk",
        )
        .expect("simulate");
        assert_eq!(sim.programmed, 18);

        let prover_points = oracle.lock().unwrap().queries().to_vec();
        let prover = OracleQueryCounts::classify(&prover_points);
        let mut chv = OracleChallenger::new(b"b3-preimage-zk", oracle.clone());
        let ro = crate::sim_oracle::ro_context(sim.proof.proof_nonce, oracle.clone());
        setup
            .verify_with_ro(&sim.commitment, &sim.proof, &digests, &ro, &mut chv)
            .expect("simulated proof verifies");
        let all_points = oracle.lock().unwrap().queries().to_vec();
        let verifier = OracleQueryCounts::classify(&all_points[prover_points.len()..]);
        assert_eq!(
            verifier.pow_candidates,
            crate::sim_game::PRODUCTION_PCS_OPENINGS
                * crate::sim_game::PRODUCTION_GRIND_BITS_PER_OPENING.len() as u64,
            "recorded verifier grind sites must match the production schedule",
        );

        println!("prover oracle counts: {prover:?}");
        println!("verifier oracle counts: {verifier:?}");
        let pow_bound = production_grinding_candidate_bound(128);
        let protocol_bound = prover.non_pow_calls() + pow_bound + verifier.total_calls;
        println!("pow candidate bound: {pow_bound}");
        println!("protocol query bound: {protocol_bound}");
        println!(
            "final zk bits: {:.15}",
            SimGameLedger::production(64, protocol_bound).final_bits()
        );

        let artifact: serde_json::Value = serde_json::from_str(include_str!(
            "../../../../docs/artifacts/sim_game_error_table.json"
        ))
        .expect("game artifact");
        let pinned = &artifact["random_oracle_ledger"];
        assert_eq!(pinned["prover_total_calls"], prover.total_calls);
        assert_eq!(pinned["prover_non_pow_calls"], prover.non_pow_calls());
        assert_eq!(pinned["verifier_total_calls"], verifier.total_calls);
        assert_eq!(pinned["grinding_candidate_bound"], pow_bound);
        assert_eq!(pinned["protocol_query_bound"], protocol_bound);
    }

    /// **Control 1: the vector the simulator commits is not a witness.**
    /// Overwriting the output region destroys the compression relation, so
    /// the patched vector fails the R1CS — which is the whole reason the
    /// zerocheck had to be simulated rather than run.
    #[test]
    fn the_simulators_committed_vector_is_not_a_valid_witness() {
        use crate::r1cs_hashes::blake3::{ParamPinning, build_block_r1cs_pinned, generate_witness};

        let n_log = 3usize;
        let r1cs = build_block_r1cs_pinned(n_log, ParamPinning::RootHash64);
        let own = msgs_of(0x1111, 1);
        let target = Blake3PreimageSetup::digests_of(&msgs_of(0x2222, 1));

        let mut all: Vec<Compression> = own.iter().map(message_compression).collect();
        all.resize(
            1usize << n_log,
            ParamPinning::RootHash64.padding_compression(),
        );
        let mut z = generate_witness(&all, n_log);
        assert!(r1cs.satisfies(&z), "the unpatched trace is a valid witness");

        // Patch out_lo of block 0 to the target digest.
        for w in 0..8usize {
            let word = u32::from_le_bytes(target[0][w * 4..w * 4 + 4].try_into().unwrap());
            for b in 0..32usize {
                z[256 + w * 32 + b] = (word >> b) & 1 == 1;
            }
        }
        assert!(
            !r1cs.satisfies(&z),
            "patching the output region must break the R1CS — otherwise the \
             simulator would not need to fabricate the zerocheck at all"
        );
    }

    /// **Control 2: an honest prover cannot produce this proof.** Running the
    /// real prover on the same patched vector — i.e. without simulating the
    /// zerocheck — is rejected. So the simulator's acceptance comes from the
    /// simulation, not from the patched vector being secretly acceptable.
    #[test]
    fn honest_prover_on_the_patched_vector_is_rejected() {
        use crate::r1cs_hashes::blake3::{
            ParamPinning, generate_witness_with_ab_packed_and_lincheck_zk_pinned,
        };
        use crate::sim_oracle::{OracleChallenger, shared_oracle};
        use flock_core::zk::MaskSampler;

        let setup = Blake3PreimageZkSetup::new(N_TEST);
        let secret = msgs_of(0x7777, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&secret);
        let stmt = setup.statement(&digests);
        let own = msgs_of(0x8888, N_TEST);

        let layout = setup.r1cs.zk.expect("zk layout");
        let mut zrng = flock_core::zk::ZkRng::from_seed([5u8; 32]);
        let mut rand_words = vec![
            0u64;
            setup.n_block_slots()
                * crate::r1cs_hashes::common::zk_rand_words_per_block(&layout)
        ];
        zrng.fill_u64s(&mut rand_words);
        let blocks: Vec<Compression> = own.iter().map(message_compression).collect();
        let (mut z, _a, _b, _l) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
            &blocks,
            setup.n_blocks_log(),
            &layout,
            &rand_words,
            ParamPinning::RootHash64,
        );
        // Same patch the simulator applies.
        let words_per_block = (1usize << 14) / 128;
        for (i, d) in digests.iter().enumerate() {
            for half in 0..2usize {
                let mut w = flock_core::field::F128::ZERO;
                for b in 0..128usize {
                    let bit = half * 128 + b;
                    if (d[bit / 8] >> (bit % 8)) & 1 == 1 {
                        if b < 64 {
                            w.lo |= 1u64 << b;
                        } else {
                            w.hi |= 1u64 << (b - 64);
                        }
                    }
                }
                z[i * words_per_block + 2 + half] = w;
            }
        }
        let a = setup.r1cs.apply_a_packed(&z);
        let b = setup.r1cs.apply_b_packed(&z);
        let stripe =
            flock_core::lincheck::pack_z_lincheck_from_packed(&z, setup.r1cs.m, setup.r1cs.k_log);

        let lig = flock_core::pcs::ligerito::prover_config_for(
            setup.pcs_params.log_msg_len(),
            setup.pcs_params.log_batch_size,
            setup.pcs_params.profile,
        )
        .unwrap();
        let oracle = shared_oracle();
        let mut ch = OracleChallenger::new(b"b3-preimage-zk", oracle.clone());
        crate::r1cs_hashes::blake3_preimage::absorb_statement(&mut ch, &stmt);
        let mut mrng = flock_core::zk::ZkRng::from_seed([6u8; 32]);
        let mut forks = crate::prover::A1MaskForks::from_rng(&mut mrng);
        let proof_nonce = forks.proof_nonce;
        let layout_kind = setup.r1cs.layout;
        let stmt2 = stmt.clone();
        let (proof, comm, _) = crate::prover::prove_r1cs_zk_a1_with_masks_pd_nonce(
            &setup.r1cs,
            &setup.pcs_params,
            z,
            a,
            b,
            stripe,
            setup.r1cs.csc_lincheck_circuit(),
            &lig,
            forks.sources(),
            &mut |c: &mut OracleChallenger| {
                let dch = crate::digest_bind::DigestChallenges::sample(&stmt2, c);
                vec![crate::digest_bind::digest_claim(&stmt2, layout_kind, &dch)]
            },
            None, // honest zerocheck — no simulation
            None,
            proof_nonce,
            &mut ch,
        );
        let mut chv = OracleChallenger::new(b"b3-preimage-zk", oracle);
        assert!(
            setup.verify(&comm, &proof, &digests, &mut chv).is_err(),
            "an HONEST prover on the patched vector must be rejected; if this \
             passed, the digest binding would not be enforcing anything"
        );
    }

    /// **Measurement: how far is the simulated transcript from an honest one?**
    ///
    /// Acceptance is necessary, not sufficient — a simulator whose output
    /// verifies but is distributed differently is still a broken simulator.
    /// This compares, coordinate by coordinate, a simulated proof against an
    /// honest one for the same statement, and reports which classes differ
    /// *structurally* (always, in a way a distinguisher could test) rather
    /// than merely by value (as fresh randomness would).
    ///
    /// It is a diagnostic, not a proof: it can find a discrepancy but cannot
    /// certify the absence of one. What it currently shows is recorded in
    /// `docs/memos/interactive-simulator-design.md`.
    #[test]
    #[ignore = "diagnostic; run explicitly"]
    fn measure_simulated_vs_honest_transcript() {
        use crate::preimage_simulator::simulate;
        use crate::sim_oracle::shared_oracle;
        use crate::sim_seal::{SealedStatement, SimCoins};
        use crate::transcript_schema::{algebraic_vector, flatten_a1};

        let setup = Blake3PreimageZkSetup::new(N_TEST);
        let secret = msgs_of(0xD1F_0001, N_TEST);
        let digests = Blake3PreimageSetup::digests_of(&secret);

        // Honest proof of the same statement (the party that knows the
        // preimages).
        let mut hrng = flock_core::zk::ZkRng::from_seed([21u8; 32]);
        let mut hch = FsChallenger::new(b"b3-preimage-zk");
        let (hproof, hcomm) = setup
            .prove(&secret, &digests, &mut hrng, &mut hch)
            .expect("honest prove");

        // Simulated proof of the same public statement.
        let sealed = SealedStatement::new(&setup, &digests).expect("public statement");
        let oracle = shared_oracle();
        let sim =
            simulate(&sealed, SimCoins::new(0xD1FF), &oracle, b"b3-preimage-zk").expect("simulate");

        let hv = algebraic_vector(&flatten_a1(&hcomm, &hproof));
        let sv = algebraic_vector(&flatten_a1(&sim.commitment, &sim.proof));
        assert_eq!(
            hv.len(),
            sv.len(),
            "simulated and honest transcripts must have the SAME SHAPE — a \
             length difference is a distinguisher on its own"
        );
        let differing = hv.iter().zip(&sv).filter(|(a, b)| a != b).count();
        println!(
            "transcript coordinates: {} total, {} differ by value \
             (fresh randomness makes near-total difference expected)",
            hv.len(),
            differing
        );
        // Same shape is the checkable invariant here; per-class distribution
        // equality needs the coverage certificates, not this diagnostic.
        assert!(
            differing > hv.len() / 2,
            "an almost-identical transcript would mean the simulator is \
             reproducing witness-dependent values, not masking them"
        );
    }
}

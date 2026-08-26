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
//! the witness. Longer messages need chunk/tree chaining and are future work;
//! the statement encoding records the length policy so a proof for this
//! relation can never be read as a proof for another.
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
//! [`Blake3PreimageSetup`] is the non-ZK prover.
//! [`Blake3PreimageZkSetup::prove_succinct`] uses a hiding commitment, masks
//! the PIOP transcript, and proves the shifted verifier with `veil-f128`. Its
//! security proof is incomplete; see `docs/SECURITY.md`.

use flock_core::challenger::Challenger;
use flock_core::pcs::{Commitment, PcsParams};
use flock_core::proof::R1csProofLigerito;
use flock_core::r1cs::BlockR1cs;
use flock_core::ro::RoContext;

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
#[cfg(feature = "zk")]
use flock_core::zk::MaskSampler;

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
    pub fn prove_succinct<Ch: Challenger + Clone + Send>(
        &self,
        msgs: &[[u8; MESSAGE_BYTES]],
        digests: &[[u8; DIGEST_BYTES]],
        rng: &mut flock_core::zk::ZkRng,
        challenger: &mut Ch,
    ) -> Result<(crate::succinct_veil::SuccinctVeilProof, Commitment), SuccinctPreimageError> {
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
            .as_chunks::<{ MESSAGE_BYTES / 8 }>()
            .0
            .iter()
            .map(|words| {
                let mut message = [0u8; MESSAGE_BYTES];
                for (chunk, word) in message.as_chunks_mut::<8>().0.iter_mut().zip(words) {
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
        let programmed_points = oracle
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .programmed_len();
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
        let ro = RoContext::native(proof.proof_nonce);
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
        ro: &RoContext,
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

// The whole module exercises zk-gated provers/simulators (veil-only tests
// carry their own additional gate).
#[cfg(all(test, feature = "zk"))]
mod tests;

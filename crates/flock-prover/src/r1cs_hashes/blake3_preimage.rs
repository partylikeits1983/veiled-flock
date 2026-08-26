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
//! [`Blake3PreimageZkSetup::prove`] uses a hiding commitment, masks
//! the PIOP transcript, and proves the shifted verifier with `veil-f128`.
//! The exact classical-pROM theorem and exclusions are in `docs/SECURITY.md`.

use flock_core::challenger::Challenger;
#[cfg(feature = "veil")]
use flock_core::challenger::FsChallenger;
use flock_core::pcs::{Commitment, PcsParams};
use flock_core::proof::R1csProofLigerito;
use flock_core::r1cs::BlockR1cs;

use crate::digest_bind::{
    DigestChallenges, DigestLayout, DigestStatement, PaddingDigest, digest_claim,
    digest_claim_point, digest_claim_value,
};

/// Pinned SHA-256 Fiat--Shamir domain for the sole public full-ZK protocol.
pub const VEIL_FLOCK_FS_DOMAIN: &[u8] = b"veil-flock-blake3-preimage";
#[cfg(feature = "zk")]
use crate::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk_pinned;
use crate::r1cs_hashes::blake3::{
    BLAKE3_IV, Compression, FLAGS_ROOT_HASH, K_LOG, ParamPinning, ROOT_HASH_BLOCK_LEN,
    build_block_r1cs_pinned, build_block_r1cs_zk_pinned,
    generate_witness_with_ab_packed_and_lincheck_pinned, min_n_blocks_log,
};
#[cfg(feature = "veil")]
use flock_core::zk::MaskSampler;

/// Bytes of message covered by one instance of this relation.
pub const MESSAGE_BYTES: usize = 64;
/// Bytes of digest produced per instance.
pub const DIGEST_BYTES: usize = 32;
/// Largest batch covered by the registered full-ZK circuit and PCS
/// certificates. Smaller batches are padded to the next power-of-two shape,
/// with a 256-slot production floor.
pub const MAX_ZK_PREIMAGE_BLOCKS: usize = 2048;

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
    pub programming_audit: crate::sim_oracle::ProgrammingAudit,
    pub protocol_oracle_queries: u64,
    pub pow_oracle_queries: u64,
}

/// Additive soundness ledger before Fiat--Shamir: FLOCK PIOP, the live VEIL
/// Hadamard/linear compiler, and the one recursive Ligerito opening.
#[cfg(feature = "veil")]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SuccinctInteractiveSoundnessBound {
    pub flock_piop_probability: f64,
    pub veil_constraint_probability: f64,
    pub ligerito_pcs_probability: f64,
}

#[cfg(feature = "veil")]
impl SuccinctInteractiveSoundnessBound {
    pub fn probability(self) -> f64 {
        self.flock_piop_probability
            + self.veil_constraint_probability
            + self.ligerito_pcs_probability
    }

    pub fn bits(self) -> f64 {
        -self.probability().log2()
    }
}

/// Classical-ROM soundness bound for a bounded adversary. Each completed
/// proof attempt exposes a fresh public-coin transcript; union-bound the
/// interactive error over those attempts, then charge collisions across the
/// adversary and verifier's domain-separated oracle calls. This is not a QROM
/// theorem and does not assert that concrete SHA-256 is a random oracle.
#[cfg(feature = "veil")]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SuccinctRomSoundnessBound {
    pub interactive: SuccinctInteractiveSoundnessBound,
    pub adversary_query_log2: u32,
    pub completed_proof_attempts: u64,
    pub max_protocol_oracle_queries_per_attempt: u64,
}

#[cfg(feature = "veil")]
impl SuccinctRomSoundnessBound {
    pub fn fiat_shamir_probability(self) -> f64 {
        self.completed_proof_attempts as f64 * self.interactive.probability()
    }

    pub fn oracle_collision_probability(self) -> f64 {
        let adversary_queries = 2f64.powi(self.adversary_query_log2 as i32);
        let total = adversary_queries
            + self.completed_proof_attempts as f64
                * self.max_protocol_oracle_queries_per_attempt as f64;
        total * (total - 1.0) * 0.5 * 2f64.powi(-256)
    }

    pub fn probability(self) -> f64 {
        self.fiat_shamir_probability() + self.oracle_collision_probability()
    }

    pub fn bits(self) -> f64 {
        -self.probability().log2()
    }
}

#[cfg(feature = "veil")]
impl SimulatedSuccinctPreimage {
    pub fn classical_prom_bound(
        &self,
        adversary_query_log2: u32,
        proofs: u64,
    ) -> crate::sim_game::ClassicalPromZkBound {
        crate::sim_game::ClassicalPromZkBound {
            adversary_query_log2,
            max_oracle_queries_per_proof: crate::sim_game::MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF,
            programmed_points: self.programmed_points as u64,
            proofs,
        }
    }
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
            // The full-view ZK instantiation uses the unique-decoding
            // profile. Fast/Slim rely on a separate Johnson/list-decoding
            // analysis that is not part of this protocol's theorem stack.
            profile: flock_core::pcs::ligerito::LigeritoProfile::Secure,
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

/// Full-ZK fixed-digest setup for the VEIL-FLOCK composition.
///
/// Construction validates the exact circuit digest, mask geometry, code
/// parameters, query budget, and soundness profiles before proving.
#[derive(Clone, Debug)]
pub struct Blake3PreimageZkSetup {
    pub n_blocks: usize,
    pub r1cs: BlockR1cs,
    pub pcs_params: PcsParams,
}

impl Blake3PreimageZkSetup {
    /// VEIL setup padded to the hiding-Ligerito production floor.
    /// This lets applications prove a short list while the public statement
    /// deterministically fills the remaining slots with the fixed padding
    /// digest.
    #[cfg(feature = "veil")]
    pub fn new(n_blocks: usize) -> Self {
        assert!(
            (1..=MAX_ZK_PREIMAGE_BLOCKS).contains(&n_blocks),
            "n_blocks must be in 1..={MAX_ZK_PREIMAGE_BLOCKS}"
        );
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
            profile: flock_core::pcs::ligerito::LigeritoProfile::Secure,
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
    fn ligerito_prover_config(&self) -> flock_core::pcs::ligerito::ProverConfig {
        let log_n = self.pcs_params.log_msg_len();
        flock_core::pcs::ligerito::prover_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        )
        .unwrap_or_else(|error| panic!("registered Secure Ligerito prover config: {error}"))
    }

    #[cfg(feature = "veil")]
    fn ligerito_verifier_config(&self) -> flock_core::pcs::ligerito::VerifierConfig {
        let log_n = self.pcs_params.log_msg_len();
        flock_core::pcs::ligerito::verifier_config_for(
            log_n,
            self.pcs_params.log_batch_size,
            self.pcs_params.profile,
        )
        .unwrap_or_else(|error| panic!("registered Secure Ligerito verifier config: {error}"))
    }

    /// Additive whole-opening soundness of the registered Secure Ligerito
    /// PCS component. This is one term in the final protocol ledger.
    #[cfg(feature = "veil")]
    pub fn ligerito_aggregate_soundness_bits(&self) -> f64 {
        -self.ligerito_aggregate_soundness_probability().log2()
    }

    #[cfg(feature = "veil")]
    fn ligerito_aggregate_soundness_probability(&self) -> f64 {
        let effective_m = self.pcs_params.log_msg_len() + flock_core::pcs::LOG_PACKING;
        let source = flock_core::pcs::ligerito::embedded_security_config(
            effective_m,
            self.pcs_params.profile,
        )
        .expect("full-ZK setup requires a registered Secure Ligerito configuration");
        let config = flock_core::pcs::ligerito::LigeritoSecurityConfig::from_toml_str(source)
            .expect("registered Secure Ligerito configuration must validate");
        config
            .aggregate_soundness_bound()
            .expect("registered Secure Ligerito aggregate bound")
            .probability()
    }

    /// Fail-closed additive soundness certificate for the exact interactive
    /// protocol instantiated by this setup.
    #[cfg(feature = "veil")]
    pub fn interactive_soundness_bound(
        &self,
    ) -> Result<SuccinctInteractiveSoundnessBound, SuccinctPreimageError> {
        let lincheck = self.r1cs.csc_lincheck_circuit();
        let piop = crate::succinct_veil::certify_flock_piop_soundness(&self.r1cs, lincheck)?;
        let veil = crate::succinct_veil::certify_shifted_veil_soundness(&self.r1cs)?;
        Ok(SuccinctInteractiveSoundnessBound {
            flock_piop_probability: piop.probability(),
            veil_constraint_probability: veil.probability(),
            ligerito_pcs_probability: self.ligerito_aggregate_soundness_probability(),
        })
    }

    /// Classical-ROM soundness for a declared oracle budget and number of
    /// completed proof attempts. The attempt count must fit the oracle-query
    /// budget; callers cannot obtain a stronger bound by understating it.
    #[cfg(feature = "veil")]
    pub fn rom_soundness_bound(
        &self,
        adversary_query_log2: u32,
        completed_proof_attempts: u64,
    ) -> Result<SuccinctRomSoundnessBound, SuccinctPreimageError> {
        if adversary_query_log2 >= 128
            || completed_proof_attempts == 0
            || completed_proof_attempts as f64 > 2f64.powi(adversary_query_log2 as i32)
        {
            return Err(crate::succinct_veil::SuccinctVeilError::InvalidParameters.into());
        }
        Ok(SuccinctRomSoundnessBound {
            interactive: self.interactive_soundness_bound()?,
            adversary_query_log2,
            completed_proof_attempts,
            max_protocol_oracle_queries_per_attempt:
                crate::sim_game::MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF,
        })
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

    #[cfg(feature = "veil")]
    fn absorb_protocol<Ch: Challenger>(&self, challenger: &mut Ch) {
        challenger.observe_label(b"veil-flock-protocol");
        challenger.observe_bytes(&crate::proof_io::VEIL_FLOCK_PROTOCOL_ID);
        challenger.observe_bytes(&crate::proof_io::VEIL_FLOCK_RELATION_ID);
        challenger.observe_bytes(&crate::proof_io::VEIL_FLOCK_PARAMETER_SUITE_ID);
    }

    /// Prove the fixed-digest relation with the succinct VEIL composition and
    /// the pinned production SHA-256 Fiat--Shamir challenger.
    #[cfg(feature = "veil")]
    pub fn prove(
        &self,
        msgs: &[[u8; MESSAGE_BYTES]],
        digests: &[[u8; DIGEST_BYTES]],
    ) -> Result<(crate::succinct_veil::SuccinctVeilProof, Commitment), SuccinctPreimageError> {
        let mut rng = flock_core::zk::ZkRng::from_entropy();
        let mut challenger = FsChallenger::new(VEIL_FLOCK_FS_DOMAIN);
        self.prove_with_challenger(msgs, digests, &mut rng, &mut challenger)
    }

    #[cfg(feature = "veil")]
    fn prove_with_challenger<Ch: Challenger + Clone + Send>(
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
        let lig_config = self.ligerito_prover_config();
        self.absorb_protocol(challenger);
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
                vec![
                    crate::succinct_veil::PublicPackedDirectClaim::from_public_statement(
                        digest_claim(&statement_for_claim, self.r1cs.layout, &digest_challenges),
                    ),
                ]
            },
            None,
            challenger,
        )?)
    }

    /// Verify with the pinned production SHA-256 Fiat--Shamir challenger.
    #[cfg(feature = "veil")]
    pub fn verify(
        &self,
        commitment: &Commitment,
        proof: &crate::succinct_veil::SuccinctVeilProof,
        digests: &[[u8; DIGEST_BYTES]],
    ) -> Result<(), SuccinctPreimageError> {
        let mut challenger = FsChallenger::new(VEIL_FLOCK_FS_DOMAIN);
        self.verify_with_challenger(commitment, proof, digests, &mut challenger)
    }

    #[cfg(feature = "veil")]
    fn verify_with_challenger<Ch: Challenger + Clone>(
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
        let lig_config = self.ligerito_verifier_config();
        self.absorb_protocol(challenger);
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
                vec![
                    crate::succinct_veil::PublicPackedDirectClaimValue::from_public_statement(
                        digest_claim_point(&statement, layout, &digest_challenges),
                        digest_claim_value(&statement, &digest_challenges),
                    ),
                ]
            },
            challenger,
        )?;
        Ok(())
    }

    /// Programmable-ROM simulator for the succinct composition. The API has
    /// no preimage parameter: it builds a public-fiber representative, patches
    /// only its public digest cells, and simulates the zerocheck that would
    /// otherwise reject that vector. The representative is used only for
    /// linear processing covered by the joint masking theorem. The resulting
    /// shifted VEIL circuit is genuinely satisfied by simulator-owned masks,
    /// so the ordinary ZK VEIL prover is invoked only on a valid assignment.
    #[cfg(feature = "veil")]
    pub fn simulate(
        &self,
        digests: &[[u8; DIGEST_BYTES]],
        oracle: crate::sim_oracle::SharedOracle,
    ) -> Result<SimulatedSuccinctPreimage, SuccinctPreimageError> {
        let mut rng = flock_core::zk::ZkRng::from_entropy();
        self.simulate_with_rng(digests, oracle, &mut rng)
    }

    #[cfg(all(feature = "veil", test))]
    fn simulate_with_seed(
        &self,
        digests: &[[u8; DIGEST_BYTES]],
        seed: [u8; 32],
        oracle: crate::sim_oracle::SharedOracle,
    ) -> Result<SimulatedSuccinctPreimage, SuccinctPreimageError> {
        let mut rng = flock_core::zk::ZkRng::from_seed(seed);
        self.simulate_with_rng(digests, oracle, &mut rng)
    }

    #[cfg(feature = "veil")]
    fn simulate_with_rng(
        &self,
        digests: &[[u8; DIGEST_BYTES]],
        oracle: crate::sim_oracle::SharedOracle,
        rng: &mut flock_core::zk::ZkRng,
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
        let mut message_rng = rng.fork(b"veil-flock-simulator-public-fiber-messages");
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
        let lig_config = self.ligerito_prover_config();
        let mut challenger =
            crate::sim_oracle::OracleChallenger::new(VEIL_FLOCK_FS_DOMAIN, oracle.clone());
        self.absorb_protocol(&mut challenger);
        absorb_statement(&mut challenger, &statement);
        let source_rng = rng.fork(b"succinct-veil-zc-simulator");
        let mut source = crate::succinct_veil::RomZerocheckSimulator::new(self.r1cs.m, source_rng);
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
            rng,
            &mut |ch: &mut crate::sim_oracle::OracleChallenger| {
                let digest_challenges = DigestChallenges::sample(&statement_for_claim, ch);
                vec![
                    crate::succinct_veil::PublicPackedDirectClaim::from_public_statement(
                        digest_claim(&statement_for_claim, self.r1cs.layout, &digest_challenges),
                    ),
                ]
            },
            Some(&mut source),
            &mut challenger,
        )?;
        let expected_programmed = 1 + self.r1cs.m - flock_core::zerocheck::K_SKIP;
        let oracle_guard = oracle.lock().unwrap_or_else(|error| error.into_inner());
        let programming_audit =
            oracle_guard.audit_programming(&proof.proof_nonce, expected_programmed);
        let protocol_oracle_queries = oracle_guard.total_answer_count();
        let pow_oracle_queries = oracle_guard.pow_answer_count();
        drop(oracle_guard);
        if !programming_audit.is_valid()
            || protocol_oracle_queries > crate::sim_game::MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF
        {
            return Err(crate::succinct_veil::SuccinctVeilError::ProgrammingCollision.into());
        }
        Ok(SimulatedSuccinctPreimage {
            proof,
            commitment,
            programmed_points: programming_audit.programmed_points,
            programming_audit,
            protocol_oracle_queries,
            pow_oracle_queries,
        })
    }
}

/// Absorb the public digest statement into the transcript.
///
/// This must happen before any challenge is drawn: it is what makes every
/// subsequent challenge — and therefore the whole proof — specific to this
/// digest list, in this order, with this padding rule. Without it a proof
/// could be replayed against a permuted or truncated list.
pub(crate) fn absorb_statement<Ch: Challenger>(challenger: &mut Ch, stmt: &DigestStatement) {
    challenger.observe_label(b"flock-blake3-preimage");
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
        assert_eq!(
            setup.pcs_params.profile,
            flock_core::pcs::ligerito::LigeritoProfile::Secure
        );
        assert!(setup.ligerito_aggregate_soundness_bits() > 114.0);
        let interactive = setup.interactive_soundness_bound().unwrap();
        assert!(interactive.bits() > 106.0);
        assert!(interactive.bits() < 110.0);
        let rom = setup.rom_soundness_bound(64, 1).unwrap();
        assert!(rom.bits() > 106.0);
        let many_attempts = setup.rom_soundness_bound(64, 1u64 << 32).unwrap();
        assert!(many_attempts.bits() < rom.bits());
        let mut messages = msgs_of(0x51_CC_1C_7, n);
        // Detect accidental raw-witness serialization.
        messages[0] = [0xA5; MESSAGE_BYTES];
        let digests = Blake3PreimageSetup::digests_of(&messages);
        let (proof, commitment) = setup
            .prove(&messages, &digests)
            .expect("prove succinct VEIL");

        let bundle = crate::proof_io::VeilFlockProofBundle::new(
            digests.clone(),
            commitment.clone(),
            proof.clone(),
        );
        let encoded = bundle.to_bytes().expect("serialize canonical bundle");
        assert!(
            encoded.len() <= crate::proof_io::MAX_VEIL_FLOCK_BUNDLE_BYTES as usize,
            "succinct proof unexpectedly grew to {} bytes",
            encoded.len()
        );
        assert!(
            encoded
                .windows(MESSAGE_BYTES)
                .all(|window| window != &messages[0][..]),
            "serialized proof contains the raw preimage marker"
        );

        let decoded = crate::proof_io::VeilFlockProofBundle::from_bytes(&encoded)
            .expect("canonical bundle roundtrip");
        assert_eq!(decoded, bundle);
        setup
            .verify(&decoded.commitment, &decoded.proof, &decoded.digests)
            .expect("verify decoded bundle");
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert!(crate::proof_io::VeilFlockProofBundle::from_bytes(&trailing).is_err());
        let mut wrong_id = bundle.clone();
        wrong_id.protocol_id[0] ^= 1;
        assert!(wrong_id.to_bytes().is_err());

        setup
            .verify(&commitment, &proof, &digests)
            .expect("verify succinct VEIL");

        let rejects = |proof_under_test: &crate::succinct_veil::SuccinctVeilProof,
                       commitment_under_test: &Commitment,
                       digests_under_test: &[[u8; DIGEST_BYTES]]| {
            assert!(
                setup
                    .verify(commitment_under_test, proof_under_test, digests_under_test)
                    .is_err()
            );
        };

        let mut changed_message = proof.clone();
        changed_message.masked_zerocheck.round1_ab[0] += flock_core::field::F128::ONE;
        rejects(&changed_message, &commitment, &digests);

        let mut changed_lincheck = proof.clone();
        changed_lincheck.masked_lincheck.z_partial[0] += flock_core::field::F128::ONE;
        rejects(&changed_lincheck, &commitment, &digests);

        let mut changed_ring_claim = proof.clone();
        changed_ring_claim.masked_ring_claims[0].witness[0] += flock_core::field::F128::ONE;
        rejects(&changed_ring_claim, &commitment, &digests);

        let mut changed_ring_blind = proof.clone();
        changed_ring_blind.masked_ring_claims[1].blind[0] += flock_core::field::F128::ONE;
        rejects(&changed_ring_blind, &commitment, &digests);

        let mut changed_direct_blind = proof.clone();
        changed_direct_blind.public_direct_blind_values[0] += flock_core::field::F128::ONE;
        rejects(&changed_direct_blind, &commitment, &digests);

        let mut oversized_blind_grind = proof.clone();
        oversized_blind_grind.blind_grind_nonce = crate::succinct_veil::MAX_BLIND_GRIND_TRIALS;
        rejects(&oversized_blind_grind, &commitment, &digests);

        assert_eq!(proof.pcs_open.ligerito.fold_grinding_nonces.len(), 1);
        let mut oversized_ligerito_grind = proof.clone();
        oversized_ligerito_grind
            .pcs_open
            .ligerito
            .fold_grinding_nonces[0] = crate::succinct_veil::MAX_LIGERITO_GRIND_TRIALS;
        rejects(&oversized_ligerito_grind, &commitment, &digests);

        let mut changed_blinded_slice = proof.clone();
        changed_blinded_slice.pcs_open.ring_switches[0].s_hat_v[0] += flock_core::field::F128::ONE;
        rejects(&changed_blinded_slice, &commitment, &digests);

        let mut changed_pcs_mode = proof.clone();
        changed_pcs_mode.pcs_open.zk_blind = Some(flock_core::pcs::ZkBlindOpening {
            y_g: flock_core::field::F128::ZERO,
            c_grind_nonce: 0,
        });
        rejects(&changed_pcs_mode, &commitment, &digests);

        let mut changed_veil = proof.clone();
        changed_veil.veil.linear.rlc_vector[0] += flock_core::field::F128::ONE;
        rejects(&changed_veil, &commitment, &digests);

        let mut changed_hadamard = proof.clone();
        changed_hadamard.veil.hadamard.phi[0] += flock_core::field::F128::ONE;
        rejects(&changed_hadamard, &commitment, &digests);

        let mut changed_pcs = proof.clone();
        changed_pcs.pcs_open.ligerito.initial_proof.opened_rows[0][0] +=
            flock_core::field::F128::ONE;
        rejects(&changed_pcs, &commitment, &digests);

        let mut changed_pcs_salt = proof.clone();
        changed_pcs_salt.pcs_open.ligerito.initial_proof.leaf_salts[0][0] ^= 1;
        rejects(&changed_pcs_salt, &commitment, &digests);

        let mut changed_linear_salt = proof.clone();
        changed_linear_salt.veil.linear.opening.salts[0][0] ^= 1;
        rejects(&changed_linear_salt, &commitment, &digests);

        let mut changed_hadamard_salt = proof.clone();
        changed_hadamard_salt.veil.hadamard.opening.salts[0][0] ^= 1;
        rejects(&changed_hadamard_salt, &commitment, &digests);

        let mut changed_nonce = proof.clone();
        changed_nonce.proof_nonce[0] ^= 1;
        rejects(&changed_nonce, &commitment, &digests);

        let mut changed_outer_tree_nonce = proof.clone();
        changed_outer_tree_nonce.tree_nonces.outer[0] ^= 1;
        rejects(&changed_outer_tree_nonce, &commitment, &digests);

        let mut changed_linear_tree_nonce = proof.clone();
        changed_linear_tree_nonce.tree_nonces.veil_linear[0] ^= 1;
        rejects(&changed_linear_tree_nonce, &commitment, &digests);

        let mut changed_hadamard_tree_nonce = proof.clone();
        changed_hadamard_tree_nonce.tree_nonces.veil_hadamard[0] ^= 1;
        rejects(&changed_hadamard_tree_nonce, &commitment, &digests);

        let mut changed_commitment = commitment.clone();
        changed_commitment.root[0] ^= 1;
        rejects(&proof, &changed_commitment, &digests);

        let mut wrong_digests = digests.clone();
        wrong_digests[0][0] ^= 1;
        rejects(&proof, &commitment, &wrong_digests);
    }

    #[cfg(feature = "veil")]
    #[test]
    fn succinct_ring_messages_use_fresh_masks() {
        let setup = Blake3PreimageZkSetup::new(2);
        let messages = msgs_of(0x5A17, 2);
        let digests = Blake3PreimageSetup::digests_of(&messages);
        let prove = || setup.prove(&messages, &digests).expect("prove");
        let (first, first_commitment) = prove();
        let (second, second_commitment) = prove();
        assert_ne!(first.proof_nonce, second.proof_nonce);
        assert_ne!(first.tree_nonces.outer, second.tree_nonces.outer);
        assert_ne!(
            first.tree_nonces.veil_linear,
            second.tree_nonces.veil_linear
        );
        assert_ne!(
            first.tree_nonces.veil_hadamard,
            second.tree_nonces.veil_hadamard
        );
        assert_ne!(first.tree_nonces.outer, first.tree_nonces.veil_linear);
        assert_ne!(first.tree_nonces.outer, first.tree_nonces.veil_hadamard);
        assert_ne!(
            first.tree_nonces.veil_linear,
            first.tree_nonces.veil_hadamard
        );
        assert_ne!(first_commitment.root, second_commitment.root);
        assert_ne!(
            first.pcs_open.ligerito.initial_proof.leaf_salts,
            second.pcs_open.ligerito.initial_proof.leaf_salts
        );
        assert_ne!(first.veil.linear.commitment, second.veil.linear.commitment);
        assert_ne!(
            first.veil.linear.opening.salts,
            second.veil.linear.opening.salts
        );
        assert_ne!(
            first.veil.hadamard.commitment,
            second.veil.hadamard.commitment
        );
        assert_ne!(
            first.veil.hadamard.opening.salts,
            second.veil.hadamard.opening.salts
        );
        assert_ne!(
            first.masked_ring_claims[0].witness,
            second.masked_ring_claims[0].witness
        );
        assert_ne!(
            first.masked_ring_claims[1].witness,
            second.masked_ring_claims[1].witness
        );
    }

    #[cfg(feature = "veil")]
    #[test]
    fn succinct_veil_public_only_simulator_is_accepted() {
        let setup = Blake3PreimageZkSetup::new(2);
        // Arbitrary public targets; the simulator API receives no messages
        // and makes no attempt to invert them.
        let digests = vec![[0x42; DIGEST_BYTES], [0xA7; DIGEST_BYTES]];
        let oracle = crate::sim_oracle::shared_oracle();
        let simulated = setup
            .simulate(&digests, oracle.clone())
            .expect("simulate without a preimage");
        assert_eq!(
            simulated.programmed_points,
            1 + setup.r1cs.m - flock_core::zerocheck::K_SKIP
        );
        assert!(simulated.classical_prom_bound(64, 1).distinguishing_bits() > 126.0);
        assert!(simulated.programming_audit.is_valid());
        assert!(
            simulated.protocol_oracle_queries
                <= crate::sim_game::MAX_PROTOCOL_ORACLE_QUERIES_PER_PROOF
        );
        {
            let oracle = oracle.lock().unwrap_or_else(|error| error.into_inner());
            for channel in [
                flock_core::ro::RoChannel::Witness,
                flock_core::ro::RoChannel::VeilLinear,
                flock_core::ro::RoChannel::VeilHadamard,
            ] {
                assert!(
                    oracle.channel_query_count(channel) > 0,
                    "the shared oracle must receive {channel:?} hashes"
                );
            }
        }

        let mut verifier =
            crate::sim_oracle::OracleChallenger::new(VEIL_FLOCK_FS_DOMAIN, oracle.clone());
        setup
            .verify_with_challenger(
                &simulated.commitment,
                &simulated.proof,
                &digests,
                &mut verifier,
            )
            .expect("the generic verifier accepts the simulated proof");
    }

    #[cfg(feature = "veil")]
    #[test]
    fn succinct_simulator_aborts_on_a_prequeried_programming_point() {
        use flock_core::ro::ByteOracle;

        let setup = Blake3PreimageZkSetup::new(2);
        let digests = vec![[0x42; DIGEST_BYTES], [0xA7; DIGEST_BYTES]];
        let seed = [0x94; 32];

        let discovery_oracle = crate::sim_oracle::shared_oracle();
        setup
            .simulate_with_seed(&digests, seed, discovery_oracle.clone())
            .expect("deterministic discovery simulation");
        let programmed_point = discovery_oracle
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .programmed_points()
            .into_iter()
            .next()
            .expect("simulator programs at least one challenge point");

        let attacked_oracle = crate::sim_oracle::shared_oracle();
        let external = crate::sim_oracle::ProgrammableByteOracle::new(attacked_oracle.clone());
        let _ = external.answer(&programmed_point);
        assert!(matches!(
            setup.simulate_with_seed(&digests, seed, attacked_oracle),
            Err(SuccinctPreimageError::Protocol(
                crate::succinct_veil::SuccinctVeilError::ProgrammingCollision
            ))
        ));
    }

    /// Honest proof round trip.
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
}

//! Certificate gating for the zero-knowledge API: **fail closed**.
//!
//! The ZK claim is not a property of the code alone — it holds for the
//! explicitly enumerated statement shapes whose mask-coverage certificates
//! have actually been produced and checked. Everything else (other batch
//! sizes, other hashes, statements that bind public I/O such as the hash
//! chain, other PCS parameters or fold orders) is **out of scope**, and the
//! API rejects it rather than silently emitting a proof with no evidence
//! behind it.
//!
//! A [`ZkCertificate`] binds every input the certificate's validity depends
//! on: protocol version, circuit digest, zk layout digest, transcript schema
//! version, field representation, fold order, endianness, PCS parameters,
//! batch size, generator revision, plus the list of evidence tests that
//! produced it. [`require_certified`] is called by the gated prove entry
//! points; it returns an error (never a silent pass) when no certificate
//! matches.
//!
//! Adding a configuration is deliberately a code change with review: run the
//! certificate suite (`scripts/zk-certify.sh`) at the new shape, then add a
//! [`ZkCertificate`] entry recording its digests and evidence.

use flock_core::pcs::PcsParams;
use flock_core::r1cs::BlockR1cs;

/// Wire/protocol version of the reference construction. Bumped for A2 (the
/// lincheck mask channel): the wire format gained `comm_s`, `open_s`,
/// `sigma_lc` and `s_eval`, and the lincheck transcript changed meaning, so
/// an A1′-only certificate must not certify this protocol.
pub const PROTOCOL_VERSION: &str = "flock-zk-a1a2-v1";

/// Field representation the certificates were computed over.
pub const FIELD_REPR: &str = "gf2_128_ghash";

/// Fold order / univariate-skip convention the certificates assume.
pub const FOLD_ORDER: &str = "uniskip6-lsb-first-v0";

/// Byte/bit order of the packed witness the certificates assume.
pub const ENDIANNESS: &str = "le-lsb-first";

/// Which statement family a certificate covers. Only BLAKE3 *batch*
/// statements are in scope: they bind no caller-supplied message, chaining
/// value, or hash output, which is what makes the self-generated-witness
/// simulator valid. Chain / Merkle-path statements bind public endpoints and
/// are deliberately absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementFamily {
    Blake3Batch,
}

/// A checked certificate for one exact configuration.
#[derive(Clone, Debug)]
pub struct ZkCertificate {
    pub protocol_version: &'static str,
    pub family: StatementFamily,
    /// Number of BLAKE3 compressions in the batch.
    pub batch_size: usize,
    /// `r1cs.statement_digest()` — binds the matrices, shape, and zk layout.
    pub circuit_digest: [u8; 32],
    /// Transcript schema version the coordinate classification was made at.
    pub transcript_schema_version: u32,
    pub field_repr: &'static str,
    pub fold_order: &'static str,
    pub endianness: &'static str,
    pub pcs_m: usize,
    pub pcs_log_inv_rate: usize,
    pub pcs_log_batch_size: usize,
    /// Certificate-generator revision (bump when the probing methodology or
    /// the certified predicate changes).
    pub generator_rev: &'static str,
    /// Tests that constitute this certificate's evidence. Must match what
    /// `scripts/zk-certify.sh` runs (asserted by a test).
    pub evidence: &'static [&'static str],
}

/// Why a configuration was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkGateError {
    /// The statement family has no ZK support at all (SHA-256, Keccak, or a
    /// statement that binds public I/O such as the hash chain).
    UnsupportedStatement { what: &'static str },
    /// A BLAKE3 batch statement, but no certificate exists for this exact
    /// configuration (batch size / PCS parameters / circuit digest).
    Uncertified { batch_size: usize, m: usize },
    /// Every mask draw failed the per-proof coverage self-check. Emitting
    /// anyway would mean emitting a proof whose hiding is not established,
    /// so the prover fails closed instead.
    MaskCoverageExhausted { attempts: usize },
}

impl std::fmt::Display for ZkGateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedStatement { what } => write!(
                f,
                "zero-knowledge is not supported for {what}: the ZK claim covers \
                 BLAKE3 batch statements with no externally bound hash claims"
            ),
            Self::Uncertified { batch_size, m } => write!(
                f,
                "no zk certificate for this configuration (batch_size={batch_size}, m={m}); \
                 run scripts/zk-certify.sh at this shape and register a ZkCertificate"
            ),
            Self::MaskCoverageExhausted { attempts } => write!(
                f,
                "all {attempts} mask draws failed the coverage self-check; \
                 refusing to emit a proof whose hiding is not established"
            ),
        }
    }
}

impl std::error::Error for ZkGateError {}

/// Evidence set behind the currently certified configuration. Kept in sync
/// with `scripts/zk-certify.sh` by `zk_certificate_evidence_matches_script`.
const EVIDENCE_V1: &[&str] = &[
    "affine_classes_exactly_covered",
    "full_conditional_coverage_zk_zerocheck",
    "conditional_coverage_p_rho",
    "prove_verify_r1cs_zk_a1_roundtrip",
    "h1_inner_image_witness_independent_on_round_block",
    "p_channel_image_requires_nondegenerate_q",
    "joint_certificate_smoke",
    "joint_certificate_negative_controls",
    "simulator_translation_exact_transcript_equality",
    "joint_conditional_coverage_full_transcript",
    "mask_only_coordinates_are_witness_independent",
    "production_mask_channel_covers_round_block",
    "production_s_hat_v_randomizer_margin",
    "production_checked_prove_verifies",
    "blake3_witness_has_no_linear_difference_family",
    "l3_round1_region_alignment_holds",
];

/// The certified configurations. **One entry today**: the 256-block BLAKE3
/// batch reference fixture (m=22). Deliberately minimal — every entry is a
/// claim that the certificate suite was run and passed at that shape.
pub const CERTIFIED: &[ZkCertificate] = &[ZkCertificate {
    protocol_version: PROTOCOL_VERSION,
    family: StatementFamily::Blake3Batch,
    batch_size: 256,
    // Pinned by `zk_certificate_digest_matches_setup`; regenerate with that
    // test's printout after any change to the BLAKE3 zk statement.
    circuit_digest: [
        0x4a, 0x39, 0x8c, 0xa2, 0xe7, 0x3d, 0x9d, 0x1f, 0x70, 0x61, 0x1b, 0xd6, 0xa2, 0xa4, 0x08,
        0xb0, 0x40, 0x4a, 0xab, 0xdd, 0xcf, 0x6c, 0xf7, 0x5c, 0x29, 0xcf, 0xa4, 0x12, 0xf7, 0x2f,
        0x84, 0x23,
    ],
    transcript_schema_version: crate::transcript_schema::A1_SCHEMA_VERSION,
    field_repr: FIELD_REPR,
    fold_order: FOLD_ORDER,
    endianness: ENDIANNESS,
    pcs_m: 22,
    pcs_log_inv_rate: 1,
    pcs_log_batch_size: 6,
    generator_rev: "cert-gen-v1",
    evidence: EVIDENCE_V1,
}];

/// Look up the certificate for a configuration, ignoring the circuit digest
/// (shape match only).
fn find_shape(family: StatementFamily, batch_size: usize, params: &PcsParams) -> Option<&'static ZkCertificate> {
    CERTIFIED.iter().find(|c| {
        c.family == family
            && c.batch_size == batch_size
            && c.pcs_m == params.m
            && c.pcs_log_inv_rate == params.log_inv_rate
            && c.pcs_log_batch_size == params.log_batch_size
            && c.protocol_version == PROTOCOL_VERSION
            && c.transcript_schema_version == crate::transcript_schema::A1_SCHEMA_VERSION
            && c.field_repr == FIELD_REPR
            && c.fold_order == FOLD_ORDER
            && c.endianness == ENDIANNESS
    })
}

/// Gate the ZK prove path: `Ok` only when a certificate matches this exact
/// configuration **and** the statement's own digest matches the certified
/// circuit. Fail-closed by construction: an unknown shape has no entry.
pub fn require_certified(
    family: StatementFamily,
    batch_size: usize,
    r1cs: &BlockR1cs,
    params: &PcsParams,
) -> Result<&'static ZkCertificate, ZkGateError> {
    let cert = find_shape(family, batch_size, params)
        .ok_or(ZkGateError::Uncertified { batch_size, m: params.m })?;
    if r1cs.statement_digest() != cert.circuit_digest {
        return Err(ZkGateError::Uncertified { batch_size, m: params.m });
    }
    Ok(cert)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The registry's evidence list must be exactly what the certificate
    /// runner script executes — otherwise the gate would vouch for tests
    /// that never run (or miss ones that do).
    #[test]
    fn zk_certificate_evidence_matches_script() {
        let script = include_str!("../../../scripts/zk-certify.sh");
        for cert in CERTIFIED {
            for name in cert.evidence {
                assert!(
                    script.contains(name),
                    "certificate evidence `{name}` is not run by scripts/zk-certify.sh"
                );
            }
        }
    }

    /// Unsupported families and uncertified shapes are rejected, not
    /// silently proved. (Digest-matching is exercised by the BLAKE3-side
    /// test, which owns the real statement.)
    #[test]
    fn uncertified_shapes_are_rejected() {
        let params = PcsParams {
            m: 22,
            log_inv_rate: 1,
            log_batch_size: 6,
            profile: Default::default(),
            zk: true,
        };
        // A batch size with no certificate.
        assert!(find_shape(StatementFamily::Blake3Batch, 512, &params).is_none());
        // Certified batch size but different PCS parameters.
        let mut other = params.clone();
        other.log_inv_rate = 2;
        assert!(find_shape(StatementFamily::Blake3Batch, 256, &other).is_none());
        // The certified shape resolves.
        assert!(find_shape(StatementFamily::Blake3Batch, 256, &params).is_some());
    }
}

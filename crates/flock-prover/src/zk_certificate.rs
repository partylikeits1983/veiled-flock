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
//! on: protocol identifier, circuit digest, zk layout digest, field
//! representation, fold order, endianness, PCS parameters, batch size,
//! generator identifier, plus the list of evidence tests that
//! produced it. [`require_certified`] is called by the gated prove entry
//! points; it returns an error (never a silent pass) when no certificate
//! matches.
//!
//! Adding a configuration is deliberately a code change with review: run the
//! certificate suite (`scripts/zk-certify.sh`) at the new shape, then add a
//! [`ZkCertificate`] entry recording its digests and evidence.

use flock_core::pcs::PcsParams;
use flock_core::r1cs::BlockR1cs;

/// Stable protocol identifier bound by every certificate.
pub const PROTOCOL_ID: &str = "flock-zk-fv";

/// Field representation the certificates were computed over.
pub const FIELD_REPR: &str = "gf2_128_ghash";

/// Fold order / univariate-skip convention the certificates assume.
pub const FOLD_ORDER: &str = "uniskip6-lsb-first";

/// Byte/bit order of the packed witness the certificates assume.
pub const ENDIANNESS: &str = "le-lsb-first";

/// Which statement family a certificate covers. Batch and fixed-digest
/// BLAKE3 use different circuits and simulators, so they require distinct
/// entries. Chain and Merkle-path statements remain deliberately absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementFamily {
    Blake3Batch,
    Blake3Preimage,
}

/// A checked certificate for one exact configuration.
#[derive(Clone, Debug)]
pub struct ZkCertificate {
    pub protocol_id: &'static str,
    pub family: StatementFamily,
    /// Number of BLAKE3 compressions in the batch.
    pub batch_size: usize,
    /// `r1cs.statement_digest()` — binds the matrices, shape, and zk layout.
    pub circuit_digest: [u8; 32],
    pub field_repr: &'static str,
    pub fold_order: &'static str,
    pub endianness: &'static str,
    pub pcs_m: usize,
    pub pcs_log_inv_rate: usize,
    pub pcs_log_batch_size: usize,
    /// Identifier of the certificate generator and certified predicate.
    pub generator_id: &'static str,
    /// Tests that constitute this certificate's evidence. Must be exactly
    /// the set of tests `scripts/zk-certify.sh` runs — asserted in both
    /// directions by `zk_certificate_evidence_matches_script`, by exact name
    /// (the last `::` segment of each `run` invocation), not substring.
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
                 only the registered BLAKE3 batch and 64-byte fixed-digest families"
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

/// Evidence set behind the currently certified configuration. Exactly the
/// set of tests `scripts/zk-certify.sh` runs, in script order — asserted in
/// both directions by `zk_certificate_evidence_matches_script`.
#[allow(dead_code)]
const EVIDENCE: &[&str] = &[
    "native_tree_hasher_matches_one_shot_reference",
    "external_backend_reproduces_native_digests_and_records",
    "tree_root_separates_nonce_channel_depth_level_index",
    "external_framed_tree_matches_native_and_records_every_node",
    "framed_midstate_simd_matches_scalar_all_tail_shapes",
    "concrete_symbolic_kernels_match_native_references",
    "toy_exact_polynomials_match_evaluation_and_degree_semantics",
    "challenge_dependent_inversion_is_not_part_of_sym_scalar",
    "symbolic_mask_matrix_matches_native_and_has_100_bit_margin",
    "closed_form_translation_preserves_open_rows_and_combined_vector",
    "structural_l0_rank_certificate_matches_actual_ntt_on_every_small_query_set",
    "l0_entropy_counting_gate_holds_for_fixture_and_production",
    "qstar_functional_matrix_matches_dense_schedule",
    "affine_linear_qstar_has_full_conditioned_rank_across_certified_shapes",
    "a1_schema_manifest_and_bijectivity",
    "a1_schema_matches_wire_order",
    "oracle_pow_state_digest_is_an_oracle_query",
    "game_hops_are_complete_and_ordered",
    "production_ledger_exposes_recursive_sibling_gate_at_q64",
    "recorded_leaf_queries_reconstruct_committed_message",
    "prefix_diverges_on_statement_nonce_and_protocol_tuple",
    "simulated_prefix_is_rejected_and_fresh_prefix_reaches_extractor",
    "field_mask_spans_conditioned_round_block_for_fixed_digest",
    "undersized_mask_does_not_span_the_round_block",
    "the_digest_claim_is_a_public_function_of_the_statement",
    "fixed_digest_circuit_is_not_the_batch_circuit",
    "extractor_recovers_the_preimages_from_an_honest_commitment",
    "extraction_fails_on_the_simulators_commitment",
    "simulator_produces_an_accepting_proof_without_any_preimage",
    "production_random_oracle_ledger_matches_artifact",
    "honest_prover_on_the_patched_vector_is_rejected",
    "zk_preimage_roundtrip",
    "prove_verify_r1cs_zk_a1_roundtrip",
];

/// Certified configurations. The registry is populated only from a green
/// `scripts/zk-certify.sh` run and binds each exact circuit digest.
pub const CERTIFIED: &[ZkCertificate] = &[
    ZkCertificate {
        protocol_id: PROTOCOL_ID,
        family: StatementFamily::Blake3Batch,
        batch_size: 256,
        circuit_digest: [
            0xc4, 0x6a, 0x68, 0x63, 0x2b, 0xd4, 0x23, 0x19, 0x26, 0x37, 0x21, 0x6b, 0xdd, 0x8d,
            0x61, 0xe2, 0x95, 0x6a, 0xaf, 0xa0, 0x03, 0x04, 0xfe, 0x30, 0x80, 0x8d, 0xf2, 0xe8,
            0x34, 0xe7, 0x82, 0x3f,
        ],
        field_repr: FIELD_REPR,
        fold_order: FOLD_ORDER,
        endianness: ENDIANNESS,
        pcs_m: 22,
        pcs_log_inv_rate: 1,
        pcs_log_batch_size: 6,
        generator_id: "symbolic-fv-ro",
        evidence: EVIDENCE,
    },
    ZkCertificate {
        protocol_id: PROTOCOL_ID,
        family: StatementFamily::Blake3Preimage,
        batch_size: 256,
        circuit_digest: [
            0x33, 0xcb, 0x2a, 0x40, 0x4f, 0x1b, 0x19, 0x77, 0x5e, 0x0c, 0x38, 0x11, 0x89, 0xd1,
            0x4e, 0xc9, 0x0d, 0x00, 0xf9, 0xcd, 0x75, 0xa9, 0x68, 0x5d, 0x1f, 0xc0, 0x1c, 0x6b,
            0x72, 0x58, 0x2d, 0x4f,
        ],
        field_repr: FIELD_REPR,
        fold_order: FOLD_ORDER,
        endianness: ENDIANNESS,
        pcs_m: 22,
        pcs_log_inv_rate: 1,
        pcs_log_batch_size: 6,
        generator_id: "symbolic-fv-ro",
        evidence: EVIDENCE,
    },
];

/// Look up the certificate for a configuration, ignoring the circuit digest
/// (shape match only).
fn find_shape(
    family: StatementFamily,
    batch_size: usize,
    params: &PcsParams,
) -> Option<&'static ZkCertificate> {
    CERTIFIED.iter().find(|c| {
        c.family == family
            && c.batch_size == batch_size
            && c.pcs_m == params.m
            && c.pcs_log_inv_rate == params.log_inv_rate
            && c.pcs_log_batch_size == params.log_batch_size
            && c.protocol_id == PROTOCOL_ID
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
    let cert = find_shape(family, batch_size, params).ok_or(ZkGateError::Uncertified {
        batch_size,
        m: params.m,
    })?;
    if r1cs.statement_digest() != cert.circuit_digest {
        return Err(ZkGateError::Uncertified {
            batch_size,
            m: params.m,
        });
    }
    Ok(cert)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "prints exact circuit digests for an intentional certificate re-pin"]
    fn emit_production_circuit_digests() {
        let batch = crate::r1cs_hashes::blake3::Blake3Setup::with_zk(256);
        let preimage = crate::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup::new(256);
        let hex = |digest: [u8; 32]| {
            digest
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        };
        println!("batch={}", hex(batch.r1cs.statement_digest()));
        println!("preimage={}", hex(preimage.r1cs.statement_digest()));
    }

    #[test]
    fn registered_production_circuit_digests_match() {
        let batch = crate::r1cs_hashes::blake3::Blake3Setup::with_zk(256);
        let preimage = crate::r1cs_hashes::blake3_preimage::Blake3PreimageZkSetup::new(256);
        require_certified(
            StatementFamily::Blake3Batch,
            256,
            &batch.r1cs,
            &batch.pcs_params,
        )
        .expect("batch certificate must match its exact circuit");
        require_certified(
            StatementFamily::Blake3Preimage,
            256,
            &preimage.r1cs,
            &preimage.pcs_params,
        )
        .expect("preimage certificate must match its exact circuit");
        assert!(
            require_certified(
                StatementFamily::Blake3Preimage,
                256,
                &batch.r1cs,
                &batch.pcs_params,
            )
            .is_err(),
            "a batch circuit must not inherit the fixed-digest certificate"
        );
    }

    /// Test names the certify script actually invokes: the third argument of
    /// every `run` line, reduced to its bare name (last `::` segment, since
    /// lib tests are addressed by full module path).
    fn script_evidence_names(script: &str) -> std::collections::BTreeSet<&str> {
        script
            .lines()
            .filter_map(|line| line.trim_start().strip_prefix("run "))
            .filter_map(|rest| rest.split_whitespace().nth(2))
            .map(|name| name.rsplit("::").next().unwrap_or(name))
            .collect()
    }

    /// The registry's evidence list must be exactly what the certificate
    /// runner script executes — in both directions, by exact name. A
    /// substring check is not enough: it passes for tests the script never
    /// runs (name embedded in a comment) and cannot notice tests the script
    /// runs but the registry does not vouch for.
    #[test]
    fn zk_certificate_evidence_matches_script() {
        let ran = script_evidence_names(include_str!("../../../scripts/zk-certify.sh"));
        assert!(!ran.is_empty(), "no `run` lines parsed from zk-certify.sh");
        for cert in CERTIFIED {
            let listed: std::collections::BTreeSet<&str> = cert.evidence.iter().copied().collect();
            assert_eq!(
                listed.len(),
                cert.evidence.len(),
                "duplicate names in the evidence list"
            );
            let not_run: Vec<_> = listed.difference(&ran).collect();
            assert!(
                not_run.is_empty(),
                "certificate evidence not run by scripts/zk-certify.sh: {not_run:?}"
            );
            let not_listed: Vec<_> = ran.difference(&listed).collect();
            assert!(
                not_listed.is_empty(),
                "scripts/zk-certify.sh runs tests the certificate does not list \
                 as evidence: {not_listed:?}"
            );
        }
    }

    /// Unsupported families and uncertified shapes are rejected, not
    /// silently proved. While the registry is intentionally empty after a
    /// protocol bump, the previously certified production shape must also
    /// remain closed. (Digest matching is exercised by the BLAKE3-side test.)
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
        if CERTIFIED.is_empty() {
            assert!(find_shape(StatementFamily::Blake3Batch, 256, &params).is_none());
        } else {
            assert!(find_shape(StatementFamily::Blake3Batch, 256, &params).is_some());
            assert!(find_shape(StatementFamily::Blake3Preimage, 256, &params).is_some());
        }
    }
}

use super::{
    DIGEST_HEX_BYTES, MAX_BUNDLE_BYTES, MAX_DIGEST_FILE_BYTES, MAX_MESSAGES, Paths, decode_bundle,
    digest_hex, parse_digests_text, parse_paths, run_prove, run_verify, verify_expected_digests,
};
use flock_prover::proof_io::MAGIC;
use flock_prover::r1cs_hashes::blake3_preimage::DIGEST_BYTES;

#[test]
fn decoder_rejects_oversized_input() {
    let bytes = vec![0; MAX_BUNDLE_BYTES as usize + 1];
    assert!(decode_bundle(&bytes).is_err());
}

#[test]
fn decoder_rejects_bare_legacy_bincode() {
    let bytes = 1u64.to_le_bytes();
    assert!(decode_bundle(&bytes).is_err());
}

#[test]
fn decoder_rejects_an_unbounded_digest_vector() {
    let mut bytes = Vec::from(MAGIC);
    bytes.push(5); // VEIL-FLOCK BLAKE3-preimage flavor.
    bytes.extend_from_slice(&u64::MAX.to_le_bytes());
    assert!(decode_bundle(&bytes).is_err());
}

#[test]
fn digest_text_parser_accepts_hex_lines() {
    let first = [0x12; DIGEST_BYTES];
    let second = [0xAB; DIGEST_BYTES];
    let text = format!("{} \r\n{}\n", digest_hex(&first), digest_hex(&second));

    assert_eq!(parse_digests_text(&text).unwrap(), vec![first, second]);
}

#[test]
fn digest_file_byte_limit_allows_benign_whitespace() {
    let max_crlf_with_trailing_space = MAX_MESSAGES * (DIGEST_HEX_BYTES + 3);

    assert!(MAX_DIGEST_FILE_BYTES as usize >= max_crlf_with_trailing_space);
    assert!(MAX_DIGEST_FILE_BYTES < MAX_BUNDLE_BYTES);
}

#[test]
fn digest_text_parser_rejects_empty_and_malformed_inputs() {
    assert!(parse_digests_text("").is_err());
    assert!(parse_digests_text("abcd").is_err());

    let invalid_hex = format!("{}zz", "00".repeat(DIGEST_BYTES - 1));
    assert!(parse_digests_text(&invalid_hex).is_err());

    let non_ascii = "é".repeat(DIGEST_BYTES);
    assert!(parse_digests_text(&non_ascii).is_err());
}

#[test]
fn verifier_checks_bundle_digests_against_external_statement() {
    let digest = [0x11; DIGEST_BYTES];
    let changed = [0x22; DIGEST_BYTES];

    assert!(verify_expected_digests(&[digest], &[digest]).is_ok());
    assert!(verify_expected_digests(&[digest], &[changed]).is_err());
    assert!(verify_expected_digests(&[digest], &[digest, digest]).is_err());
}

#[test]
fn parser_accepts_expected_digest_path() {
    let paths = parse_paths(
        ["--in", "proof.bin", "--digests", "expected-digests.hex"]
            .into_iter()
            .map(String::from),
    )
    .unwrap();

    assert_eq!(paths.input.as_deref(), Some("proof.bin"));
    assert_eq!(paths.digests.as_deref(), Some("expected-digests.hex"));
}

#[test]
fn parser_rejects_duplicate_paths() {
    let result = parse_paths(
        ["--in", "first.bin", "--in", "second.bin"]
            .into_iter()
            .map(String::from),
    );

    assert!(result.is_err());
}

#[test]
fn command_handlers_reject_unsupported_paths() {
    let prove_paths = Paths {
        message: Some("missing-message.bin".to_string()),
        output: Some("proof.bin".to_string()),
        input: None,
        digests: Some("ignored-digests.hex".to_string()),
    };
    let verify_paths = Paths {
        message: Some("ignored-message.bin".to_string()),
        output: None,
        input: Some("proof.bin".to_string()),
        digests: Some("expected-digests.hex".to_string()),
    };

    assert_eq!(
        run_prove(prove_paths).unwrap_err(),
        "prove: --digests is not supported"
    );
    assert_eq!(
        run_verify(verify_paths).unwrap_err(),
        "verify: --message is not supported"
    );
}

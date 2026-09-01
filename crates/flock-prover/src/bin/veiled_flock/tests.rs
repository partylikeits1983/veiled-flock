use super::{
    MAX_BUNDLE_BYTES, decode_bundle, encode_digest_list, parse_digest_list,
    validate_expected_digests,
};
use flock_prover::proof_io::MAGIC;

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
fn digest_list_roundtrips_hex_lines() {
    let digests = vec![[0x0a; 32], [0xf0; 32]];
    let encoded = encode_digest_list(&digests);
    assert_eq!(parse_digest_list(&encoded).unwrap(), digests);
}

#[test]
fn digest_list_rejects_non_hex_or_wrong_width() {
    assert!(parse_digest_list("abcd").is_err());
    assert!(
        parse_digest_list("00000000000000000000000000000000000000000000000000000000000000xz")
            .is_err()
    );
}

#[test]
fn expected_digests_must_match_bundle_copy() {
    let bundle_digests = vec![[1u8; 32]];
    assert!(validate_expected_digests(&bundle_digests, &bundle_digests).is_ok());

    let expected = vec![[2u8; 32]];
    assert!(validate_expected_digests(&bundle_digests, &expected).is_err());
}

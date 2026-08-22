use super::*;

#[test]
fn decoder_rejects_oversized_input() {
    let bytes = vec![0; MAX_BUNDLE_BYTES as usize + 1];
    assert!(decode_bundle(&bytes).is_err());
}

#[test]
fn decoder_rejects_an_unbounded_digest_vector() {
    let mut bytes = MAGIC.to_vec();
    bytes.extend_from_slice(&u64::MAX.to_le_bytes());
    assert!(decode_bundle(&bytes).is_err());
}

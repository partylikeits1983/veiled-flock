use super::{MAX_BUNDLE_BYTES, decode_bundle};
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

//! Test helpers for example-level zero-knowledge regressions.

use flock_core::field::F128;

use crate::proof::ZkProof;

/// Return whether the serialized proof contains the canonical little-endian
/// encoding of `value`. This is only a regression tripwire for examples.
pub fn proof_contains_f128_encoding(proof: &ZkProof, value: F128) -> bool {
    let mut needle = [0u8; 16];
    needle[..8].copy_from_slice(&value.lo.to_le_bytes());
    needle[8..].copy_from_slice(&value.hi.to_le_bytes());
    let proof_bytes = bincode::serialize(proof).expect("serializable proof");
    proof_bytes
        .windows(needle.len())
        .any(|window| window == needle)
}

/// Assert that non-trivial field values are absent from the public proof bytes.
pub fn assert_no_unmasked_f128_values(proof: &ZkProof, values: impl IntoIterator<Item = F128>) {
    for value in values {
        if value.is_zero() || value == F128::ONE {
            continue;
        }
        assert!(
            !proof_contains_f128_encoding(proof, value),
            "proof contains an unmasked F128 value: {value:?}"
        );
    }
}

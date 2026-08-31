//! Test helpers for example-level zero-knowledge regressions.

use flock_core::field::F128;

use crate::proof::ZkProof;

fn f128_encoding(value: F128) -> [u8; 16] {
    let mut encoding = [0u8; 16];
    encoding[..8].copy_from_slice(&value.lo.to_le_bytes());
    encoding[8..].copy_from_slice(&value.hi.to_le_bytes());
    encoding
}

fn contains_f128_encoding(proof_bytes: &[u8], value: F128) -> bool {
    let encoding = f128_encoding(value);
    proof_bytes
        .windows(encoding.len())
        .any(|window| window == encoding)
}

/// Return whether the serialized proof contains the canonical little-endian
/// encoding of `value`. This is only a regression tripwire for examples.
#[must_use]
pub fn proof_contains_f128_encoding(proof: &ZkProof, value: F128) -> bool {
    let proof_bytes = bincode::serialize(proof).expect("serializable proof");
    contains_f128_encoding(&proof_bytes, value)
}

/// Assert that non-trivial field values are absent from the public proof bytes.
pub fn assert_no_unmasked_f128_values(proof: &ZkProof, values: impl IntoIterator<Item = F128>) {
    let proof_bytes = bincode::serialize(proof).expect("serializable proof");
    for value in values {
        if value.is_zero() || value == F128::ONE {
            continue;
        }
        assert!(
            !contains_f128_encoding(&proof_bytes, value),
            "proof contains an unmasked F128 value: {value:?}"
        );
    }
}

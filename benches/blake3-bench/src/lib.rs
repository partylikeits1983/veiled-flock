//! BLAKE3 chain builder, public linkage check, and native-rate calibration for
//! the `blake3_e2e` bin. The generic harness lives in `bench-harness`.

use bench_harness::{SplitMix, amortized_rate, calibration_links_for};
use flock_prover::r1cs_hashes::blake3_preimage::{DIGEST_BYTES, MESSAGE_BYTES};

/// Fiat–Shamir domain for the BLAKE3 e2e suite. The bin and the criterion target
/// share these three constants so their artifacts stay comparable.
pub const DOMAIN: &[u8] = b"veiled-flock-bench-blake3-e2e-v0";
/// Seed for the honest chain builder.
pub const CHAIN_SEED: u64 = 0xC0FFEE_42;
/// Seed for the zk masking Rng.
pub const ZK_SEED: [u8; 32] = [0x42; 32];

/// Build an honest BLAKE3 chain of `n` single-block messages, head seeded from
/// `seed`: `digest_i = blake3(message_i)`, `message_{i+1} = digest_i || zeros`.
pub fn blake3_chain(n: usize, seed: u64) -> (Vec<[u8; MESSAGE_BYTES]>, Vec<[u8; DIGEST_BYTES]>) {
    let mut rng = SplitMix(seed);
    let mut messages = Vec::with_capacity(n);
    let mut digests = Vec::with_capacity(n);
    let mut head = rng.bytes32();
    for _ in 0..n {
        let mut message = [0u8; MESSAGE_BYTES];
        message[..DIGEST_BYTES].copy_from_slice(&head);
        let digest: [u8; DIGEST_BYTES] = *blake3::hash(&message).as_bytes();
        messages.push(message);
        digests.push(digest);
        head = digest;
    }
    (messages, digests)
}

/// Check chain linkage over a public digest list: `blake3(digest_i || zeros) ==
/// digest_{i+1}`. Benched verify paths run it to cover the full relation.
pub fn verify_chain_linkage(digests: &[[u8; DIGEST_BYTES]]) -> bool {
    digests.windows(2).all(|pair| {
        let mut message = [0u8; MESSAGE_BYTES];
        message[..DIGEST_BYTES].copy_from_slice(&pair[0]);
        *blake3::hash(&message).as_bytes() == pair[1]
    })
}

/// Measure the native BLAKE3 chain rate once, in hashes per second.
/// Not pure — it measures wall time, so it does not belong in a unit test.
pub fn blake3_native_rate_with(smoke: bool) -> f64 {
    amortized_rate(calibration_links_for(smoke), |count| {
        let mut head = SplitMix(0xBA5E_11E5).bytes32();
        for _ in 0..count {
            let mut message = [0u8; MESSAGE_BYTES];
            message[..DIGEST_BYTES].copy_from_slice(&head);
            head = *blake3::hash(std::hint::black_box(&message)).as_bytes();
        }
        std::hint::black_box(head);
    })
}

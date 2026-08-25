//! BLAKE3 domain code for the end-to-end proving benchmark (the
//! `blake3_e2e` bin, `src/blake3.rs` in this crate): the chain builder,
//! the public linkage check, and the native-rate calibration. The
//! generic harness (timer, CLI, rows, run driver) lives in the
//! `bench-harness` crate.

use bench_harness::{SplitMix, amortized_rate, calibration_links_for};
use flock_prover::r1cs_hashes::blake3_preimage::{DIGEST_BYTES, MESSAGE_BYTES};

/// Fiat–Shamir domain for the BLAKE3 e2e suite. The bin and the
/// criterion target share these three constants so their artifacts stay
/// comparable.
pub const DOMAIN: &[u8] = b"veiled-flock-bench-blake3-e2e-v0";
/// Seed for the honest chain builder.
pub const CHAIN_SEED: u64 = 0xC0FFEE_42;
/// Seed for the zk masking Rng.
pub const ZK_SEED: [u8; 32] = [0x42; 32];

/// Build an honest BLAKE3 hash chain of `n` single-block messages.
///
/// The head of `message_0` is 32 pseudo-random bytes derived from `seed`
/// via splitmix64. Then `digest_i = blake3(message_i)` and
/// `message_{i+1} = digest_i || zeros`. Returns `(messages, digests)`,
/// one pair per chain link.
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

/// Check chain linkage over a public digest list.
///
/// The chain rule is public, so linkage needs no witness: the check is
/// `blake3(digest_i || zeros) == digest_{i + 1}` for every link. Returns
/// `true` when every link holds. Benched verify paths run this so the
/// measured time covers the full public-chain relation.
pub fn verify_chain_linkage(digests: &[[u8; DIGEST_BYTES]]) -> bool {
    digests.windows(2).all(|pair| {
        let mut message = [0u8; MESSAGE_BYTES];
        message[..DIGEST_BYTES].copy_from_slice(&pair[0]);
        *blake3::hash(&message).as_bytes() == pair[1]
    })
}

/// Measure the native BLAKE3 chain rate once, in hashes per second.
/// Env-free: the caller resolves smoke mode. Not pure — it measures wall
/// time, so it does not belong in a unit test.
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

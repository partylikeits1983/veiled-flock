#[cfg(not(feature = "std"))]
use std::prelude::v1::*;

use crate::r1cs_hashes::blake3_preimage::{
    Blake3PreimageZkSetup, DIGEST_BYTES, MAX_ZK_PREIMAGE_BLOCKS, MESSAGE_BYTES,
};

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "env")]
unsafe extern "C" {
    fn performance_now() -> f64;
}

#[cfg(target_arch = "wasm32")]
fn now_ms() -> f64 {
    unsafe { performance_now() }
}

#[cfg(not(target_arch = "wasm32"))]
fn now_ms() -> f64 {
    0.0
}

#[unsafe(no_mangle)]
pub extern "C" fn veiled_flock_wasm_bench_max_blocks() -> usize {
    MAX_ZK_PREIMAGE_BLOCKS
}

#[unsafe(no_mangle)]
pub extern "C" fn veiled_flock_wasm_bench_blake3_preimage(n_blocks: usize, samples: usize) -> f64 {
    let n_blocks = n_blocks.clamp(1, MAX_ZK_PREIMAGE_BLOCKS);
    let samples = samples.max(1);
    let setup = Blake3PreimageZkSetup::new(n_blocks);
    let mut messages = vec![[0u8; MESSAGE_BYTES]; n_blocks];
    for (block, message) in messages.iter_mut().enumerate() {
        for (index, byte) in message.iter_mut().enumerate() {
            *byte = block.wrapping_mul(31).wrapping_add(index) as u8;
        }
    }
    let digests = messages
        .iter()
        .map(|message| {
            let mut digest = [0u8; DIGEST_BYTES];
            digest.copy_from_slice(::blake3::hash(message).as_bytes());
            digest
        })
        .collect::<Vec<_>>();

    let mut best_prove_ms = f64::INFINITY;
    for sample in 0..samples {
        let mut seed = [0u8; 32];
        seed[..8].copy_from_slice(&(sample as u64).to_le_bytes());
        seed[8..16].copy_from_slice(&(n_blocks as u64).to_le_bytes());
        let mut rng = flock_core::zk::ZkRng::from_seed(seed);

        let start = now_ms();
        let Ok((proof, commitment)) = setup.prove_with_rng(&messages, &digests, &mut rng) else {
            return -1.0;
        };
        let prove_ms = now_ms() - start;

        let start = now_ms();
        if setup.verify(&commitment, &proof, &digests).is_err() {
            return -2.0;
        }
        let verify_ms = now_ms() - start;
        core::hint::black_box((proof.blind_grind_nonce, verify_ms));
        best_prove_ms = best_prove_ms.min(prove_ms);
    }
    best_prove_ms
}

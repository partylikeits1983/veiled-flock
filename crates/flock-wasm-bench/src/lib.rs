#![no_std]

#[macro_use]
extern crate alloc;

use alloc::vec::Vec;

use flock_prover::r1cs_hashes::blake3_preimage::{
    Blake3PreimageZkSetup, DIGEST_BYTES, MAX_ZK_PREIMAGE_BLOCKS, MESSAGE_BYTES,
};

#[cfg(not(target_arch = "wasm32"))]
compile_error!("flock-wasm-bench only supports the wasm32-unknown-unknown target");

#[global_allocator]
static ALLOC: dlmalloc::GlobalDlmalloc = dlmalloc::GlobalDlmalloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    core::arch::wasm32::unreachable()
}

#[link(wasm_import_module = "env")]
unsafe extern "C" {
    fn performance_now() -> f64;
}

const STATUS_OK: i32 = 0;
const STATUS_NULL_RESULT: i32 = -1;
const STATUS_INVALID_INPUT: i32 = -2;
const STATUS_PROVE_FAILED: i32 = -3;
const STATUS_VERIFY_FAILED: i32 = -4;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct VeiledFlockWasmBenchResult {
    pub status: i32,
    pub n_blocks: usize,
    pub samples: usize,
    pub prove_ms: f64,
    pub verify_ms: f64,
}

impl VeiledFlockWasmBenchResult {
    const fn new(status: i32, n_blocks: usize, samples: usize) -> Self {
        Self {
            status,
            n_blocks,
            samples,
            prove_ms: 0.0,
            verify_ms: 0.0,
        }
    }
}

fn now_ms() -> f64 {
    unsafe { performance_now() }
}

#[unsafe(no_mangle)]
pub extern "C" fn veiled_flock_wasm_bench_max_blocks() -> usize {
    MAX_ZK_PREIMAGE_BLOCKS
}

#[unsafe(no_mangle)]
pub extern "C" fn veiled_flock_wasm_bench_result_size() -> usize {
    core::mem::size_of::<VeiledFlockWasmBenchResult>()
}

#[unsafe(no_mangle)]
/// # Safety
///
/// When `out` is non-null, it must be aligned and valid to write one
/// [`VeiledFlockWasmBenchResult`].
pub unsafe extern "C" fn veiled_flock_wasm_bench_blake3_preimage(
    n_blocks: usize,
    samples: usize,
    out: *mut VeiledFlockWasmBenchResult,
) -> i32 {
    if out.is_null() {
        return STATUS_NULL_RESULT;
    }
    let result = run_bench(n_blocks, samples);
    let status = result.status;
    unsafe { out.write(result) };
    status
}

fn run_bench(n_blocks: usize, samples: usize) -> VeiledFlockWasmBenchResult {
    if !(1..=MAX_ZK_PREIMAGE_BLOCKS).contains(&n_blocks) || samples == 0 {
        return VeiledFlockWasmBenchResult::new(STATUS_INVALID_INPUT, n_blocks, samples);
    }

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
    let mut best_verify_ms = f64::INFINITY;
    for sample in 0..samples {
        let mut seed = [0u8; 32];
        seed[..8].copy_from_slice(&(sample as u64).to_le_bytes());
        seed[8..16].copy_from_slice(&(n_blocks as u64).to_le_bytes());
        let mut rng = flock_prover::zk::ZkRng::from_seed(seed);

        let start = now_ms();
        let Ok((proof, commitment)) = setup.prove_with_rng(&messages, &digests, &mut rng) else {
            return VeiledFlockWasmBenchResult::new(STATUS_PROVE_FAILED, n_blocks, samples);
        };
        let prove_ms = now_ms() - start;

        let start = now_ms();
        if setup.verify(&commitment, &proof, &digests).is_err() {
            return VeiledFlockWasmBenchResult::new(STATUS_VERIFY_FAILED, n_blocks, samples);
        }
        let verify_ms = now_ms() - start;
        core::hint::black_box(proof.blind_grind_nonce);
        best_prove_ms = best_prove_ms.min(prove_ms);
        best_verify_ms = best_verify_ms.min(verify_ms);
    }

    VeiledFlockWasmBenchResult {
        status: STATUS_OK,
        n_blocks,
        samples,
        prove_ms: best_prove_ms,
        verify_ms: best_verify_ms,
    }
}

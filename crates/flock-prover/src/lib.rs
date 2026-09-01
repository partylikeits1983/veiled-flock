#![cfg_attr(not(feature = "std"), no_std)]

//! `flock-prover`: the Apple-silicon-optimized end-to-end Flock prover.
//!
//! Builds on [`flock_core`] (the protocol library + verifier) with the
//! top-level prove orchestration ([`prover`]), the monolithic hash R1CS
//! encoders ([`r1cs_hashes`]), and the hash-chain / Merkle-path statement
//! builders ([`chain`], [`merkle_path`], [`proof_io`]).
//!
//! For convenience, the entire `flock_core` API is re-exported here, so code
//! depending on `flock-prover` can reach `field`, `pcs`, `verifier`, etc.
//! through this crate.
//!
//! Workspace-wide Clippy `allow`s for the hand-tuned numeric kernels are
//! declared in `[workspace.lints.clippy]` at the repo root.

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[cfg(not(feature = "parallel"))]
extern crate flock_core as rayon;
#[cfg(not(feature = "std"))]
extern crate flock_core as std;

#[cfg(all(feature = "wasm-bench", not(feature = "std"), target_arch = "wasm32"))]
#[global_allocator]
static ALLOC: dlmalloc::GlobalDlmalloc = dlmalloc::GlobalDlmalloc;

#[cfg(all(feature = "wasm-bench", not(feature = "std"), target_arch = "wasm32"))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

#[cfg(not(feature = "std"))]
#[allow(unused_macros)]
macro_rules! eprintln {
    ($($arg:tt)*) => {{
        let _ = core::format_args!($($arg)*);
    }};
}

#[cfg(not(feature = "std"))]
#[allow(unused_macros)]
macro_rules! println {
    ($($arg:tt)*) => {{
        let _ = core::format_args!($($arg)*);
    }};
}

pub use flock_core::*;

pub mod chain;
pub mod digest_bind;
pub mod ligerito_decode;
pub mod merkle_path;
pub mod preimage_extractor;
#[cfg(feature = "std")]
pub mod proof_io;
pub mod prover;
pub mod r1cs_hashes;
#[cfg(feature = "veil")]
pub mod sim_game;
#[cfg(feature = "std")]
pub mod sim_oracle;
#[cfg(feature = "veil")]
pub mod succinct_veil;
#[cfg(feature = "wasm-bench")]
pub mod wasm_bench;

//! The shared driver of the example binaries: time the prover and the
//! verifier and print the same report for every example.

use std::time::Instant;

use crate::error::VeilError;
use crate::proof::ZkProof;

/// Run `prove`, print the mask length, the prover time, and the proof size,
/// then run `verify` and print its time. Panics with the error on failure,
/// as an example binary should.
pub fn run_example(
    prove: impl FnOnce() -> Result<(ZkProof, usize), VeilError>,
    verify: impl FnOnce(ZkProof) -> Result<(), VeilError>,
) {
    eprintln!("\n=== ZK BACKEND ===");
    let now = Instant::now();
    let (proof, mask_length) = prove().expect("zk prove failed");
    eprintln!("Mask length: {mask_length}");
    eprintln!("Prover time: {:?}", now.elapsed());
    eprintln!(
        "Proof size: {} bytes",
        bincode::serialize(&proof)
            .expect("serializable proof")
            .len()
    );

    let now = Instant::now();
    verify(proof).expect("zk verification failed");
    eprintln!("Verifier time: {:?}", now.elapsed());
    eprintln!("ZK backend: PASSED");
}

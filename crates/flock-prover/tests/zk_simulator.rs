//! The explicit HVZK simulator for BLAKE3 batch statements (feedback item #2).
//!
//! A BLAKE3 batch statement binds no public input (its digest is the matrices
//! and layout only; the verifier compares the accepted claim against nothing
//! caller-supplied; the only pinned wire is the constant-one wire, pinned to
//! 1). So a valid witness is efficiently self-generatable — hash arbitrary
//! self-chosen messages — and the simulator is simply the honest zk prover run
//! on such a self-generated witness. It receives ONLY the public statement
//! (here, the batch size), never a real witness, and it programs no oracle and
//! rewinds nothing, so it is also the NIZK simulator after Fiat–Shamir.
//!
//! This test realizes that simulator and checks it produces an accepting proof
//! for the statement, jointly generating every transcript value (commitment
//! root, PIOP messages, Ligerito openings + Merkle paths, y_r, y_g, and the
//! reduced claim v = ẑ(r)) — because it IS the honest prover on a witness it
//! knows. Combined with the transcript witness-indistinguishability certified
//! in `zk_leakage_certificate.rs`, the simulated and honest distributions
//! coincide up to the certified error.

#![cfg(feature = "zk")]

use flock_core::challenger::FsChallenger;
use flock_prover::r1cs_hashes::blake3::{Blake3Setup, Compression};

/// Deterministic PRNG so the test is reproducible; in production the simulator
/// draws its self-generated witness and masks from OS entropy.
struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        ((z ^ (z >> 31)) & 0xFFFF_FFFF) as u32
    }
}

/// The simulator: given ONLY the public statement (batch size `n`), produce an
/// accepting proof without any witness. Picks arbitrary compressions, then runs
/// the honest zk prover.
fn simulate(n: usize, rng: &mut Rng) -> (Blake3Setup, flock_core::proof::R1csProofLigerito, flock_core::pcs::Commitment) {
    let setup = Blake3Setup::with_zk(n);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect();
    let mut ch = FsChallenger::new(b"flock-zkb-blake3");
    let (proof, commitment, _claim) = setup.prove_fast_zk(&blocks, &mut ch);
    (setup, proof, commitment)
}

#[test]
fn simulator_produces_accepting_proof_without_a_witness() {
    let n = 256; // smallest production batch (m = 22)
    let mut rng = Rng(0x51_3D_1A_70);

    // The simulator sees only `n` (the public statement carries no I/O).
    let (setup, proof, commitment) = simulate(n, &mut rng);

    // The simulated proof verifies under the unchanged verifier.
    let mut vch = FsChallenger::new(b"flock-zkb-blake3");
    assert!(
        setup.verify(&commitment, &proof, &mut vch).is_ok(),
        "the witness-free simulator must produce an accepting proof"
    );

    // A second simulator run (fresh self-generated witness + fresh masks)
    // yields a different transcript that still verifies — the simulator is
    // randomized, matching the honest prover's per-proof freshness.
    let mut rng2 = Rng(0x0B_AD_C0_DE);
    let (setup2, proof2, commitment2) = simulate(n, &mut rng2);
    let mut vch2 = FsChallenger::new(b"flock-zkb-blake3");
    assert!(setup2.verify(&commitment2, &proof2, &mut vch2).is_ok());
    assert_ne!(
        commitment.root, commitment2.root,
        "independent simulator runs must differ (fresh masks/witness)"
    );
}

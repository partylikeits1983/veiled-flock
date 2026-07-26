//! **Production-configuration measurements** for the certified BLAKE3 batch
//! shape (`Blake3Setup::with_zk(256)`, m = 22).
//!
//! The complete-transcript joint certificate is computed at a reduced
//! fixture, because exact full-support probing at m = 22 would need millions
//! of prover runs. What can be measured *at the production shape* — and is
//! measured here rather than assumed — are the facts the transfer argument
//! actually rests on:
//!
//! 1. the degree-2 mask channel is **surjective onto the round-pair block**
//!    at the production configuration, established by random-probe spanning
//!    through the real fold kernels (random probing can only under-estimate
//!    a rank, so reaching full output rank is a proof of surjectivity, not
//!    evidence for it);
//! 2. the same measurement **fails for a degenerate `Q`**, so it is not
//!    vacuous at this size either;
//! 3. the per-proof coverage self-check — the construct that replaces the
//!    withdrawn ε_rank bound — **passes at the production configuration**,
//!    which is what makes ε_rank = 0 a statement about proofs that would
//!    actually be emitted;
//! 4. the randomizer margin that binds the `s_hat_v` slices is far larger
//!    here than at the fixture, quantified.

#![cfg(feature = "zk")]

use flock_core::challenger::FsChallenger;
use flock_core::field::F128;
use flock_prover::r1cs_hashes::blake3::Blake3Setup;
use flock_prover::zk_rank_check::check_mask_coverage;

struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
}

fn pack_bits(n: usize, mut f: impl FnMut(usize) -> bool) -> Vec<u8> {
    let mut out = vec![0u8; n / 8];
    for i in 0..n {
        if f(i) {
            out[i / 8] |= 1 << (i % 8);
        }
    }
    out
}

/// (1)+(2)+(3): the mask channel covers the round-pair block at m = 22, a
/// degenerate `Q` does not, and the per-proof self-check passes there.
#[test]
#[ignore = "production shape (m=22): thousands of full-cube fold passes"]
fn production_mask_channel_covers_round_block() {
    let setup = Blake3Setup::with_zk(256);
    let m = setup.m();
    assert_eq!(m, 22, "the certified production configuration is m = 22");
    let n = 1usize << m;

    let mut rng = Rng(0x9C0D_E22);
    let q_random = pack_bits(n, |_| rng.next_u64() & 1 == 1);
    let q_const = pack_bits(n, |_| true);
    let ch = FsChallenger::new(b"flock-prod-cert");

    let ok = check_mask_coverage(&q_random, m, 0xBEEF, &ch)
        .expect("at the production configuration a uniform Q must cover the round-pair block");
    println!(
        "production m={m}: round-pair block {} bits, spanned {} with {} probes",
        ok.target_bits, ok.rank, ok.probes
    );
    assert!(ok.covered());

    let bad = check_mask_coverage(&q_const, m, 0xBEEF, &ch)
        .expect_err("a constant Q must NOT cover the degree-2 half at production size either");
    println!(
        "production m={m}: constant Q spans only {} of {} bits",
        bad.report.rank, bad.report.target_bits
    );
    assert!(bad.report.rank < ok.target_bits);
    // It reaches about the G(1) half and no more.
    assert!(bad.report.rank * 2 <= ok.target_bits + 256);
}

/// (4) The randomizer margin that binds the `s_hat_v` bit-slices. Slice `r`
/// sees only witness bits at positions ≡ r (mod 128), so the sizing rule is
/// `blocks × A-chunks-per-block ≥ 128`, and the certificate showed the
/// residual concentrating in exactly that class when the margin was thin.
/// This records the production margin against the fixture's.
#[test]
fn production_s_hat_v_randomizer_margin() {
    let setup = Blake3Setup::with_zk(256);
    let layout = setup.r1cs.zk.expect("zk setup carries a layout");
    let blocks = setup.n_block_slots();
    // A-type randomizer bits per block, from the layout the encoder builds.
    let a_chunks_per_block = layout.a_bits().count() / 128;
    let per_residue = blocks * a_chunks_per_block;
    let margin = per_residue as f64 / 128.0;
    println!(
        "production: {blocks} blocks × {a_chunks_per_block} A-chunks = {per_residue} \
         per bit-residue → {margin:.1}× the 128-bit requirement"
    );
    // The reduced fixture that carries the complete-transcript certificate
    // runs at 16 × 24 / 128 = 3×; production must be at least that.
    assert!(
        margin >= 3.0,
        "production margin {margin:.1}× is below the fixture's 3×, so the \
         certificate's transfer argument would run the wrong way"
    );
}

/// The gated production entry point emits a verifying proof, and the
/// checked variant — the one that makes ε_rank = 0 for emitted proofs —
/// also works at this configuration.
#[test]
#[ignore = "production shape (m=22) end-to-end with the per-proof check"]
fn production_checked_prove_verifies() {
    let setup = Blake3Setup::with_zk(256);
    let mut rng = Rng(0x0B10_C25);
    let blocks: Vec<_> = (0..256)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u64() as u32);
            let msg: [u32; 16] = std::array::from_fn(|_| rng.next_u64() as u32);
            (cv, msg, 0u64, 64u32, 11u32)
        })
        .collect();
    let mut zk_rng = flock_core::zk::ZkRng::from_entropy();
    let mut ch = FsChallenger::new(b"flock-prod-checked");
    let (proof, comm, report) = setup
        .prove_zk_a1_checked(&blocks, &mut zk_rng, 4, &mut ch)
        .expect("certified configuration");
    println!(
        "production checked prove: coverage {}/{} bits, {} resample(s)",
        report.rank, report.target_bits, report.resamples
    );
    assert!(report.covered());
    let mut chv = FsChallenger::new(b"flock-prod-checked");
    setup.verify_zk_a1(&comm, &proof, &mut chv).expect("checked proof must verify");
    let _ = F128::ZERO;
}

/// **Why the complete-transcript certificate needs a synthetic vehicle.**
///
/// The coverage criterion reasons about *claim-preserving combinations* of
/// witness-difference directions, which requires the sampled differences to
/// span a genuine space of witness differences — i.e. a linear sub-family of
/// valid witnesses. The audit fixture supplies one by construction (payload
/// bits that feed no product row).
///
/// A real BLAKE3 statement does not, and this records why: the witness is a
/// compression trace, so the map from message bits to witness is nonlinear.
/// Flipping two message bits separately and then together does **not** give
/// the sum of the two witness differences. Consequently the criterion cannot
/// be evaluated directly on a BLAKE3 statement, no matter how much compute
/// is available, and the certificate must be computed on a vehicle that has
/// a linear family and transferred structurally.
///
/// This is a statement about the *methodology*, not about the protocol: it
/// is why the paper's principal limitation is phrased as transfer, and why
/// no amount of probing at m=22 would remove it.
#[test]
fn blake3_witness_has_no_linear_difference_family() {
    let setup = Blake3Setup::with_zk(256);
    let n_log = setup.n_blocks_log();
    let mk = |bits: (bool, bool)| -> Vec<bool> {
        let mut rng = Rng(0xB1A_3E7);
        let blocks: Vec<_> = (0..256)
            .map(|i| {
                let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u64() as u32);
                let mut msg: [u32; 16] = std::array::from_fn(|_| rng.next_u64() as u32);
                if i == 0 {
                    // Two independent single-bit perturbations of block 0.
                    if bits.0 {
                        msg[0] ^= 1;
                    }
                    if bits.1 {
                        msg[1] ^= 1;
                    }
                }
                (cv, msg, 0u64, 64u32, 11u32)
            })
            .collect();
        let _ = n_log;
        setup.generate_witness(&blocks)
    };

    let w00 = mk((false, false));
    let w10 = mk((true, false));
    let w01 = mk((false, true));
    let w11 = mk((true, true));

    // Linearity would mean (w10 ⊕ w00) ⊕ (w01 ⊕ w00) == (w11 ⊕ w00).
    let mut additive = 0usize;
    let mut violations = 0usize;
    for i in 0..w00.len() {
        let d1 = w10[i] ^ w00[i];
        let d2 = w01[i] ^ w00[i];
        let d12 = w11[i] ^ w00[i];
        if d1 ^ d2 == d12 {
            additive += 1;
        } else {
            violations += 1;
        }
    }
    println!(
        "BLAKE3 witness additivity over {} bits: {additive} additive, {violations} violating",
        w00.len()
    );
    assert!(
        violations > 0,
        "the BLAKE3 witness map appears additive in the message bits, which \
         would contradict it being a hash trace — re-examine the fixture"
    );
}

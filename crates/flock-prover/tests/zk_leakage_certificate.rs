//! WS-0 tripwire: EXACT (not sampled) leakage certificate for the PIOP
//! transcript, and the decisive check of whether the *shipped* conditional
//! (mixture) certificate actually covers the full transcript.
//!
//! Two facts are established here exactly, on the same fixture and fixed
//! challenges as `zk_piop_audit.rs` / `zk_affinity_probe.rs`:
//!
//! 1. **The shipped mixture theorem's `h_coset` hypothesis is FALSE for the
//!    full transcript** (`final_b_breaks_full_mixture_hcoset`). `final_b_eval`
//!    has an *identically zero* `u_A`-derivative (the b-cube reads B- and
//!    real rows, but A-randomizer rows select only the constant-1 wire on the
//!    b-side), yet it *varies with* `u_B`. So a cross-`u_B` offset difference
//!    has a nonzero `final_b` component that provably lies OUTSIDE the
//!    `u_A`-image — violating `MaskingMixture.h_coset` (∀ b b′,
//!    f w b − f w′ b′ ∈ V0). The shipped `zk_affinity_probe` certificate only
//!    passed because its 6-value subsets never sampled the `final_b`
//!    coordinate. This is why the mixture theorem must be replaced by the
//!    *triangular* restatement (a u_B-stage covering final_b etc., then a
//!    conditioned u_A/m-stage) — and why the round-pair class needs a mask
//!    channel that is affine with witness-independent coefficients.
//!
//! 2. **The triangular structure is viable**
//!    (`final_b_covered_by_b_stage`): the `final_b` coordinate *is* inside the
//!    image of the B-species map, and so are its witness-difference and
//!    cross-`u_B` offset components — the pieces the mixture theorem
//!    mis-assigned to the u_A-image belong to the u_B-stage.
//!
//! An offline exact full-image coverage certificate for the affine classes
//! (`affine_classes_exactly_covered`, `#[ignore]`) confirms that for the
//! genuinely-affine transcript coordinates, witness-difference directions lie
//! in the mask image — which for an affine map is *exact* distribution
//! equality, no sampling.

#![cfg(feature = "zk")]

use flock_core::challenger::{Challenger, RandomChallenger};
use flock_core::field::F128;
use flock_core::lincheck::{self, pack_z_lincheck_from_packed};
use flock_core::pcs::{self, ring_switch};
use flock_core::r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout};
use flock_core::zerocheck::{self, PaddingSpec};

struct RecordingChallenger<C: Challenger> {
    inner: C,
    observed: Vec<F128>,
}

impl<C: Challenger> Challenger for RecordingChallenger<C> {
    fn observe_label(&mut self, label: &[u8]) {
        self.inner.observe_label(label);
    }
    fn observe_f128(&mut self, value: F128) {
        self.observed.push(value);
        self.inner.observe_f128(value);
    }
    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.observed.extend_from_slice(values);
        self.inner.observe_f128_slice(values);
    }
    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.inner.observe_bytes(bytes);
    }
    fn sample_f128(&mut self) -> F128 {
        self.inner.sample_f128()
    }
    fn grind_pow(&mut self, bits: u32) -> u64 {
        self.inner.grind_pow(bits)
    }
    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.inner.verify_pow(nonce, bits)
    }
}

const M: usize = 15;
const K_LOG: usize = 12;
const K_SKIP: usize = 6;
const K: usize = 1 << K_LOG;
const BLOCKS: usize = 1 << (M - K_LOG);

const PAYLOAD_BASE: usize = 1;
const N_PAYLOAD: usize = 64;
const PROD_BASE: usize = PAYLOAD_BASE + N_PAYLOAD;
const N_PROD: usize = 16;
const A_RAND_BASE: usize = 128;
const N_A_RAND: usize = 24 * 128;
const B_RAND_BASE: usize = A_RAND_BASE + N_A_RAND;
const N_B_RAND: usize = 2 * 128;
const USEFUL: usize = B_RAND_BASE + N_B_RAND;

const A_BITS: usize = N_A_RAND * BLOCKS;
const B_BITS: usize = N_B_RAND * BLOCKS;
const CH_SEED: u64 = 0x7777_1234;

// Transcript layout (see zk_affinity_probe.rs):
//   [round1_ab(64) ‖ round1_c(64) ‖ zc round pairs(2·(M−6)) ‖
//    final_a, final_b ‖ lincheck pairs(2·(K_LOG−6)) ‖ z_partial(64) ‖
//    c_eval ‖ w ‖ s_hat_v_c(128) ‖ s_hat_v_ab(128)]
const ZC_PAIRS_LEN: usize = 2 * (M - 6);
const FINAL_A_IDX: usize = 128 + ZC_PAIRS_LEN;
const FINAL_B_IDX: usize = FINAL_A_IDX + 1;

fn masked_r1cs() -> BlockR1cs {
    let mut a_rows: Vec<Vec<usize>> = vec![Vec::new(); K];
    let mut b_rows: Vec<Vec<usize>> = vec![Vec::new(); K];
    a_rows[0] = vec![0];
    b_rows[0] = vec![0];
    for s in PAYLOAD_BASE..PAYLOAD_BASE + N_PAYLOAD {
        a_rows[s] = vec![s];
        b_rows[s] = vec![0];
    }
    for i in 0..N_PROD {
        let s = PROD_BASE + i;
        a_rows[s] = vec![PAYLOAD_BASE + 2 * i];
        b_rows[s] = vec![PAYLOAD_BASE + 2 * i + 1];
    }
    for s in A_RAND_BASE..A_RAND_BASE + N_A_RAND {
        a_rows[s] = vec![s];
        b_rows[s] = vec![0];
    }
    for s in B_RAND_BASE..B_RAND_BASE + N_B_RAND {
        a_rows[s] = vec![0];
        b_rows[s] = vec![s];
    }
    let identity = SparseBinaryMatrix {
        num_rows: K,
        num_cols: K,
        rows: (0..K).map(|i| vec![i]).collect(),
    };
    BlockR1cs {
        m: M,
        k_log: K_LOG,
        k_skip: K_SKIP,
        useful_bits: USEFUL,
        a_0: SparseBinaryMatrix {
            num_rows: K,
            num_cols: K,
            rows: a_rows,
        },
        b_0: SparseBinaryMatrix {
            num_rows: K,
            num_cols: K,
            rows: b_rows,
        },
        c_0: identity,
        layout: WitnessLayout::RowMajor,
        const_pin: None,
        zk: None,
        digest_cache: std::sync::OnceLock::new(),
        csc_cache: std::sync::OnceLock::new(),
    }
}

fn witness(payload: &[bool], u_a: &[bool], u_b: &[bool]) -> Vec<F128> {
    assert_eq!(payload.len(), N_PAYLOAD * BLOCKS);
    assert_eq!(u_a.len(), A_BITS);
    assert_eq!(u_b.len(), B_BITS);
    let mut z = vec![false; 1 << M];
    for blk in 0..BLOCKS {
        let base = blk * K;
        z[base] = true;
        for j in 0..N_PAYLOAD {
            z[base + PAYLOAD_BASE + j] = payload[blk * N_PAYLOAD + j];
        }
        for i in 0..N_PROD {
            z[base + PROD_BASE + i] =
                z[base + PAYLOAD_BASE + 2 * i] & z[base + PAYLOAD_BASE + 2 * i + 1];
        }
        for j in 0..N_A_RAND {
            z[base + A_RAND_BASE + j] = u_a[blk * N_A_RAND + j];
        }
        for j in 0..N_B_RAND {
            z[base + B_RAND_BASE + j] = u_b[blk * N_B_RAND + j];
        }
    }
    pcs::pack_witness(&z, M)
}

fn transcript(r1cs: &BlockR1cs, z_packed: &[F128]) -> Vec<F128> {
    let a_packed = r1cs.apply_a_packed(z_packed);
    let b_packed = r1cs.apply_b_packed(z_packed);
    let cast = |v: &[F128]| -> &[u8] {
        unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
    };
    let stripe = pack_z_lincheck_from_packed(z_packed, M, K_LOG);
    let padding = r1cs.padding_spec();

    let mut ch = RecordingChallenger {
        inner: RandomChallenger::new(CH_SEED),
        observed: Vec::new(),
    };
    let (_zc_proof, zc_claim, s_hat_v_c) = zerocheck::prove_packed_padded_capture_s_hat_v_c(
        cast(&a_packed),
        cast(&b_packed),
        cast(z_packed),
        M,
        &padding,
        &mut ch,
    );
    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);
    let circuit = r1cs.sparse_lincheck_circuit();
    let (_lc_proof, lc_claim, z_vec_pre) = lincheck::prove_padded_capture_z_vec(
        &stripe,
        M,
        K_LOG,
        K_SKIP,
        r1cs.useful_bits,
        &circuit,
        &x_ab,
        &mut ch,
    );
    let s_hat_v_ab = ring_switch::s_hat_v_from_z_vec(&z_vec_pre, &lc_claim.r_inner_rest[1..]);

    let mut out = ch.observed;
    out.push(zc_claim.c_eval);
    out.push(lc_claim.w);
    out.extend_from_slice(&s_hat_v_c);
    out.extend_from_slice(&s_hat_v_ab);
    out
}

struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.next_u64() & 1 == 1).collect()
    }
}

fn unit(n: usize, i: usize) -> Vec<bool> {
    let mut v = vec![false; n];
    v[i] = true;
    v
}

// --- F₂ linear algebra on one F128 coordinate (128 bits = 2 u64 words) ---

/// Row-reduced basis of a subspace of F₂^128 (one transcript coordinate).
#[derive(Default)]
struct Coord128Space {
    // basis[i] has a leading 1 at bit `pivots[i]`, reduced against the rest.
    basis: Vec<[u64; 2]>,
    pivots: Vec<usize>,
}

impl Coord128Space {
    fn reduce(&self, mut v: [u64; 2]) -> [u64; 2] {
        for (b, &p) in self.basis.iter().zip(&self.pivots) {
            let (w, msk) = (p / 64, 1u64 << (p % 64));
            if v[w] & msk != 0 {
                v[0] ^= b[0];
                v[1] ^= b[1];
            }
        }
        v
    }
    /// Insert v; return true if it grew the space.
    fn insert(&mut self, v: [u64; 2]) -> bool {
        let r = self.reduce(v);
        if r == [0, 0] {
            return false;
        }
        let p = if r[0] != 0 {
            r[0].trailing_zeros() as usize
        } else {
            64 + r[1].trailing_zeros() as usize
        };
        self.basis.push(r);
        self.pivots.push(p);
        true
    }
    fn contains(&self, v: [u64; 2]) -> bool {
        self.reduce(v) == [0, 0]
    }
}

fn coord(t: &[F128], i: usize) -> [u64; 2] {
    [t[i].lo, t[i].hi]
}
fn coord_xor(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    [a[0] ^ b[0], a[1] ^ b[1]]
}

// --- F₂ linear algebra over a wide vector (dynamic width) ---

#[derive(Default)]
struct F2Space {
    basis: Vec<Vec<u64>>,
    pivots: Vec<usize>,
}

impl F2Space {
    fn reduce(&self, mut v: Vec<u64>) -> Vec<u64> {
        for (b, &p) in self.basis.iter().zip(&self.pivots) {
            let (w, msk) = (p / 64, 1u64 << (p % 64));
            if v[w] & msk != 0 {
                for k in 0..v.len() {
                    v[k] ^= b[k];
                }
            }
        }
        v
    }
    fn insert(&mut self, v: Vec<u64>) -> bool {
        let r = self.reduce(v);
        let Some(p) = first_set_bit(&r) else {
            return false;
        };
        self.basis.push(r);
        self.pivots.push(p);
        true
    }
    fn rank(&self) -> usize {
        self.basis.len()
    }
}

fn first_set_bit(v: &[u64]) -> Option<usize> {
    for (i, &w) in v.iter().enumerate() {
        if w != 0 {
            return Some(i * 64 + w.trailing_zeros() as usize);
        }
    }
    None
}

fn flatten(vals: &[F128]) -> Vec<u64> {
    let mut out = Vec::with_capacity(vals.len() * 2);
    for v in vals {
        out.push(v.lo);
        out.push(v.hi);
    }
    out
}

// ---------------------------------------------------------------------------
// A1′ validation: the degree-2 committed mask channel γ·P·Q closes the
// round-pair leak. This de-risks the amendment BEFORE any kernel surgery,
// analogously to the WS-0 tripwire.
//
// The mask channel adds γ·(round pairs of the P·Q product-sumcheck) to the
// zerocheck round pairs, where P, Q are fresh full-support committed random
// multilinears carrying NO witness. So the mask contribution's distribution
// is witness-independent by construction; the combined round pair is
// G_j(witness) + γ·M_j(P,Q). Hiding reduces to: for (almost) every fixed Q,
// the map P ↦ (all round-pair coordinates of P·Q) is SURJECTIVE onto the
// round-pair space (2·(m−k_skip) F128 = 2304 bits here). Then at fixed Q the
// combined value is uniform over that space regardless of the witness term
// G_j — exact distribution equality (affine-in-P, full image), and mixing
// over Q keeps it witness-independent since Q is witness-free.
//
// A degree-1 (multilinear) channel would give M_j(∞)=0 and FAIL this test on
// the ∞-coordinates — which is exactly why the linear amendment is
// insufficient and the degree-2 P·Q channel is required.
// ---------------------------------------------------------------------------

const N_MLV: usize = M - K_SKIP; // 9 multilinear rounds
const ROUND_PAIR_VALUES: usize = 2 * N_MLV; // 18 F128 (G(1),G(∞)) per round

/// Round pairs of the P·Q product sumcheck at the fixed challenge schedule
/// (same seed ⇒ same challenges as any other run: RandomChallenger ignores
/// observations). Returns the 18 round-pair F128 values, interleaved
/// (m1_0, minf_0, m1_1, minf_1, …).
fn mask_round_pairs(p_bits: &[bool], q_bits: &[bool]) -> Vec<F128> {
    let mut zp = vec![false; 1 << M];
    zp.copy_from_slice(p_bits);
    let mut zq = vec![false; 1 << M];
    zq.copy_from_slice(q_bits);
    let p_packed = pcs::pack_witness(&zp, M);
    let q_packed = pcs::pack_witness(&zq, M);
    let zero_c = pcs::pack_witness(&vec![false; 1 << M], M);
    let cast = |v: &[F128]| -> &[u8] {
        unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
    };
    let mut ch = RandomChallenger::new(CH_SEED);
    let (proof, _claim) = zerocheck::prove_packed_padded(
        cast(&p_packed),
        cast(&q_packed),
        cast(&zero_c),
        M,
        &PaddingSpec::dense(M),
        &mut ch,
    );
    assert_eq!(proof.multilinear_rounds.len(), N_MLV);
    let mut out = Vec::with_capacity(ROUND_PAIR_VALUES);
    for (m1, minf) in &proof.multilinear_rounds {
        out.push(*m1);
        out.push(*minf);
    }
    out
}

/// Verifier's multilinear telescoping (mirrors `zerocheck::verify`): given the
/// initial running claim and the round pairs `(G(1),G(∞))`, propagate the
/// running claim through all rounds. `r_eq[i]` is the eq weight of round i
/// (= `claim.r_rest[i]`), `rhos[i]` the round challenge.
fn telescope(init: F128, rounds: &[(F128, F128)], r_eq: &[F128], rhos: &[F128]) -> F128 {
    let mut c = init;
    for (i, &(g1, ginf)) in rounds.iter().enumerate() {
        let one_plus_req = F128::ONE + r_eq[i];
        let g0 = (c + r_eq[i] * g1) * one_plus_req.inv();
        let rho = rhos[i];
        let one_plus_rho = F128::ONE + rho;
        c = g0 * one_plus_rho + g1 * rho + ginf * rho * one_plus_rho;
    }
    c
}

/// The telescoping is affine in the initial claim; recover the unique initial
/// claim that reaches `target` (= what the real verifier reconstructs, since
/// the proof verifies). Over F₂₁₂₈: `init = (target − β)·α⁻¹` with
/// `β = telescope(0)`, `α = telescope(1) − telescope(0)`.
fn recover_init(target: F128, rounds: &[(F128, F128)], r_eq: &[F128], rhos: &[F128]) -> F128 {
    let beta = telescope(F128::ZERO, rounds, r_eq, rhos);
    let alpha = telescope(F128::ONE, rounds, r_eq, rhos) + beta;
    (target + beta) * alpha.inv()
}

/// A1′ COMBINED COMPLETENESS + SOUNDNESS (reference, fixed challenges).
///
/// Builds the amended zerocheck's combined transcript from the real prover
/// primitives — main product-sumcheck on (a,b) and mask product-sumcheck on
/// (P,Q) at identical challenges — and checks the combined verifier's final
/// equation, `combined_running == final_a·final_b + γ·P(ρ)·Q(ρ)`. By linearity
/// of the sumcheck in both the initial claim and the messages, the honest
/// combined proof satisfies it (completeness); tampering any masked round pair
/// breaks it (the round-pair channel is bound). This validates the amendment's
/// arithmetic on real prover output; the remaining WS-1 work is wiring the
/// combined sumcheck into the single-pass Fiat–Shamir prover/verifier and
/// opening P,Q at ρ through the PCS.
#[test]
fn a1_prime_combined_completeness_and_soundness() {
    let r1cs = masked_r1cs();
    let mut rng = Rng(0x0C0FFEE);
    let payload = rng.bits(N_PAYLOAD * BLOCKS);
    let ua = rng.bits(A_BITS);
    let ub = rng.bits(B_BITS);
    let z_main = witness(&payload, &ua, &ub);

    // Main product-sumcheck (a·b) via the real prover.
    let a_packed = r1cs.apply_a_packed(&z_main);
    let b_packed = r1cs.apply_b_packed(&z_main);
    let cast = |v: &[F128]| -> &[u8] {
        unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
    };
    let padding = r1cs.padding_spec();
    let (main_proof, main_claim) = zerocheck::prove_packed_padded(
        cast(&a_packed),
        cast(&b_packed),
        cast(&z_main),
        M,
        &padding,
        &mut RandomChallenger::new(CH_SEED),
    );

    // Mask product-sumcheck (P·Q), full-support random, at the SAME challenges
    // (RandomChallenger ignores observations ⇒ identical schedule).
    let mut zp = vec![false; 1 << M];
    zp.copy_from_slice(&rng.bits(1 << M));
    let mut zq = vec![false; 1 << M];
    zq.copy_from_slice(&rng.bits(1 << M));
    let p_packed = pcs::pack_witness(&zp, M);
    let q_packed = pcs::pack_witness(&zq, M);
    let zero_c = pcs::pack_witness(&vec![false; 1 << M], M);
    let (mask_proof, mask_claim) = zerocheck::prove_packed_padded(
        cast(&p_packed),
        cast(&q_packed),
        cast(&zero_c),
        M,
        &PaddingSpec::dense(M),
        &mut RandomChallenger::new(CH_SEED),
    );

    // Challenges are identical (same seed).
    assert_eq!(main_claim.z, mask_claim.z);
    assert_eq!(main_claim.mlv_challenges, mask_claim.mlv_challenges);
    let r_eq = &main_claim.r_rest; // r[k_skip..]; r_eq[i] used at round i
    let rhos = &main_claim.mlv_challenges;

    // Reconstructed initial claims (= what the real verifier derives).
    let ab_init = recover_init(
        main_claim.a_eval * main_claim.b_eval,
        &main_proof.multilinear_rounds,
        r_eq,
        rhos,
    );
    let sigma_z = recover_init(
        mask_claim.a_eval * mask_claim.b_eval,
        &mask_proof.multilinear_rounds,
        r_eq,
        rhos,
    );

    let gamma = F128 { lo: 0x9E37_79B9, hi: 0x1234_5678 };

    // Combined proof: round1 unmasked (randomizer-covered), mlv round pairs
    // masked by γ·M_j, initial claim shifted by γ·σ_z, final gains γ·P(ρ)Q(ρ).
    let combined_rounds: Vec<(F128, F128)> = main_proof
        .multilinear_rounds
        .iter()
        .zip(&mask_proof.multilinear_rounds)
        .map(|(&(g1, gi), &(m1, mi))| (g1 + gamma * m1, gi + gamma * mi))
        .collect();
    let combined_init = ab_init + gamma * sigma_z;
    let combined_final = telescope(combined_init, &combined_rounds, r_eq, rhos);
    let expected =
        main_claim.a_eval * main_claim.b_eval + gamma * (mask_claim.a_eval * mask_claim.b_eval);
    assert_eq!(
        combined_final, expected,
        "A1′ combined completeness: the combined sumcheck must telescope to \
         final_a·final_b + γ·P(ρ)·Q(ρ)"
    );

    // Soundness: tampering a masked round pair breaks the combined check.
    let mut tampered = combined_rounds.clone();
    tampered[N_MLV / 2].1 += F128::ONE;
    assert_ne!(
        telescope(combined_init, &tampered, r_eq, rhos),
        expected,
        "tampering a masked round pair must break the combined check"
    );
}

#[test]
fn a1_prime_masks_round_pairs() {
    let mut rng = Rng(0xA1B2C3);
    let n = 1 << M;

    // The mask channel is disabled if the OTHER factor is zero: negative
    // control. Q = 0 ⇒ P·Q = 0 ⇒ no round-pair coverage.
    {
        let p = rng.bits(n);
        let q0 = vec![false; n];
        let m = mask_round_pairs(&p, &q0);
        assert!(
            m.iter().all(|&v| v == F128::ZERO),
            "P·0 must give zero mask messages (channel disabled)"
        );
    }

    // For UNIFORM random Q (as A1′ samples it), the map P ↦ round-pairs(P·Q)
    // must be SURJECTIVE onto the full round-pair space — including the ∞
    // (leading-coefficient) coordinates a degree-1 channel cannot reach.
    for qi in 0..3 {
        let q = rng.bits(n);
        let mut img = F2Space::default();
        let full = ROUND_PAIR_VALUES * 128;
        for i in 0..n {
            if img.rank() == full {
                break;
            }
            img.insert(flatten(&mask_round_pairs(&unit(n, i), &q)));
        }
        assert_eq!(
            img.rank(),
            full,
            "uniform Q draw {qi}: P ↦ round-pairs(P·Q) image is rank {} of {full} \
             — round pairs not uniformly masked",
            img.rank()
        );
    }

    // Edge case (documents why Q must be sampled UNIFORMLY, not structured,
    // and motivates the bad-mask probability bound in the proof): a CONSTANT
    // Q has zero slope, so M_j(∞) = Σ eq·ΔP·ΔQ ≡ 0 — the ∞ (leading)
    // coordinates get NO coverage; only the 9 G(1) coordinates are hit. Such
    // Q form a measure-≈0 set the uniform draw avoids w.h.p.
    {
        let q_const = vec![true; n];
        let mut img = F2Space::default();
        for i in 0..n {
            img.insert(flatten(&mask_round_pairs(&unit(n, i), &q_const)));
        }
        assert_eq!(
            img.rank(),
            N_MLV * 128,
            "constant Q should cover exactly the G(1) half ({} bits)",
            N_MLV * 128
        );
    }
}

// ---------------------------------------------------------------------------
// Fact 1 (C4a): final_b breaks the shipped mixture theorem's h_coset on the
// full transcript. EXACT — no sampling in the load-bearing steps.
// ---------------------------------------------------------------------------
#[test]
fn final_b_breaks_full_mixture_hcoset() {
    let r1cs = masked_r1cs();
    let mut rng = Rng(0xC4A);
    let payload = rng.bits(N_PAYLOAD * BLOCKS);
    let ua0 = vec![false; A_BITS];
    let ub0 = vec![false; B_BITS];

    let base = transcript(&r1cs, &witness(&payload, &ua0, &ub0));
    let fb0 = coord(&base, FINAL_B_IDX);

    // (i) final_b VARIES with u_B.
    let ub1 = rng.bits(B_BITS);
    let t_ub1 = transcript(&r1cs, &witness(&payload, &ua0, &ub1));
    let fb1 = coord(&t_ub1, FINAL_B_IDX);
    assert_ne!(fb0, fb1, "final_b must depend on u_B (it is a b-side value)");

    // (ii) final_b has an IDENTICALLY ZERO u_A-derivative: no single-A-bit
    //      flip changes it. This is structural (the b-cube reads A-rand rows
    //      only through the constant-1 wire), verified here over ALL A bits.
    for i in 0..A_BITS {
        let t = transcript(&r1cs, &witness(&payload, &unit(A_BITS, i), &ub0));
        assert_eq!(
            coord(&t, FINAL_B_IDX),
            fb0,
            "A-bit {i} moved final_b — the zero-u_A-derivative claim is false"
        );
    }

    // (iii) Therefore the cross-u_B offset difference b0↔b1 is NOT in the
    //       u_A-image at u_B = ub0: every u_A direction leaves final_b fixed,
    //       so the whole u_A-image has final_b-component 0, while the offset's
    //       final_b-component is fb0 ⊕ fb1 ≠ 0. This is exactly the mixture
    //       theorem's h_coset (∀ b b′, f w b − f w′ b′ ∈ Image A_{u_B})
    //       FAILING on the full transcript. (The shipped conditional
    //       certificate's 6-value subsets never sampled FINAL_B_IDX.)
    let offset_fb = coord_xor(fb0, fb1);
    assert_ne!(offset_fb, [0, 0]);
    // The u_A-image on final_b is {0}; the offset is nonzero ⇒ not covered.
    // (No basis needed: (ii) proved the image is exactly {0} here.)
}

// ---------------------------------------------------------------------------
// Fact 2: the triangular structure is viable — final_b IS covered by the
// B-species (u_B) image, on both witness-difference and cross-u_B offset.
// ~B_BITS probe runs (a few seconds).
// ---------------------------------------------------------------------------
#[test]
fn final_b_covered_by_b_stage() {
    let r1cs = masked_r1cs();
    let mut rng = Rng(0xB57A6E);
    let payload = rng.bits(N_PAYLOAD * BLOCKS);
    let payload2 = rng.bits(N_PAYLOAD * BLOCKS);
    let ua0 = vec![false; A_BITS];
    let ub0 = vec![false; B_BITS];

    let base = transcript(&r1cs, &witness(&payload, &ua0, &ub0));
    let fb_base = coord(&base, FINAL_B_IDX);

    // Build the B-species image on the final_b coordinate.
    let mut img = Coord128Space::default();
    for i in 0..B_BITS {
        let t = transcript(&r1cs, &witness(&payload, &ua0, &unit(B_BITS, i)));
        img.insert(coord_xor(coord(&t, FINAL_B_IDX), fb_base));
    }

    // Witness-difference on final_b lies in the B-image (same masks, other
    // payload).
    let t_w2 = transcript(&r1cs, &witness(&payload2, &ua0, &ub0));
    let wit_diff = coord_xor(coord(&t_w2, FINAL_B_IDX), fb_base);
    assert!(
        img.contains(wit_diff),
        "final_b witness-difference escapes the B-species image"
    );

    // Cross-u_B offset on final_b lies in the B-image too (this is the
    // component the mixture theorem wrongly demanded of the u_A-image).
    let ub1 = rng.bits(B_BITS);
    let t_ub1 = transcript(&r1cs, &witness(&payload, &ua0, &ub1));
    let cross = coord_xor(coord(&t_ub1, FINAL_B_IDX), fb_base);
    assert!(
        img.contains(cross),
        "final_b cross-u_B offset escapes the B-species image"
    );
}

// ---------------------------------------------------------------------------
// Offline: EXACT full-image coverage for the affine transcript classes.
// For an affine map, image-coverage of witness directions IS exact
// distribution equality (no sampling). Excludes the bilinear round pairs
// (128..FINAL_A_IDX), which the amendment/triangular argument handles.
// ~26k probe runs + per-coordinate F₂ elimination; run offline.
// ---------------------------------------------------------------------------
#[test]
#[ignore = "offline exact certificate (~26k prover runs)"]
fn affine_classes_exactly_covered() {
    let r1cs = masked_r1cs();
    let mut rng = Rng(0xAFF14E);
    let payload = rng.bits(N_PAYLOAD * BLOCKS);
    let ua0 = vec![false; A_BITS];
    let ub0 = vec![false; B_BITS];
    let base = transcript(&r1cs, &witness(&payload, &ua0, &ub0));
    let n = base.len();

    // Affine coordinate set: everything except the bilinear round pairs.
    let affine: Vec<usize> = (0..n).filter(|&i| !(128..FINAL_A_IDX).contains(&i)).collect();

    // Per-coordinate mask image over (A-bits ∪ B-bits).
    let mut imgs: Vec<Coord128Space> = (0..n).map(|_| Coord128Space::default()).collect();
    let probe = |mask_a: &[bool], mask_b: &[bool], imgs: &mut Vec<Coord128Space>| {
        let t = transcript(&r1cs, &witness(&payload, mask_a, mask_b));
        for &i in &affine {
            imgs[i].insert(coord_xor(coord(&t, i), coord(&base, i)));
        }
    };
    for i in 0..A_BITS {
        probe(&unit(A_BITS, i), &ub0, &mut imgs);
    }
    for i in 0..B_BITS {
        probe(&ua0, &unit(B_BITS, i), &mut imgs);
    }

    // Affinity gate on the affine coordinates: for random mask pairs the
    // defect must be zero, i.e. the extracted linear map is exact there.
    for _ in 0..64 {
        let ua = rng.bits(A_BITS);
        let ub = rng.bits(B_BITS);
        let t_a = transcript(&r1cs, &witness(&payload, &ua, &ub0));
        let t_b = transcript(&r1cs, &witness(&payload, &ua0, &ub));
        let t_ab = transcript(&r1cs, &witness(&payload, &ua, &ub));
        for &i in &affine {
            let d = coord_xor(
                coord_xor(coord(&t_ab, i), coord(&t_a, i)),
                coord_xor(coord(&t_b, i), coord(&base, i)),
            );
            assert_eq!(d, [0, 0], "affine coordinate {i} shows a bilinear defect");
        }
    }

    // Witness-difference directions lie in the per-coordinate image ⇒ exact
    // distribution equality on every affine coordinate.
    for _ in 0..16 {
        let p2 = rng.bits(N_PAYLOAD * BLOCKS);
        let t = transcript(&r1cs, &witness(&p2, &ua0, &ub0));
        for &i in &affine {
            assert!(
                imgs[i].contains(coord_xor(coord(&t, i), coord(&base, i))),
                "affine coordinate {i}: witness direction escapes the mask image"
            );
        }
    }
}

//! The conditional (fixed-`u_B`) PIOP leakage certificate, plus the affinity
//! structure probes that justify it.
//!
//! `zk_piop_audit.rs` certifies k-wise joint uniformity from random-
//! combination probes over BOTH randomizer species at once. That inference
//! is valid only where the transcript is jointly affine in the masks — which
//! it is for every message class EXCEPT the zerocheck round pairs
//! `(G(1), G(∞))`: round messages evaluate products of folded â·b̂ values,
//! and once a fold group spans the boundary between an A-region and a
//! B-region (or real rows), the products contribute `u_A·u_B` cross terms
//! and witness-dependent coefficients on the masks.
//!
//! The valid argument for that class is conditional. A-rows meet only the
//! constant-1 wire on the b̂-side (and B-rows only on the â-side), so no
//! `u_A·u_A` or `u_B·u_B` terms exist: at any FIXED `u_B` the whole
//! transcript is affine in `u_A`. If for every `(witness, u_B)` the
//! `u_A`-image is the full free space, the transcript is uniform on the same
//! public coset for every `u_B`, and witness-independence of the joint
//! distribution follows by mixing over `u_B` — the mixture masking theorem
//! (`lean/Flockzk/MaskingMixture.lean`). The tests here check its
//! hypotheses on the real prover, on the same fixture and fixed challenges
//! as `zk_piop_audit.rs`:
//!
//! * `affinity_structure_probes` — measures the F₂ affinity defect
//!   `T(u_A⊕u_B) ⊕ T(u_A) ⊕ T(u_B) ⊕ T(0)` and asserts the structure the
//!   certificate relies on: the joint defect and the mask-delta
//!   witness-dependence are confined to the zerocheck round-pair class
//!   (every other class is jointly affine with witness-independent linear
//!   part — those are covered by `zk_piop_audit.rs` and the plain masking
//!   theorem), there are no within-species defects, and at fixed `u_B` the
//!   transcript is affine in `u_A` everywhere.
//! * `repaired_rank_certificate_fixed_ub` — at fixed random `u_B` draws,
//!   random `u_A` probes (now genuinely affine deltas) must reach FULL rank
//!   on sampled value subsets — including one drawn entirely from the
//!   round-pair class — and both the witness-difference directions and the
//!   cross-`u_B` offset differences must lie inside the `u_A`-image. These
//!   are exactly the constant-image and coset-coverage hypotheses of the
//!   mixture theorem.

#![cfg(feature = "zk")]

use flock_core::challenger::{Challenger, RandomChallenger};
use flock_core::field::F128;
use flock_core::lincheck::{self, pack_z_lincheck_from_packed};
use flock_core::pcs::{self, ring_switch};
use flock_core::r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout};
use flock_core::ro::RoContext;
use flock_core::zerocheck;

struct RecordingChallenger<C: Challenger> {
    inner: C,
    observed: Vec<F128>,
}

impl<C: Challenger> Challenger for RecordingChallenger<C> {
    fn ro_context(&self, nonce: [u8; 32]) -> RoContext {
        self.inner.ro_context(nonce)
    }

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

// Same masked-identity fixture as zk_piop_audit.rs (m=15, k_log=12,
// 8 blocks; constant wire, payload, product rows, A- and B-randomizers).
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

/// Run zerocheck + lincheck at fixed challenges; return the full revealed
/// PIOP vector (same layout as zk_piop_audit.rs).
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

use flock_test_util::Rng;
fn xor(t1: &[F128], t0: &[F128]) -> Vec<F128> {
    t1.iter().zip(t0.iter()).map(|(a, b)| *a + *b).collect()
}

/// Zerocheck round-pair value range: `[128, 128 + 2·(M−6))` — index
/// `128 + 2j` / `129 + 2j` is round j's `G(1)` / `G(∞)`.
fn zc_pair_range() -> std::ops::Range<usize> {
    128..128 + 2 * (M - 6)
}

/// Assert `defect` is zero outside the zerocheck round-pair class; return
/// how many round-pair positions are nonzero.
fn assert_confined_to_zc_pairs(name: &str, defect: &[F128]) -> usize {
    let pairs = zc_pair_range();
    let mut in_class = 0usize;
    for (i, v) in defect.iter().enumerate() {
        if *v == F128::ZERO {
            continue;
        }
        assert!(
            pairs.contains(&i),
            "{name}: nonzero defect at transcript index {i}, outside the \
             zerocheck round-pair class — a message class believed jointly \
             affine is not"
        );
        in_class += 1;
    }
    println!(
        "{name}: {in_class}/{} round-pair positions nonzero",
        pairs.len()
    );
    in_class
}

/// Structure probes: the affinity defects and mask-map witness-dependence
/// are confined to the zerocheck round pairs; no within-species defects;
/// at fixed `u_B` the transcript is affine in `u_A` everywhere.
#[test]
fn affinity_structure_probes() {
    let r1cs = masked_r1cs();
    let mut rng = Rng(0xA111);
    let p0 = rng.bits(N_PAYLOAD * BLOCKS);
    let p1 = rng.bits(N_PAYLOAD * BLOCKS);
    let ua0 = vec![false; A_BITS];
    let ub0 = vec![false; B_BITS];
    let ua1 = rng.bits(A_BITS);
    let ua2 = rng.bits(A_BITS);
    let ub1 = rng.bits(B_BITS);
    let ub2 = rng.bits(B_BITS);
    let x = |a: &[bool], b: &[bool]| -> Vec<bool> {
        a.iter().zip(b.iter()).map(|(x, y)| x ^ y).collect()
    };
    let t = |p: &[bool], ua: &[bool], ub: &[bool]| transcript(&r1cs, &witness(p, ua, ub));

    let base = t(&p0, &ua0, &ub0);
    let n = base.len();

    // Cross-species affinity defect: bilinear u_A·u_B terms live in the
    // round pairs and nowhere else. (If this count ever drops to zero the
    // transcript has become jointly affine and the unconditional audit in
    // zk_piop_audit.rs covers everything on its own.)
    let d_a = xor(&t(&p0, &ua1, &ub0), &base);
    let d_b = xor(&t(&p0, &ua0, &ub1), &base);
    let d_ab = xor(&t(&p0, &ua1, &ub1), &base);
    let defect: Vec<F128> = (0..n).map(|i| d_ab[i] + d_a[i] + d_b[i]).collect();
    let nz = assert_confined_to_zc_pairs("A x B affinity defect", &defect);
    assert!(
        nz > 0,
        "expected bilinear round-pair terms; structure changed"
    );

    // No within-species cross terms: A-rows only ever meet the constant-1
    // wire on the b̂-side, and symmetrically for B-rows.
    let d_a2 = xor(&t(&p0, &ua2, &ub0), &base);
    let d_a12 = xor(&t(&p0, &x(&ua1, &ua2), &ub0), &base);
    for i in 0..n {
        assert_eq!(
            d_a12[i] + d_a[i] + d_a2[i],
            F128::ZERO,
            "A x A defect at {i}"
        );
    }
    let d_b2 = xor(&t(&p0, &ua0, &ub2), &base);
    let d_b12 = xor(&t(&p0, &ua0, &x(&ub1, &ub2)), &base);
    for i in 0..n {
        assert_eq!(
            d_b12[i] + d_b[i] + d_b2[i],
            F128::ZERO,
            "B x B defect at {i}"
        );
    }

    // Witness-dependence of the mask→transcript map is likewise confined to
    // the round pairs (everywhere else the linear part is witness-
    // independent, as the plain masking theorem requires).
    let base1 = t(&p1, &ua0, &ub0);
    let d_a_w1 = xor(&t(&p1, &ua1, &ub0), &base1);
    let defect_w: Vec<F128> = (0..n).map(|i| d_a_w1[i] + d_a[i]).collect();
    assert_confined_to_zc_pairs("A-species mask-delta witness-dependence", &defect_w);
    let d_b_w1 = xor(&t(&p1, &ua0, &ub1), &base1);
    let defect_wb: Vec<F128> = (0..n).map(|i| d_b_w1[i] + d_b[i]).collect();
    assert_confined_to_zc_pairs("B-species mask-delta witness-dependence", &defect_wb);

    // The certificate's affinity hypothesis: at fixed nonzero u_B the
    // transcript is affine in u_A — everywhere, round pairs included.
    let base_c = t(&p0, &ua0, &ub1);
    let c_a1 = xor(&t(&p0, &ua1, &ub1), &base_c);
    let c_a2 = xor(&t(&p0, &ua2, &ub1), &base_c);
    let c_a12 = xor(&t(&p0, &x(&ua1, &ua2), &ub1), &base_c);
    for i in 0..n {
        assert_eq!(
            c_a12[i] + c_a1[i] + c_a2[i],
            F128::ZERO,
            "A x A defect at fixed u_B, index {i}"
        );
    }
}

/// F₂ row-reduce; returns rank.
fn rank_f2(rows: &mut [Vec<u64>], dim: usize) -> usize {
    let mut rank = 0usize;
    for bit in 0..dim {
        let (w, msk) = (bit / 64, 1u64 << (bit % 64));
        let Some(p) = (rank..rows.len()).find(|&r| rows[r][w] & msk != 0) else {
            continue;
        };
        rows.swap(rank, p);
        let pivot = rows[rank].clone();
        for (r, row) in rows.iter_mut().enumerate() {
            if r != rank && row[w] & msk != 0 {
                for k in 0..row.len() {
                    row[k] ^= pivot[k];
                }
            }
        }
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    rank
}

fn restrict(delta: &[F128], subset: &[usize]) -> Vec<u64> {
    let mut out = vec![0u64; subset.len() * 2];
    for (k, &vi) in subset.iter().enumerate() {
        out[2 * k] = delta[vi].lo;
        out[2 * k + 1] = delta[vi].hi;
    }
    out
}

/// The conditional rank certificate: hold `u_B` fixed, so the `u_A`-probe
/// deltas are genuinely affine and full rank IS a valid inference of
/// conditional joint uniformity; then check the mixture theorem's
/// constant-image and coset-coverage hypotheses across `u_B` draws.
#[test]
fn repaired_rank_certificate_fixed_ub() {
    const SUBSET_VALUES: usize = 6;
    const SUBSET_DIM: usize = SUBSET_VALUES * 128;
    const N_PROBES: usize = SUBSET_DIM + 340;

    let r1cs = masked_r1cs();
    let mut rng = Rng(0xF1CED);
    let p0 = rng.bits(N_PAYLOAD * BLOCKS);
    let p1 = rng.bits(N_PAYLOAD * BLOCKS);

    let mut prev_base: Option<Vec<F128>> = None;
    for trial in 0..2 {
        let ub_fixed = rng.bits(B_BITS);
        let base = transcript(&r1cs, &witness(&p0, &vec![false; A_BITS], &ub_fixed));
        let n = base.len();

        let mut rand_deltas = Vec::with_capacity(N_PROBES);
        for _ in 0..N_PROBES {
            let ua = rng.bits(A_BITS);
            let t = transcript(&r1cs, &witness(&p0, &ua, &ub_fixed));
            rand_deltas.push(xor(&t, &base));
        }
        // Witness delta at the SAME fixed u_B.
        let wit_delta = xor(
            &transcript(&r1cs, &witness(&p1, &vec![false; A_BITS], &ub_fixed)),
            &base,
        );

        // Subsets: one per-class spread (as in zk_piop_audit.rs) plus one
        // drawn entirely from the round-pair class — the class the
        // unconditional audit cannot validly certify.
        let pairs = zc_pair_range();
        let s_hat_ab = n - 128;
        let s_hat_c = n - 256;
        let z_partial = n - 258 - 64;
        let spread: Vec<usize> = vec![
            (rng.next_u64() as usize) % 64,
            64 + (rng.next_u64() as usize) % 64,
            pairs.start + (rng.next_u64() as usize) % pairs.len(),
            z_partial + (rng.next_u64() as usize) % 64,
            s_hat_c + (rng.next_u64() as usize) % 128,
            s_hat_ab + (rng.next_u64() as usize) % 128,
        ];
        let mut pure_zc: Vec<usize> = Vec::new();
        while pure_zc.len() < SUBSET_VALUES {
            let i = pairs.start + (rng.next_u64() as usize) % pairs.len();
            if !pure_zc.contains(&i) {
                pure_zc.push(i);
            }
        }

        for (label, subset) in [
            ("per-class spread", &spread),
            ("pure zc_round_pair", &pure_zc),
        ] {
            let mut rows: Vec<Vec<u64>> = rand_deltas.iter().map(|d| restrict(d, subset)).collect();
            let rank = rank_f2(&mut rows, SUBSET_DIM);
            println!("trial {trial} [{label}] rank = {rank}/{SUBSET_DIM}");
            assert_eq!(rank, SUBSET_DIM, "trial {trial} [{label}]: not full rank");

            let mut with_wit: Vec<Vec<u64>> = rand_deltas
                .iter()
                .chain(std::iter::once(&wit_delta))
                .map(|d| restrict(d, subset))
                .collect();
            assert_eq!(
                rank_f2(&mut with_wit, SUBSET_DIM),
                SUBSET_DIM,
                "trial {trial} [{label}]: witness delta escapes the u_A-image"
            );

            // Cross-slice coset condition (the b ≠ b′ case of the mixture
            // theorem's h_coset): the offset difference between two
            // fixed-u_B slices must also lie in the u_A-image.
            if let Some(pb) = &prev_base {
                let cross = xor(&base, pb);
                let mut with_cross: Vec<Vec<u64>> = rand_deltas
                    .iter()
                    .chain(std::iter::once(&cross))
                    .map(|d| restrict(d, subset))
                    .collect();
                assert_eq!(
                    rank_f2(&mut with_cross, SUBSET_DIM),
                    SUBSET_DIM,
                    "trial {trial} [{label}]: cross-u_B offset escapes the u_A-image"
                );
            }
        }
        prev_base = Some(base);
    }
}

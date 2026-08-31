//! Affinity structure probe for the conditional masked PIOP argument.
//!
//! The full rank audit now lives in `flock_core`, but it relies on a structural
//! fact: outside the zerocheck round-pair class the revealed PIOP transcript is
//! jointly affine in the two randomizer species, and at fixed B-randomizers it
//! is affine in A-randomizers everywhere. This test checks that fact on the
//! current prover APIs with a synthetic masked-identity fixture.

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

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.inner.sample_f128_vec(n)
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

fn f128_bytes(values: &[F128]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(values.len() * 16);
    for value in values {
        bytes.extend_from_slice(&value.lo.to_le_bytes());
        bytes.extend_from_slice(&value.hi.to_le_bytes());
    }
    bytes
}

fn transcript(r1cs: &BlockR1cs, z_packed: &[F128]) -> Vec<F128> {
    let a_packed = r1cs.apply_a_packed(z_packed);
    let b_packed = r1cs.apply_b_packed(z_packed);
    let a_bytes = f128_bytes(&a_packed);
    let b_bytes = f128_bytes(&b_packed);
    let z_bytes = f128_bytes(z_packed);
    let stripe = pack_z_lincheck_from_packed(z_packed, M, K_LOG);
    let padding = r1cs.padding_spec();

    let mut ch = RecordingChallenger {
        inner: RandomChallenger::new(CH_SEED),
        observed: Vec::new(),
    };
    let (_zc_proof, zc_claim, s_hat_v_c) = zerocheck::prove_packed_padded_capture_s_hat_v_c(
        &a_bytes, &b_bytes, &z_bytes, M, &padding, &mut ch,
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
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.next_u64() & 1 == 1).collect()
    }
}

fn xor(t1: &[F128], t0: &[F128]) -> Vec<F128> {
    t1.iter().zip(t0.iter()).map(|(a, b)| *a + *b).collect()
}

fn zc_pair_range() -> std::ops::Range<usize> {
    128..128 + 2 * (M - 6)
}

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
             zerocheck round-pair class"
        );
        in_class += 1;
    }
    in_class
}

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

    let d_a = xor(&t(&p0, &ua1, &ub0), &base);
    let d_b = xor(&t(&p0, &ua0, &ub1), &base);
    let d_ab = xor(&t(&p0, &ua1, &ub1), &base);
    let defect: Vec<F128> = (0..n).map(|i| d_ab[i] + d_a[i] + d_b[i]).collect();
    let nz = assert_confined_to_zc_pairs("A x B affinity defect", &defect);
    assert!(nz > 0, "expected bilinear zerocheck round-pair terms");

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

    let base1 = t(&p1, &ua0, &ub0);
    let d_a_w1 = xor(&t(&p1, &ua1, &ub0), &base1);
    let defect_w: Vec<F128> = (0..n).map(|i| d_a_w1[i] + d_a[i]).collect();
    assert_confined_to_zc_pairs("A-species witness-dependence", &defect_w);
    let d_b_w1 = xor(&t(&p1, &ua0, &ub1), &base1);
    let defect_wb: Vec<F128> = (0..n).map(|i| d_b_w1[i] + d_b[i]).collect();
    assert_confined_to_zc_pairs("B-species witness-dependence", &defect_wb);

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

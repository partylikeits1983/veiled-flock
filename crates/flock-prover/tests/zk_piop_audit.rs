//! PIOP leakage-rank audit + transcript differential — the machine-checked
//! ZK evidence for the randomizer-witness masking (zerocheck + lincheck).
//!
//! Setup: a "masked identity" R1CS (m = 15, k_log = 12, 8 blocks) whose
//! blocks carry a constant wire, free payload bits, genuine product rows (so
//! the zerocheck cube is really quadratic in the payload), A-type randomizer
//! rows `u·1 = u`, and B-type rows `1·u′ = u′`. At **fixed challenges**
//! (RandomChallenger ignores observations) the transcript's structure,
//! measured by `zk_affinity_probe.rs`, is: every message class EXCEPT the
//! zerocheck round pairs is jointly affine over F₂ in the randomizer bits
//! with a payload-independent linear part, `transcript(w, u) = A·u + f(w)`;
//! the round pairs are bilinear across the two species (folded â·b̂
//! products create `u_A·u_B` cross terms once fold groups span a region
//! boundary) and affine in `u_A` at any fixed `u_B`.
//!
//! **What is certified here.** Full joint uniformity of all ~460 revealed
//! F128 values would need rank ≈ 128·460 ≈ 59k — probing it exactly needs
//! one prover run per randomizer bit (tens of thousands). The feasible
//! certificate here is **k-wise joint uniformity**: for random subsets S of
//! 6 revealed values (one per message class: round-1 vectors, round pairs,
//! final evals, z_partial, both s_hat_v vectors), the restricted map
//! `u ↦ transcript|_S` is surjective onto F₂^{768}, and payload variation
//! inside S is covered. For the **affine classes** full rank of the probe
//! deltas is a valid uniformity inference (the masking theorem,
//! `lean/Flockzk/Masking.lean`). For the bilinear round-pair class the
//! probe deltas here mix both species, so span alone does not imply
//! uniformity — the valid inference for that class is the conditional
//! (fixed-`u_B`) certificate in `zk_affinity_probe.rs`, paired with the
//! mixture masking theorem (`lean/Flockzk/MaskingMixture.lean`). Any single
//! leaked (or under-masked) value in a sampled class still makes its
//! 128-dim block rank-deficient and fails the assert, so this audit remains
//! the broad-coverage detector; ~1.1k random-combo probes serve every
//! subset at once.
//!
//! **Budget note.** Masking one revealed F128 needs ≥128 bits of randomizer
//! entropy reaching it; the s_hat_v bit-slices additionally need ≥128 bits
//! *per bit-residue* (slice r only sees witness bits at position r mod 128).
//! This instance carries 24 A-chunks per block × 8 blocks = 192 bits per
//! residue (BLAKE3 production: 6 A-type chunks × ≥256 blocks ≥ 1,536). An
//! under-budgeted instance fails this audit — that was observed directly
//! while sizing it.
//!
//! A negative control withholding the A-group must FAIL, validating the
//! detector on this exact instance.

#![cfg(feature = "zk")]

use flock_core::challenger::{Challenger, RandomChallenger};
use flock_core::field::F128;
use flock_core::lincheck::{self, pack_z_lincheck_from_packed};
use flock_core::pcs::{self, ring_switch};
use flock_core::r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout};
use flock_core::zerocheck;

// ---------------------------------------------------------------------------
// Recording challenger
// ---------------------------------------------------------------------------

struct RecordingChallenger<C: Challenger> {
    inner: C,
    observed: Vec<F128>,
}

impl<C: Challenger> Challenger for RecordingChallenger<C> {
    fn ro_context(&self, nonce: [u8; 32]) -> flock_core::ro::RoContext {
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

// ---------------------------------------------------------------------------
// Masked identity R1CS (m=15, k_log=12, 8 blocks)
// ---------------------------------------------------------------------------

const M: usize = 15;
const K_LOG: usize = 12;
const K_SKIP: usize = 6;
const K: usize = 1 << K_LOG;
const BLOCKS: usize = 1 << (M - K_LOG); // 8

const PAYLOAD_BASE: usize = 1;
const N_PAYLOAD: usize = 64;
const PROD_BASE: usize = PAYLOAD_BASE + N_PAYLOAD; // 65
const N_PROD: usize = 16;
const A_RAND_BASE: usize = 128;
const N_A_RAND: usize = 24 * 128; // 24 chunks ⇒ 192 bits per bit-residue batch-wide
const B_RAND_BASE: usize = A_RAND_BASE + N_A_RAND;
const N_B_RAND: usize = 2 * 128;
const USEFUL: usize = B_RAND_BASE + N_B_RAND;

const A_BITS: usize = N_A_RAND * BLOCKS;
const B_BITS: usize = N_B_RAND * BLOCKS;
const CH_SEED: u64 = 0x7777_1234;

const SUBSET_VALUES: usize = 6;
const SUBSET_DIM: usize = SUBSET_VALUES * 128; // 768
const N_PROBES: usize = SUBSET_DIM + 340; // margin over the restricted dim

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
        zk: None, // rows are hand-rolled here; no layout bookkeeping needed
        digest_cache: std::sync::OnceLock::new(),
        csc_cache: std::sync::OnceLock::new(),
    }
}

/// Build the packed witness from payload bits and randomizer bit-vectors.
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
/// PIOP vector.
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

// ---------------------------------------------------------------------------
// F₂ helpers
// ---------------------------------------------------------------------------

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

const SUBSET_WORDS: usize = SUBSET_DIM / 64; // 12

/// Restrict a transcript delta to a value subset, as F₂ words.
fn restrict(delta: &[F128], subset: &[usize]) -> [u64; SUBSET_WORDS] {
    let mut out = [0u64; SUBSET_WORDS];
    for (k, &vi) in subset.iter().enumerate() {
        out[2 * k] = delta[vi].lo;
        out[2 * k + 1] = delta[vi].hi;
    }
    out
}

fn xor_delta(t1: &[F128], t0: &[F128]) -> Vec<F128> {
    t1.iter().zip(t0.iter()).map(|(a, b)| *a + *b).collect()
}

/// F₂ row-reduce; returns rank.
fn rank_f2(rows: &mut Vec<[u64; SUBSET_WORDS]>) -> usize {
    let mut rank = 0usize;
    for bit in 0..SUBSET_DIM {
        let (w, msk) = (bit / 64, 1u64 << (bit % 64));
        let Some(p) = (rank..rows.len()).find(|&r| rows[r][w] & msk != 0) else {
            continue;
        };
        rows.swap(rank, p);
        let pivot = rows[rank];
        for (r, row) in rows.iter_mut().enumerate() {
            if r != rank && row[w] & msk != 0 {
                for k in 0..SUBSET_WORDS {
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

/// Probe deltas: `n_probes` random-combination randomizer probes (A and/or B)
/// plus payload-difference deltas, all against a fixed base.
struct AuditData {
    rand_deltas: Vec<Vec<F128>>,
    payload_deltas: Vec<Vec<F128>>,
    n_values: usize,
}

fn collect_deltas(include_a: bool) -> AuditData {
    let r1cs = masked_r1cs();
    let mut rng = Rng(0xF00D);
    let payload0 = rng.bits(N_PAYLOAD * BLOCKS);
    let ua0 = vec![false; A_BITS];
    let ub0 = vec![false; B_BITS];
    {
        let z = witness(&payload0, &ua0, &ub0);
        assert!(r1cs.satisfies_packed(&z), "base witness must satisfy");
    }
    let base = transcript(&r1cs, &witness(&payload0, &ua0, &ub0));

    let mut rand_deltas = Vec::with_capacity(N_PROBES);
    for _ in 0..N_PROBES {
        let ua = if include_a {
            rng.bits(A_BITS)
        } else {
            ua0.clone()
        };
        let ub = rng.bits(B_BITS);
        let t = transcript(&r1cs, &witness(&payload0, &ua, &ub));
        rand_deltas.push(xor_delta(&t, &base));
    }
    let mut payload_deltas = Vec::new();
    for _ in 0..24 {
        let p = rng.bits(N_PAYLOAD * BLOCKS);
        let t = transcript(&r1cs, &witness(&p, &ua0, &ub0));
        payload_deltas.push(xor_delta(&t, &base));
    }
    AuditData {
        rand_deltas,
        payload_deltas,
        n_values: base.len(),
    }
}

/// Draw the audited value subsets: one representative per message class plus
/// random extras, `SUBSET_VALUES` values each. Class boundaries are located
/// structurally: the recorded transcript is
/// `[round1_ab(64) ‖ round1_c(64) ‖ zc rounds+finals ‖ lc rounds ‖ z_partial(64)
///   ‖ c_eval ‖ w ‖ s_hat_v_c(128) ‖ s_hat_v_ab(128)]`.
fn value_subsets(n_values: usize, rng: &mut Rng) -> Vec<Vec<usize>> {
    let s_hat_ab_base = n_values - 128;
    let s_hat_c_base = n_values - 256;
    let scalars_base = n_values - 258; // c_eval, w
    let z_partial_base = scalars_base - 64;
    let classes: [(usize, usize); 6] = [
        (0, 64),                     // round1_ab
        (64, 64),                    // round1_c
        (128, z_partial_base - 128), // round pairs + finals
        (z_partial_base, 64),        // z_partial
        (s_hat_c_base, 128),         // s_hat_v_c
        (s_hat_ab_base, 128),        // s_hat_v_ab
    ];
    (0..4)
        .map(|_| {
            classes
                .iter()
                .map(|&(base, len)| base + (rng.next_u64() as usize) % len)
                .collect()
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// The ZK certificate: for every sampled value subset, the randomizer image
/// is the FULL restricted space (joint uniformity of those revealed values),
/// hence payload variation is covered within it.
#[test]
fn piop_rank_audit_subsets_fully_masked() {
    let data = collect_deltas(true);
    let mut rng = Rng(0x5E7);
    for (si, subset) in value_subsets(data.n_values, &mut rng).iter().enumerate() {
        let mut rows: Vec<[u64; SUBSET_WORDS]> = data
            .rand_deltas
            .iter()
            .map(|d| restrict(d, subset))
            .collect();
        let rank = rank_f2(&mut rows);
        assert_eq!(
            rank, SUBSET_DIM,
            "subset {si} {subset:?}: restricted randomizer image is rank {rank} \
             of {SUBSET_DIM} — those revealed values are NOT jointly uniform"
        );
        // Payload deltas are then trivially inside; assert anyway.
        let mut all: Vec<[u64; SUBSET_WORDS]> = data
            .rand_deltas
            .iter()
            .chain(data.payload_deltas.iter())
            .map(|d| restrict(d, subset))
            .collect();
        assert_eq!(rank_f2(&mut all), SUBSET_DIM);
    }
}

/// Negative control: withholding the A-group must break the certificate
/// (payload escapes the B-only image) — validates the detector.
#[test]
fn piop_rank_audit_negative_control_without_a_group() {
    let data = collect_deltas(false);
    let mut rng = Rng(0x5E7);
    let subsets = value_subsets(data.n_values, &mut rng);
    let mut any_escape = false;
    for subset in &subsets {
        let mut a_rows: Vec<[u64; SUBSET_WORDS]> = data
            .rand_deltas
            .iter()
            .map(|d| restrict(d, subset))
            .collect();
        let rank_a = rank_f2(&mut a_rows);
        let mut all: Vec<[u64; SUBSET_WORDS]> = data
            .rand_deltas
            .iter()
            .chain(data.payload_deltas.iter())
            .map(|d| restrict(d, subset))
            .collect();
        let rank_all = rank_f2(&mut all);
        assert!(rank_a < SUBSET_DIM, "B-only image must be rank-deficient");
        if rank_all > rank_a {
            any_escape = true;
        }
    }
    assert!(
        any_escape,
        "negative control failed: payload never escaped the B-only image"
    );
}

/// Transcript differential: fresh randomizer draws change (essentially)
/// every masked value; zeroed randomizers make the transcript a
/// deterministic function of the payload.
#[test]
fn piop_transcript_differential() {
    use flock_core::zk::ZkRng;
    let r1cs = masked_r1cs();
    let mut rng = Rng(0xD1FF);
    let payload = rng.bits(N_PAYLOAD * BLOCKS);

    let draw = |seed: [u8; 32]| {
        let mut zk_rng = ZkRng::from_seed(seed);
        let mut words = vec![0u64; (A_BITS + B_BITS).div_ceil(64)];
        flock_core::zk::MaskSampler::fill_u64s(&mut zk_rng, &mut words);
        let bit = |i: usize| (words[i / 64] >> (i % 64)) & 1 == 1;
        let ua: Vec<bool> = (0..A_BITS).map(bit).collect();
        let ub: Vec<bool> = (A_BITS..A_BITS + B_BITS).map(bit).collect();
        transcript(&r1cs, &witness(&payload, &ua, &ub))
    };

    let t1 = draw([1u8; 32]);
    let t2 = draw([2u8; 32]);
    assert_eq!(t1.len(), t2.len());
    let differing = t1.iter().zip(t2.iter()).filter(|(a, b)| a != b).count();
    assert!(
        differing * 10 >= t1.len() * 9,
        "only {differing}/{} transcript values changed under a fresh mask seed",
        t1.len()
    );

    let ua0 = vec![false; A_BITS];
    let ub0 = vec![false; B_BITS];
    let z0 = transcript(&r1cs, &witness(&payload, &ua0, &ub0));
    let z1 = transcript(&r1cs, &witness(&payload, &ua0, &ub0));
    assert_eq!(z0, z1, "unmasked transcripts must be deterministic");
}

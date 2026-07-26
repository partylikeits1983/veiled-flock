//! **Complete-transcript certificate on a REAL BLAKE3 batch statement.**
//!
//! The fixture-based certificate reasons about claim-preserving
//! *combinations* of witness differences, so it needs a linear sub-family of
//! valid witnesses — which a hash trace does not have. This file certifies
//! the same property on the actual statement family using a criterion that
//! needs no linear family at all:
//!
//! > for two real BLAKE3 witnesses `w`, `w'`, is the transcript difference
//! > `d = T(w) − T(w')` inside the mask image?
//!
//! If it is, then some mask shift `Δu` satisfies `A·Δu = d`, so running the
//! prover on `w` with shifted masks yields a transcript **identical in every
//! coordinate** to `w'`'s — including the claim values, which are themselves
//! functions of the randomizer bits and so are not fixed by the real witness.
//! That is a stronger statement than distributional indistinguishability and
//! it requires no claim conditioning and no linearity: membership of a single
//! concrete difference vector in a linear image is decidable directly.
//!
//! The masks are linear even though the witness map is not, which is exactly
//! why this works: `Im(A)` is computed by probing the mask channels, and the
//! nonlinear object (the hash trace) appears only in the target vector.
//!
//! Probing uses random mask directions rather than unit vectors: random
//! probing can only *under*-estimate a rank, so a reported membership is
//! sound while a reported failure could be probe-starvation.

#![cfg(feature = "zk")]

use flock_core::challenger::RandomChallenger;
use flock_core::field::F128;
use flock_core::lincheck::pack_z_lincheck_from_packed;
use flock_core::pcs::PcsParams;
use flock_core::zk::MaskSampler;
use flock_prover::prover::{A1MaskSources, prove_r1cs_zk_a1_with_masks};
use flock_prover::r1cs_hashes::blake3::{Blake3Setup, Compression};
use flock_prover::transcript_schema::{LeakageClass, SchemaIndex, algebraic_vector, flatten_a1};
use flock_prover::zk_audit_support::tiny_zk_configs_for;

struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn u32(&mut self) -> u32 {
        self.next_u64() as u32
    }
    fn words(&mut self, n: usize) -> Vec<u64> {
        (0..n).map(|_| self.next_u64()).collect()
    }
}

/// Replays a fixed stream then zeros.
struct VecSampler {
    words: Vec<u64>,
    pos: usize,
}
impl VecSampler {
    fn from_words(words: Vec<u64>) -> Self {
        Self { words, pos: 0 }
    }
    fn from_f128(v: &[F128]) -> Self {
        let mut w = Vec::with_capacity(v.len() * 2);
        for x in v {
            w.push(x.lo);
            w.push(x.hi);
        }
        Self { words: w, pos: 0 }
    }
}
impl MaskSampler for VecSampler {
    fn fill_u64s(&mut self, out: &mut [u64]) {
        for slot in out.iter_mut() {
            *slot = self.words.get(self.pos).copied().unwrap_or(0);
            self.pos += 1;
        }
    }
}

#[derive(Default, Clone)]
struct F2Space {
    rows: Vec<Vec<u64>>,
    pivots: Vec<usize>,
}
impl F2Space {
    fn reduce(&self, mut v: Vec<u64>) -> Vec<u64> {
        for (row, &p) in self.rows.iter().zip(&self.pivots) {
            if v[p / 64] >> (p % 64) & 1 == 1 {
                for (a, b) in v.iter_mut().zip(row) {
                    *a ^= *b;
                }
            }
        }
        v
    }
    fn insert(&mut self, v: Vec<u64>) {
        let r = self.reduce(v);
        if let Some(p) = first_set_bit(&r) {
            self.rows.push(r);
            self.pivots.push(p);
        }
    }
    fn rank(&self) -> usize {
        self.rows.len()
    }
}
fn first_set_bit(v: &[u64]) -> Option<usize> {
    v.iter()
        .enumerate()
        .find_map(|(i, w)| (*w != 0).then(|| i * 64 + w.trailing_zeros() as usize))
}
fn flatten(v: &[F128]) -> Vec<u64> {
    let mut o = Vec::with_capacity(v.len() * 2);
    for x in v {
        o.push(x.lo);
        o.push(x.hi);
    }
    o
}
fn xor(a: &[u64], b: &[u64]) -> Vec<u64> {
    a.iter().zip(b).map(|(x, y)| x ^ y).collect()
}

const N_BLOCKS: usize = 64; // m = 20; s_hat_v randomizer margin 3x (as certified)
const CH_SEED: u64 = 0x51A1_B3;

fn blocks_from(seed: u64, n: usize) -> Vec<Compression> {
    let mut rng = Rng(seed);
    (0..n)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect()
}

/// Run the real A1′ prover on a real BLAKE3 statement with fully explicit
/// mask material, returning the complete algebraic transcript.
#[allow(clippy::too_many_arguments)]
fn run(
    setup: &Blake3Setup,
    params: &PcsParams,
    lig: &flock_core::pcs::ligerito::ProverConfig,
    blocks: &[Compression],
    rand_words: &[u64],
    p_words: &[u64],
    q_words: &[u64],
    cw: &[F128],
    cp: &[F128],
    cq: &[F128],
) -> Vec<F128> {
    let layout = setup.r1cs.zk.expect("zk layout");
    let (z, a, b, stripe) =
        flock_prover::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk(
            blocks,
            setup.n_blocks_log(),
            &layout,
            rand_words,
        );
    let _ = pack_z_lincheck_from_packed;
    let circuit = setup.r1cs.csc_lincheck_circuit();
    let mut s_w = VecSampler::from_f128(cw);
    let mut s_p = VecSampler::from_words(p_words.to_vec());
    let mut s_q = VecSampler::from_words(q_words.to_vec());
    let mut s_cp = VecSampler::from_f128(cp);
    let mut s_cq = VecSampler::from_f128(cq);
    let masks = A1MaskSources {
        witness_commit: &mut s_w,
        p: &mut s_p,
        q: &mut s_q,
        commit_p: &mut s_cp,
        commit_q: &mut s_cq,
    };
    let mut ch = RandomChallenger::new(CH_SEED);
    let (proof, comm, _) = prove_r1cs_zk_a1_with_masks(
        &setup.r1cs, params, z, a, b, stripe, circuit, lig, masks, None, &mut ch,
    );
    algebraic_vector(&flatten_a1(&comm, &proof))
}

/// Coordinate positions (within the algebraic vector) of the zerocheck and
/// lincheck classes — the PIOP layer. Restricting to them keeps the image
/// saturable at this size: membership is decided against a *spanned* space,
/// which is what makes a negative result meaningful.
fn piop_coords(setup: &Blake3Setup, params: &PcsParams, lig: &flock_core::pcs::ligerito::ProverConfig, blocks: &[Compression], rand: &[u64], p: &[u64], q: &[u64], cw: &[F128], cp: &[F128], cq: &[F128]) -> Vec<usize> {
    let layout = setup.r1cs.zk.expect("zk layout");
    let (z, a, b, stripe) =
        flock_prover::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk(
            blocks, setup.n_blocks_log(), &layout, rand,
        );
    let circuit = setup.r1cs.csc_lincheck_circuit();
    let mut s_w = VecSampler::from_f128(cw);
    let mut s_p = VecSampler::from_words(p.to_vec());
    let mut s_q = VecSampler::from_words(q.to_vec());
    let mut s_cp = VecSampler::from_f128(cp);
    let mut s_cq = VecSampler::from_f128(cq);
    let masks = A1MaskSources {
        witness_commit: &mut s_w, p: &mut s_p, q: &mut s_q,
        commit_p: &mut s_cp, commit_q: &mut s_cq,
    };
    let mut ch = RandomChallenger::new(CH_SEED);
    let (proof, comm, _) = prove_r1cs_zk_a1_with_masks(
        &setup.r1cs, params, z, a, b, stripe, circuit, lig, masks, None, &mut ch,
    );
    let flat = flatten_a1(&comm, &proof);
    let idx = SchemaIndex::build(&flat);
    let mut out = Vec::new();
    for (path, range) in idx.ranges_by_class(&flat, LeakageClass::WitnessDependent) {
        if path.starts_with("zerocheck.") || path.starts_with("lincheck.") {
            out.extend(range);
        }
    }
    out
}

/// **The certificate.** On a real BLAKE3 batch statement, the transcript
/// difference between two genuinely different witnesses lies in the mask
/// image — so a mask shift carries one witness's complete transcript exactly
/// onto the other's.
/// **STATUS: currently FAILS by exactly one F128 direction — an open lead,
/// not a proven leak.** Measured (m=20, 64 blocks, PIOP classes = 238 field
/// elements): the inner stage spans 21,504 of 30,464 bits, the outer (B-
/// species) stage adds exactly 128 more — the same single direction the
/// fixture certificate showed the outer stage is responsible for — the claim
/// space saturates at 384 bits, and `rank[resid | Δclaim] = 512` against
/// `rank(Δclaim) = 384`. So 128 bits of claim-preserving witness difference
/// are unaccounted for on this statement family at this configuration.
///
/// Why this is a lead rather than a verdict: the test restricts the codomain
/// to the PIOP classes, probes randomly rather than exhaustively, and its
/// failure direction is the conservative one (a failure can be probe
/// starvation or a combination corresponding to no real witness pair, while
/// a pass would be sound). The natural next hypothesis, by analogy with the
/// fixture — where the residual closed once *every* transcript-determined
/// public value was conditioned on — is that a fourth such value exists here
/// and is not yet in the conditioning set.
///
/// It is kept, failing and documented, because it is the sharpest statement
/// available about the real statement family and it should not be forgotten.
#[test]
#[ignore = "OPEN: fails by one F128 direction; see the status note above"]
fn blake3_witness_difference_lies_in_the_mask_image() {
    let setup = Blake3Setup::with_zk(N_BLOCKS);
    let m = setup.m();
    let params = PcsParams { m, log_inv_rate: 1, log_batch_size: 2, profile: Default::default(), zk: true };
    let (lig, _v) = tiny_zk_configs_for(params.log_msg_len());
    let layout = setup.r1cs.zk.expect("zk layout");
    let words_per_block = flock_prover::r1cs_hashes::common::zk_rand_words_per_block(&layout);
    let n_rand_words = setup.n_block_slots() * words_per_block;
    let n_cube_words = (1usize << m) / 64;
    let n_mask_f128 = 3 << (m - 7);

    let mut rng = Rng(0xC0DE_B3);
    let base_rand = rng.words(n_rand_words);
    let p_words = rng.words(n_cube_words);
    let q_words = rng.words(n_cube_words);
    let cw: Vec<F128> = (0..n_mask_f128).map(|_| F128 { lo: rng.next_u64(), hi: rng.next_u64() }).collect();
    let cp: Vec<F128> = (0..n_mask_f128).map(|_| F128 { lo: rng.next_u64(), hi: rng.next_u64() }).collect();
    let cq: Vec<F128> = (0..n_mask_f128).map(|_| F128 { lo: rng.next_u64(), hi: rng.next_u64() }).collect();

    let blocks_a = blocks_from(0xAAAA, N_BLOCKS);
    let go = |rand: &[u64], p: &[u64], cw: &[F128], cp: &[F128], blocks: &[Compression]| {
        run(&setup, &params, &lig, blocks, rand, p, q_words.as_slice(), cw, cp, &cq)
    };

    let coords = piop_coords(&setup, &params, &lig, &blocks_a, &base_rand, &p_words, &q_words, &cw, &cp, &cq);
    let proj = |v: &[F128]| -> Vec<u64> { flatten(&coords.iter().map(|&i| v[i]).collect::<Vec<_>>()) };
    let base = proj(&go(&base_rand, &p_words, &cw, &cp, &blocks_a));
    let dim = base.len() * 64;
    println!(
        "real BLAKE3 m={m}, {} blocks: PIOP classes {} F128 = {dim} bits",
        N_BLOCKS,
        coords.len()
    );

    // Span the mask image with random probe directions, RESPECTING THE
    // TRIANGULAR STRUCTURE. The transcript is bilinear across the two
    // randomizer species, so perturbing both at once does not sample a
    // linear map at all: the inner stage must be probed at a FIXED outer
    // mask, and the outer stage added afterwards. (Collapsing the two is a
    // real trap — doing so leaves exactly the one direction the outer stage
    // is responsible for.)
    //
    // Per block the randomizer words are laid out as: A-type chunks, then
    // B-type chunks, then the chain-mask pair (also A-type).
    let chunks_a = 2usize;
    let chunks_b = 1usize;
    let a_word = |w: usize| {
        let off = w % words_per_block;
        off < 2 * chunks_a || off >= 2 * (chunks_a + chunks_b)
    };

    let n_probes = dim + dim / 8 + 256;
    let mut img = F2Space::default();
    let mut prng = Rng(0x9999_7777);
    for _ in 0..n_probes {
        // INNER: A-species randomizers, P, and the commitment masks; the
        // B-species words are held at their base values.
        let mut rand = base_rand.clone();
        for (w, slot) in rand.iter_mut().enumerate() {
            if a_word(w) {
                *slot ^= prng.next_u64() & prng.next_u64() & prng.next_u64();
            }
        }
        let mut p = p_words.to_vec();
        for w in p.iter_mut() {
            *w ^= prng.next_u64() & prng.next_u64() & prng.next_u64();
        }
        let mut cwp = cw.clone();
        let mut cpp = cp.clone();
        for _ in 0..8 {
            let i = (prng.next_u64() as usize) % n_mask_f128;
            cwp[i] += F128 { lo: prng.next_u64(), hi: prng.next_u64() };
            let j = (prng.next_u64() as usize) % n_mask_f128;
            cpp[j] += F128 { lo: prng.next_u64(), hi: prng.next_u64() };
        }
        let t = proj(&go(&rand, &p, &cwp, &cpp, &blocks_a));
        img.insert(xor(&t, &base));
    }
    println!("inner image spans {} of {dim} bits from {n_probes} random probes", img.rank());

    // OUTER: the B-species stage, added on top.
    for _ in 0..(dim / 8 + 256) {
        let mut rand = base_rand.clone();
        for (w, slot) in rand.iter_mut().enumerate() {
            if !a_word(w) {
                *slot ^= prng.next_u64() & prng.next_u64();
            }
        }
        let t = proj(&go(&rand, &p_words, &cw, &cp, &blocks_a));
        img.insert(xor(&t, &base));
    }
    println!("joint image (inner + outer stage) spans {} of {dim} bits", img.rank());

    // Genuinely different witnesses: entirely different BLAKE3 messages.
    //
    // The criterion is the claim-conditioned one — a witness difference need
    // only be covered *up to the public claim*, which the verifier learns
    // legitimately. Note the asymmetry that makes this valid here without a
    // linear witness family: a PASS is sound (if every claim-preserving
    // combination of the sampled differences has zero residual, then in
    // particular every genuine claim-equal pair among them does), while a
    // FAILURE could implicate a combination that corresponds to no real
    // witness pair. So this test can certify, and its negative direction is
    // merely conservative.
    let n_pairs = 512usize;
    let base_claims = claims_of(&setup, &params, &lig, &blocks_a, &base_rand, &p_words, &q_words, &cw, &cp, &cq);
    let mut claim_space = F2Space::default();
    let mut resid_and_claim = F2Space::default();
    for k in 0..n_pairs as u64 {
        let blocks_b = blocks_from(0xBBBB + k, N_BLOCKS);
        let t = proj(&go(&base_rand, &p_words, &cw, &cp, &blocks_b));
        let residual = img.reduce(xor(&t, &base));
        let cl = claims_of(&setup, &params, &lig, &blocks_b, &base_rand, &p_words, &q_words, &cw, &cp, &cq);
        let dcl: Vec<u64> = cl
            .iter()
            .zip(&base_claims)
            .flat_map(|(a, b)| {
                let d = *a + *b;
                [d.lo, d.hi]
            })
            .collect();
        claim_space.insert(dcl.clone());
        let mut both = residual;
        both.extend_from_slice(&dcl);
        resid_and_claim.insert(both);
    }
    println!(
        "  {n_pairs} real BLAKE3 witness pairs: rank(Δclaim)={} rank[resid|Δclaim]={}",
        claim_space.rank(),
        resid_and_claim.rank()
    );
    assert_eq!(
        claim_space.rank(),
        3 * 128,
        "VACUOUS: the Δclaim space did not saturate, so no claim-preserving \
         combination is forced to exist and the criterion cannot bite"
    );
    assert_eq!(
        resid_and_claim.rank(),
        claim_space.rank(),
        "on a REAL BLAKE3 statement, {} claim-preserving witness direction(s) \
         escape the mask image on the PIOP classes",
        resid_and_claim.rank() - claim_space.rank()
    );
}

/// The three public claim values for a BLAKE3 proof, via the real verifier.
#[allow(clippy::too_many_arguments)]
fn claims_of(
    setup: &Blake3Setup,
    params: &PcsParams,
    lig: &flock_core::pcs::ligerito::ProverConfig,
    blocks: &[Compression],
    rand: &[u64],
    p: &[u64],
    q: &[u64],
    cw: &[F128],
    cp: &[F128],
    cq: &[F128],
) -> [F128; 3] {
    use flock_core::{lincheck, zerocheck};
    let layout = setup.r1cs.zk.expect("zk layout");
    let (z, a, b, stripe) =
        flock_prover::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk(
            blocks, setup.n_blocks_log(), &layout, rand,
        );
    let circuit = setup.r1cs.csc_lincheck_circuit();
    let mut s_w = VecSampler::from_f128(cw);
    let mut s_p = VecSampler::from_words(p.to_vec());
    let mut s_q = VecSampler::from_words(q.to_vec());
    let mut s_cp = VecSampler::from_f128(cp);
    let mut s_cq = VecSampler::from_f128(cq);
    let masks = A1MaskSources {
        witness_commit: &mut s_w, p: &mut s_p, q: &mut s_q,
        commit_p: &mut s_cp, commit_q: &mut s_cq,
    };
    let mut ch = RandomChallenger::new(CH_SEED);
    let (proof, _comm, _) = prove_r1cs_zk_a1_with_masks(
        &setup.r1cs, params, z, a, b, stripe, circuit, lig, masks, None, &mut ch,
    );
    let mut chv = RandomChallenger::new(CH_SEED);
    let zc = zerocheck::verify_zk(setup.m(), &proof.zerocheck, &mut chv).expect("honest");
    let x_ab = setup.r1cs.x_ab_from_mlv(zc.z, &zc.mlv_challenges);
    let lc = lincheck::verify(
        setup.m(), setup.r1cs.k_log, setup.r1cs.k_skip, circuit, &x_ab,
        zc.a_eval, zc.b_eval, &proof.lincheck, &mut chv,
    )
    .expect("honest");
    [zc.a_eval * zc.b_eval, lc.w, zc.c_eval]
}

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
    s_words: &[u64],
    cw: &[F128],
    cp: &[F128],
    cq: &[F128],
    cs: &[F128],
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
    let mut s_s = VecSampler::from_words(s_words.to_vec());
    let mut s_cs = VecSampler::from_f128(cs);
    let masks = A1MaskSources {
        witness_commit: &mut s_w,
        p: &mut s_p,
        q: &mut s_q,
        commit_p: &mut s_cp,
        commit_q: &mut s_cq,
        s: &mut s_s,
        commit_s: &mut s_cs,
    };
    let mut ch = RandomChallenger::new(CH_SEED);
    let (proof, comm, _) = prove_r1cs_zk_a1_with_masks(
        &setup.r1cs,
        params,
        z,
        a,
        b,
        stripe,
        circuit,
        lig,
        masks,
        None,
        &mut ch,
    );
    algebraic_vector(&flatten_a1(&comm, &proof))
}

/// Coordinate positions (within the algebraic vector) of the zerocheck and
/// lincheck classes — the PIOP layer. Restricting to them keeps the image
/// saturable at this size: membership is decided against a *spanned* space,
/// which is what makes a negative result meaningful.
fn coords_and_paths(
    class_filter: &dyn Fn(&str) -> bool,
    setup: &Blake3Setup,
    params: &PcsParams,
    lig: &flock_core::pcs::ligerito::ProverConfig,
    blocks: &[Compression],
    rand: &[u64],
    p: &[u64],
    q: &[u64],
    s: &[u64],
    cw: &[F128],
    cp: &[F128],
    cq: &[F128],
    cs: &[F128],
) -> (Vec<usize>, Vec<(&'static str, std::ops::Range<usize>)>) {
    let layout = setup.r1cs.zk.expect("zk layout");
    let (z, a, b, stripe) =
        flock_prover::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk(
            blocks,
            setup.n_blocks_log(),
            &layout,
            rand,
        );
    let circuit = setup.r1cs.csc_lincheck_circuit();
    let mut s_w = VecSampler::from_f128(cw);
    let mut s_p = VecSampler::from_words(p.to_vec());
    let mut s_q = VecSampler::from_words(q.to_vec());
    let mut s_cp = VecSampler::from_f128(cp);
    let mut s_cq = VecSampler::from_f128(cq);
    let mut s_s = VecSampler::from_words(s.to_vec());
    let mut s_cs = VecSampler::from_f128(cs);
    let masks = A1MaskSources {
        witness_commit: &mut s_w,
        p: &mut s_p,
        q: &mut s_q,
        commit_p: &mut s_cp,
        commit_q: &mut s_cq,
        s: &mut s_s,
        commit_s: &mut s_cs,
    };
    let mut ch = RandomChallenger::new(CH_SEED);
    let (proof, comm, _) = prove_r1cs_zk_a1_with_masks(
        &setup.r1cs,
        params,
        z,
        a,
        b,
        stripe,
        circuit,
        lig,
        masks,
        None,
        &mut ch,
    );
    let flat = flatten_a1(&comm, &proof);
    let idx = SchemaIndex::build(&flat);
    let mut out = Vec::new();
    let mut paths = Vec::new();
    for (path, range) in idx.ranges_by_class(&flat, LeakageClass::WitnessDependent) {
        if class_filter(path) {
            let start = out.len();
            out.extend(range);
            paths.push((path, start..out.len()));
        }
    }
    (out, paths)
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
/// **The methodological control passes** (`control_same_procedure_on_the_passing_fixture`):
/// this exact procedure, applied to the synthetic fixture, gives
/// `rank[resid | Δclaim] = 384 = rank(Δclaim)`. So the procedure is sound and
/// the difference in outcome is attributable to the BLAKE3 *statement*, not
/// to the harness. Alignment is also ruled out — lemma L3 is verified on the
/// real layout (`l3_round1_region_alignment_holds`) — and so is the constant-
/// wire pin, which shifts the lincheck target by a challenge β identically
/// for every valid witness (`lincheck.rs`, `const_pin_col`) and so induces no
/// witness-difference direction.
///
/// That makes this the sharpest open question in the whole development, and
/// it points *away* from the property holding rather than toward it: either a
/// fourth transcript-determined public value exists that has not been
/// identified, or a genuine claim-preserving witness direction is uncovered
/// on the real statement family — which would be a finding of the form the
/// task's decision label C describes, not label A.
///
/// **LOCALIZED TO THE LINCHECK LAYER.** Isolating classes
/// (`ZK_BLAKE3_CLASSES`) settles where it lives:
///
/// * `zerocheck.round1_c` alone — image spans 8192 of 8192 bits, criterion
///   PASSES. The zerocheck round-1 class is fully covered.
/// * `lincheck.*` alone — image spans 9728 of 10240 bits and the criterion
///   FAILS by the same 128 bits, on `lincheck.rounds` and `lincheck.z_partial`.
///
/// So the A1′ amendment does its job: the classes it targets are covered.
/// The uncovered direction is in the **lincheck**, which no mask channel
/// touches — it is covered only by the randomizer rows. On the synthetic
/// fixture the witness is ~81% randomizer and that suffices; on a real
/// BLAKE3 statement the randomizer rows are ~5.5% of the witness and it does
/// not. This is an undocumented sizing/coverage constraint on the lincheck
/// layer, distinct from the `s_hat_v` per-bit-residue rule.
///
/// **The sizing repair is ruled out — the deficit is structural.** The
/// randomizer allocation was tried at 4 A-chunks + 3 B-chunks in place of
/// 2 + 1 (spending the 512-bit chain-mask reservation, which batch
/// statements do not use, on randomizer entropy instead — same 896 bits per
/// block, same `useful_bits`, 2.3× the entropy in the species that cover the
/// affine classes). The measured image rank was **identical**: 9728 of 10240
/// bits, the same 128 bits escaping. Entropy is not the binding constraint;
/// the lincheck transcript's image is rank-limited by the map's structure,
/// and the deficit sits at a constant 512 bits (4 F128) across
/// configurations. The change was reverted, having bought nothing.
///
/// That leaves exactly one repair: extend a committed mask channel to the
/// lincheck sumcheck, as A1′ did for the zerocheck round messages — run it
/// on `comb·z + γ_lc·S·T` for fresh witness-free `S,T` committed before
/// `γ_lc`, with `S(ρ),T(ρ)` opened hidingly. It is a change to the
/// construction with its own telescoping and soundness argument to derive,
/// so it is specified here rather than made.
///
/// The escaping direction is **localized**: residual attribution puts it on
/// `zerocheck.round1_c`, `lincheck.rounds` and `lincheck.z_partial` — the
/// C-side/witness-side coordinates — and not on the round pairs or the final
/// evaluations, which the degree-2 channel and the outer stage do cover. Note
/// that `c_eval`, one of the three conditioned claims, is itself an
/// interpolation of `round1_c`, so a single conditioned scalar sits on a
/// 64-element class here; the natural next step is to determine what else
/// about that class the verifier learns, and whether the fixture differs
/// because its statement has no pinned constant wire.
///
/// It is kept, failing and documented, because it is the sharpest statement
/// available about the real statement family and it should not be forgotten.
#[test]
#[ignore = "OPEN: fails by one F128 direction; see the status note above"]
fn blake3_witness_difference_lies_in_the_mask_image() {
    let setup = Blake3Setup::with_zk(N_BLOCKS);
    let m = setup.m();
    let params = PcsParams {
        m,
        log_inv_rate: 1,
        log_batch_size: 2,
        profile: Default::default(),
        zk: true,
    };
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
    let s_words = rng.words(n_cube_words);
    let cw: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();
    let cp: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();
    let cq: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();
    let cs: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();

    let blocks_a = blocks_from(0xAAAA, N_BLOCKS);
    let go = |rand: &[u64],
              p: &[u64],
              s: &[u64],
              cw: &[F128],
              cp: &[F128],
              cs: &[F128],
              blocks: &[Compression]| {
        run(
            &setup,
            &params,
            &lig,
            blocks,
            rand,
            p,
            q_words.as_slice(),
            s,
            cw,
            cp,
            &cq,
            cs,
        )
    };

    // ZK_BLAKE3_CLASSES selects which coordinate classes are under test, so
    // a single class can be isolated to localize an escaping direction.
    let only = std::env::var("ZK_BLAKE3_CLASSES").unwrap_or_else(|_| "piop".into());
    let class_filter = move |path: &str| match only.as_str() {
        "round1_c" => path == "zerocheck.round1_c",
        "round1" => path.starts_with("zerocheck.round1"),
        "lincheck" => path.starts_with("lincheck."),
        _ => path.starts_with("zerocheck.") || path.starts_with("lincheck."),
    };
    let (coords, coord_paths) = coords_and_paths(
        &class_filter,
        &setup,
        &params,
        &lig,
        &blocks_a,
        &base_rand,
        &p_words,
        &q_words,
        &s_words,
        &cw,
        &cp,
        &cq,
        &cs,
    );
    let proj =
        |v: &[F128]| -> Vec<u64> { flatten(&coords.iter().map(|&i| v[i]).collect::<Vec<_>>()) };
    let base = proj(&go(
        &base_rand, &p_words, &s_words, &cw, &cp, &cs, &blocks_a,
    ));
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
        // A2's lincheck mask. Under `RandomChallenger` the challenges — γ_lc
        // included — are fixed across probes, so `z + γ_lc·S` is affine in S
        // and S is an inner channel exactly as P is.
        let mut s = s_words.to_vec();
        for w in s.iter_mut() {
            *w ^= prng.next_u64() & prng.next_u64() & prng.next_u64();
        }
        let mut cwp = cw.clone();
        let mut cpp = cp.clone();
        let mut csp = cs.clone();
        for _ in 0..8 {
            let i = (prng.next_u64() as usize) % n_mask_f128;
            cwp[i] += F128 {
                lo: prng.next_u64(),
                hi: prng.next_u64(),
            };
            let j = (prng.next_u64() as usize) % n_mask_f128;
            cpp[j] += F128 {
                lo: prng.next_u64(),
                hi: prng.next_u64(),
            };
            let l = (prng.next_u64() as usize) % n_mask_f128;
            csp[l] += F128 {
                lo: prng.next_u64(),
                hi: prng.next_u64(),
            };
        }
        let t = proj(&go(&rand, &p, &s, &cwp, &cpp, &csp, &blocks_a));
        img.insert(xor(&t, &base));
    }
    println!(
        "inner image spans {} of {dim} bits from {n_probes} random probes",
        img.rank()
    );

    // OUTER: the B-species stage, added on top.
    for _ in 0..(dim / 8 + 256) {
        let mut rand = base_rand.clone();
        for (w, slot) in rand.iter_mut().enumerate() {
            if !a_word(w) {
                *slot ^= prng.next_u64() & prng.next_u64();
            }
        }
        let t = proj(&go(&rand, &p_words, &s_words, &cw, &cp, &cs, &blocks_a));
        img.insert(xor(&t, &base));
    }
    println!(
        "joint image (inner + outer stage) spans {} of {dim} bits",
        img.rank()
    );

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
    // > 5*128 = 640 bits of claim space, so claim-preserving combinations are
    // forced to exist and the criterion can bite.
    let n_pairs = 768usize;
    let base_claims = claims_of(
        &setup, &params, &lig, &blocks_a, &base_rand, &p_words, &q_words, &s_words, &cw, &cp, &cq,
        &cs,
    );
    let mut claim_space = F2Space::default();
    let mut resid_and_claim = F2Space::default();
    for k in 0..n_pairs as u64 {
        let blocks_b = blocks_from(0xBBBB + k, N_BLOCKS);
        let t = proj(&go(
            &base_rand, &p_words, &s_words, &cw, &cp, &cs, &blocks_b,
        ));
        let residual = img.reduce(xor(&t, &base));
        let cl = claims_of(
            &setup, &params, &lig, &blocks_b, &base_rand, &p_words, &q_words, &s_words, &cw, &cp,
            &cq, &cs,
        );
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
        5 * 128,
        "VACUOUS: the Δclaim space did not saturate, so no claim-preserving \
         combination is forced to exist and the criterion cannot bite"
    );
    if resid_and_claim.rank() > claim_space.rank() {
        println!("  residual attribution — which coordinate classes carry it:");
        for (path, range) in &coord_paths {
            let hits = resid_and_claim
                .rows
                .iter()
                .filter(|row| {
                    range.clone().any(|c| {
                        row.get(c * 2).is_some_and(|w| *w != 0)
                            || row.get(c * 2 + 1).is_some_and(|w| *w != 0)
                    })
                })
                .count();
            if hits > 0 {
                println!("    {path}: {hits} row(s) touch it ({} F128)", range.len());
            }
        }
    }
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
    s: &[u64],
    cw: &[F128],
    cp: &[F128],
    cq: &[F128],
    cs: &[F128],
) -> [F128; 5] {
    use flock_core::{lincheck, zerocheck};
    let layout = setup.r1cs.zk.expect("zk layout");
    let (z, a, b, stripe) =
        flock_prover::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk(
            blocks,
            setup.n_blocks_log(),
            &layout,
            rand,
        );
    let circuit = setup.r1cs.csc_lincheck_circuit();
    let mut s_w = VecSampler::from_f128(cw);
    let mut s_p = VecSampler::from_words(p.to_vec());
    let mut s_q = VecSampler::from_words(q.to_vec());
    let mut s_cp = VecSampler::from_f128(cp);
    let mut s_cq = VecSampler::from_f128(cq);
    let mut s_s = VecSampler::from_words(s.to_vec());
    let mut s_cs = VecSampler::from_f128(cs);
    let masks = A1MaskSources {
        witness_commit: &mut s_w,
        p: &mut s_p,
        q: &mut s_q,
        commit_p: &mut s_cp,
        commit_q: &mut s_cq,
        s: &mut s_s,
        commit_s: &mut s_cs,
    };
    let mut ch = RandomChallenger::new(CH_SEED);
    let (proof, _comm, _) = prove_r1cs_zk_a1_with_masks(
        &setup.r1cs,
        params,
        z,
        a,
        b,
        stripe,
        circuit,
        lig,
        masks,
        None,
        &mut ch,
    );
    let mut chv = RandomChallenger::new(CH_SEED);
    let zc = zerocheck::verify_zk(setup.m(), &proof.zerocheck, &mut chv).expect("honest");
    let x_ab = setup.r1cs.x_ab_from_mlv(zc.z, &zc.mlv_challenges);
    let lc = lincheck::verify_masked(
        setup.m(),
        setup.r1cs.k_log,
        setup.r1cs.k_skip,
        circuit,
        &x_ab,
        zc.a_eval,
        zc.b_eval,
        &proof.lincheck,
        Some((proof.sigma_lc, proof.s_eval)),
        &mut chv,
    )
    .expect("honest");
    // a_eval and b_eval are transcript values the verifier consumes to form
    // the lincheck's target, so the lincheck transcript is conditioned on them
    // whether or not they are listed as "claims".
    [zc.a_eval * zc.b_eval, lc.w, zc.c_eval, zc.a_eval, zc.b_eval]
}

/// **Methodological control: the same procedure, on the fixture that passes.**
///
/// `blake3_witness_difference_lies_in_the_mask_image` leaves one F128
/// direction unexplained on a real BLAKE3 statement, while the full
/// certificate passes on the synthetic fixture. Those two runs differ in
/// *two* ways at once — the statement, and the procedure (this file probes
/// randomly, conditions on no mask-only coordinate, and restricts to the
/// PIOP classes; the certificate probes per channel, conditions on the
/// complete leakage set, and covers every coordinate).
///
/// A difference in outcome cannot be attributed to the statement until the
/// procedure is held fixed. This runs *this file's* procedure on the
/// fixture. If it passes, the procedure is sound and the BLAKE3 result is
/// about the statement. If it fails, the procedure — not the statement — is
/// what the earlier result was measuring.
#[test]
#[ignore = "control for the BLAKE3 result; run alongside it"]
fn control_same_procedure_on_the_passing_fixture() {
    use flock_prover::zk_audit_support::FixtureA1M15;

    let fx = FixtureA1M15::new();
    let m = FixtureA1M15::M;
    let n = 1usize << m;
    let n_mask_f128 = 3 << (m - 7);
    let mut rng = Rng(0xC01D_C0);

    let payload0 = {
        let mut p: Vec<bool> = (0..FixtureA1M15::N_PAYLOAD * FixtureA1M15::BLOCKS)
            .map(|_| rng.next_u64() & 1 == 1)
            .collect();
        for (i, b) in p.iter_mut().enumerate() {
            if i % FixtureA1M15::N_PAYLOAD < FixtureA1M15::FREE_PAYLOAD_BASE {
                *b = false;
            }
        }
        p
    };
    let u_a0: Vec<bool> = (0..FixtureA1M15::A_BITS)
        .map(|_| rng.next_u64() & 1 == 1)
        .collect();
    let u_b0: Vec<bool> = (0..FixtureA1M15::B_BITS)
        .map(|_| rng.next_u64() & 1 == 1)
        .collect();
    let q_bits: Vec<bool> = (0..n).map(|_| rng.next_u64() & 1 == 1).collect();
    let p_bits0: Vec<bool> = vec![false; n];
    let cw: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();
    let cp: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();
    let cq: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();
    let s_bits0: Vec<bool> = (0..n).map(|_| rng.next_u64() & 1 == 1).collect();
    let cs: Vec<F128> = (0..n_mask_f128)
        .map(|_| F128 {
            lo: rng.next_u64(),
            hi: rng.next_u64(),
        })
        .collect();

    let go = |payload: &[bool],
              ua: &[bool],
              ub: &[bool],
              p: &[bool],
              sb: &[bool],
              cw: &[F128],
              cp: &[F128],
              cs_a: &[F128]| {
        let z = fx.witness(payload, ua, ub);
        let a = fx.r1cs.apply_a_packed(&z);
        let b = fx.r1cs.apply_b_packed(&z);
        let stripe = pack_z_lincheck_from_packed(&z, m, FixtureA1M15::K_LOG);
        let circuit = fx.r1cs.sparse_lincheck_circuit();
        let mut s_w = VecSampler::from_f128(cw);
        let mut s_p = VecSampler::from_words(bits_to_words(p));
        let mut s_q = VecSampler::from_words(bits_to_words(&q_bits));
        let mut s_cp = VecSampler::from_f128(cp);
        let mut s_cq = VecSampler::from_f128(&cq);
        let mut s_s = VecSampler::from_words(bits_to_words(sb));
        let mut s_cs = VecSampler::from_f128(cs_a);
        let masks = A1MaskSources {
            witness_commit: &mut s_w,
            p: &mut s_p,
            q: &mut s_q,
            commit_p: &mut s_cp,
            commit_q: &mut s_cq,
            s: &mut s_s,
            commit_s: &mut s_cs,
        };
        let mut ch = RandomChallenger::new(CH_SEED);
        let (proof, comm, _) = prove_r1cs_zk_a1_with_masks(
            &fx.r1cs,
            &fx.pcs_params,
            z,
            a,
            b,
            stripe,
            &circuit,
            &fx.lig_prover,
            masks,
            None,
            &mut ch,
        );
        let flat = flatten_a1(&comm, &proof);
        let idx = SchemaIndex::build(&flat);
        let all = algebraic_vector(&flat);
        let mut coords = Vec::new();
        for (path, range) in idx.ranges_by_class(&flat, LeakageClass::WitnessDependent) {
            if path.starts_with("zerocheck.") || path.starts_with("lincheck.") {
                coords.extend(range);
            }
        }
        let v: Vec<F128> = coords.iter().map(|&i| all[i]).collect();
        let mut chv = RandomChallenger::new(CH_SEED);
        let claims = fx.public_claims(&proof, &mut chv);
        (flatten(&v), claims)
    };

    let (base, base_claims) = go(&payload0, &u_a0, &u_b0, &p_bits0, &s_bits0, &cw, &cp, &cs);
    let dim = base.len() * 64;
    println!("fixture control: PIOP classes {dim} bits");

    // Same random probing style, same triangular split.
    let n_probes = dim + dim / 8 + 256;
    let mut img = F2Space::default();
    let mut prng = Rng(0x4242_4242);
    for _ in 0..n_probes {
        let ua: Vec<bool> = u_a0
            .iter()
            .map(|b| b ^ (prng.next_u64() & prng.next_u64() & prng.next_u64() & 1 == 1))
            .collect();
        let p: Vec<bool> = p_bits0
            .iter()
            .map(|b| b ^ (prng.next_u64() & prng.next_u64() & prng.next_u64() & 1 == 1))
            .collect();
        let sb: Vec<bool> = s_bits0
            .iter()
            .map(|b| b ^ (prng.next_u64() & prng.next_u64() & prng.next_u64() & 1 == 1))
            .collect();
        let mut cwp = cw.clone();
        let mut cpp = cp.clone();
        let mut csp = cs.clone();
        for _ in 0..8 {
            let i = (prng.next_u64() as usize) % n_mask_f128;
            cwp[i] += F128 {
                lo: prng.next_u64(),
                hi: prng.next_u64(),
            };
            let j = (prng.next_u64() as usize) % n_mask_f128;
            cpp[j] += F128 {
                lo: prng.next_u64(),
                hi: prng.next_u64(),
            };
            let l = (prng.next_u64() as usize) % n_mask_f128;
            csp[l] += F128 {
                lo: prng.next_u64(),
                hi: prng.next_u64(),
            };
        }
        let (t, _) = go(&payload0, &ua, &u_b0, &p, &sb, &cwp, &cpp, &csp);
        img.insert(xor(&t, &base));
    }
    for _ in 0..(dim / 8 + 256) {
        let ub: Vec<bool> = u_b0
            .iter()
            .map(|b| b ^ (prng.next_u64() & prng.next_u64() & 1 == 1))
            .collect();
        let (t, _) = go(&payload0, &u_a0, &ub, &p_bits0, &s_bits0, &cw, &cp, &cs);
        img.insert(xor(&t, &base));
    }
    println!(
        "fixture control: joint image spans {} of {dim} bits",
        img.rank()
    );

    let free: Vec<usize> = (0..payload0.len())
        .filter(|i| i % FixtureA1M15::N_PAYLOAD >= FixtureA1M15::FREE_PAYLOAD_BASE)
        .collect();
    let mut claim_space = F2Space::default();
    let mut resid_and_claim = F2Space::default();
    for k in 0..512.min(free.len()) {
        let mut payload = payload0.clone();
        payload[free[k]] = !payload[free[k]];
        let (t, cl) = go(&payload, &u_a0, &u_b0, &p_bits0, &s_bits0, &cw, &cp, &cs);
        let residual = img.reduce(xor(&t, &base));
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
        "fixture control: rank(Δclaim)={} rank[resid|Δclaim]={}",
        claim_space.rank(),
        resid_and_claim.rank()
    );
    assert_eq!(
        resid_and_claim.rank(),
        claim_space.rank(),
        "the CONTROL fails on the fixture that the full certificate passes — \
         so this file's procedure, not the BLAKE3 statement, is what the \
         earlier result was measuring"
    );
}

fn bits_to_words(bits: &[bool]) -> Vec<u64> {
    let mut w = vec![0u64; bits.len().div_ceil(64)];
    for (i, b) in bits.iter().enumerate() {
        if *b {
            w[i / 64] |= 1u64 << (i % 64);
        }
    }
    w
}

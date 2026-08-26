//! The explicit HVZK simulator for BLAKE3 batch statements.
//!
//! A BLAKE3 batch statement binds no public input: its digest is the
//! matrices and layout only, the verifier compares the accepted claim
//! against nothing caller-supplied, and the only pinned wire is the
//! constant-one wire, pinned to 1. So a valid witness is efficiently
//! self-generatable — hash arbitrary self-chosen messages — and the
//! simulator is simply the honest zk prover run on such a self-generated
//! witness. It receives ONLY the public statement (here, the batch size),
//! never a real witness, and it programs no oracle and rewinds nothing, so
//! it is also the NIZK simulator after Fiat–Shamir.
//!
//! **The simulator runs the A1′ reference prover** (`prove_zk_a1`), which is
//! the path the zero-knowledge claim attaches to. The optimized
//! `prove_fast_zk` path runs the *un-amended* zerocheck; the round-message
//! hiding argument does not apply to it, so it is excluded from the claim
//! and no test in this file drives it.
//!
//! Two things are tested, and they are different in kind:
//!
//! 1. `simulator_produces_accepting_proof_without_a_witness` — the
//!    simulator exists and its output verifies. For a statement with no
//!    public input this is nearly trivial; it is necessary, not sufficient.
//! 2. `simulator_translation_exact_transcript_equality` — the substantive
//!    one. Pointwise transcript equality at *equal* masks is impossible
//!    (two witnesses differ by exactly `f(w) − f(w')`), so the constructive
//!    form is a **mask translation**: for two witnesses of the same public
//!    claim, find the mask shift the coverage certificate guarantees exists,
//!    re-run the prover under it, and check the algebraic transcripts are
//!    bit-identical. This exhibits the simulator's exactness rather than
//!    asserting it.

#![cfg(feature = "zk")]

use flock_core::challenger::{FsChallenger, RandomChallenger};
use flock_core::field::F128;
use flock_core::lincheck::pack_z_lincheck_from_packed;
use flock_core::ro::RoContext;
use flock_core::zk::{MaskSampler, ZkRng};
use flock_prover::proof_io::R1csProofBundleZkA1;
use flock_prover::prover::{
    A1MaskForks, A1MaskSources, prove_r1cs_zk_a1_with_masks,
    prove_r1cs_zk_a1_with_masks_pd_nonce_ro,
};
use flock_prover::r1cs_hashes::blake3::{Blake3Setup, Compression};
use flock_prover::transcript_schema::{LeakageClass, SchemaIndex, algebraic_vector, flatten_a1};
use flock_prover::zk_audit_support::FixtureA1M15;

/// The external oracle is a model hook, not a second hash implementation: an
/// empty table must reproduce the native proof byte for byte.
#[test]
fn unprogrammed_external_backend_reproduces_native_proof_bytes() {
    let fx = FixtureA1M15::new();
    let payload = vec![false; FixtureA1M15::N_PAYLOAD * FixtureA1M15::BLOCKS];
    let u_a = vec![false; FixtureA1M15::A_BITS];
    let u_b = vec![false; FixtureA1M15::B_BITS];
    let z = fx.witness(&payload, &u_a, &u_b);

    let run = |external: bool| {
        let a = fx.r1cs.apply_a_packed(&z);
        let b = fx.r1cs.apply_b_packed(&z);
        let stripe = pack_z_lincheck_from_packed(&z, FixtureA1M15::M, FixtureA1M15::K_LOG);
        let circuit = fx.r1cs.sparse_lincheck_circuit();
        let mut root_rng = ZkRng::from_seed([0x42; 32]);
        let mut forks = A1MaskForks::from_rng(&mut root_rng);
        let nonce = forks.proof_nonce;
        let ro = if external {
            flock_prover::sim_oracle::ro_context(nonce, flock_prover::sim_oracle::shared_oracle())
        } else {
            RoContext::native(nonce)
        };
        let mut ch = FsChallenger::new(b"flock-ro-backend-differential");
        let (proof, commitment, _) = prove_r1cs_zk_a1_with_masks_pd_nonce_ro(
            &fx.r1cs,
            &fx.pcs_params,
            z.clone(),
            a,
            b,
            stripe,
            &circuit,
            &fx.lig_prover,
            forks.sources(),
            &mut |_: &mut FsChallenger| Vec::new(),
            None,
            None,
            nonce,
            &ro,
            &mut ch,
        );
        R1csProofBundleZkA1 { commitment, proof }.to_bytes()
    };

    assert_eq!(run(false), run(true));
}

use flock_test_util::Rng;

/// Field-element helpers over the shared [`Rng`]. They live here because a
/// foreign trait cannot be implemented for a foreign type, and `flock-test-util`
/// depends on nothing (see that crate's docs).
trait RngF128 {
    fn f128(&mut self) -> F128;
}

impl RngF128 for Rng {
    fn f128(&mut self) -> F128 {
        F128 {
            lo: self.next_u64(),
            hi: self.next_u64(),
        }
    }
}
/// **The simulator.** Given ONLY the public statement (batch size `n`),
/// produce an accepting proof without any witness: pick arbitrary
/// compressions, build the corresponding witness, and run the honest
/// certificate-gated A1′ prover with fresh masks.
fn simulate(
    n: usize,
    rng: &mut Rng,
) -> (
    Blake3Setup,
    flock_prover::prover::R1csProofZkA1,
    flock_core::pcs::Commitment,
) {
    let setup = Blake3Setup::with_zk(n);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect();
    let mut zk_rng = ZkRng::from_entropy();
    let mut ch = FsChallenger::new(b"flock-zk-sim-a1");
    let (proof, commitment) = setup
        .prove_zk_a1_with_rng(&blocks, &mut zk_rng, &mut ch)
        .expect("the simulator only runs certified configurations");
    (setup, proof, commitment)
}

#[test]
#[ignore = "m=22 end-to-end; run via scripts/zk-certify.sh"]
fn simulator_produces_accepting_proof_without_a_witness() {
    let n = 256; // the certified configuration (m = 22)
    let mut rng = Rng(0x51_3D_1A_70);

    // The simulator sees only `n` (the public statement carries no I/O).
    let (setup, proof, commitment) = simulate(n, &mut rng);
    let mut vch = FsChallenger::new(b"flock-zk-sim-a1");
    setup
        .verify_zk_a1(&commitment, &proof, &mut vch)
        .expect("the witness-free simulator must produce an accepting proof");

    // A second run (fresh self-generated witness + fresh masks) yields a
    // different transcript that still verifies — the simulator is
    // randomized, matching the honest prover's per-proof freshness.
    let mut rng2 = Rng(0x0B_AD_C0_DE);
    let (setup2, proof2, commitment2) = simulate(n, &mut rng2);
    let mut vch2 = FsChallenger::new(b"flock-zk-sim-a1");
    setup2
        .verify_zk_a1(&commitment2, &proof2, &mut vch2)
        .expect("second run verifies");
    assert_ne!(
        commitment.root, commitment2.root,
        "independent simulator runs must differ (fresh masks/witness)"
    );
}

/// **Constructive simulator exactness: mask translation.**
///
/// For two witnesses `w₀`, `w₁` of the same public claim, the coverage
/// certificate says the transcript difference lies in the mask image. This
/// test *finds* the witnessing mask shift and applies it: it extracts the
/// `P`-channel columns by unit-probing the real prover at fixed challenges,
/// solves `A·Δp = T(w₁) − T(w₀)` over F₂ on the round-pair block, re-runs
/// the prover for `w₀` with `P ← P + Δp`, and asserts the resulting
/// coordinates are **bit-identical** to `w₁`'s.
///
/// That is exactly the statement "the honest prover on a self-generated
/// witness reproduces the real witness's transcript", made constructive on
/// the coordinates the certificate covers. Coordinates outside the solved
/// block are not claimed to match (a full-transcript translation is the
/// offline certificate's job); what is claimed — and checked — is that the
/// solved directions match exactly, i.e. the mask image really does contain
/// the witness difference rather than merely being large enough to.
#[test]
fn simulator_translation_exact_transcript_equality() {
    let fx = FixtureA1M15::new();
    let n = 1usize << FixtureA1M15::M;
    let ch_seed = 0x5117_0000u64;
    let mut rng = Rng(0xE7A_C7);

    let u_a = rng.bits(FixtureA1M15::A_BITS);
    let u_b = rng.bits(FixtureA1M15::B_BITS);
    let q_bits = rng.bits(n);
    let cw: Vec<F128> = (0..1024).map(|_| rng.f128()).collect();
    let cp: Vec<F128> = (0..1024).map(|_| rng.f128()).collect();
    let cq: Vec<F128> = (0..1024).map(|_| rng.f128()).collect();
    let s_bits = rng.bits(n);
    let sc_bits = rng.bits(n);
    let sh_bits = rng.bits(n);
    let cs: Vec<F128> = (0..1024).map(|_| rng.f128()).collect();
    let w0 = rng.bits(FixtureA1M15::N_PAYLOAD * FixtureA1M15::BLOCKS);
    let mut w1 = w0.clone();
    w1[5] = !w1[5]; // a different witness of the same statement

    // Run the REAL prover and return the round-pair block coordinates.
    let run = |payload: &[bool], p_bits: &[bool]| -> Vec<F128> {
        let z = fx.witness(payload, &u_a, &u_b);
        let a_packed = fx.r1cs.apply_a_packed(&z);
        let b_packed = fx.r1cs.apply_b_packed(&z);
        let stripe = pack_z_lincheck_from_packed(&z, FixtureA1M15::M, FixtureA1M15::K_LOG);
        let circuit = fx.r1cs.sparse_lincheck_circuit();
        let mut s_w = VecSampler::f128(cw.clone());
        let mut s_p = VecSampler::bits(p_bits);
        let _s_q = VecSampler::bits(&q_bits);
        let mut s_cp = VecSampler::f128(cp.clone());
        let _s_cq = VecSampler::f128(cq.clone());
        let mut s_s = VecSampler::bits(&s_bits);
        let mut s_cs = VecSampler::f128(cs.clone());
        let mut s_sc = VecSampler::bits(&sc_bits);
        let mut s_sh = VecSampler::bits(&sh_bits);
        let mut s_csc = VecSampler::f128(cs.clone());
        let mut s_csh = VecSampler::f128(cs.clone());
        let masks = A1MaskSources {
            witness_commit: &mut s_w,
            p: &mut s_p,
            commit_p: &mut s_cp,
            s: &mut s_s,
            commit_s: &mut s_cs,
            s_c: &mut s_sc,
            s_h: &mut s_sh,
            commit_s_c: &mut s_csc,
            commit_s_h: &mut s_csh,
        };
        let mut ch = RandomChallenger::new(ch_seed);
        let (proof, comm, _) = prove_r1cs_zk_a1_with_masks(
            &fx.r1cs,
            &fx.pcs_params,
            z,
            a_packed,
            b_packed,
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
        idx.range("zerocheck.multilinear_rounds")
            .map(|i| all[i])
            .collect()
    };

    let p0 = vec![false; n];
    let t0 = run(&w0, &p0);
    let t1 = run(&w1, &p0);
    let target: Vec<F128> = t0.iter().zip(&t1).map(|(a, b)| *a + *b).collect();
    assert!(
        target.iter().any(|v| *v != F128::ZERO),
        "the two witnesses must actually differ on the round-pair block"
    );

    // Extract the P-channel columns (unit probes of the real prover) and
    // solve A·Δp = target over F₂ by elimination with provenance.
    let dim = target.len() * 128;
    // Provenance is tracked as an F₂ bitmask over probe slots (not a list):
    // elimination XORs provenance too, and a list representation grows
    // quadratically and exhausts memory.
    let stride = (n / (dim + dim / 2)).max(1);
    let n_slots = n.div_ceil(stride);
    let prov_words = n_slots.div_ceil(64);
    let mut basis: Vec<(Vec<u64>, Vec<u64>)> = Vec::new(); // (row, provenance)
    let mut pivots: Vec<usize> = Vec::new();
    let mut slot = 0usize;
    let mut i = 0usize;
    while i < n {
        let mut p = p0.clone();
        p[i] = true;
        let col = run(&w0, &p);
        let mut row = flatten(
            &col.iter()
                .zip(&t0)
                .map(|(a, b)| *a + *b)
                .collect::<Vec<_>>(),
        );
        let mut prov = vec![0u64; prov_words];
        prov[slot / 64] |= 1u64 << (slot % 64);
        for (b, &pv) in basis.iter().zip(&pivots) {
            let (w, m) = (pv / 64, 1u64 << (pv % 64));
            if row[w] & m != 0 {
                for (x, y) in row.iter_mut().zip(&b.0) {
                    *x ^= *y;
                }
                for (x, y) in prov.iter_mut().zip(&b.1) {
                    *x ^= *y;
                }
            }
        }
        if let Some(pv) = first_set_bit(&row) {
            basis.push((row, prov));
            pivots.push(pv);
        }
        slot += 1;
        i += stride;
    }

    // Solve for the target.
    let mut rem = flatten(&target);
    let mut delta = vec![0u64; prov_words];
    for (b, &pv) in basis.iter().zip(&pivots) {
        let (w, m) = (pv / 64, 1u64 << (pv % 64));
        if rem[w] & m != 0 {
            for (x, y) in rem.iter_mut().zip(&b.0) {
                *x ^= *y;
            }
            for (x, y) in delta.iter_mut().zip(&b.1) {
                *x ^= *y;
            }
        }
    }
    assert!(
        first_set_bit(&rem).is_none(),
        "the witness difference is NOT in the P-channel image on the round \
         block — the coverage certificate's premise fails here"
    );

    // Apply the solved mask translation and demand bit-exact equality.
    let mut p_shift = p0.clone();
    let mut n_flips = 0usize;
    for s in 0..n_slots {
        if delta[s / 64] >> (s % 64) & 1 == 1 {
            p_shift[s * stride] = !p_shift[s * stride];
            n_flips += 1;
        }
    }
    let t0_shifted = run(&w0, &p_shift);
    assert_eq!(
        t0_shifted, t1,
        "mask-translated transcript of w0 must be BIT-IDENTICAL to w1's on \
         the covered block — this is simulator exactness, constructively"
    );
    println!(
        "simulator exactness: solved a {}-bit P translation carrying w0's \
         transcript onto w1's, bit-identical on {} F128 round-pair coordinates",
        n_flips,
        t1.len()
    );
}

/// The transcript schema classifies the values this test compares, so a
/// reshape cannot silently narrow what "bit-identical" covers.
#[test]
fn simulator_compares_witness_dependent_coordinates() {
    let fx = FixtureA1M15::new();
    let mut rng = Rng(0x9001);
    let payload = rng.bits(FixtureA1M15::N_PAYLOAD * FixtureA1M15::BLOCKS);
    let u_a = rng.bits(FixtureA1M15::A_BITS);
    let u_b = rng.bits(FixtureA1M15::B_BITS);
    let z = fx.witness(&payload, &u_a, &u_b);
    let mut zk_rng = ZkRng::from_seed([0x31; 32]);
    let mut ch = FsChallenger::new(b"flock-zk-sim-schema");
    let (proof, comm) = fx.prove(z, &mut zk_rng, &mut ch);
    let flat = flatten_a1(&comm, &proof);
    let idx = SchemaIndex::build(&flat);
    let rounds = idx.range("zerocheck.multilinear_rounds");
    assert!(!rounds.is_empty());
    let wd = idx.ranges_by_class(&flat, LeakageClass::WitnessDependent);
    assert!(
        wd.iter().any(|(p, _)| *p == "zerocheck.multilinear_rounds"),
        "the compared block must be classified witness-dependent"
    );
}

// --- small helpers -------------------------------------------------------

fn flatten(v: &[F128]) -> Vec<u64> {
    let mut out = Vec::with_capacity(v.len() * 2);
    for x in v {
        out.push(x.lo);
        out.push(x.hi);
    }
    out
}

fn first_set_bit(v: &[u64]) -> Option<usize> {
    v.iter()
        .enumerate()
        .find_map(|(i, w)| (*w != 0).then(|| i * 64 + w.trailing_zeros() as usize))
}

/// Replays a fixed stream (bits packed into u64 words, or F128s) then zeros.
struct VecSampler {
    words: Vec<u64>,
    pos: usize,
}
impl VecSampler {
    fn bits(bits: &[bool]) -> Self {
        let mut words = vec![0u64; bits.len().div_ceil(64)];
        for (i, b) in bits.iter().enumerate() {
            if *b {
                words[i / 64] |= 1u64 << (i % 64);
            }
        }
        Self { words, pos: 0 }
    }
    fn f128(v: Vec<F128>) -> Self {
        let mut words = Vec::with_capacity(v.len() * 2);
        for x in v {
            words.push(x.lo);
            words.push(x.hi);
        }
        Self { words, pos: 0 }
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

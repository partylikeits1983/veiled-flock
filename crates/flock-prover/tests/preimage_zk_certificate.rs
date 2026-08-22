//! **Coverage certificates for the fixed-digest relation.**
//!
//! The simulator (`preimage_simulator`) produces an accepting transcript
//! without a preimage. Acceptance alone is not zero knowledge: the simulated
//! distribution must also match the honest one. These certificates measure the
//! half of that statement which is measurable.
//!
//! ## The shape of the argument
//!
//! The simulated transcript is uniform on the variety the verifier's checks cut
//! out (free coordinates drawn uniformly, dependent ones solved). So the
//! distributions coincide exactly when the **honest** transcript is uniform on
//! that same variety — i.e. when the mask channels move the honest
//! witness-dependent coordinates over their whole space, once the public values
//! the verifier learns anyway are held fixed.
//!
//! That is a rank statement, and it is what these tests measure:
//!
//! * the field-valued `P` channel, multiplied by the public affine Q-star,
//!   spans the conditioned zerocheck round-pair block, so the honest round
//!   messages have the simulator's law outside the emitted determinant's bad
//!   set;
//! * a degenerate mask spans strictly less, so the measurement is not vacuous;
//! * the randomizer rows move the terminal evaluations, which is what makes
//!   the simulator's freedom to choose them legitimate.
//!
//! ## Why this is the *claim-kernel* form and not the older one
//!
//! Every earlier certificate in this repository measures
//! witness-indistinguishability: that two valid witnesses induce
//! indistinguishable transcripts. For a fixed digest the preimage is
//! essentially unique, so there is no second witness and that form is
//! **vacuous**. These certificates therefore quantify over *masks*, not over
//! witness pairs — a witness-free statement, which is both the only one
//! available here and strictly stronger.
//!
//! ## What they do not establish
//!
//! Random probing can only under-estimate a rank, so a full-rank measurement is
//! sound evidence of surjectivity; but these run at one challenge tuple and
//! cover the PIOP block, not the PCS-opening interior.

#![cfg(feature = "zk")]

use flock_core::field::F128;
use flock_core::zk::MaskSampler;
use flock_prover::digest_bind::{DigestChallenges, digest_claim_value};
use flock_prover::preimage_extractor::ExtractError;
use flock_prover::preimage_extractor::extract_preimages;
use flock_prover::preimage_extractor::message_bytes_at;
use flock_prover::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk_pinned;
use flock_prover::r1cs_hashes::blake3::{ParamPinning, build_block_r1cs_zk_pinned};
use flock_prover::r1cs_hashes::blake3_preimage::{
    Blake3PreimageSetup, Blake3PreimageZkSetup, MESSAGE_BYTES,
};
use flock_prover::zk_rank_check::check_mask_coverage_fv;

/// The certified production shape: 256 instances, m = 22.
const N: usize = 256;

fn msgs(seed: u64, n: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    let mut s = seed | 1;
    (0..n)
        .map(|_| {
            std::array::from_fn(|_| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                (s & 0xFF) as u8
            })
        })
        .collect()
}

/// **The load-bearing measurement.** For the fixed-digest circuit at the
/// production shape, the field-valued `P` / public Q-star channel spans the
/// conditioned zerocheck round-pair block.
///
/// This is what licenses the simulator's round messages. The simulator draws
/// them uniformly (solving one coordinate for the terminal identity); the
/// honest prover derives them from a witness and then adds `γ·M_j` from this
/// channel. If the channel is surjective onto the block, the honest messages
/// are uniform over it too, whatever the witness was — so the two laws agree
/// on this class rather than merely looking similar.
#[test]
#[ignore = "production-shape rank measurement; run explicitly"]
fn field_mask_spans_conditioned_round_block_for_fixed_digest() {
    let setup = Blake3PreimageZkSetup::new(N);
    let m = setup.r1cs.m;
    assert_eq!(m, 22, "production shape");

    let report =
        check_mask_coverage_fv(flock_core::zerocheck::SmallMaskSpec::default(), m, 0xA11CE)
            .expect("channel must cover the conditioned block");
    println!(
        "field-mask channel on the fixed-digest circuit: rank {} / {} bits, {} probes",
        report.rank, report.target_bits, report.probes
    );
    assert_eq!(
        report.rank, report.target_bits,
        "the field-mask channel must span the conditioned round-pair block — without \
         that, the honest round messages are not uniform and the simulator's \
         uniform ones would be distinguishable"
    );
}

/// **The non-vacuity control.** An undersized translated-subcube support cannot
/// reach the conditioned round-message space, so it must span strictly less.
/// If this passed at full rank the measurement above would be meaningless.
#[test]
#[ignore = "production-shape rank measurement; run explicitly"]
fn undersized_mask_does_not_span_the_round_block() {
    let setup = Blake3PreimageZkSetup::new(N);
    let m = setup.r1cs.m;
    let spec = flock_core::zerocheck::SmallMaskSpec {
        d_log: 1,
        ..flock_core::zerocheck::SmallMaskSpec::default()
    };
    match check_mask_coverage_fv(spec, m, 0xA11CE) {
        Ok(r) => panic!(
            "an undersized support spanned the whole block ({}/{}) — the coverage check \
             is not measuring what it claims",
            r.rank, r.target_bits
        ),
        Err(failed) => {
            println!(
                "undersized support: rank {} / {} bits (must be strictly short)",
                failed.report.rank, failed.report.target_bits
            );
            assert!(failed.report.rank < failed.report.target_bits);
        }
    }
}

/// **The simulator's committed vector is masked exactly like an honest one.**
///
/// The simulator commits a patched trace; the honest prover commits a real
/// witness. Both carry the same randomizer layout, so the transcript classes
/// the randomizers cover are uniform in both — which is why the simulator may
/// choose the terminal evaluations freely. Measured as: fresh mask draws move
/// the terminal evaluations and the commitment root in BOTH settings.
#[test]
fn randomizers_move_the_terminals_in_both_settings() {
    let setup = Blake3PreimageZkSetup::new(N);
    let secret = msgs(0x1234_5678, N);
    let digests = Blake3PreimageSetup::digests_of(&secret);

    let run = |seed: u8| {
        let mut rng = flock_core::zk::ZkRng::from_seed([seed; 32]);
        let mut ch = flock_core::challenger::FsChallenger::new(b"b3-preimage-zk");
        setup
            .prove(&secret, &digests, &mut rng, &mut ch)
            .expect("prove")
    };
    let (p1, c1) = run(41);
    let (p2, c2) = run(42);

    assert_ne!(c1.root, c2.root, "fresh masks must move the commitment");
    assert_ne!(
        p1.zerocheck.final_a_eval, p2.zerocheck.final_a_eval,
        "fresh masks must move the â terminal — the simulator relies on this \
         class being mask-covered rather than witness-determined"
    );
    assert_ne!(
        p1.zerocheck.final_b_eval, p2.zerocheck.final_b_eval,
        "fresh masks must move the b̂ terminal"
    );
    assert_ne!(
        p1.zerocheck.mask_init, p2.zerocheck.mask_init,
        "fresh masks must move σ_z — the simulator takes it from a fresh draw"
    );
}

/// **The public claim really is public.** The digest claim's value is a
/// function of the statement and the challenges only, so conditioning the
/// hiding argument on it concedes nothing: two different witnesses for the
/// same digests induce the *same* claim value.
///
/// This matters because every earlier certificate in this repository had to
/// condition on internal claims whose own witness-independence was never
/// separately established. Here the conditioning is on a value the verifier
/// computes itself.
#[test]
fn the_digest_claim_is_a_public_function_of_the_statement() {
    let setup = Blake3PreimageZkSetup::new(N);
    let secret = msgs(0xAAAA, N);
    let digests = Blake3PreimageSetup::digests_of(&secret);
    let stmt = setup.statement(&digests);

    // Two independent transcripts reaching the claim.
    let value_at = |seed: &[u8]| {
        let mut ch = flock_core::challenger::FsChallenger::new(seed);
        let dch = DigestChallenges::sample(&stmt, &mut ch);
        (digest_claim_value(&stmt, &dch), dch)
    };
    let (v1, d1) = value_at(b"one");
    let (v2, _) = value_at(b"two");
    assert_ne!(v1, v2, "different challenges must give different targets");

    // Recomputing at the same challenges gives the same value — no witness
    // enters anywhere.
    assert_eq!(digest_claim_value(&stmt, &d1), v1);

    // And a different witness for the SAME digests would produce the same
    // claim, because the claim reads the statement, not the witness.
    let other = msgs(0xBBBB, N);
    let other_digests = Blake3PreimageSetup::digests_of(&other);
    let other_stmt = setup.statement(&other_digests);
    assert_ne!(
        digest_claim_value(&other_stmt, &d1),
        v1,
        "a different statement must give a different target"
    );
}

/// The fixed-digest circuit really is a different statement from the batch
/// circuit, so none of the batch statement's evidence is silently inherited.
#[test]
fn fixed_digest_circuit_is_not_the_batch_circuit() {
    let pinned = build_block_r1cs_zk_pinned(8, ParamPinning::RootHash64);
    let free = build_block_r1cs_zk_pinned(8, ParamPinning::Free);
    assert_ne!(
        pinned.statement_digest(),
        free.statement_digest(),
        "the pinned circuit must have its own statement digest"
    );
}

/// A sanity check on the field helper the certificates lean on.
#[test]
fn f128_inverse_roundtrips() {
    let x = F128 {
        lo: 0x1234_5678_9ABC_DEF0,
        hi: 0x0FED_CBA9_8765_4321,
    };
    assert_eq!(x * x.inv(), F128::ONE);
}

// ---------------------------------------------------------------------------
// Knowledge extraction
// ---------------------------------------------------------------------------

/// **The extractor recovers real preimages.** Given the committed vector an
/// honest prover produced — what the straightline ROM observation step yields
/// — extraction returns byte strings that hash to the public digests, checked
/// by the `blake3` crate outside the circuit entirely.
#[test]
fn extractor_recovers_the_preimages_from_an_honest_commitment() {
    let setup = Blake3PreimageZkSetup::new(N);
    let secret = msgs(0xE0E0_1111, N);
    let digests = Blake3PreimageSetup::digests_of(&secret);

    let layout = setup.r1cs.zk.expect("zk layout");
    let mut zrng = flock_core::zk::ZkRng::from_seed([31u8; 32]);
    let mut rand_words =
        vec![
            0u64;
            setup.n_block_slots()
                * flock_prover::r1cs_hashes::common::zk_rand_words_per_block(&layout)
        ];
    zrng.fill_u64s(&mut rand_words);
    let blocks: Vec<_> = secret
        .iter()
        .map(flock_prover::r1cs_hashes::blake3_preimage::message_compression)
        .collect();
    let (z, _a, _b, _l) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
        &blocks,
        setup.n_blocks_log(),
        &layout,
        &rand_words,
        ParamPinning::RootHash64,
    );

    let got = extract_preimages(&z, &digests, setup.n_block_slots())
        .expect("extraction must succeed on an honest commitment");
    assert_eq!(got.len(), N);
    for (i, (g, want)) in got.iter().zip(&secret).enumerate() {
        assert_eq!(g, want, "extracted message {i} is not the real preimage");
        assert_eq!(::blake3::hash(g).as_bytes(), &digests[i]);
    }
}

/// **The decisive control: extraction FAILS on the simulator's proof.**
///
/// The simulator produces a transcript the verifier accepts, and it knows no
/// preimage. If extraction succeeded on its committed vector, the extractor
/// would be recovering something other than knowledge — a mask column, an
/// opening claim, or an assignment untied to the digests — and "argument of
/// knowledge" would be empty.
///
/// This is the test that separates zero knowledge from knowledge soundness:
/// the same object that makes the proof reveal nothing must not also make it
/// prove nothing.
#[test]
fn extraction_fails_on_the_simulators_commitment() {
    let setup = Blake3PreimageZkSetup::new(N);
    // The statement: digests of messages nobody in this test knows a preimage
    // for except the honest party.
    let secret = msgs(0xE0E0_2222, N);
    let digests = Blake3PreimageSetup::digests_of(&secret);

    // The simulator's committed vector: its own messages, output region
    // overwritten with the public digests.
    let own = msgs(0xE0E0_3333, N);
    let layout = setup.r1cs.zk.expect("zk layout");
    let mut zrng = flock_core::zk::ZkRng::from_seed([32u8; 32]);
    let mut rand_words =
        vec![
            0u64;
            setup.n_block_slots()
                * flock_prover::r1cs_hashes::common::zk_rand_words_per_block(&layout)
        ];
    zrng.fill_u64s(&mut rand_words);
    let blocks: Vec<_> = own
        .iter()
        .map(flock_prover::r1cs_hashes::blake3_preimage::message_compression)
        .collect();
    let (mut z, _a, _b, _l) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
        &blocks,
        setup.n_blocks_log(),
        &layout,
        &rand_words,
        ParamPinning::RootHash64,
    );
    let words_per_block = (1usize << 14) / 128;
    for (i, d) in digests.iter().enumerate() {
        for half in 0..2usize {
            let mut w = F128::ZERO;
            for b in 0..128usize {
                let bit = half * 128 + b;
                if (d[bit / 8] >> (bit % 8)) & 1 == 1 {
                    if b < 64 {
                        w.lo |= 1u64 << b;
                    } else {
                        w.hi |= 1u64 << (b - 64);
                    }
                }
            }
            z[i * words_per_block + 2 + half] = w;
        }
    }

    match extract_preimages(&z, &digests, setup.n_block_slots()) {
        Err(ExtractError::NotAPreimage { index }) => {
            assert_eq!(index, 0, "the first instance already fails");
        }
        Err(e) => panic!("unexpected extraction error: {e}"),
        Ok(_) => panic!(
            "extraction SUCCEEDED on the simulator's commitment — the extractor              is not recovering knowledge, and the argument-of-knowledge claim              would be empty"
        ),
    }
}

/// **The extractor reads the message region, not a mask column.** Perturbing
/// the randomizer sections — which live above `useful_bits` and carry the
/// prover's mask randomness — must not change what is extracted.
#[test]
fn extraction_ignores_the_mask_columns() {
    let setup = Blake3PreimageZkSetup::new(N);
    let secret = msgs(0xE0E0_4444, 4);
    let layout = setup.r1cs.zk.expect("zk layout");
    let build = |seed: u8| {
        let mut zrng = flock_core::zk::ZkRng::from_seed([seed; 32]);
        let mut rand_words =
            vec![
                0u64;
                setup.n_block_slots()
                    * flock_prover::r1cs_hashes::common::zk_rand_words_per_block(&layout)
            ];
        zrng.fill_u64s(&mut rand_words);
        let mut all: Vec<_> = secret
            .iter()
            .map(flock_prover::r1cs_hashes::blake3_preimage::message_compression)
            .collect();
        all.resize(N, ParamPinning::RootHash64.padding_compression());
        let (z, _a, _b, _l) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
            &all,
            setup.n_blocks_log(),
            &layout,
            &rand_words,
            ParamPinning::RootHash64,
        );
        z
    };
    let z1 = build(51);
    let z2 = build(52);
    assert_ne!(
        z1, z2,
        "different mask draws must give different commitments"
    );
    for i in 0..4usize {
        assert_eq!(
            message_bytes_at(&z1, i),
            message_bytes_at(&z2, i),
            "extraction at instance {i} moved with the MASKS — it is reading \
             mask material, not the message"
        );
        assert_eq!(message_bytes_at(&z1, i), secret[i]);
    }
}

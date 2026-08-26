//! Integration tests for the BLAKE3 R1CS encoder: witness and matrix
//! agreement, the lincheck circuit, the Ligerito round trips, the zk and
//! pinned-parameter paths, and the chain end-to-end tests.
//!
//! Tests that read the encoder's private surface stay in
//! `crates/flock-prover/src/r1cs_hashes/blake3/tests.rs`.

use flock_core::challenger::FsChallenger;
use flock_core::field::F128;
use flock_core::lincheck::pack_z_lincheck_from_packed;
use flock_core::lincheck::{LincheckCircuit, SparseMatrixCircuit};
use flock_core::pcs::ligerito::LigeritoProfile;
use flock_prover::r1cs_hashes::blake3::*;
#[cfg(feature = "zk")]
use flock_prover::zk_certificate::{CERTIFIED, StatementFamily, require_certified};

use flock_test_util::Rng;
/// BLAKE3 chunk flags (subset).
const CHUNK_START: u32 = 1 << 0;

const CHUNK_END: u32 = 1 << 1;

const ROOT: u32 = 1 << 3;

/// Batch-major witness equality vs the row-major driver (word-transpose
/// + identical stripe), incl. padding slots via a non-power-of-two count.
#[test]
fn batch_major_witness_matches_row_major_transposed() {
    for (n_inputs, n_log) in [(8usize, 3usize), (11, 4)] {
        let mut rng = Rng::new(0xBA7C_B3 + n_log as u64);
        let inputs: Vec<Compression> = (0..n_inputs)
            .map(|_| {
                let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
                let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                let counter = ((rng.next_u32() as u64) << 32) | (rng.next_u32() as u64);
                (cv, m, counter, 64u32, 11u32)
            })
            .collect();

        let (z_r, a_r, b_r, stripe_r) =
            generate_witness_with_ab_packed_and_lincheck(&inputs, n_log);
        let (z_b, a_b, b_b, stripe_b) = generate_witness_batch_major(&inputs, n_log);

        assert_eq!(stripe_b, stripe_r, "stripe diverged (n_log={n_log})");

        let chunks_per_block = K / 128;
        let transpose = |row: &[flock_core::field::F128]| {
            let mut out = vec![flock_core::field::F128::ZERO; row.len()];
            for o in 0..1usize << n_log {
                for c in 0..chunks_per_block {
                    out[(c << n_log) + o] = row[o * chunks_per_block + c];
                }
            }
            out
        };
        assert_eq!(z_b, transpose(&z_r), "z diverged (n_log={n_log})");
        assert_eq!(a_b, transpose(&a_r), "a diverged (n_log={n_log})");
        assert_eq!(b_b, transpose(&b_r), "b diverged (n_log={n_log})");
    }
}

/// Batch-major end-to-end Ligerito roundtrip + tamper rejection.
#[test]
#[ignore]
fn batch_major_prove_fast_roundtrip() {
    let setup = Blake3Setup::new_batch_major(256);
    let mut rng = Rng::new(0xBA7C_F013);
    let inputs: Vec<Compression> = (0..256)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            let counter = ((rng.next_u32() as u64) << 32) | (rng.next_u32() as u64);
            (cv, m, counter, 64u32, 11u32)
        })
        .collect();

    let mut ch_p = FsChallenger::new(b"flock-lig-batch-major-v0");
    let (proof, commitment, claim_p) = setup.prove_fast(&inputs, &mut ch_p);
    let mut ch_v = FsChallenger::new(b"flock-lig-batch-major-v0");
    let claim_v = setup
        .verify(&commitment, &proof, &mut ch_v)
        .unwrap_or_else(|e| panic!("batch-major verifier rejected: {e:?}"));
    assert_eq!(claim_p, claim_v);

    let mut bad = proof.clone();
    bad.zerocheck.final_a_eval.lo ^= 1;
    let mut ch = FsChallenger::new(b"flock-lig-batch-major-v0");
    assert!(
        setup.verify(&commitment, &bad, &mut ch).is_err(),
        "tampered batch-major proof accepted"
    );
}

#[test]
fn layout_constants() {
    // I/O-aligned layout: cv in slot 0, out_lo in slot 1 (both 256-bit).
    assert_eq!(CV_BASE, 0);
    assert_eq!(OUT_LO_BASE, 256);
    assert_eq!(Z_CONST_POS, 512);
    assert_eq!(M_BASE, 513);
    assert_eq!(GS_BASE, 1153);
    assert_eq!(G_STRIDE, 250);
    assert_eq!(N_G, 56);
    assert_eq!(OUT_HI_BASE, 15_153);
    assert_eq!(USEFUL_BITS, 15_409);
    assert!(USEFUL_BITS <= K);
    assert_eq!(CV_BASE % SLOT_BITS, 0);
    assert_eq!(OUT_LO_BASE % SLOT_BITS, 0);
}

/// Reference compression matches the `blake3` crate for empty input
/// (a single root-block, single-chunk, ROOT-flagged compression).
#[test]
fn compress_matches_blake3_crate_empty() {
    let state = blake3_compress(
        &BLAKE3_IV,
        &[0u32; 16],
        0,
        0,
        CHUNK_START | CHUNK_END | ROOT,
    );
    let mut got = [0u8; 32];
    for w in 0..8 {
        got[w * 4..w * 4 + 4].copy_from_slice(&state[w].to_le_bytes());
    }
    let expected = *::blake3::hash(b"").as_bytes();
    assert_eq!(got, expected);
}

/// Reference compression matches the `blake3` crate for a full 64-byte
/// input (single block + single chunk + root).
#[test]
fn compress_matches_blake3_crate_64_bytes() {
    let mut rng = Rng::new(0xDEAD_BEEF);
    let mut bytes = [0u8; 64];
    for byte in bytes.iter_mut() {
        *byte = (rng.next_u32() & 0xFF) as u8;
    }
    let mut m = [0u32; 16];
    for i in 0..16 {
        m[i] = u32::from_le_bytes(bytes[i * 4..i * 4 + 4].try_into().unwrap());
    }
    let state = blake3_compress(&BLAKE3_IV, &m, 0, 64, CHUNK_START | CHUNK_END | ROOT);
    let mut got = [0u8; 32];
    for w in 0..8 {
        got[w * 4..w * 4 + 4].copy_from_slice(&state[w].to_le_bytes());
    }
    let expected = *::blake3::hash(&bytes).as_bytes();
    assert_eq!(got, expected);
}

#[test]
fn honest_witness_satisfies_r1cs() {
    let mut rng = Rng::new(0xCAFE_F00D);
    for &n_blocks in &[1usize, 3, 8] {
        let n_log = min_n_blocks_log(n_blocks).max(3);
        let r1cs = build_block_r1cs(n_log);
        let blocks: Vec<Compression> = (0..n_blocks)
            .map(|_| {
                let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
                let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                (cv, m, rng.next_u32() as u64, 64u32, 11u32)
            })
            .collect();
        let z = generate_witness(&blocks, n_log);
        assert_eq!(z.len(), r1cs.n());
        assert!(
            r1cs.satisfies(&z),
            "witness for {n_blocks} compressions fails R1CS"
        );
    }
}

/// `generate_witness_with_ab_packed` agrees with the matrix-vector
/// products `apply_a_packed(z)` and `apply_b_packed(z)`. Also asserts
/// `apply_c_packed(z) == z` (C = I), validating the aliasing assumption
/// used by prove_fast.
#[test]
fn generate_witness_with_ab_packed_matches_apply() {
    for &n_blocks in &[1usize, 4, 8] {
        let n_log = min_n_blocks_log(n_blocks).max(3);
        let r1cs = build_block_r1cs(n_log);
        let mut rng = Rng::new(0xABCD_5A55 + n_blocks as u64);
        let blocks: Vec<Compression> = (0..n_blocks)
            .map(|_| {
                let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
                let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                (cv, m, rng.next_u32() as u64, 64u32, 11u32)
            })
            .collect();

        let (z, a, b) = generate_witness_with_ab_packed(&blocks, n_log);
        let a_ref = r1cs.apply_a_packed(&z);
        let b_ref = r1cs.apply_b_packed(&z);
        let c_ref = r1cs.apply_c_packed(&z);
        assert_eq!(a, a_ref, "a mismatch at n_blocks={n_blocks}");
        assert_eq!(b, b_ref, "b mismatch at n_blocks={n_blocks}");
        // C = I, so c == z. prove_fast relies on this for the c-aliasing.
        assert_eq!(c_ref, z, "C is not identity at n_blocks={n_blocks}");
        assert!(r1cs.satisfies_packed(&z));
    }
}

/// The fused generator produces (z, a, b) byte-identical to
/// `generate_witness_with_ab_packed` AND a lincheck stripe byte-identical
/// `Blake3LincheckCircuit` walker matches the sparse fold byte-for-byte
/// at random α + random eq_inner.
#[test]
fn lincheck_circuit_matches_sparse() {
    let mut rng = Rng::new(0xB1A_E3_CCA1);
    let (a_0, b_0) = build_matrices();
    let sparse = SparseMatrixCircuit::new(&a_0, &b_0);
    let walker = Blake3LincheckCircuit;
    assert_eq!(sparse.n_cols(), walker.n_cols());

    let n_cols = walker.n_cols();
    let alpha = F128 {
        lo: ((rng.next_u32() as u64) << 32) | rng.next_u32() as u64,
        hi: ((rng.next_u32() as u64) << 32) | rng.next_u32() as u64,
    };
    let eq_inner: Vec<F128> = (0..n_cols)
        .map(|_| F128 {
            lo: ((rng.next_u32() as u64) << 32) | rng.next_u32() as u64,
            hi: ((rng.next_u32() as u64) << 32) | rng.next_u32() as u64,
        })
        .collect();

    let expected = sparse.fold_alpha_batched(alpha, &eq_inner);
    let got = walker.fold_alpha_batched(alpha, &eq_inner);
    for c in 0..n_cols {
        assert_eq!(expected[c], got[c], "comb mismatch at col {c}");
    }

    // CSC gather (what prove_fast/verify actually use) matches too.
    let csc = flock_core::lincheck::CscCircuit::from_matrices(&a_0, &b_0);
    let got_csc = csc.fold_alpha_batched(alpha, &eq_inner);
    assert_eq!(expected, got_csc, "CSC fold mismatch");
}

/// to `pack_z_lincheck_from_packed(z)`.
#[test]
fn fused_lincheck_matches_separate() {
    for &n_blocks in &[1usize, 4, 8, 13] {
        let n_log = min_n_blocks_log(n_blocks).max(3);
        let r1cs = build_block_r1cs(n_log);
        let mut rng = Rng::new(0xABCD_EF00 + n_blocks as u64);
        let blocks: Vec<Compression> = (0..n_blocks)
            .map(|_| {
                let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
                let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                (cv, m, rng.next_u32() as u64, 64u32, 11u32)
            })
            .collect();

        let (z1, a1, b1) = generate_witness_with_ab_packed(&blocks, n_log);
        let lincheck_ref = pack_z_lincheck_from_packed(&z1, r1cs.m, r1cs.k_log);
        let (z2, a2, b2, lincheck_new) =
            generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
        assert_eq!(z1, z2, "z mismatch at n_blocks={n_blocks}");
        assert_eq!(a1, a2, "a mismatch at n_blocks={n_blocks}");
        assert_eq!(b1, b2, "b mismatch at n_blocks={n_blocks}");
        assert_eq!(
            lincheck_ref, lincheck_new,
            "lincheck stripe mismatch at n_blocks={n_blocks}"
        );
    }
}

/// Full prove→verify round-trip through the Ligerito PCS for EACH named
/// profile (fast = JohnsonOod 100-bit, slim = JohnsonOod 100-bit + query
/// grinding, secure = UDR 120-bit). 256 blocks → m=22, the smallest
/// embedded config. Drives OOD binding + fold grinding through the real
/// R1CS / ring-switch / recursive-sumcheck pipeline end to end.
#[test]
fn prove_verify_ligerito_all_profiles() {
    let blocks: Vec<Compression> = {
        let mut rng = Rng::new(0x9A11_0F11);
        (0..256)
            .map(|_| {
                let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
                let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
                (cv, m, 0u64, 64u32, 11u32)
            })
            .collect()
    };
    for profile in [
        LigeritoProfile::Fast,
        LigeritoProfile::Slim,
        LigeritoProfile::Secure,
    ] {
        let setup = Blake3Setup::with_profile(256, profile);
        let mut ch_p = FsChallenger::new(b"flock-blake3-prof");
        let (proof, commitment, claim_p) = setup.prove_ligerito(&blocks, &mut ch_p);
        let mut ch_v = FsChallenger::new(b"flock-blake3-prof");
        let claim_v = setup
            .verify(&commitment, &proof, &mut ch_v)
            .unwrap_or_else(|e| {
                panic!(
                    "ligerito verify rejected for profile {}: {e:?}",
                    profile.as_str()
                )
            });
        assert_eq!(
            claim_p,
            claim_v,
            "claim mismatch for profile {}",
            profile.as_str()
        );
    }
}

/// Ligerito-backend prove_fast roundtrip. Needs ≥ 256 blocks (m=22) for
/// the default Ligerito config at log_batch_size=6.
#[test]
#[ignore]
fn prove_fast_ligerito_roundtrip() {
    let setup = Blake3Setup::new(256);
    let mut rng = Rng::new(0xb1a_3211e);
    let blocks: Vec<Compression> = (0..256)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect();
    let mut ch_p = FsChallenger::new(b"flock-blake3-lig-v0");
    let (proof, commitment, claim_p) = setup.prove_fast(&blocks, &mut ch_p);
    let mut ch_v = FsChallenger::new(b"flock-blake3-lig-v0");
    let claim_v = setup
        .verify(&commitment, &proof, &mut ch_v)
        .unwrap_or_else(|e| panic!("ligerito verify rejected: {e:?}"));
    assert_eq!(claim_p, claim_v);
}

/// End-to-end zk BLAKE3 batch roundtrip (the M4 gate): randomizer rows in
/// the witness, hiding commit, blinded open — verified by the unchanged
/// verifier. Plus satisfiability of the zk witness, mask-seed freshness,
/// and tamper rejection.
#[cfg(feature = "zk")]
#[test]
#[ignore] // Heavier — Ligerito needs m=22
fn prove_fast_zk_ligerito_roundtrip() {
    let setup = Blake3Setup::with_zk(256);
    assert!(setup.r1cs.zk.is_some());
    assert_eq!(
        setup.r1cs.useful_bits,
        1 << K_LOG,
        "blake3 zk fills the block"
    );
    let mut rng = Rng::new(0xb1a_3211e);
    let blocks: Vec<Compression> = (0..256)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect();

    // The zk witness (randomizers included) must satisfy the zk R1CS.
    {
        let layout = setup.r1cs.zk.unwrap();
        let n_total = setup.n_block_slots();
        let mut wr = flock_core::zk::ZkRng::from_seed([9u8; 32]);
        let mut rand_words =
            vec![
                0u64;
                n_total * flock_prover::r1cs_hashes::common::zk_rand_words_per_block(&layout)
            ];
        flock_core::zk::MaskSampler::fill_u64s(&mut wr, &mut rand_words);
        let (z_packed, _a, _b, _stripe) = generate_witness_with_ab_packed_and_lincheck_zk(
            &blocks,
            setup.n_blocks_log(),
            &layout,
            &rand_words,
        );
        assert!(
            setup.r1cs.satisfies_packed(&z_packed),
            "zk witness must satisfy the zk-extended R1CS"
        );
    }

    let prove_seeded = |seed: [u8; 32]| {
        let mut zk_rng = flock_core::zk::ZkRng::from_seed(seed);
        let mut ch_p = FsChallenger::new(b"flock-blake3-lig-zk-v0");
        setup.prove_fast_zk_with_rng(&blocks, &mut zk_rng, &mut ch_p)
    };
    let (proof, commitment, claim_p) = prove_seeded([1u8; 32]);
    let mut ch_v = FsChallenger::new(b"flock-blake3-lig-zk-v0");
    let claim_v = setup
        .verify(&commitment, &proof, &mut ch_v)
        .unwrap_or_else(|e| panic!("zk verify rejected honest proof: {e:?}"));
    assert_eq!(claim_p, claim_v);
    assert!(proof.pcs_open.zk_blind.is_some());

    // Fresh seed ⇒ fresh commitment root and different masked values, still verifies.
    let (proof2, commitment2, _) = prove_seeded([2u8; 32]);
    let mut ch_v2 = FsChallenger::new(b"flock-blake3-lig-zk-v0");
    setup
        .verify(&commitment2, &proof2, &mut ch_v2)
        .expect("fresh-seed zk proof must verify");
    assert_ne!(commitment.root, commitment2.root);
    assert_ne!(
        proof.zerocheck.final_a_eval, proof2.zerocheck.final_a_eval,
        "final_a_eval must be masked by the witness randomizers"
    );
    assert_ne!(
        proof.lincheck.z_partial, proof2.lincheck.z_partial,
        "z_partial must be masked by the witness randomizers"
    );

    // Tamper rejection in zk mode.
    for tamper in 0..3 {
        let mut bad = proof.clone();
        match tamper {
            0 => bad.lincheck.z_partial[0].lo ^= 1,
            1 => bad.zerocheck.final_a_eval.lo ^= 1,
            _ => bad.pcs_open.zk_blind.as_mut().unwrap().y_g.lo ^= 1,
        }
        let mut ch = FsChallenger::new(b"flock-blake3-lig-zk-v0");
        assert!(
            setup.verify(&commitment, &bad, &mut ch).is_err(),
            "tamper {tamper} must be rejected"
        );
    }
}

/// **Z10: end-to-end A1′ reference prover/verifier on a real BLAKE3 zk
/// statement.** Generates a real zk witness (with randomizer rows), runs
/// `prove_r1cs_zk_a1` (masked zerocheck a*b+gamma*P*Q-star plus the hiding
/// P and witness openings), and verifies through
/// `verify_r1cs_zk_a1`. Confirms the full amended pipeline produces an
/// accepting proof; fresh masks give a different transcript that still
/// verifies; tampering `P(ρ)`, `σ_z`, or a masked round message is
/// rejected.
///
/// **Not `#[ignore]`d, deliberately.** It costs under a second in release
/// and it is the only fast-suite test that exercises the *batch-major*
/// witness layout end to end. That matters for amendment A2: batch-major
/// `ab_claim_point` reshuffles the quirky point, and `S` is opened at
/// exactly that point, so the A2 opening takes a code path the row-major
/// m=15 fixture never reaches.
#[cfg(feature = "zk")]
#[test]
fn prove_verify_r1cs_zk_a1_roundtrip() {
    let setup = Blake3Setup::with_zk(256);
    let layout = setup.r1cs.zk.unwrap();
    let mut rng = Rng::new(0xA1E2E);
    let blocks: Vec<Compression> = (0..256)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect();
    let lc_circuit = setup.r1cs.csc_lincheck_circuit();

    let prove = |seed: [u8; 32]| {
        let n_total = setup.n_block_slots();
        let mut wr = flock_core::zk::ZkRng::from_seed(seed);
        let mut rand_words =
            vec![
                0u64;
                n_total * flock_prover::r1cs_hashes::common::zk_rand_words_per_block(&layout)
            ];
        flock_core::zk::MaskSampler::fill_u64s(&mut wr, &mut rand_words);
        let (z_packed, a_f128, b_f128, stripe) = generate_witness_with_ab_packed_and_lincheck_zk(
            &blocks,
            setup.n_blocks_log(),
            &layout,
            &rand_words,
        );
        let mut zk_rng = flock_core::zk::ZkRng::from_seed(seed);
        let mut ch = FsChallenger::new(b"flock-a1-e2e-v0");
        flock_prover::prover::prove_r1cs_zk_a1(
            &setup.r1cs,
            &setup.pcs_params,
            z_packed,
            a_f128,
            b_f128,
            stripe,
            lc_circuit,
            &mut zk_rng,
            &mut ch,
        )
    };

    let (proof, comm) = prove([1u8; 32]);
    let mut chv = FsChallenger::new(b"flock-a1-e2e-v0");
    flock_prover::prover::verify_r1cs_zk_a1(
        &setup.r1cs,
        &setup.pcs_params,
        &proof,
        &comm,
        lc_circuit,
        &mut chv,
    )
    .expect("A1′ e2e proof must verify");

    // Fresh masks ⇒ different transcript, still verifies.
    let (proof2, comm2) = prove([2u8; 32]);
    let mut chv2 = FsChallenger::new(b"flock-a1-e2e-v0");
    flock_prover::prover::verify_r1cs_zk_a1(
        &setup.r1cs,
        &setup.pcs_params,
        &proof2,
        &comm2,
        lc_circuit,
        &mut chv2,
    )
    .expect("fresh-mask A1′ proof must verify");
    assert_ne!(
        proof.proof_nonce, proof2.proof_nonce,
        "the per-proof RO nonce must be fresh"
    );
    assert_ne!(comm.root, comm2.root, "fresh witness mask ⇒ fresh root");
    assert_ne!(
        proof.zerocheck.final_p_eval, proof2.zerocheck.final_p_eval,
        "fresh P ⇒ different P(ρ)"
    );

    // Tamper rejection.
    for t in 0..4 {
        let mut bad = proof.clone();
        match t {
            0 => bad.zerocheck.final_p_eval.lo ^= 1,
            1 => bad.zerocheck.mask_init.lo ^= 1,
            2 => bad.zerocheck.multilinear_rounds[2].1.lo ^= 1,
            _ => bad.proof_nonce[0] ^= 1,
        }
        let mut ch = FsChallenger::new(b"flock-a1-e2e-v0");
        assert!(
            flock_prover::prover::verify_r1cs_zk_a1(
                &setup.r1cs,
                &setup.pcs_params,
                &bad,
                &comm,
                lc_circuit,
                &mut ch
            )
            .is_err(),
            "A1′ tamper {t} must be rejected"
        );
    }
}

/// The certified circuit digest in the ZK certificate registry must be
/// the digest of the real 256-block BLAKE3 zk statement; the gate is
/// otherwise vouching for a circuit nobody proves against. On failure
/// this prints the current digest for an intentional re-pin.
#[cfg(feature = "zk")]
#[test]
fn zk_certificate_digest_matches_setup() {
    let setup = Blake3Setup::with_zk(256);
    let digest = setup.r1cs.statement_digest();
    let Some(cert) = CERTIFIED
        .iter()
        .find(|c| c.family == StatementFamily::Blake3Batch && c.batch_size == 256)
    else {
        assert!(
            require_certified(
                StatementFamily::Blake3Batch,
                256,
                &setup.r1cs,
                &setup.pcs_params,
            )
            .is_err(),
            "an empty certificate registry must fail closed"
        );
        return;
    };
    if cert.circuit_digest != digest {
        let body: Vec<String> = digest.iter().map(|b| format!("0x{b:02x}")).collect();
        panic!(
            "certified circuit_digest is stale. Current statement digest:\n[{}]",
            body.join(", ")
        );
    }
    assert_eq!(cert.pcs_m, setup.pcs_params.m);
    assert_eq!(cert.pcs_log_inv_rate, setup.pcs_params.log_inv_rate);
    assert_eq!(cert.pcs_log_batch_size, setup.pcs_params.log_batch_size);
}

/// The ZK API fails closed: an uncertified batch size is refused before
/// any proving work happens. (Constructing the setup is cheap relative
/// to proving; the gate rejects at the entry point.)
#[cfg(feature = "zk")]
#[test]
#[ignore = "builds a second large zk setup; run with --ignored"]
fn zk_a1_rejects_uncertified_batch_size() {
    let setup = Blake3Setup::with_zk(512);
    let blocks: Vec<Compression> = (0..512)
        .map(|_| ([0u32; 8], [0u32; 16], 0, 64, 11))
        .collect();
    let mut ch = FsChallenger::new(b"flock-a1-gate-test");
    let res = setup.prove_zk_a1(&blocks, &mut ch);
    assert!(
        matches!(
            res,
            Err(flock_prover::zk_certificate::ZkGateError::Uncertified { .. })
        ),
        "uncertified batch size must be refused, got {:?}",
        res.map(|_| "Ok")
    );
}

/// Generic (matrix-driven) Ligerito prove produces a byte-identical
/// proof to the specialized `prove_fast` — pins that the generic path
/// (bool trace → pack → apply → prove) and the fused path agree.
#[test]
fn prove_ligerito_generic_matches_prove_fast() {
    let setup = Blake3Setup::new(256);
    let mut rng = Rng::new(0xb1a_63112);
    let blocks: Vec<Compression> = (0..256)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, 0u64, 64u32, 11u32)
        })
        .collect();
    let mut ch_f = FsChallenger::new(b"flock-blake3-gvf");
    let (proof_f, commit_f, claim_f) = setup.prove_fast(&blocks, &mut ch_f);
    let mut ch_g = FsChallenger::new(b"flock-blake3-gvf");
    let (proof_g, commit_g, claim_g) = setup.prove_ligerito(&blocks, &mut ch_g);
    assert_eq!(commit_f.root, commit_g.root);
    assert_eq!(claim_f, claim_g);
    assert_eq!(
        bincode::serialize(&proof_f).unwrap(),
        bincode::serialize(&proof_g).unwrap(),
        "generic and fused Ligerito proofs must be byte-identical"
    );
}

/// Constant-wire pin (docs/const-wire-pin.md). `new(250)` has padding
/// blocks (filled with a valid all-zero-input compression, constant = 1)
/// so the honest proof verifies; the all-zero witness must be rejected by
/// the pin. (For BLAKE3 the pin lives on the R1CS-built CSC circuit, not
/// the walker.)
#[test]
#[ignore] // Heavier — Ligerito needs m=22; run with `cargo test const_pin_all_zero_rejected -- --ignored`
fn const_pin_all_zero_rejected() {
    let n = 250; // 6 padding blocks at n_block_slots = 256 (m = 22)
    let setup = Blake3Setup::new(n);

    // (1) Honest proof with filled padding verifies.
    let mut rng = Rng::new(0x5EED_B1A3);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| {
            let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            (cv, m, rng.next_u32() as u64, 64u32, 11u32)
        })
        .collect();
    let mut ch_p = FsChallenger::new(b"honest");
    let (proof, commitment, claim_p) = setup.prove_fast(&blocks, &mut ch_p);
    let mut ch_v = FsChallenger::new(b"honest");
    let claim_v = setup
        .verify(&commitment, &proof, &mut ch_v)
        .unwrap_or_else(|e| panic!("honest padded proof rejected: {e:?}"));
    assert_eq!(claim_p, claim_v);

    // (2) All-zero witness must be rejected by the pin.
    let zeros: Vec<Compression> = vec![([0u32; 8], [0u32; 16], 0u64, 0u32, 0u32); n];
    let (mut z, mut a, mut b, mut zlc) =
        generate_witness_with_ab_packed_and_lincheck(&zeros, setup.n_blocks_log());
    z.iter_mut()
        .for_each(|v| *v = flock_core::field::F128::ZERO);
    a.iter_mut()
        .for_each(|v| *v = flock_core::field::F128::ZERO);
    b.iter_mut()
        .for_each(|v| *v = flock_core::field::F128::ZERO);
    zlc.iter_mut().for_each(|v| *v = 0);
    let circuit = setup.r1cs.csc_lincheck_circuit();
    let mut ch_p = FsChallenger::new(b"poc");
    let (proof, commitment, _) = flock_prover::prover::prove_fast_ligerito_from_witness(
        &setup.r1cs,
        &setup.pcs_params,
        z,
        a,
        b,
        zlc,
        circuit,
        None,
        &mut ch_p,
    );
    let mut ch_v = FsChallenger::new(b"poc");
    let res = setup.verify(&commitment, &proof, &mut ch_v);
    assert!(
        matches!(res, Err(flock_core::verifier::VerifyError::Lincheck(_))),
        "all-zero witness must be rejected by the constant-wire pin; got {res:?}"
    );
}

#[test]
fn setup_sizes_correctly() {
    for &(n_blocks, expected_n_log) in &[(1usize, 3), (8, 3), (9, 4), (16, 4), (17, 5), (1000, 10)]
    {
        let setup = Blake3Setup::new(n_blocks);
        assert_eq!(setup.n_blocks_log(), expected_n_log, "n_blocks={n_blocks}");
        assert_eq!(setup.m(), K_LOG + expected_n_log);
        assert!(setup.n_block_slots() >= n_blocks);
    }
}

/// The pinning is enforced, not merely conventional: a witness that uses
/// a different chaining value, counter, length or flag word — even though
/// it is a perfectly valid *compression* — violates the pinned rows.
#[test]
fn pinned_rows_reject_off_parameter_compressions() {
    let mut rng = Rng::new(0xABCD_0042);
    let n_log = 3usize;
    let r1cs = build_block_r1cs_pinned(n_log, ParamPinning::RootHash64);
    let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
    let pad = ParamPinning::RootHash64.padding_compression();

    let cases: [(&str, Compression); 4] = [
        (
            "wrong cv",
            ([7u32; 8], m, 0, ROOT_HASH_BLOCK_LEN, FLAGS_ROOT_HASH),
        ),
        (
            "wrong counter",
            (BLAKE3_IV, m, 1, ROOT_HASH_BLOCK_LEN, FLAGS_ROOT_HASH),
        ),
        ("wrong block_len", (BLAKE3_IV, m, 0, 32, FLAGS_ROOT_HASH)),
        (
            "wrong flags",
            (BLAKE3_IV, m, 0, ROOT_HASH_BLOCK_LEN, CHUNK_START),
        ),
    ];
    for (name, block) in cases {
        let mut all = vec![block];
        all.resize(1usize << n_log, pad);
        let z = generate_witness(&all, n_log);
        assert!(
            !r1cs.satisfies(&z),
            "{name}: a valid compression outside the pinned parameters must \
             NOT satisfy the fixed-digest circuit"
        );
    }

    // Control: the on-parameter compression does satisfy it.
    let mut all = vec![(BLAKE3_IV, m, 0u64, ROOT_HASH_BLOCK_LEN, FLAGS_ROOT_HASH)];
    all.resize(1usize << n_log, pad);
    assert!(r1cs.satisfies(&generate_witness(&all, n_log)));
}

/// Pinning changes the statement digest, so a proof for the free circuit
/// can never be read as a proof for the fixed-digest one.
#[test]
fn pinning_changes_the_statement_digest() {
    let free = build_block_r1cs_pinned(3, ParamPinning::Free);
    let pinned = build_block_r1cs_pinned(3, ParamPinning::RootHash64);
    assert_ne!(free.statement_digest(), pinned.statement_digest());
}

/// Chaining-value and message helpers over the shared [`Rng`].
trait RngChain {
    fn cv(&mut self) -> [u32; 8];
    fn msg(&mut self) -> [u32; 16];
}

impl RngChain for Rng {
    fn cv(&mut self) -> [u32; 8] {
        std::array::from_fn(|_| self.next_u32())
    }
    fn msg(&mut self) -> [u32; 16] {
        std::array::from_fn(|_| self.next_u32())
    }
}

/// The new chaining value out of `compress` is `state[0..8]` = `out_lo`.
fn out_cv(block: &Compression) -> [u32; 8] {
    let (cv, m, ctr, blen, flags) = block;
    let st = blake3_compress(cv, m, *ctr, *blen, *flags);
    let mut o = [0u32; 8];
    o.copy_from_slice(&st[0..8]);
    o
}

/// Build an honest CV chain: each instance's input cv = previous instance's
/// output cv. Messages/counter/flags are arbitrary per instance. Returns the
/// blocks plus public endpoints (cv_0, cv_last).
fn honest_chain(n: usize, seed: u64) -> (Vec<Compression>, [u32; 8], [u32; 8]) {
    let mut rng = Rng(seed);
    let cv0 = rng.cv();
    let mut blocks = Vec::with_capacity(n);
    let mut cur = cv0;
    for _ in 0..n {
        let block: Compression = (cur, rng.msg(), rng.next_u64(), rng.next_u32(), rng.next_u32());
        cur = out_cv(&block); // next input cv = this output cv
        blocks.push(block);
    }
    let cv_last = cur; // = out_cv(blocks[n-1])
    (blocks, cv0, cv_last)
}

/// Ligerito-backend chain roundtrip. Needs ≥ 128 blocks (m=21+).
#[test]
#[ignore]
fn chain_prove_verify_ligerito_roundtrip() {
    // K=256 → n_log=8 → m=22 (smallest Ligerito target with BLAKE3 K_LOG=14).
    let setup = Blake3Setup::new(256);
    let n = setup.n_block_slots();
    let (blocks, cv0, cv_last) = honest_chain(n, 0xB3_511_3E);
    let mut chp = FsChallenger::new(b"b3-chain-lig");
    let (proof, comm) = setup.prove_chain(&blocks, &mut chp);
    let mut chv = FsChallenger::new(b"b3-chain-lig");
    setup
        .verify_chain(&comm, &proof, &cv0, &cv_last, &mut chv)
        .expect("ligerito chain must verify");
}

#[test]
#[ignore] // Heavier — Ligerito needs m=22
fn chain_wrong_endpoint_rejects() {
    let setup = Blake3Setup::new(256);
    let n = setup.n_block_slots();
    let (blocks, cv0, mut cv_last) = honest_chain(n, 0xB3_1234);

    let mut chp = FsChallenger::new(b"b3-chain");
    let (proof, comm) = setup.prove_chain(&blocks, &mut chp);

    cv_last[0] ^= 1; // corrupt the public output endpoint
    let mut chv = FsChallenger::new(b"b3-chain");
    assert!(
        setup
            .verify_chain(&comm, &proof, &cv0, &cv_last, &mut chv)
            .is_err()
    );
}

#[test]
#[ignore] // Heavier — Ligerito needs m=22
fn chain_broken_link_rejects() {
    let setup = Blake3Setup::new(256);
    let n = setup.n_block_slots();
    let (mut blocks, cv0, cv_last) = honest_chain(n, 0xB3_55);

    // Break the chain: instance 2's input cv no longer equals out_cv(block 1).
    let mut rng = Rng(0xB3_999);
    blocks[2].0 = rng.cv();

    let mut chp = FsChallenger::new(b"b3-chain");
    let (proof, comm) = setup.prove_chain(&blocks, &mut chp);
    let mut chv = FsChallenger::new(b"b3-chain");
    assert!(
        setup
            .verify_chain(&comm, &proof, &cv0, &cv_last, &mut chv)
            .is_err()
    );
}

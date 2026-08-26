//! The one BLAKE3 preimage test that reads the `pub(crate)` helper
//! `absorb_statement`. Every other preimage test lives in
//! `crates/flock-prover/tests/r1cs_hashes_blake3_preimage.rs`.

use super::*;
use crate::r1cs_hashes::blake3::ParamPinning;
use crate::r1cs_hashes::blake3::generate_witness_with_ab_packed_and_lincheck_zk_pinned;
use crate::sim_oracle::{OracleChallenger, shared_oracle};
use flock_core::zk::MaskSampler;

/// The smallest batch with a registered Ligerito config: m = k_log +
/// n_log = 14 + 8 = 22, the production shape.
const N_TEST: usize = 256;

fn msgs_of(seed: u64, n: usize) -> Vec<[u8; MESSAGE_BYTES]> {
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

/// **Control 2: an honest prover cannot produce this proof.** Running the
/// real prover on the same patched vector — i.e. without simulating the
/// zerocheck — is rejected. So the simulator's acceptance comes from the
/// simulation, not from the patched vector being secretly acceptable.
#[test]
fn honest_prover_on_the_patched_vector_is_rejected() {
    let setup = Blake3PreimageZkSetup::new(N_TEST);
    let secret = msgs_of(0x7777, N_TEST);
    let digests = Blake3PreimageSetup::digests_of(&secret);
    let stmt = setup.statement(&digests);
    let own = msgs_of(0x8888, N_TEST);

    let layout = setup.r1cs.zk.expect("zk layout");
    let mut zrng = flock_core::zk::ZkRng::from_seed([5u8; 32]);
    let mut rand_words = vec![
        0u64;
        setup.n_block_slots()
            * crate::r1cs_hashes::common::zk_rand_words_per_block(&layout)
    ];
    zrng.fill_u64s(&mut rand_words);
    let blocks: Vec<Compression> = own.iter().map(message_compression).collect();
    let (mut z, _a, _b, _l) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
        &blocks,
        setup.n_blocks_log(),
        &layout,
        &rand_words,
        ParamPinning::RootHash64,
    );
    // Same patch the simulator applies.
    let words_per_block = (1usize << 14) / 128;
    for (i, d) in digests.iter().enumerate() {
        for half in 0..2usize {
            let mut w = flock_core::field::F128::ZERO;
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
    let a = setup.r1cs.apply_a_packed(&z);
    let b = setup.r1cs.apply_b_packed(&z);
    let stripe =
        flock_core::lincheck::pack_z_lincheck_from_packed(&z, setup.r1cs.m, setup.r1cs.k_log);

    let lig = flock_core::pcs::ligerito::prover_config_for(
        setup.pcs_params.log_msg_len(),
        setup.pcs_params.log_batch_size,
        setup.pcs_params.profile,
    )
    .unwrap();
    let oracle = shared_oracle();
    let mut ch = OracleChallenger::new(b"b3-preimage-zk", oracle.clone());
    crate::r1cs_hashes::blake3_preimage::absorb_statement(&mut ch, &stmt);
    let mut mrng = flock_core::zk::ZkRng::from_seed([6u8; 32]);
    let mut forks = crate::prover::A1MaskForks::from_rng(&mut mrng);
    let proof_nonce = forks.proof_nonce;
    let layout_kind = setup.r1cs.layout;
    let stmt2 = stmt.clone();
    let (proof, comm, _) = crate::prover::prove_r1cs_zk_a1_with_masks_pd_nonce(
        &setup.r1cs,
        &setup.pcs_params,
        z,
        a,
        b,
        stripe,
        setup.r1cs.csc_lincheck_circuit(),
        &lig,
        forks.sources(),
        &mut |c: &mut OracleChallenger| {
            let dch = crate::digest_bind::DigestChallenges::sample(&stmt2, c);
            vec![crate::digest_bind::digest_claim(&stmt2, layout_kind, &dch)]
        },
        None, // honest zerocheck — no simulation
        None,
        proof_nonce,
        &mut ch,
    );
    let mut chv = OracleChallenger::new(b"b3-preimage-zk", oracle);
    assert!(
        setup.verify(&comm, &proof, &digests, &mut chv).is_err(),
        "an HONEST prover on the patched vector must be rejected; if this \
         passed, the digest binding would not be enforcing anything"
    );
}

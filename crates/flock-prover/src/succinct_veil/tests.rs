use super::{MaskLayout, SuccinctVeilError};
use crate::r1cs_hashes::blake3::build_block_r1cs_zk;

#[test]
fn succinct_shape_rejects_nonidentity_c() {
    let mut r1cs = build_block_r1cs_zk(3);
    assert!(MaskLayout::new(&r1cs).is_ok());
    r1cs.c_0.rows[0].clear();
    assert!(matches!(
        MaskLayout::new(&r1cs),
        Err(SuccinctVeilError::InvalidShape("R1CS mask geometry"))
    ));
}

// -- ChainMaskShape (Part 7a) -----------------------------------------------

/// Pin keccak's (p, |S|) across the permitted batch range. `sized_for`
/// retunes move the pair; this test fails loudly instead of silently.
#[test]
fn chain_mask_shape_keccak_pinned_across_batch_range() {
    for n_log in [6usize, 8, 12, 19] {
        let layout = crate::r1cs_hashes::keccak::zk_layout(16 + n_log);
        let shape = super::ChainMaskShape::from_layout(&layout, 16);
        assert_eq!(shape.pair_index, 11, "n_log = {n_log}");
        assert_eq!(shape.s_coords, vec![0, 1, 3], "n_log = {n_log}");
        assert_eq!(shape.extra_rounds(), 3);
    }
}

/// Pin blake3's (p, |S|): its zk_config takes no m, so they are constants.
#[test]
fn chain_mask_shape_blake3_pinned() {
    let layout = crate::r1cs_hashes::blake3::zk_layout();
    let shape = super::ChainMaskShape::from_layout(&layout, 14);
    assert_eq!(shape.pair_index, 31);
    assert_eq!(shape.s_coords, vec![0, 1, 2, 3, 4]);
    assert_eq!(shape.extra_rounds(), 5);
}

#[test]
#[should_panic(expected = "chain-mask slot pair")]
fn chain_mask_shape_rejects_layout_without_pair() {
    let cfg = flock_core::zk::ZkConfig {
        rand_chunks_a: 1,
        rand_chunks_b: 1,
        chain_mask: false,
    };
    let layout = flock_core::zk::ZkBlockLayout::new(14, 1024, None, &cfg);
    let _ = super::ChainMaskShape::from_layout(&layout, 14);
}

/// The chain section is CONDITIONAL: absent, the layout is byte-identical
/// to the chainless one; present, observed_count grows by exactly
/// 2 * (n_log + 1 + |S|).
#[test]
fn mask_layout_chain_section_is_conditional() {
    let r1cs = crate::r1cs_hashes::keccak::build_block_r1cs_zk(6);
    let base = MaskLayout::new(&r1cs).expect("chainless layout");
    let same = MaskLayout::with_chain(&r1cs, None).expect("with_chain(None)");
    assert_eq!(base.observed_count(), same.observed_count());

    let zk = r1cs.zk.expect("zk r1cs carries a layout");
    let shape = super::ChainMaskShape::from_layout(&zk, r1cs.k_log);
    let chained = MaskLayout::with_chain(&r1cs, Some(&shape)).expect("chain layout");
    // n_log = 22 - 16 = 6; rounds = 6 + 1 + 3 = 10; two values per round.
    assert_eq!(
        chained.observed_count(),
        base.observed_count() + 2 * (6 + 1 + 3),
    );
}
/// Chain-value mask coverage (Part 7e, scoped audit): the chain claim's eq
/// weight on the mask-pair words is nonzero, so the pair's committed
/// uniform bits one-time-pad the opened value. One nonzero F128
/// coefficient `c` suffices: `{c * basis_b}` over the 128 field basis
/// elements spans F128 over F2, so a single mask WORD with nonzero weight
/// makes `chain_value` uniform. The JOINT uniformity of
/// (ab_value, c_value, chain_value) over the shared pool remains a
/// certification-scope audit — the path is EXPERIMENTAL and uncertified.
#[test]
fn chain_value_has_nonzero_mask_pair_weight() {
    use flock_core::zerocheck::multilinear::eq_eval;
    let layout = crate::r1cs_hashes::keccak::zk_layout(22);
    let shape = super::ChainMaskShape::from_layout(&layout, 16);
    let chain_layout = &crate::r1cs_hashes::keccak::CHAIN_LAYOUT;
    let fold = crate::r1cs_hashes::chain_common::ChainFold::new(
        chain_layout,
        (0..chain_layout.tau_pos_len())
            .map(|i| flock_core::field::F128 {
                lo: 0x1111 * (i as u64 + 3),
                hi: 0x7,
            })
            .collect(),
    );
    // Pseudo-random bound challenges standing in for the FS transcript.
    let claims = crate::chain::ChainClaimsExt {
        instance_point: (0..6)
            .map(|i| flock_core::field::F128 {
                lo: 0xABCD + i as u64,
                hi: 0x99,
            })
            .collect(),
        sel0: flock_core::field::F128 { lo: 0x5, hi: 0x1 },
        s_high: (0..shape.extra_rounds())
            .map(|i| flock_core::field::F128 {
                lo: 0xF0F0 + i as u64,
                hi: 0x3,
            })
            .collect(),
        value: flock_core::field::F128::ZERO,
    };
    let point = crate::r1cs_hashes::chain_common::build_chain_claim_point_ext(
        chain_layout,
        flock_core::r1cs::WitnessLayout::RowMajor,
        &fold,
        &claims,
        &shape.s_coords,
    );
    assert_eq!(point.len(), 22 - 7);

    // First word of the mask pair's IN slot, instance 0 (RowMajor):
    // within-block word index = pair_index * 2 * words_per_region.
    let words_per_region = 1usize << chain_layout.tau_pos_len();
    let word = shape.pair_index * 2 * words_per_region;
    let word_bits: Vec<flock_core::field::F128> = (0..point.len())
        .map(|j| {
            if (word >> j) & 1 == 1 {
                flock_core::field::F128::ONE
            } else {
                flock_core::field::F128::ZERO
            }
        })
        .collect();
    let weight = eq_eval(&point, &word_bits);
    assert_ne!(
        weight,
        flock_core::field::F128::ZERO,
        "the chain claim must reach the mask pair",
    );
}

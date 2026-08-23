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

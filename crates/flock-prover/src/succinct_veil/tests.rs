use super::{MaskLayout, RING_WIDTH, SuccinctVeilError, scale_ring_expressions};
use crate::r1cs_hashes::blake3::build_block_r1cs_zk;
use flock_core::field::F128;
use veil_f128::LinearCombination;

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

#[test]
fn ring_constraint_map_matches_packed_field_scaling() {
    let slices = (0..RING_WIDTH)
        .map(|i| F128::new(i as u64 * 0x9e37 + 1, (i as u64).rotate_left(17)))
        .collect::<Vec<_>>();
    let scalar = F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let expressions = (0..RING_WIDTH)
        .map(LinearCombination::variable)
        .collect::<Vec<_>>();
    let evaluated = scale_ring_expressions(&expressions, scalar)
        .iter()
        .map(|expression| expression.evaluate(&slices).unwrap())
        .collect::<Vec<_>>();

    assert_eq!(
        evaluated,
        flock_core::pcs::ring_switch::scale_s_hat_v(&slices, scalar)
    );
}

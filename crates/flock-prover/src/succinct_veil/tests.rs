use super::{MaskLayout, SuccinctVeilError};

#[test]
fn succinct_shape_rejects_nonidentity_c() {
    let mut r1cs = crate::r1cs_hashes::blake3::build_block_r1cs_zk(3);
    assert!(MaskLayout::new(&r1cs).is_ok());
    r1cs.c_0.rows[0].clear();
    assert!(matches!(
        MaskLayout::new(&r1cs),
        Err(SuccinctVeilError::InvalidShape("R1CS mask geometry"))
    ));
}

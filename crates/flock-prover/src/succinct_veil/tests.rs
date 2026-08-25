use super::{MaskLayout, SuccinctVeilError, validate_succinct_parameters};
use crate::r1cs_hashes::{blake3::build_block_r1cs_zk, blake3_preimage::Blake3PreimageZkSetup};

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
fn succinct_profile_validation_accepts_only_the_supported_circuit_and_pcs() {
    let setup = Blake3PreimageZkSetup::new_succinct(2);
    validate_succinct_parameters(&setup.r1cs, &setup.pcs_params)
        .expect("supported succinct profile");

    let unsupported_shape = Blake3PreimageZkSetup::new(2);
    assert!(matches!(
        validate_succinct_parameters(&unsupported_shape.r1cs, &unsupported_shape.pcs_params),
        Err(SuccinctVeilError::InvalidParameters)
    ));

    let mut modified_circuit = setup.r1cs.clone();
    modified_circuit.a_0.rows[0].push(0);
    assert!(matches!(
        validate_succinct_parameters(&modified_circuit, &setup.pcs_params),
        Err(SuccinctVeilError::InvalidParameters)
    ));

    let mut unsupported_pcs = setup.pcs_params.clone();
    unsupported_pcs.log_inv_rate = 2;
    assert!(matches!(
        validate_succinct_parameters(&setup.r1cs, &unsupported_pcs),
        Err(SuccinctVeilError::InvalidParameters)
    ));
}

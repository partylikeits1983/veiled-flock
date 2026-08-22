use super::*;

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CodecFixture {
    count: u64,
    values: Vec<u64>,
}

#[test]
fn bundle_codec_is_explicit_fixint_and_roundtrips() {
    let fixture = CodecFixture {
        count: 300,
        values: vec![1, 252, 65_536, u64::MAX],
    };
    let encoded = bundle_options().serialize(&fixture).unwrap();

    // Bincode 1.3's root helper uses the same fixed-integer encoding.
    assert_eq!(encoded, bincode::serialize(&fixture).unwrap());
    assert_eq!(
        bundle_options()
            .deserialize::<CodecFixture>(&encoded)
            .unwrap(),
        fixture
    );
}

#[test]
fn decoder_rejects_oversized_input() {
    let bytes = vec![0; MAX_BUNDLE_BYTES as usize + 1];
    assert!(decode_bundle(&bytes).is_err());
}

#[test]
fn decoder_rejects_an_unbounded_digest_vector() {
    let bytes = u64::MAX.to_le_bytes();
    assert!(decode_bundle(&bytes).is_err());
}

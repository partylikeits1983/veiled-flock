//! Fixed inputs shared by the preimage timing and profiling examples.
//! Their operation loops intentionally keep different measurement semantics.

use flock_prover::r1cs_hashes::blake3_preimage::MESSAGE_BYTES;

pub const SIZES: [usize; 7] = [64, 128, 256, 512, 1024, 2048, 4096];
pub const FLOCK_BENCHMARK_DOMAIN: &[u8] = b"flock-blake3-preimage-scaling";

pub fn messages(size: usize) -> Vec<[u8; MESSAGE_BYTES]> {
    (0..size)
        .map(|message_index| {
            std::array::from_fn(|byte_index| {
                let word = (message_index as u64)
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .rotate_left((byte_index % 64) as u32)
                    ^ byte_index as u64;
                word as u8
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_inputs_match_the_published_workload() {
        // Recorded and checked against the original generator before extraction.
        let expected: serde_json::Value =
            serde_json::from_str(include_str!("preimage-vectors.json")).unwrap();
        assert_eq!(serde_json::to_value(SIZES).unwrap(), expected["sizes"]);
        assert_eq!(
            std::str::from_utf8(FLOCK_BENCHMARK_DOMAIN).unwrap(),
            expected["domain"].as_str().unwrap()
        );
        let actual = messages(4096);
        for vector in expected["messages"].as_array().unwrap() {
            let index = vector["index"].as_u64().unwrap() as usize;
            let hex = actual[index]
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();
            assert_eq!(hex, vector["hex"].as_str().unwrap(), "message {index}");
        }
    }
}

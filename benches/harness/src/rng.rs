//! Deterministic Rng for bench inputs.

/// Deterministic splitmix64 generator for bench inputs.
pub struct SplitMix(pub u64);

impl SplitMix {
    /// Return the next pseudo-random word.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Return 32 pseudo-random bytes.
    pub fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.as_chunks_mut::<8>().0 {
            *chunk = self.next_u64().to_le_bytes();
        }
        out
    }
}

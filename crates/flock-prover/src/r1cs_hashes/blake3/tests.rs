//! BLAKE3 encoder tests that read the module's private surface: the
//! bit-index helpers `out_lo_bit`, `out_hi_bit`, `g_add_carry_bit`, the
//! constant `ADD_A2`, and `ParamPinning::pinned`. Every other BLAKE3 test
//! lives in `crates/flock-prover/tests/r1cs_hashes_blake3.rs`.

use super::*;

/// SplitMix64.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }
    fn next_u32(&mut self) -> u32 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        (z ^ (z >> 31)) as u32
    }
}

/// BLAKE3 chunk flags (subset).
const CHUNK_START: u32 = 1 << 0;

const CHUNK_END: u32 = 1 << 1;

const ROOT: u32 = 1 << 3;

/// Witness's out_lo / out_hi slots equal the BLAKE3 finalization XORs.
#[test]
fn witness_encodes_correct_output() {
    let mut rng = Rng::new(0x1234_5678);
    let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
    let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
    let counter = ((rng.next_u32() as u64) << 32) | (rng.next_u32() as u64);
    let block_len = 64;
    let flags = CHUNK_START | CHUNK_END | ROOT;
    let z = build_block_witness(&cv, &m, counter, block_len, flags);
    let expected = blake3_compress(&cv, &m, counter, block_len, flags);
    for w in 0..8 {
        let mut got = 0u32;
        for b in 0..WORD_BITS {
            if z[out_lo_bit(w, b)] {
                got |= 1 << b;
            }
        }
        assert_eq!(got, expected[w], "out_lo[{w}] mismatch");
        let mut got_hi = 0u32;
        for b in 0..WORD_BITS {
            if z[out_hi_bit(w, b)] {
                got_hi |= 1 << b;
            }
        }
        assert_eq!(got_hi, expected[w + 8], "out_hi[{w}] mismatch");
    }
}

#[test]
fn mutated_witness_fails() {
    let mut rng = Rng::new(0xBEEF_F00D);
    let cv: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
    let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
    let r1cs = build_block_r1cs(3);
    let blocks = vec![(cv, m, 0u64, 64u32, 11u32)];
    let mut z = generate_witness(&blocks, 3);
    assert!(r1cs.satisfies(&z));
    // Flip a carry_aux bit inside G #10 (middle of round 1).
    z[g_add_carry_bit(10, ADD_A2, 5)] ^= true;
    assert!(
        !r1cs.satisfies(&z),
        "tampered carry bit should violate R1CS"
    );
}

// -----------------------------------------------------------------------
// Fixed-digest relation: the pinned circuit computes a real BLAKE3 hash
// -----------------------------------------------------------------------

/// The pinning constants ARE BLAKE3's single-block root-hash
/// configuration: compressing a 64-byte message under them reproduces the
/// `blake3` crate's digest of those bytes. This is what licenses reading
/// `out_lo` as "the BLAKE3 hash of the message".
#[test]
fn root_hash_pinning_matches_the_blake3_crate() {
    let mut rng = Rng::new(0x9E37_79B9);
    let mut bytes = [0u8; 64];
    for b in bytes.iter_mut() {
        *b = (rng.next_u32() & 0xFF) as u8;
    }
    let mut m = [0u32; 16];
    for (i, w) in m.iter_mut().enumerate() {
        *w = u32::from_le_bytes(bytes[i * 4..i * 4 + 4].try_into().unwrap());
    }
    let p = ParamPinning::RootHash64.pinned().expect("pinned params");
    assert_eq!(p.cv, BLAKE3_IV);
    assert_eq!(p.counter, 0);
    assert_eq!(p.block_len, 64);
    assert_eq!(p.flags, CHUNK_START | CHUNK_END | ROOT);

    let state = blake3_compress(&p.cv, &m, p.counter, p.block_len, p.flags);
    let mut got = [0u8; 32];
    for w in 0..8 {
        got[w * 4..w * 4 + 4].copy_from_slice(&state[w].to_le_bytes());
    }
    assert_eq!(got, *::blake3::hash(&bytes).as_bytes());
}

/// An honest preimage witness satisfies the pinned R1CS, and its `out_lo`
/// region carries exactly the real BLAKE3 digest of the message.
#[test]
fn pinned_witness_satisfies_and_carries_the_digest() {
    let mut rng = Rng::new(0x5EED_1234);
    let n_log = 3usize;
    let r1cs = build_block_r1cs_pinned(n_log, ParamPinning::RootHash64);
    let n_blocks = 5usize;
    let msgs: Vec<[u32; 16]> = (0..n_blocks)
        .map(|_| std::array::from_fn(|_| rng.next_u32()))
        .collect();
    let blocks: Vec<Compression> = msgs
        .iter()
        .map(|m| (BLAKE3_IV, *m, 0u64, ROOT_HASH_BLOCK_LEN, FLAGS_ROOT_HASH))
        .collect();
    // Padding slots must carry the pinning's padding compression, or the
    // pinned rows fail there.
    let mut all = blocks.clone();
    all.resize(
        1usize << n_log,
        ParamPinning::RootHash64.padding_compression(),
    );
    let z = generate_witness(&all, n_log);
    assert!(
        r1cs.satisfies(&z),
        "honest preimage witness must satisfy the pinned R1CS"
    );

    // out_lo of each real block is the BLAKE3 digest of its message.
    for (i, m) in msgs.iter().enumerate() {
        let mut bytes = [0u8; 64];
        for (j, w) in m.iter().enumerate() {
            bytes[j * 4..j * 4 + 4].copy_from_slice(&w.to_le_bytes());
        }
        let expected = *::blake3::hash(&bytes).as_bytes();
        let mut got = [0u8; 32];
        for w in 0..8 {
            let mut word = 0u32;
            for b in 0..WORD_BITS {
                if z[i * K + out_lo_bit(w, b)] {
                    word |= 1 << b;
                }
            }
            got[w * 4..w * 4 + 4].copy_from_slice(&word.to_le_bytes());
        }
        assert_eq!(got, expected, "block {i}: out_lo is not BLAKE3(message)");
    }
}

/// The padding slot's digest is a publicly computable constant —
/// BLAKE3 of the all-zero 64-byte message — NOT zero. A digest statement
/// that assumed zero padding would compute the wrong target.
#[test]
fn padding_digest_is_the_hash_of_zeros_not_zero() {
    let words = ParamPinning::RootHash64.padding_digest_words();
    let mut got = [0u8; 32];
    for w in 0..8 {
        got[w * 4..w * 4 + 4].copy_from_slice(&words[w].to_le_bytes());
    }
    assert_eq!(got, *::blake3::hash(&[0u8; 64]).as_bytes());
    assert_ne!(words, [0u32; 8], "padding digest must not be zero");

    // And it is what the witness actually carries in a padding slot.
    let n_log = 2usize;
    let pad = ParamPinning::RootHash64.padding_compression();
    let all = vec![pad; 1usize << n_log];
    let z = generate_witness(&all, n_log);
    for w in 0..8 {
        let mut word = 0u32;
        for b in 0..WORD_BITS {
            if z[K + out_lo_bit(w, b)] {
                word |= 1 << b;
            }
        }
        assert_eq!(word, words[w], "padding slot out_lo[{w}] mismatch");
    }
}

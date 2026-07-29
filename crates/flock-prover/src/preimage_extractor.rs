//! **The knowledge extractor** for the fixed-digest relation.
//!
//! Zero knowledge says a proof reveals nothing. It says nothing about whether
//! the prover *knew* anything — for that the argument needs an extractor, and
//! without one "argument of knowledge" is a phrase rather than a claim.
//!
//! ## What the extractor must produce, and what must not satisfy it
//!
//! It must output byte strings `x_1..x_n` that the caller can hash **outside
//! the circuit** and compare against the public digests. Three near-misses
//! would each be worthless, and this module is written so that none of them
//! can pass unnoticed:
//!
//! 1. recovering the **mask columns** (the randomizer rows, `P`, `Q`, `S`,
//!    `S_c`, `S_h`) instead of witness columns — they are also committed data,
//!    and an extractor that read the wrong region would look successful;
//! 2. recovering an assignment that satisfies the R1CS but is **not tied to
//!    the public digests**;
//! 3. recovering an *opening claim* rather than the committed message.
//!
//! The guard against all three is the same: extraction ends with an external
//! `BLAKE3(x_i) == y_i` check that the circuit plays no part in.
//!
//! ## Where the committed message comes from
//!
//! In the classical ROM the extractor is **straightline**: it reads the
//! prover's random-oracle query transcript, and because every Merkle leaf the
//! prover commits is an oracle query, it recovers the committed codeword and
//! decodes it. That step is the standard BCS argument and is not specific to
//! this system.
//!
//! What *is* specific to this system — and is where a mistake would actually
//! hide — is everything after: which coordinates of the committed vector are
//! the message, how they are packed, and whether what comes out is a real
//! preimage or a mask column. That is what this module implements and tests.
//! [`extract_preimages`] therefore takes the committed message as its input,
//! which is exactly what the ROM observation step yields; the tests supply it
//! from an honest run and from a simulated one, and the two must behave
//! differently.

use flock_core::field::F128;

use crate::r1cs_hashes::blake3::{K_LOG, M_BASE, WORD_BITS};
use crate::r1cs_hashes::blake3_preimage::{DIGEST_BYTES, MESSAGE_BYTES};

/// Why extraction failed.
#[derive(Debug, PartialEq, Eq)]
pub enum ExtractError {
    /// The committed vector is the wrong shape for this statement.
    BadShape { expected: usize, got: usize },
    /// A recovered candidate does not hash to the public digest. This is the
    /// check that makes the extractor meaningful: it fails for a prover that
    /// knew no preimage, however well-formed its proof looked.
    NotAPreimage { index: usize },
}

impl std::fmt::Display for ExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BadShape { expected, got } => {
                write!(f, "committed message has {got} words, expected {expected}")
            }
            Self::NotAPreimage { index } => write!(
                f,
                "recovered candidate {index} does not hash to the public digest — \
                 the prover did not know a preimage"
            ),
        }
    }
}

impl std::error::Error for ExtractError {}

/// Read the message words of instance `i` out of a packed committed vector.
///
/// The message occupies bits `[M_BASE, M_BASE + 512)` of each block, and the
/// packed representation puts logical bit `j` of the block at bit `j % 128` of
/// packed word `j / 128`. Nothing else in the block is touched — in
/// particular the randomizer sections, which live above `useful_bits`, are
/// never read, so a mask column cannot be mistaken for a message.
pub fn message_bytes_at(z_packed: &[F128], instance: usize) -> [u8; MESSAGE_BYTES] {
    let words_per_block = (1usize << K_LOG) / 128;
    let base = instance * words_per_block;
    let mut out = [0u8; MESSAGE_BYTES];
    for w in 0..16usize {
        let mut word = 0u32;
        for b in 0..WORD_BITS {
            let bit = M_BASE + w * WORD_BITS + b;
            let packed = z_packed[base + bit / 128];
            let set = if bit % 128 < 64 {
                (packed.lo >> (bit % 128)) & 1 == 1
            } else {
                (packed.hi >> (bit % 128 - 64)) & 1 == 1
            };
            if set {
                word |= 1 << b;
            }
        }
        out[w * 4..w * 4 + 4].copy_from_slice(&word.to_le_bytes());
    }
    out
}

/// Extract the preimages a proof's committed vector encodes, and **verify them
/// outside the circuit**.
///
/// `z_packed` is the committed message, as the straightline ROM observation
/// step yields it. `digests` is the public statement.
///
/// Returning `Ok` means: these byte strings hash to those digests, checked by
/// the `blake3` crate with no reference to the circuit, the proof, or any
/// claim inside it. That is the whole content of "the prover knew a preimage".
pub fn extract_preimages(
    z_packed: &[F128],
    digests: &[[u8; DIGEST_BYTES]],
    n_block_slots: usize,
) -> Result<Vec<[u8; MESSAGE_BYTES]>, ExtractError> {
    let words_per_block = (1usize << K_LOG) / 128;
    let expected = n_block_slots * words_per_block;
    if z_packed.len() != expected {
        return Err(ExtractError::BadShape {
            expected,
            got: z_packed.len(),
        });
    }
    let mut out = Vec::with_capacity(digests.len());
    for (i, d) in digests.iter().enumerate() {
        let candidate = message_bytes_at(z_packed, i);
        if ::blake3::hash(&candidate).as_bytes() != d {
            return Err(ExtractError::NotAPreimage { index: i });
        }
        out.push(candidate);
    }
    Ok(out)
}

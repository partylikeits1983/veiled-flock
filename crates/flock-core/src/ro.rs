//! Domain-separated random-oracle layer for the point-hashed roles: Merkle
//! leaves, Merkle internal nodes, and proof-of-work queries.
//!
//! # Why this module exists
//!
//! Before this layer, every SHA-256 use in the system — Merkle leaves, internal
//! nodes, Fiat–Shamir squeezes, and PoW grinding — hashed undifferentiated byte
//! strings. A 40-byte PoW query was syntactically indistinguishable from a
//! 40-byte leaf; the ROM model that the zero-knowledge and knowledge proofs rely
//! on requires those uses to be *disjoint* oracle domains. This module gives
//! every point-hashed role an injective framing, so no two roles can ever accept
//! the same encoded input.
//!
//! The streaming Fiat–Shamir duplex ([`crate::challenger`]) stays as it is; it
//! is not point-keyed. This module covers only the roles that hash a
//! self-contained point: `ROLE_LEAF`, `ROLE_NODE`, `ROLE_POW`.
//!
//! # Framing
//!
//! Every point is `header (64 bytes) ‖ level (4 LE) ‖ index (8 LE) ‖ payload`,
//! and its digest is exactly `SHA256` of that concatenation. The 64-byte header
//! is constant across a whole (tree, role); [`RoTreeHasher`] compresses it once
//! into a SHA-256 midstate and continues each node's hash from there, so at
//! block-aligned leaf sizes (the production shapes) there is **zero** extra
//! per-node compression versus the old untagged hash — the 12-byte `level‖index`
//! prefix fits in the final padding block's slack.
//!
//! Because the framed digest is a plain `SHA256` of the concatenation, a
//! [`RecordingOracle`] that observes the full framed point bytes sees exactly
//! what the production hasher computes — which is what lets the straightline
//! extractor (Phase 5) reconstruct the committed leaves from an adversary's
//! query transcript.

use crate::merkle::Hash;
use sha2::{Digest, Sha256};

/// Fixed magic distinguishing this framing from any other 7-byte-tagged data.
pub const RO_MAGIC: [u8; 7] = *b"FLOCKRO";

/// Role byte for a Merkle leaf hash.
pub const ROLE_LEAF: u8 = 0x10;
/// Role byte for a Merkle internal-node hash.
pub const ROLE_NODE: u8 = 0x11;
/// Role byte for a proof-of-work query.
pub const ROLE_POW: u8 = 0x12;

/// Which committed object a tree belongs to. Distinct channels get disjoint
/// leaf/node domains so an opened leaf of one commitment can never be reused as
/// a leaf of another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum RoChannel {
    /// The witness / message commitment (`commit_zk` of `[μ ‖ z]`).
    Witness = 0,
    /// The `P` mask commitment.
    MaskP = 1,
    /// The `Q` mask commitment (unused once Design A deletes it, reserved).
    MaskQ = 2,
    /// The lincheck `S` mask commitment.
    MaskS = 3,
    /// The A3 `S_c` mask commitment.
    MaskSc = 4,
    /// The A3 `S_h` mask commitment.
    MaskSh = 5,
    /// The succinct VEIL compiler's committed linear-witness matrix.
    VeilLinear = 6,
    /// The succinct VEIL compiler's committed Hadamard matrix.
    VeilHadamard = 7,
}

impl RoChannel {
    #[inline]
    pub fn as_u8(self) -> u8 {
        self as u8
    }
}

/// The immutable context every point-oracle call is framed against: the
/// per-tree/object nonce (public; provides freshness) and the backend that answers
/// queries (native SHA-256, or an external recording/programmable oracle used
/// in the simulator and extractor).
#[derive(Clone)]
pub struct RoContext {
    nonce: [u8; 32],
    backend: RoBackend,
}

/// How point hashes are answered.
#[derive(Clone)]
pub enum RoBackend {
    /// Production SHA-256, computed directly (with the midstate optimization).
    Native,
    /// An external oracle that observes/answers every framed point — recording
    /// (extractor) or programmable (simulator).
    External(std::sync::Arc<dyn ByteOracle>),
}

impl RoContext {
    /// A production context with a fresh per-tree/object `nonce`.
    pub fn native(nonce: [u8; 32]) -> Self {
        Self {
            nonce,
            backend: RoBackend::Native,
        }
    }

    /// A context with the all-zero nonce, for the non-zk paths that make no
    /// freshness/hiding claim. Roles are still separated by tag.
    pub fn plain() -> Self {
        Self {
            nonce: [0u8; 32],
            backend: RoBackend::Native,
        }
    }

    /// A context routing every point through an external oracle.
    pub fn external(nonce: [u8; 32], oracle: std::sync::Arc<dyn ByteOracle>) -> Self {
        Self {
            nonce,
            backend: RoBackend::External(oracle),
        }
    }

    #[inline]
    pub fn nonce(&self) -> &[u8; 32] {
        &self.nonce
    }

    #[inline]
    pub fn is_native(&self) -> bool {
        matches!(self.backend, RoBackend::Native)
    }
}

/// The 64-byte constant header for a (role, channel, tree-depth) context.
///
/// Layout (little-endian for multibyte integers):
/// ```text
///   [0]      role
///   [1..8]   RO_MAGIC ("FLOCKRO")
///   [8]      channel
///   [9]      tree depth (Ligerito recursion level of the whole tree)
///   [10..16] reserved (zero)
///   [16..48] nonce
///   [48..56] leaf_len (u64 LE)
///   [56..64] reserved (zero)
/// ```
pub fn encode_header(
    role: u8,
    channel: RoChannel,
    tree_depth: u8,
    nonce: &[u8; 32],
    leaf_len: u64,
) -> [u8; 64] {
    let mut h = [0u8; 64];
    h[0] = role;
    h[1..8].copy_from_slice(&RO_MAGIC);
    h[8] = channel.as_u8();
    h[9] = tree_depth;
    // h[10..16] reserved, already zero.
    h[16..48].copy_from_slice(nonce);
    h[48..56].copy_from_slice(&leaf_len.to_le_bytes());
    h
}

/// Assemble the full framed point bytes for a node: `header ‖ level ‖ index ‖
/// payload`. This is the exact preimage whose SHA-256 is the node's digest, and
/// the exact bytes a [`RecordingOracle`] observes.
pub fn encode_point(header: &[u8; 64], level: u32, index: u64, payload: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(64 + 12 + payload.len());
    v.extend_from_slice(header);
    v.extend_from_slice(&encode_location(level, index));
    v.extend_from_slice(payload);
    v
}

/// Encode the per-point location prefix shared by tree leaves and nodes.
#[inline]
pub fn encode_location(level: u32, index: u64) -> [u8; 12] {
    let mut location = [0u8; 12];
    location[..4].copy_from_slice(&level.to_le_bytes());
    location[4..].copy_from_slice(&index.to_le_bytes());
    location
}

/// The PoW point: `[ROLE_POW] ‖ state(32) ‖ nonce8(8)` — 41 bytes, one SHA-256
/// compression, so grinding cost is unchanged. The FS transcript `state` is the
/// per-attempt base digest.
pub fn encode_pow_point(state: &[u8; 32], pow_nonce: u64) -> [u8; 41] {
    let mut p = [0u8; 41];
    p[0] = ROLE_POW;
    p[1..33].copy_from_slice(state);
    p[33..41].copy_from_slice(&pow_nonce.to_le_bytes());
    p
}

/// An oracle that answers a framed point with a 32-byte digest, observing it.
///
/// Object-safe so test/simulator/extractor backends can be stored as
/// `Arc<dyn ByteOracle>`. The production path does not go through this trait
/// (it uses the midstate hasher directly); this is for external recording and
/// programming.
pub trait ByteOracle: Send + Sync {
    /// Answer (and observe) a framed point. Must equal `SHA256(point)` unless
    /// the point has been explicitly programmed.
    fn answer(&self, point: &[u8]) -> Hash;
}

/// Native random-oracle answer for an already encoded point.
#[inline]
pub fn hash_point(point: &[u8]) -> Hash {
    Sha256::digest(point).into()
}

/// A hasher specialized to one (tree, role) context: it holds the header
/// midstate so each node hash is `continue-from-midstate(level ‖ index ‖
/// payload)`, byte-identical to `SHA256(header ‖ level ‖ index ‖ payload)`.
pub enum RoTreeHasher<'a> {
    /// Native: a SHA-256 state that has absorbed the 64-byte header (one
    /// compression, done once), cloned per node.
    Native {
        mid: Sha256,
        mid_words: [u32; 8],
        header: [u8; 64],
    },
    /// External: full framed points are handed to the oracle.
    External {
        oracle: &'a dyn ByteOracle,
        header: [u8; 64],
    },
}

impl<'a> RoTreeHasher<'a> {
    /// Build a hasher for `role` over `ctx`'s backend, at Ligerito tree depth
    /// `tree_depth`, hashing leaves of `leaf_len` bytes.
    pub fn new(
        ctx: &'a RoContext,
        role: u8,
        channel: RoChannel,
        tree_depth: u8,
        leaf_len: u64,
    ) -> Self {
        let header = encode_header(role, channel, tree_depth, ctx.nonce(), leaf_len);
        match &ctx.backend {
            RoBackend::Native => {
                let mut mid = Sha256::new();
                mid.update(header);
                let mut mid_words = crate::merkle::SHA256_IV;
                sha2::compress256(&mut mid_words, &[header.into()]);
                RoTreeHasher::Native {
                    mid,
                    mid_words,
                    header,
                }
            }
            RoBackend::External(oracle) => RoTreeHasher::External {
                oracle: oracle.as_ref(),
                header,
            },
        }
    }

    /// Hash one framed node at `(level, index)` over `payload`.
    #[inline]
    pub fn hash(&self, level: u32, index: u64, payload: &[u8]) -> Hash {
        match self {
            RoTreeHasher::Native { mid, .. } => {
                let mut h = mid.clone();
                h.update(level.to_le_bytes());
                h.update(index.to_le_bytes());
                h.update(payload);
                h.finalize().into()
            }
            RoTreeHasher::External { oracle, header } => {
                oracle.answer(&encode_point(header, level, index, payload))
            }
        }
    }

    /// The (constant) header this hasher frames against — for building the same
    /// point bytes an external oracle would observe.
    pub fn header(&self) -> &[u8; 64] {
        match self {
            RoTreeHasher::Native { header, .. } | RoTreeHasher::External { header, .. } => header,
        }
    }

    /// Native SHA-256 state after the 64-byte tree header has been compressed.
    /// The architecture-specific four-way kernels continue from these words.
    #[inline]
    pub(crate) fn native_midstate(&self) -> Option<&[u32; 8]> {
        match self {
            RoTreeHasher::Native { mid_words, .. } => Some(mid_words),
            RoTreeHasher::External { .. } => None,
        }
    }
}

/// A recording oracle: answers every framed point with production SHA-256 and
/// records `(point, digest)` in query order. The Phase-5 straightline extractor
/// reads this transcript to reconstruct committed leaves.
///
/// Interior-mutable and `Send + Sync` so it can be shared across the rayon
/// hashing of one tree; records are keyed later by parsing the framed points,
/// so recording order does not matter for correctness.
pub struct RecordingOracle {
    log: std::sync::Mutex<Vec<(Vec<u8>, Hash)>>,
    record: bool,
}

impl RecordingOracle {
    pub fn new() -> Self {
        Self {
            log: std::sync::Mutex::new(Vec::new()),
            record: true,
        }
    }

    /// A recording oracle that answers but does not retain points (bounded
    /// memory) — for byte-compat checks that only need production digests.
    pub fn answering_only() -> Self {
        Self {
            log: std::sync::Mutex::new(Vec::new()),
            record: false,
        }
    }

    /// Every observed `(framed point, digest)`, in observation order.
    pub fn queries(&self) -> Vec<(Vec<u8>, Hash)> {
        self.log.lock().unwrap().clone()
    }

    /// Leaf-query preimages for `channel`, keyed by leaf index. Parses the
    /// framed header so recording order is irrelevant. Returns the payload
    /// (the bytes after the `level‖index` prefix) per index.
    pub fn leaf_payloads(&self, channel: RoChannel) -> Vec<(u64, Vec<u8>)> {
        let log = self.log.lock().unwrap();
        let mut out = Vec::new();
        for (point, _) in log.iter() {
            if point.len() < 64 + 12 {
                continue;
            }
            if point[0] != ROLE_LEAF || point[1..8] != RO_MAGIC || point[8] != channel.as_u8() {
                continue;
            }
            let index = u64::from_le_bytes(point[68..76].try_into().unwrap());
            out.push((index, point[76..].to_vec()));
        }
        out
    }
}

impl Default for RecordingOracle {
    fn default() -> Self {
        Self::new()
    }
}

impl ByteOracle for RecordingOracle {
    fn answer(&self, point: &[u8]) -> Hash {
        let digest = hash_point(point);
        if self.record {
            self.log.lock().unwrap().push((point.to_vec(), digest));
        }
        digest
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn ctx() -> RoContext {
        RoContext::native([7u8; 32])
    }

    #[test]
    fn native_tree_hasher_matches_one_shot_reference() {
        // The midstate hasher must equal SHA256(header ‖ level ‖ index ‖ payload)
        // for every tail shape (block-aligned, one tail block, two tail blocks).
        let ctx = ctx();
        for leaf_len in [64usize, 100, 60, 56, 128, 12, 0] {
            let payload: Vec<u8> = (0..leaf_len).map(|i| (i as u8).wrapping_mul(37)).collect();
            let hasher = RoTreeHasher::new(&ctx, ROLE_LEAF, RoChannel::Witness, 0, leaf_len as u64);
            for (level, index) in [(0u32, 0u64), (0, 3), (5, 12345)] {
                let got = hasher.hash(level, index, &payload);
                let want: Hash =
                    Sha256::digest(encode_point(hasher.header(), level, index, &payload)).into();
                assert_eq!(got, want, "leaf_len={leaf_len} level={level} index={index}");
            }
        }
    }

    #[test]
    fn ro_first_byte_roles_are_disjoint() {
        assert_ne!(ROLE_LEAF, ROLE_NODE);
        assert_ne!(ROLE_LEAF, ROLE_POW);
        assert_ne!(ROLE_NODE, ROLE_POW);
        assert!(
            [ROLE_LEAF, ROLE_NODE, ROLE_POW]
                .iter()
                .all(|role| !(0x01..=0x05).contains(role))
        );
        // No two (role, channel, depth) contexts share a header prefix, so no
        // two point-oracle domains can collide under any payload.
        let nonce = [9u8; 32];
        let mut seen = std::collections::HashSet::new();
        for role in [ROLE_LEAF, ROLE_NODE] {
            for channel in [
                RoChannel::Witness,
                RoChannel::MaskP,
                RoChannel::MaskQ,
                RoChannel::MaskS,
                RoChannel::MaskSc,
                RoChannel::MaskSh,
                RoChannel::VeilLinear,
                RoChannel::VeilHadamard,
            ] {
                for depth in [0u8, 1, 2] {
                    let h = encode_header(role, channel, depth, &nonce, 64);
                    assert!(
                        seen.insert(h),
                        "duplicate header role={role} ch={channel:?} depth={depth}"
                    );
                }
            }
        }
    }

    #[test]
    fn leaf_point_cannot_parse_as_pow_point() {
        // A leaf point starts with ROLE_LEAF (0x10); a PoW point with ROLE_POW
        // (0x12). First byte alone separates them, for any payload/state.
        let ctx = ctx();
        let hasher = RoTreeHasher::new(&ctx, ROLE_LEAF, RoChannel::Witness, 0, 40);
        let leaf_point = encode_point(hasher.header(), 0, 0, &[0u8; 40]);
        let pow_point = encode_pow_point(&[0u8; 32], 0);
        assert_eq!(leaf_point[0], ROLE_LEAF);
        assert_eq!(pow_point[0], ROLE_POW);
        assert_ne!(leaf_point[0], pow_point[0]);
    }

    #[test]
    fn nonce_separates_otherwise_identical_points() {
        let a = RoContext::native([1u8; 32]);
        let b = RoContext::native([2u8; 32]);
        let ha = RoTreeHasher::new(&a, ROLE_LEAF, RoChannel::Witness, 0, 32);
        let hb = RoTreeHasher::new(&b, ROLE_LEAF, RoChannel::Witness, 0, 32);
        let payload = [5u8; 32];
        assert_ne!(ha.hash(0, 0, &payload), hb.hash(0, 0, &payload));
    }

    #[test]
    fn level_and_index_separate_nodes() {
        let ctx = ctx();
        let h = RoTreeHasher::new(&ctx, ROLE_NODE, RoChannel::Witness, 0, 64);
        let p = [3u8; 64];
        let base = h.hash(0, 0, &p);
        assert_ne!(base, h.hash(1, 0, &p), "level must matter");
        assert_ne!(base, h.hash(0, 1, &p), "index must matter");
    }

    #[test]
    fn external_backend_reproduces_native_digests_and_records() {
        // An unprogrammed recording oracle must give byte-identical digests to
        // the native path, and observe every framed leaf point.
        let nonce = [4u8; 32];
        let native = RoContext::native(nonce);
        let rec = Arc::new(RecordingOracle::new());
        let ext = RoContext::external(nonce, rec.clone());

        let hn = RoTreeHasher::new(&native, ROLE_LEAF, RoChannel::MaskP, 0, 48);
        let he = RoTreeHasher::new(&ext, ROLE_LEAF, RoChannel::MaskP, 0, 48);
        for idx in 0..8u64 {
            let payload: Vec<u8> = (0..48).map(|i| (i as u8) ^ (idx as u8)).collect();
            assert_eq!(
                hn.hash(0, idx, &payload),
                he.hash(0, idx, &payload),
                "idx={idx}"
            );
        }
        let payloads = rec.leaf_payloads(RoChannel::MaskP);
        assert_eq!(payloads.len(), 8);
        // Wrong channel yields nothing.
        assert!(rec.leaf_payloads(RoChannel::Witness).is_empty());
        // Indices are recovered from the frame regardless of order.
        let mut idxs: Vec<u64> = payloads.iter().map(|(i, _)| *i).collect();
        idxs.sort_unstable();
        assert_eq!(idxs, (0..8).collect::<Vec<_>>());
    }
}

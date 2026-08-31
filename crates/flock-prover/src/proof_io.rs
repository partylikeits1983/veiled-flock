//! Serialize / deserialize proofs to bytes (and files).
//!
//! Two bundle types: [`R1csProofBundleLigerito`] for the base R1CS proof and
//! [`ChainProofBundleLigerito`] for the hash-chain proof. Both pair a proof
//! with its commitment (which the verifier needs); the chain bundle
//! additionally carries the public endpoint bits.
//!
//! On-disk format:
//! ```text
//!   bytes 0..5    "FLOCK"                  (5-byte magic)
//!   byte  5       flavor: 6 = R1CS Ligerito v2, 7 = Chain Ligerito v2,
//!                 5 = VEIL-FLOCK BLAKE3-preimage
//!                 (0/1 reserved: legacy BaseFold, 2/3 retired unbounded Ligerito)
//!   bytes 6..     fixed-int bincode payload; size-limited, no trailing bytes
//! ```
//!
//! ## Round-trip example
//! ```ignore
//! let bundle = R1csProofBundleLigerito { commitment, proof };
//! let bytes = bundle.to_bytes();
//! std::fs::write("proof.bin", &bytes)?;
//! ...
//! let bundle = read_r1cs_bundle_ligerito_from_file("proof.bin")?;
//! // Then call e.g. `setup.verify(&bundle.commitment, &bundle.proof, ...)`.
//! ```

use std::io::{self, Read};
use std::path::Path;

use bincode::Options;
use serde::{Deserialize, Serialize, de::DeserializeOwned};

use flock_core::pcs::Commitment;

/// Magic bytes prepended to every serialized proof. Lets readers reject
/// random binary data early.
pub const MAGIC: [u8; 5] = *b"FLOCK";

/// Which hash function a chain proof is over. Carried in
/// [`ChainProofBundle`] so the verifier (e.g. the CLI) can pick the right
/// `*_chain` setup without out-of-band info.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HashKind {
    Blake3,
    Sha2,
    Keccak,
}

impl HashKind {
    /// Parse a CLI-style name; case-insensitive. Accepts `blake3`, `sha2` /
    /// `sha256`, `keccak` / `keccak_f`.
    pub fn parse(s: &str) -> Option<Self> {
        match s.to_ascii_lowercase().as_str() {
            "blake3" => Some(Self::Blake3),
            "sha2" | "sha256" | "sha-2" | "sha-256" => Some(Self::Sha2),
            "keccak" | "keccak_f" | "keccak-f" => Some(Self::Keccak),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Blake3 => "blake3",
            Self::Sha2 => "sha2",
            Self::Keccak => "keccak",
        }
    }
}

/// Retired Ligerito flavor bytes used by the pre-hardening variable-int,
/// trailing-byte-tolerant bincode payloads.
const FLAVOR_R1CS_LIGERITO_RETIRED: u8 = 2;
const FLAVOR_CHAIN_LIGERITO_RETIRED: u8 = 3;
const RETIRED_FLAVORS: [u8; 2] = [FLAVOR_R1CS_LIGERITO_RETIRED, FLAVOR_CHAIN_LIGERITO_RETIRED];

/// Hardened flavor discriminator (1 byte). Lets a generic reader peek what
/// kind of bundle a file holds without parsing the payload first.
const FLAVOR_R1CS_LIGERITO: u8 = 6;
const FLAVOR_CHAIN_LIGERITO: u8 = 7;
/// Full-view VEIL-FLOCK proof for the fixed 64-byte BLAKE3-preimage relation.
const FLAVOR_VEIL_FLOCK_BLAKE3_PREIMAGE: u8 = 5;

/// All flavor bytes this build understands (for the unknown-flavor check).
const KNOWN_FLAVORS: [u8; 3] = [
    FLAVOR_R1CS_LIGERITO,
    FLAVOR_CHAIN_LIGERITO,
    FLAVOR_VEIL_FLOCK_BLAKE3_PREIMAGE,
];

pub const MAX_R1CS_LIGERITO_BUNDLE_BYTES: u64 = 64 * 1024 * 1024;
pub const MAX_CHAIN_LIGERITO_BUNDLE_BYTES: u64 = 64 * 1024 * 1024;
#[cfg(feature = "veil")]
pub const MAX_VEIL_FLOCK_BUNDLE_BYTES: u64 = 1024 * 1024;

/// Header size = 5-byte magic + 1-byte flavor.
const HEADER_LEN: usize = 6;

const MAX_R1CS_LIGERITO_PAYLOAD_BYTES: u64 = MAX_R1CS_LIGERITO_BUNDLE_BYTES - (HEADER_LEN as u64);
const MAX_CHAIN_LIGERITO_PAYLOAD_BYTES: u64 = MAX_CHAIN_LIGERITO_BUNDLE_BYTES - (HEADER_LEN as u64);
#[cfg(feature = "veil")]
const MAX_VEIL_FLOCK_PAYLOAD_BYTES: u64 = MAX_VEIL_FLOCK_BUNDLE_BYTES - (HEADER_LEN as u64);

const MAX_ANY_LIGERITO_BUNDLE_BYTES: u64 =
    if MAX_R1CS_LIGERITO_BUNDLE_BYTES > MAX_CHAIN_LIGERITO_BUNDLE_BYTES {
        MAX_R1CS_LIGERITO_BUNDLE_BYTES
    } else {
        MAX_CHAIN_LIGERITO_BUNDLE_BYTES
    };

/// Errors from `from_bytes` / `read_from_file`.
#[derive(Debug)]
pub enum DeserializeError {
    /// The 5-byte magic prefix did not match `FLOCK`.
    BadMagic,
    /// The flavor byte is not a bundle flavor this build understands.
    UnknownFlavor(u8),
    /// The flavor byte is a retired pre-hardening Ligerito format.
    RetiredFlavor(u8),
    /// `from_bytes` was called with a slice shorter than `HEADER_LEN`.
    Truncated,
    /// The expected flavor and the file's flavor disagree (e.g. trying to
    /// load a `ChainProofBundle` from an R1CS bundle file).
    FlavorMismatch { expected: u8, found: u8 },
    /// The bincode-deserialization step failed (corrupted payload, etc.).
    Bincode(bincode::Error),
}

impl std::fmt::Display for DeserializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BadMagic => write!(f, "bad magic: not a FLOCK proof file"),
            Self::UnknownFlavor(v) => write!(f, "unknown flavor byte: {v}"),
            Self::RetiredFlavor(v) => write!(
                f,
                "retired proof bundle flavor byte {v}: regenerate with the hardened format"
            ),
            Self::Truncated => write!(f, "input shorter than header ({HEADER_LEN} bytes)"),
            Self::FlavorMismatch { expected, found } => {
                write!(f, "flavor mismatch: expected {expected}, found {found}")
            }
            Self::Bincode(e) => write!(f, "bincode error: {e}"),
        }
    }
}

impl std::error::Error for DeserializeError {}

impl From<bincode::Error> for DeserializeError {
    fn from(e: bincode::Error) -> Self {
        Self::Bincode(e)
    }
}

/// Bundles a base R1CS proof with its commitment for self-contained
/// serialization. Verification still needs the relevant [`flock_core::r1cs::BlockR1cs`]
/// (or a `*Setup`) on the verifier side — that's a public artifact derived
/// from the setup parameters, not part of the proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csProofBundleLigerito {
    pub commitment: Commitment,
    pub proof: flock_core::proof::R1csProofLigerito,
}

/// Bundles a hash-chain proof with its commitment + public endpoint bits
/// (`cv_0_phys` and `cv_last_phys` are the physical within-slot bool layouts
/// returned by per-hash `*_to_phys_bits` helpers — `region_bits` long each)
/// plus the [`HashKind`] discriminator so a verifier can pick the right
/// per-hash setup from the bundle alone.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChainProofBundleLigerito {
    pub hash_kind: HashKind,
    pub commitment: Commitment,
    pub proof: crate::r1cs_hashes::chain_common::ChainProofLigerito,
    pub cv_0_phys: Vec<bool>,
    pub cv_last_phys: Vec<bool>,
}

/// Canonical wire bundle for the full-view VEIL-FLOCK BLAKE3 preimage
/// instantiation. The outer flavor byte fixes this payload shape.
#[cfg(feature = "veil")]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VeilFlockProofBundle {
    pub digests: Vec<[u8; 32]>,
    pub commitment: Commitment,
    pub proof: crate::succinct_veil::SuccinctVeilProof,
}

#[cfg(feature = "veil")]
impl VeilFlockProofBundle {
    pub fn new(
        digests: Vec<[u8; 32]>,
        commitment: Commitment,
        proof: crate::succinct_veil::SuccinctVeilProof,
    ) -> Self {
        Self {
            digests,
            commitment,
            proof,
        }
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>, bincode::Error> {
        let mut out = Vec::with_capacity(HEADER_LEN + 1024);
        write_header(&mut out, FLAVOR_VEIL_FLOCK_BLAKE3_PREIMAGE);
        serialize_payload(&mut out, self, MAX_VEIL_FLOCK_PAYLOAD_BYTES)?;
        Ok(out)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DeserializeError> {
        let payload = parse_payload(
            bytes,
            FLAVOR_VEIL_FLOCK_BLAKE3_PREIMAGE,
            MAX_VEIL_FLOCK_BUNDLE_BYTES,
        )?;
        deserialize_payload(payload, MAX_VEIL_FLOCK_PAYLOAD_BYTES)
    }
}

impl R1csProofBundleLigerito {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(HEADER_LEN + 1024);
        write_header(&mut out, FLAVOR_R1CS_LIGERITO);
        serialize_payload(&mut out, self, MAX_R1CS_LIGERITO_PAYLOAD_BYTES)
            .expect("bincode serialize R1csProofBundleLigerito");
        out
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DeserializeError> {
        let payload = parse_payload(bytes, FLAVOR_R1CS_LIGERITO, MAX_R1CS_LIGERITO_BUNDLE_BYTES)?;
        deserialize_payload(payload, MAX_R1CS_LIGERITO_PAYLOAD_BYTES)
    }
}

impl ChainProofBundleLigerito {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(HEADER_LEN + 1024);
        write_header(&mut out, FLAVOR_CHAIN_LIGERITO);
        serialize_payload(&mut out, self, MAX_CHAIN_LIGERITO_PAYLOAD_BYTES)
            .expect("bincode serialize ChainProofBundleLigerito");
        out
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DeserializeError> {
        let payload = parse_payload(
            bytes,
            FLAVOR_CHAIN_LIGERITO,
            MAX_CHAIN_LIGERITO_BUNDLE_BYTES,
        )?;
        deserialize_payload(payload, MAX_CHAIN_LIGERITO_PAYLOAD_BYTES)
    }
}

// ---------------------------------------------------------------------------
// Encoding helpers
// ---------------------------------------------------------------------------

fn write_header(out: &mut Vec<u8>, flavor: u8) {
    out.extend_from_slice(&MAGIC);
    out.push(flavor);
}

fn parse_payload(
    bytes: &[u8],
    expected_flavor: u8,
    max_bundle_bytes: u64,
) -> Result<&[u8], DeserializeError> {
    if bytes_len_exceeds_limit(bytes.len(), max_bundle_bytes) {
        return Err(size_limit_error());
    }
    parse_header(bytes, expected_flavor)
}

fn parse_header(bytes: &[u8], expected_flavor: u8) -> Result<&[u8], DeserializeError> {
    if bytes.len() < HEADER_LEN {
        return Err(DeserializeError::Truncated);
    }
    if bytes[0..5] != MAGIC {
        return Err(DeserializeError::BadMagic);
    }
    let flavor = bytes[5];
    if RETIRED_FLAVORS.contains(&flavor) {
        return Err(DeserializeError::RetiredFlavor(flavor));
    }
    if !KNOWN_FLAVORS.contains(&flavor) {
        return Err(DeserializeError::UnknownFlavor(flavor));
    }
    if flavor != expected_flavor {
        return Err(DeserializeError::FlavorMismatch {
            expected: expected_flavor,
            found: flavor,
        });
    }
    Ok(&bytes[HEADER_LEN..])
}

fn bundle_options(max_payload_bytes: u64) -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(max_payload_bytes)
        .reject_trailing_bytes()
}

fn serialize_payload<T: Serialize>(
    out: &mut Vec<u8>,
    value: &T,
    max_payload_bytes: u64,
) -> Result<(), bincode::Error> {
    bundle_options(max_payload_bytes).serialize_into(out, value)
}

fn deserialize_payload<T: DeserializeOwned>(
    payload: &[u8],
    max_payload_bytes: u64,
) -> Result<T, DeserializeError> {
    Ok(bundle_options(max_payload_bytes).deserialize(payload)?)
}

fn size_limit_error() -> DeserializeError {
    DeserializeError::Bincode(Box::new(bincode::ErrorKind::SizeLimit))
}

fn bytes_len_exceeds_limit(len: usize, limit: u64) -> bool {
    match u64::try_from(len) {
        Ok(len) => len > limit,
        Err(_) => true,
    }
}

// ---------------------------------------------------------------------------
// File-IO conveniences
// ---------------------------------------------------------------------------

/// Atomically write `bytes` to `path` (write-then-rename via the
/// stdlib — best-effort; on error the rename may leave a temp file behind).
pub fn write_bytes_to_file<P: AsRef<Path>>(path: P, bytes: &[u8]) -> io::Result<()> {
    let path = path.as_ref();
    let tmp = match path.parent() {
        Some(dir) => dir.join(format!(
            ".{}.tmp",
            path.file_name()
                .and_then(|f| f.to_str())
                .unwrap_or("flock-proof")
        )),
        None => Path::new(".flock-proof.tmp").to_path_buf(),
    };
    std::fs::write(&tmp, bytes)?;
    std::fs::rename(&tmp, path)
}

/// Read raw bytes from a proof file with the largest Ligerito bundle cap.
pub fn read_bytes_from_file<P: AsRef<Path>>(path: P) -> io::Result<Vec<u8>> {
    read_bytes_from_file_bounded(path, MAX_ANY_LIGERITO_BUNDLE_BYTES)
}

/// Read raw bytes from a proof file, stopping once `max_bytes + 1` bytes have
/// been observed so hostile files cannot be read fully into memory.
pub fn read_bytes_from_file_bounded<P: AsRef<Path>>(
    path: P,
    max_bytes: u64,
) -> io::Result<Vec<u8>> {
    let file = std::fs::File::open(path)?;
    let mut bytes = Vec::new();
    file.take(max_bytes.saturating_add(1))
        .read_to_end(&mut bytes)?;
    if bytes_len_exceeds_limit(bytes.len(), max_bytes) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("proof bundle exceeds the {max_bytes}-byte limit"),
        ));
    }
    Ok(bytes)
}

/// Write a Ligerito R1CS bundle to `path`.
pub fn write_r1cs_bundle_ligerito_to_file<P: AsRef<Path>>(
    path: P,
    bundle: &R1csProofBundleLigerito,
) -> io::Result<()> {
    write_bytes_to_file(path, &bundle.to_bytes())
}

/// Read a Ligerito R1CS bundle from `path`.
pub fn read_r1cs_bundle_ligerito_from_file<P: AsRef<Path>>(
    path: P,
) -> Result<R1csProofBundleLigerito, BundleReadError> {
    let bytes = read_bytes_from_file_bounded(path, MAX_R1CS_LIGERITO_BUNDLE_BYTES)
        .map_err(BundleReadError::Io)?;
    R1csProofBundleLigerito::from_bytes(&bytes).map_err(BundleReadError::Deserialize)
}

/// Write a Ligerito chain bundle to `path`.
pub fn write_chain_bundle_ligerito_to_file<P: AsRef<Path>>(
    path: P,
    bundle: &ChainProofBundleLigerito,
) -> io::Result<()> {
    write_bytes_to_file(path, &bundle.to_bytes())
}

/// Read a Ligerito chain bundle from `path`.
pub fn read_chain_bundle_ligerito_from_file<P: AsRef<Path>>(
    path: P,
) -> Result<ChainProofBundleLigerito, BundleReadError> {
    let bytes = read_bytes_from_file_bounded(path, MAX_CHAIN_LIGERITO_BUNDLE_BYTES)
        .map_err(BundleReadError::Io)?;
    ChainProofBundleLigerito::from_bytes(&bytes).map_err(BundleReadError::Deserialize)
}

/// Combined error returned by file-read helpers: either IO failed or the
/// bytes weren't a valid bundle.
#[derive(Debug)]
pub enum BundleReadError {
    Io(io::Error),
    Deserialize(DeserializeError),
}

impl std::fmt::Display for BundleReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "I/O error: {e}"),
            Self::Deserialize(e) => write!(f, "deserialize error: {e}"),
        }
    }
}

impl std::error::Error for BundleReadError {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs_hashes::blake3::{Blake3Setup, Compression, blake3_compress, cv_to_phys_bits};
    use flock_core::challenger::FsChallenger;
    use flock_core::field::F128;
    use flock_core::lincheck::LincheckProof;
    use flock_core::pcs::ligerito::{FinalProof, LigeritoProfile, LigeritoProof, RecursiveProof};
    use flock_core::pcs::{BatchOpeningProofLigerito, PcsParams};
    use flock_core::proof::R1csProofLigerito;
    use flock_core::zerocheck::ZerocheckProof;

    /// SplitMix64.
    struct Rng(u64);
    impl Rng {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn nx(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
    }

    fn minimal_commitment() -> Commitment {
        Commitment {
            root: [0xA5; 32],
            params: PcsParams {
                m: 8,
                log_inv_rate: 1,
                log_batch_size: 1,
                profile: LigeritoProfile::Fast,
                zk: false,
            },
        }
    }

    fn empty_zerocheck_proof() -> ZerocheckProof {
        ZerocheckProof {
            round1_ab: Vec::new(),
            round1_c: Vec::new(),
            multilinear_rounds: Vec::new(),
            final_a_eval: F128::ZERO,
            final_b_eval: F128::ZERO,
            final_c_eval: F128::ZERO,
        }
    }

    fn empty_lincheck_proof() -> LincheckProof {
        LincheckProof {
            rounds: Vec::new(),
            z_partial: Vec::new(),
        }
    }

    fn empty_ligerito_proof() -> LigeritoProof {
        LigeritoProof {
            initial_root: [0; 32],
            initial_proof: RecursiveProof {
                opened_rows: Vec::new(),
                leaf_salts: Vec::new(),
                merkle_proof: Vec::new(),
            },
            recursive_roots: Vec::new(),
            recursive_proofs: Vec::new(),
            final_proof: FinalProof {
                yr: Vec::new(),
                opened_rows: Vec::new(),
                merkle_proof: Vec::new(),
            },
            sumcheck_transcript: Vec::new(),
            grinding_nonces: Vec::new(),
            ood_values: Vec::new(),
            fold_grinding_nonces: Vec::new(),
        }
    }

    fn empty_pcs_opening() -> BatchOpeningProofLigerito {
        BatchOpeningProofLigerito {
            ring_switches: Vec::new(),
            ligerito: empty_ligerito_proof(),
            zk_blind: None,
        }
    }

    fn empty_r1cs_proof() -> R1csProofLigerito {
        R1csProofLigerito {
            zerocheck: empty_zerocheck_proof(),
            lincheck: empty_lincheck_proof(),
            pcs_open: empty_pcs_opening(),
        }
    }

    fn minimal_r1cs_bundle() -> R1csProofBundleLigerito {
        R1csProofBundleLigerito {
            commitment: minimal_commitment(),
            proof: empty_r1cs_proof(),
        }
    }

    fn minimal_chain_bundle() -> ChainProofBundleLigerito {
        ChainProofBundleLigerito {
            hash_kind: HashKind::Blake3,
            commitment: minimal_commitment(),
            proof: crate::r1cs_hashes::chain_common::ChainProofLigerito {
                zerocheck: empty_zerocheck_proof(),
                lincheck: empty_lincheck_proof(),
                shift: crate::chain::ChainShiftProof {
                    rounds: Vec::new(),
                    g_at_point: F128::ZERO,
                },
                pcs_open: empty_pcs_opening(),
            },
            cv_0_phys: vec![false; 8],
            cv_last_phys: vec![false; 8],
        }
    }

    /// Build a small honest BLAKE3 chain (n=8) for the bundle tests.
    fn honest_chain(n: usize, seed: u64) -> (Vec<Compression>, [u32; 8], [u32; 8]) {
        let mut rng = Rng::new(seed);
        let mut cv: [u32; 8] = std::array::from_fn(|_| rng.nx() as u32);
        let cv0 = cv;
        let mut blocks = Vec::with_capacity(n);
        for _ in 0..n {
            let m: [u32; 16] = std::array::from_fn(|_| rng.nx() as u32);
            let counter = 0u64;
            let block_len = 64u32;
            let flags = 0u32;
            blocks.push((cv, m, counter, block_len, flags));
            let st = blake3_compress(&cv, &m, counter, block_len, flags);
            cv = st[0..8].try_into().unwrap();
        }
        (blocks, cv0, cv)
    }

    /// Default Ligerito bundle roundtrip, byte-flip rejection, and file
    /// roundtrip. Requires m ≥ 21 — use n_blocks=256 (m=22 with K_LOG=14).
    #[test]
    #[ignore] // Heavier — run with `cargo test r1cs_bundle_roundtrip -- --ignored --nocapture`
    fn r1cs_bundle_roundtrip() {
        // K=256 → n_log=8 → m=22 with BLAKE3 K_LOG=14 (smallest Ligerito target).
        let setup = Blake3Setup::new(256);
        let (blocks, _, _) = honest_chain(256, 0xDEAD_5170);
        let mut ch = FsChallenger::new(b"flock-proofio-lig");
        let (proof, commitment, _claim) = setup.prove_fast(&blocks, &mut ch);

        let bundle = R1csProofBundleLigerito {
            commitment: commitment.clone(),
            proof: proof.clone(),
        };
        let bytes = bundle.to_bytes();
        assert_eq!(&bytes[0..5], &MAGIC);
        assert_eq!(bytes[5], FLAVOR_R1CS_LIGERITO);

        let bundle2 = R1csProofBundleLigerito::from_bytes(&bytes).expect("must round-trip");
        assert_eq!(bundle2.commitment.root, commitment.root);

        let mut chv = FsChallenger::new(b"flock-proofio-lig");
        setup
            .verify(&bundle2.commitment, &bundle2.proof, &mut chv)
            .expect("verify round-tripped Ligerito R1cs proof");

        // Byte-flipping inside the payload should make verification reject.
        // The flip can either fail deserialization OR succeed-then-fail-at-
        // verify; either is acceptable evidence the proof was consumed.
        let flip_at = HEADER_LEN + (bytes.len() - HEADER_LEN) / 2;
        let mut mutated = bytes.clone();
        mutated[flip_at] ^= 0xFF;
        match R1csProofBundleLigerito::from_bytes(&mutated) {
            Err(_) => {}
            Ok(bundle3) => {
                let mut chv = FsChallenger::new(b"flock-proofio-lig");
                let res = setup.verify(&bundle3.commitment, &bundle3.proof, &mut chv);
                assert!(res.is_err(), "verify must reject byte-mutated proof");
            }
        }

        // File roundtrip.
        let path = std::env::temp_dir().join("flock-proofio-roundtrip.bin");
        write_bytes_to_file(&path, &bytes).expect("write");
        let read_back = read_bytes_from_file(&path).expect("read");
        let _ = std::fs::remove_file(&path);
        let bundle4 = R1csProofBundleLigerito::from_bytes(&read_back).expect("file round-trip");
        let mut chv = FsChallenger::new(b"flock-proofio-lig");
        setup
            .verify(&bundle4.commitment, &bundle4.proof, &mut chv)
            .expect("verify after file round-trip");

        eprintln!(
            "Ligerito R1csProofBundle: {} bytes ({:.1} KB)",
            bytes.len(),
            bytes.len() as f64 / 1024.0
        );
    }

    /// Ligerito chain bundle roundtrip. Requires m ≥ 21 — n=256 blocks.
    #[test]
    #[ignore] // Heavier — run with `cargo test chain_bundle_roundtrip -- --ignored --nocapture`
    fn chain_bundle_roundtrip_and_verify() {
        let setup = Blake3Setup::new(256);
        let (blocks, cv_0, cv_last) = honest_chain(256, 0xC0FFEE);
        let mut ch = FsChallenger::new(b"flock-proofio-test");
        let (proof, commitment) = setup.prove_chain(&blocks, &mut ch);

        let bundle = ChainProofBundleLigerito {
            hash_kind: HashKind::Blake3,
            commitment: commitment.clone(),
            proof: proof.clone(),
            cv_0_phys: cv_to_phys_bits(&cv_0),
            cv_last_phys: cv_to_phys_bits(&cv_last),
        };
        let bytes = bundle.to_bytes();
        assert_eq!(bytes[5], FLAVOR_CHAIN_LIGERITO);

        let bundle2 = ChainProofBundleLigerito::from_bytes(&bytes).expect("chain round-trip");
        assert_eq!(bundle2.cv_0_phys, bundle.cv_0_phys);
        assert_eq!(bundle2.cv_last_phys, bundle.cv_last_phys);

        let mut chv = FsChallenger::new(b"flock-proofio-test");
        setup
            .verify_chain(
                &bundle2.commitment,
                &bundle2.proof,
                &cv_0,
                &cv_last,
                &mut chv,
            )
            .expect("verify round-tripped chain proof");
    }

    #[test]
    fn rejects_bad_magic() {
        let mut bytes = vec![0u8; HEADER_LEN + 10];
        bytes[0..5].copy_from_slice(b"NOPE!");
        bytes[5] = FLAVOR_R1CS_LIGERITO;
        let res = R1csProofBundleLigerito::from_bytes(&bytes);
        assert!(matches!(res, Err(DeserializeError::BadMagic)));
    }

    #[test]
    fn rejects_flavor_mismatch() {
        // R1CS-flavored header — try to read as Chain. Header validation
        // fails before any payload deserialization, so zero payload is fine.
        let mut bytes = vec![0u8; HEADER_LEN + 10];
        bytes[0..5].copy_from_slice(&MAGIC);
        bytes[5] = FLAVOR_R1CS_LIGERITO;
        let res = ChainProofBundleLigerito::from_bytes(&bytes);
        assert!(matches!(
            res,
            Err(DeserializeError::FlavorMismatch {
                expected: FLAVOR_CHAIN_LIGERITO,
                found: FLAVOR_R1CS_LIGERITO
            })
        ));
    }

    #[test]
    fn rejects_legacy_basefold_flavor() {
        // Flavor bytes 0/1 were the legacy BaseFold bundles — now unknown.
        for legacy in [0u8, 1u8] {
            let mut bytes = vec![0u8; HEADER_LEN + 10];
            bytes[0..5].copy_from_slice(&MAGIC);
            bytes[5] = legacy;
            let res = R1csProofBundleLigerito::from_bytes(&bytes);
            assert!(matches!(res, Err(DeserializeError::UnknownFlavor(f)) if f == legacy));
        }
    }

    #[test]
    fn rejects_retired_ligerito_flavors() {
        for retired in [FLAVOR_R1CS_LIGERITO_RETIRED, FLAVOR_CHAIN_LIGERITO_RETIRED] {
            let mut bytes = vec![0u8; HEADER_LEN + 10];
            bytes[0..5].copy_from_slice(&MAGIC);
            bytes[5] = retired;
            let res = R1csProofBundleLigerito::from_bytes(&bytes);
            assert!(matches!(res, Err(DeserializeError::RetiredFlavor(f)) if f == retired));
        }
    }

    #[test]
    fn rejects_truncated() {
        let res = R1csProofBundleLigerito::from_bytes(&[0u8; 3]);
        assert!(matches!(res, Err(DeserializeError::Truncated)));
    }

    #[test]
    fn hardened_ligerito_bundles_round_trip_minimal() {
        let r1cs = minimal_r1cs_bundle();
        let r1cs_bytes = r1cs.to_bytes();
        assert_eq!(r1cs_bytes[5], FLAVOR_R1CS_LIGERITO);
        let r1cs_decoded = R1csProofBundleLigerito::from_bytes(&r1cs_bytes).expect("r1cs decode");
        assert_eq!(r1cs_decoded.commitment.root, r1cs.commitment.root);

        let chain = minimal_chain_bundle();
        let chain_bytes = chain.to_bytes();
        assert_eq!(chain_bytes[5], FLAVOR_CHAIN_LIGERITO);
        let chain_decoded =
            ChainProofBundleLigerito::from_bytes(&chain_bytes).expect("chain decode");
        assert_eq!(chain_decoded.cv_0_phys, chain.cv_0_phys);
        assert_eq!(chain_decoded.cv_last_phys, chain.cv_last_phys);
    }

    #[test]
    fn rejects_trailing_bytes_for_hardened_ligerito_bundles() {
        let mut r1cs_bytes = minimal_r1cs_bundle().to_bytes();
        r1cs_bytes.extend_from_slice(b"trailing");
        assert!(matches!(
            R1csProofBundleLigerito::from_bytes(&r1cs_bytes),
            Err(DeserializeError::Bincode(_))
        ));

        let mut chain_bytes = minimal_chain_bundle().to_bytes();
        chain_bytes.extend_from_slice(b"trailing");
        assert!(matches!(
            ChainProofBundleLigerito::from_bytes(&chain_bytes),
            Err(DeserializeError::Bincode(_))
        ));
    }

    #[test]
    fn parse_payload_rejects_bundle_size_over_limit_before_bincode() {
        let bytes = minimal_r1cs_bundle().to_bytes();
        let res = parse_payload(
            &bytes,
            FLAVOR_R1CS_LIGERITO,
            u64::try_from(bytes.len() - 1).unwrap(),
        );
        assert!(matches!(res, Err(DeserializeError::Bincode(_))));
    }

    #[test]
    fn bounded_file_read_rejects_oversized_file() {
        let path = std::env::temp_dir().join(format!(
            "flock-proofio-bounded-{}-oversized.bin",
            std::process::id()
        ));
        std::fs::write(&path, [0u8; 4]).expect("write oversized test file");
        let res = read_bytes_from_file_bounded(&path, 3);
        let _ = std::fs::remove_file(&path);
        assert!(matches!(res, Err(error) if error.kind() == io::ErrorKind::InvalidData));
    }

    #[cfg(feature = "veil")]
    #[test]
    fn veil_bincode_limit_leaves_room_for_header() {
        use bincode::Options;

        assert_eq!(
            MAX_VEIL_FLOCK_PAYLOAD_BYTES + HEADER_LEN as u64,
            MAX_VEIL_FLOCK_BUNDLE_BYTES
        );
        let vec_len_prefix = core::mem::size_of::<u64>() as u64;
        let max_vec_len = (MAX_VEIL_FLOCK_PAYLOAD_BYTES - vec_len_prefix) as usize;
        let payload = bundle_options(MAX_VEIL_FLOCK_PAYLOAD_BYTES)
            .serialize(&vec![0u8; max_vec_len])
            .expect("payload at adjusted bincode limit");
        assert_eq!(payload.len() as u64, MAX_VEIL_FLOCK_PAYLOAD_BYTES);

        let mut bundle_bytes = Vec::with_capacity(HEADER_LEN + payload.len());
        write_header(&mut bundle_bytes, FLAVOR_VEIL_FLOCK_BLAKE3_PREIMAGE);
        bundle_bytes.extend_from_slice(&payload);
        assert_eq!(bundle_bytes.len() as u64, MAX_VEIL_FLOCK_BUNDLE_BYTES);

        assert!(
            bundle_options(MAX_VEIL_FLOCK_PAYLOAD_BYTES)
                .serialize(&vec![0u8; max_vec_len + 1])
                .is_err()
        );
    }
}

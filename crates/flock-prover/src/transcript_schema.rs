//! Canonical transcript schema for the A1′ reference proof.
//!
//! Every verifier-visible field of [`R1csProofZkA1`] (plus the witness
//! commitment) is enumerated here with a [`LeakageClass`] and an
//! `fs_absorbed` flag. The ZK leakage certificates index transcript
//! coordinates through this schema instead of hand-maintained index
//! arithmetic — the mechanism whose absence produced the `final_b` blind
//! spot in the earlier mixture certificate.
//!
//! Four tripwires keep the schema honest:
//!
//! 1. **Compile-time**: [`flatten_a1`] destructures every proof struct
//!    exhaustively (no `..` patterns). Adding, removing, or renaming any
//!    field in any proof struct is a compile error here until the schema is
//!    updated.
//! 2. **Bijectivity**: [`unflatten_a1`] rebuilds the exact proof from the
//!    flattened fields; `unflatten_a1(flatten_a1(p)) == p` proves no value
//!    escapes classification.
//! 3. **Pinned hash**: [`schema_hash`] commits to the ordered
//!    `(path, class, fs_absorbed, unit, len)` list; tests pin it per
//!    supported shape, so silent reshapes/reclassifications fail CI.
//! 4. **Wire equality**: the recorded Fiat–Shamir observation multiset must
//!    equal the flattened `fs_absorbed` value multiset
//!    (`tests/zk_transcript_schema.rs`), so a field can be neither secretly
//!    absorbed nor falsely marked absorbed.
//!
//! Verifier challenges are *not* part of the schema: they are never
//! serialized — the verifier re-derives them from the absorbed prefix.

use flock_core::field::F128;
use flock_core::lincheck::LincheckProof;
use flock_core::merkle::Hash;
use flock_core::pcs::ligerito::{FinalProof, LigeritoProof, RecursiveProof, SumcheckMessage};
use flock_core::pcs::ring_switch::RingSwitchProof;
use flock_core::pcs::{BatchOpeningProofLigerito, Commitment, PcsParams, ZkBlindOpening};
use flock_core::zerocheck::ZkZerocheckProof;

use crate::prover::R1csProofZkA1;

/// Version of the schema itself; bump on any reclassification or reshape.
pub const A1_SCHEMA_VERSION: u32 = 3;

/// Security classification of a transcript field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeakageClass {
    /// Depends on the witness; must be covered by a mask-channel image for
    /// the WI claim to hold (the `R`-side of the certificates).
    WitnessDependent,
    /// A pure mask functional (σ_z, P(ρ), Q(ρ), y_g, everything inside the
    /// P/Q openings). These form the leakage/conditioning set `L`: they
    /// reveal nothing about the witness by themselves, but conditioning on
    /// them constrains the masks, so certificates must restrict mask images
    /// to their kernel.
    MaskOnly,
    /// Recomputed by the verifier from other transcript data and checked for
    /// equality; carries no independent information.
    Derived,
    /// Hash images (Merkle roots/paths). Hiding is computational (ROM/hash
    /// assumption), carried by the ε_hash term, not by mask coverage.
    HiddenHash,
    /// Public bookkeeping: parameters, PoW nonces. No hiding claim.
    Metadata,
}

/// The value payload of one flattened field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatValue {
    /// A run of field elements (pairs/tuples flattened in wire order).
    F128s(Vec<F128>),
    /// Row-structured field elements (opened codeword rows; one inner vec
    /// per query row, all rows the same length within a field).
    F128Rows(Vec<Vec<F128>>),
    /// Raw bytes (hashes: concatenated 32-byte nodes; serialized params).
    Bytes(Vec<u8>),
    /// PoW nonces.
    U64s(Vec<u64>),
}

impl FlatValue {
    /// Number of F128 coordinates this field contributes to the algebraic
    /// transcript vector (0 for byte/nonce fields).
    pub fn f128_len(&self) -> usize {
        match self {
            FlatValue::F128s(v) => v.len(),
            FlatValue::F128Rows(rows) => rows.iter().map(|r| r.len()).sum(),
            _ => 0,
        }
    }
    fn unit(&self) -> &'static str {
        match self {
            FlatValue::F128s(_) => "f128",
            FlatValue::F128Rows(_) => "f128rows",
            FlatValue::Bytes(_) => "bytes",
            FlatValue::U64s(_) => "u64",
        }
    }
    fn len_units(&self) -> usize {
        match self {
            FlatValue::F128s(v) => v.len(),
            FlatValue::F128Rows(rows) => rows.iter().map(|r| r.len()).sum(),
            FlatValue::Bytes(b) => b.len(),
            FlatValue::U64s(v) => v.len(),
        }
    }
}

/// One classified transcript field instance.
#[derive(Clone, Debug)]
pub struct FlatField {
    /// Static path pattern (indices not included; repeated instances share
    /// the pattern and appear consecutively in flatten order).
    pub path: &'static str,
    /// Instance index for repeated patterns (ring-switch claim number,
    /// recursion level); 0 otherwise.
    pub group: usize,
    pub class: LeakageClass,
    /// Whether the honest prover absorbs this value into the Fiat–Shamir
    /// transcript (F128 fields: via `observe_f128*`; byte fields: via
    /// `observe_bytes`). Merkle paths / opened rows are checked against
    /// absorbed roots instead and carry `false`.
    pub fs_absorbed: bool,
    pub value: FlatValue,
}

fn push(
    out: &mut Vec<FlatField>,
    path: &'static str,
    group: usize,
    class: LeakageClass,
    fs_absorbed: bool,
    value: FlatValue,
) {
    out.push(FlatField {
        path,
        group,
        class,
        fs_absorbed,
        value,
    });
}

fn hashes_bytes(hashes: &[Hash]) -> Vec<u8> {
    let mut b = Vec::with_capacity(hashes.len() * 32);
    for h in hashes {
        b.extend_from_slice(h);
    }
    b
}

fn pairs_f128(pairs: &[(F128, F128)]) -> Vec<F128> {
    let mut v = Vec::with_capacity(pairs.len() * 2);
    for (a, b) in pairs {
        v.push(*a);
        v.push(*b);
    }
    v
}

fn sumcheck_f128(msgs: &[SumcheckMessage]) -> Vec<F128> {
    let mut v = Vec::with_capacity(msgs.len() * 2);
    for m in msgs {
        v.push(m.u_0);
        v.push(m.u_2);
    }
    v
}

/// Flatten one batched opening. `algebraic` is the class of every algebraic
/// value in it: `WitnessDependent` for the witness opening (masked by μ/g),
/// `MaskOnly` for the P/Q openings (all values are mask functionals — they
/// belong to the leakage set `L` in the joint certificates).
fn flatten_opening(
    out: &mut Vec<FlatField>,
    paths: &OpeningPaths,
    algebraic: LeakageClass,
    opening: &BatchOpeningProofLigerito,
) {
    use FlatValue::*;
    let BatchOpeningProofLigerito {
        ring_switches,
        ligerito,
        zk_blind,
    } = opening;
    for (i, rs) in ring_switches.iter().enumerate() {
        let RingSwitchProof { s_hat_v } = rs;
        push(
            out,
            paths.s_hat_v,
            i,
            algebraic,
            true,
            F128s(s_hat_v.clone()),
        );
    }
    let LigeritoProof {
        initial_root,
        initial_proof,
        recursive_roots,
        recursive_proofs,
        final_proof,
        sumcheck_transcript,
        grinding_nonces,
        ood_values,
        fold_grinding_nonces,
    } = ligerito;
    push(
        out,
        paths.initial_root,
        0,
        LeakageClass::HiddenHash,
        false,
        Bytes(initial_root.to_vec()),
    );
    {
        let RecursiveProof {
            opened_rows,
            merkle_proof,
        } = initial_proof;
        push(
            out,
            paths.initial_rows,
            0,
            algebraic,
            false,
            F128Rows(opened_rows.clone()),
        );
        push(
            out,
            paths.initial_merkle,
            0,
            LeakageClass::HiddenHash,
            false,
            Bytes(hashes_bytes(merkle_proof)),
        );
    }
    push(
        out,
        paths.recursive_roots,
        0,
        LeakageClass::HiddenHash,
        true,
        Bytes(hashes_bytes(recursive_roots)),
    );
    for (l, rp) in recursive_proofs.iter().enumerate() {
        let RecursiveProof {
            opened_rows,
            merkle_proof,
        } = rp;
        push(
            out,
            paths.recursive_rows,
            l,
            algebraic,
            false,
            F128Rows(opened_rows.clone()),
        );
        push(
            out,
            paths.recursive_merkle,
            l,
            LeakageClass::HiddenHash,
            false,
            Bytes(hashes_bytes(merkle_proof)),
        );
    }
    {
        let FinalProof {
            yr,
            opened_rows,
            merkle_proof,
        } = final_proof;
        push(out, paths.final_yr, 0, algebraic, true, F128s(yr.clone()));
        push(
            out,
            paths.final_rows,
            0,
            algebraic,
            false,
            F128Rows(opened_rows.clone()),
        );
        push(
            out,
            paths.final_merkle,
            0,
            LeakageClass::HiddenHash,
            false,
            Bytes(hashes_bytes(merkle_proof)),
        );
    }
    push(
        out,
        paths.sumcheck,
        0,
        algebraic,
        true,
        F128s(sumcheck_f128(sumcheck_transcript)),
    );
    push(
        out,
        paths.grinding_nonces,
        0,
        LeakageClass::Metadata,
        false,
        U64s(grinding_nonces.clone()),
    );
    push(
        out,
        paths.ood_values,
        0,
        algebraic,
        true,
        F128s(ood_values.clone()),
    );
    push(
        out,
        paths.fold_grinding_nonces,
        0,
        LeakageClass::Metadata,
        false,
        U64s(fold_grinding_nonces.clone()),
    );
    let blind = zk_blind
        .as_ref()
        .expect("A1′ openings are always hiding (zk_blind present)");
    let ZkBlindOpening { y_g, c_grind_nonce } = blind;
    push(
        out,
        paths.y_g,
        0,
        LeakageClass::MaskOnly,
        true,
        F128s(vec![*y_g]),
    );
    push(
        out,
        paths.c_grind_nonce,
        0,
        LeakageClass::Metadata,
        false,
        U64s(vec![*c_grind_nonce]),
    );
}

/// Static path names for one opening (kept `&'static` so the manifest is a
/// compile-time constant).
struct OpeningPaths {
    s_hat_v: &'static str,
    initial_root: &'static str,
    initial_rows: &'static str,
    initial_merkle: &'static str,
    recursive_roots: &'static str,
    recursive_rows: &'static str,
    recursive_merkle: &'static str,
    final_yr: &'static str,
    final_rows: &'static str,
    final_merkle: &'static str,
    sumcheck: &'static str,
    grinding_nonces: &'static str,
    ood_values: &'static str,
    fold_grinding_nonces: &'static str,
    y_g: &'static str,
    c_grind_nonce: &'static str,
}

macro_rules! opening_paths {
    ($prefix:literal) => {
        OpeningPaths {
            s_hat_v: concat!($prefix, ".ring_switches.s_hat_v"),
            initial_root: concat!($prefix, ".ligerito.initial_root"),
            initial_rows: concat!($prefix, ".ligerito.initial_proof.opened_rows"),
            initial_merkle: concat!($prefix, ".ligerito.initial_proof.merkle_proof"),
            recursive_roots: concat!($prefix, ".ligerito.recursive_roots"),
            recursive_rows: concat!($prefix, ".ligerito.recursive_proofs.opened_rows"),
            recursive_merkle: concat!($prefix, ".ligerito.recursive_proofs.merkle_proof"),
            final_yr: concat!($prefix, ".ligerito.final_proof.yr"),
            final_rows: concat!($prefix, ".ligerito.final_proof.opened_rows"),
            final_merkle: concat!($prefix, ".ligerito.final_proof.merkle_proof"),
            sumcheck: concat!($prefix, ".ligerito.sumcheck_transcript"),
            grinding_nonces: concat!($prefix, ".ligerito.grinding_nonces"),
            ood_values: concat!($prefix, ".ligerito.ood_values"),
            fold_grinding_nonces: concat!($prefix, ".ligerito.fold_grinding_nonces"),
            y_g: concat!($prefix, ".zk_blind.y_g"),
            c_grind_nonce: concat!($prefix, ".zk_blind.c_grind_nonce"),
        }
    };
}

const PCS_OPEN_PATHS: OpeningPaths = opening_paths!("pcs_open");
const OPEN_P_PATHS: OpeningPaths = opening_paths!("open_p");
const OPEN_Q_PATHS: OpeningPaths = opening_paths!("open_q");
const OPEN_S_PATHS: OpeningPaths = opening_paths!("open_s");
const OPEN_SC_PATHS: OpeningPaths = opening_paths!("open_s_c");
const OPEN_SH_PATHS: OpeningPaths = opening_paths!("open_s_h");

/// Flatten the complete A1′ proof (plus witness commitment) into classified
/// fields, in prover message order (commitments → zerocheck → lincheck →
/// P opening → Q opening → witness opening).
pub fn flatten_a1(commitment: &Commitment, proof: &R1csProofZkA1) -> Vec<FlatField> {
    use FlatValue::*;
    let mut out = Vec::with_capacity(64);
    let R1csProofZkA1 {
        zerocheck,
        lincheck,
        pcs_open,
        open_p,
        open_q,
        open_s,
        open_s_c,
        open_s_h,
        comm_p,
        comm_q,
        comm_s,
        comm_s_c,
        comm_s_h,
        sigma_lc,
        s_eval,
        mc_at_z,
        h_at_z,
    } = proof;

    let Commitment { root, params } = commitment;
    push(
        &mut out,
        "commitment.root",
        0,
        LeakageClass::HiddenHash,
        true,
        Bytes(root.to_vec()),
    );
    push(
        &mut out,
        "commitment.params",
        0,
        LeakageClass::Metadata,
        false,
        Bytes(params_bytes(params)),
    );
    let Commitment { root, params } = comm_p;
    push(
        &mut out,
        "comm_p.root",
        0,
        LeakageClass::HiddenHash,
        true,
        Bytes(root.to_vec()),
    );
    push(
        &mut out,
        "comm_p.params",
        0,
        LeakageClass::Metadata,
        false,
        Bytes(params_bytes(params)),
    );
    let Commitment { root, params } = comm_q;
    push(
        &mut out,
        "comm_q.root",
        0,
        LeakageClass::HiddenHash,
        true,
        Bytes(root.to_vec()),
    );
    push(
        &mut out,
        "comm_q.params",
        0,
        LeakageClass::Metadata,
        false,
        Bytes(params_bytes(params)),
    );
    let Commitment { root, params } = comm_s;
    push(
        &mut out,
        "comm_s.root",
        0,
        LeakageClass::HiddenHash,
        true,
        Bytes(root.to_vec()),
    );
    push(
        &mut out,
        "comm_s.params",
        0,
        LeakageClass::Metadata,
        false,
        Bytes(params_bytes(params)),
    );
    for (c, root_path, params_path) in [
        (comm_s_c, "comm_s_c.root", "comm_s_c.params"),
        (comm_s_h, "comm_s_h.root", "comm_s_h.params"),
    ] {
        let Commitment { root, params } = c;
        push(
            &mut out,
            root_path,
            0,
            LeakageClass::HiddenHash,
            true,
            Bytes(root.to_vec()),
        );
        push(
            &mut out,
            params_path,
            0,
            LeakageClass::Metadata,
            false,
            Bytes(params_bytes(params)),
        );
    }

    let ZkZerocheckProof {
        round1_ab,
        round1_c,
        mask_init,
        multilinear_rounds,
        final_a_eval,
        final_b_eval,
        final_c_eval,
        final_p_eval,
        final_q_eval,
    } = zerocheck;
    push(
        &mut out,
        "zerocheck.round1_ab",
        0,
        LeakageClass::WitnessDependent,
        true,
        F128s(round1_ab.clone()),
    );
    push(
        &mut out,
        "zerocheck.round1_c",
        0,
        LeakageClass::WitnessDependent,
        true,
        F128s(round1_c.clone()),
    );
    push(
        &mut out,
        "zerocheck.mask_init",
        0,
        LeakageClass::MaskOnly,
        true,
        F128s(vec![*mask_init]),
    );
    push(
        &mut out,
        "zerocheck.multilinear_rounds",
        0,
        LeakageClass::WitnessDependent,
        true,
        F128s(pairs_f128(multilinear_rounds)),
    );
    push(
        &mut out,
        "zerocheck.final_a_eval",
        0,
        LeakageClass::WitnessDependent,
        true,
        F128s(vec![*final_a_eval]),
    );
    push(
        &mut out,
        "zerocheck.final_b_eval",
        0,
        LeakageClass::WitnessDependent,
        true,
        F128s(vec![*final_b_eval]),
    );
    // final_c_eval is NOT absorbed: verify_zk recomputes the C-side claim
    // from round1_c and checks equality (CEvalMismatch).
    push(
        &mut out,
        "zerocheck.final_c_eval",
        0,
        LeakageClass::Derived,
        false,
        F128s(vec![*final_c_eval]),
    );
    push(
        &mut out,
        "zerocheck.final_p_eval",
        0,
        LeakageClass::MaskOnly,
        true,
        F128s(vec![*final_p_eval]),
    );
    push(
        &mut out,
        "zerocheck.final_q_eval",
        0,
        LeakageClass::MaskOnly,
        true,
        F128s(vec![*final_q_eval]),
    );
    // A3: witness-free, and NOT absorbed — bound by their commitments, and
    // consumed by the verifier to un-shift the C-claim and the AB running
    // claim.
    push(
        &mut out,
        "zerocheck.mc_at_z",
        0,
        LeakageClass::MaskOnly,
        false,
        F128s(vec![*mc_at_z]),
    );
    push(
        &mut out,
        "zerocheck.h_at_z",
        0,
        LeakageClass::MaskOnly,
        false,
        F128s(vec![*h_at_z]),
    );

    // A2: σ_lc is absorbed inside the lincheck, between the const-pin β and
    // the first round message — the position that fixes it before γ_lc.
    push(
        &mut out,
        "lincheck.sigma_lc",
        0,
        LeakageClass::MaskOnly,
        true,
        F128s(vec![*sigma_lc]),
    );

    let LincheckProof { rounds, z_partial } = lincheck;
    // Under A2 these two carry the transcript of the *shifted* witness
    // `z + γ_lc·S`. They stay classified WitnessDependent: the class records
    // what a coordinate is a function of, not how well it is masked — the
    // masking is what the joint coverage certificate has to demonstrate.
    push(
        &mut out,
        "lincheck.rounds",
        0,
        LeakageClass::WitnessDependent,
        true,
        F128s(pairs_f128(rounds)),
    );
    push(
        &mut out,
        "lincheck.z_partial",
        0,
        LeakageClass::WitnessDependent,
        true,
        F128s(z_partial.clone()),
    );
    // `s_eval` is witness-free, but it is *not* absorbed: it is bound by S's
    // commitment, and the verifier consumes it to un-shift the output claim.
    push(
        &mut out,
        "lincheck.s_eval",
        0,
        LeakageClass::MaskOnly,
        false,
        F128s(vec![*s_eval]),
    );

    // Prover message order: the P, Q and S openings run (on domain-separated
    // forked challengers) before the witness opening in `prove_r1cs_zk_a1`.
    flatten_opening(&mut out, &OPEN_P_PATHS, LeakageClass::MaskOnly, open_p);
    flatten_opening(&mut out, &OPEN_Q_PATHS, LeakageClass::MaskOnly, open_q);
    flatten_opening(&mut out, &OPEN_S_PATHS, LeakageClass::MaskOnly, open_s);
    flatten_opening(&mut out, &OPEN_SC_PATHS, LeakageClass::MaskOnly, open_s_c);
    flatten_opening(&mut out, &OPEN_SH_PATHS, LeakageClass::MaskOnly, open_s_h);
    flatten_opening(
        &mut out,
        &PCS_OPEN_PATHS,
        LeakageClass::WitnessDependent,
        pcs_open,
    );
    out
}

fn params_bytes(p: &PcsParams) -> Vec<u8> {
    bincode::serialize(p).expect("PcsParams serialize")
}

fn params_from_bytes(b: &[u8]) -> PcsParams {
    bincode::deserialize(b).expect("PcsParams deserialize")
}

// ---------------------------------------------------------------------------
// Un-flatten (bijectivity tripwire)
// ---------------------------------------------------------------------------

struct Cursor<'a> {
    fields: &'a [FlatField],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn take(&mut self, path: &str) -> &'a FlatValue {
        let f = &self.fields[self.pos];
        assert_eq!(
            f.path, path,
            "unflatten order mismatch at position {}",
            self.pos
        );
        self.pos += 1;
        &f.value
    }
    /// Take all consecutive fields with `path` (repeated instances).
    fn take_seq(&mut self, path: &str) -> Vec<&'a FlatValue> {
        let mut v = Vec::new();
        while self.pos < self.fields.len() && self.fields[self.pos].path == path {
            v.push(&self.fields[self.pos].value);
            self.pos += 1;
        }
        v
    }
    fn f128s(&mut self, path: &str) -> Vec<F128> {
        match self.take(path) {
            FlatValue::F128s(v) => v.clone(),
            other => panic!("{path}: expected F128s, got {other:?}"),
        }
    }
    fn one_f128(&mut self, path: &str) -> F128 {
        let v = self.f128s(path);
        assert_eq!(v.len(), 1, "{path}: expected a single F128");
        v[0]
    }
    fn rows(&mut self, path: &str) -> Vec<Vec<F128>> {
        match self.take(path) {
            FlatValue::F128Rows(r) => r.clone(),
            other => panic!("{path}: expected F128Rows, got {other:?}"),
        }
    }
    fn bytes(&mut self, path: &str) -> Vec<u8> {
        match self.take(path) {
            FlatValue::Bytes(b) => b.clone(),
            other => panic!("{path}: expected Bytes, got {other:?}"),
        }
    }
    fn u64s(&mut self, path: &str) -> Vec<u64> {
        match self.take(path) {
            FlatValue::U64s(v) => v.clone(),
            other => panic!("{path}: expected U64s, got {other:?}"),
        }
    }
}

fn f128_pairs(v: Vec<F128>) -> Vec<(F128, F128)> {
    assert_eq!(v.len() % 2, 0);
    v.chunks_exact(2).map(|c| (c[0], c[1])).collect()
}

fn bytes_hashes(b: &[u8]) -> Vec<Hash> {
    assert_eq!(b.len() % 32, 0);
    b.chunks_exact(32)
        .map(|c| <Hash>::try_from(c).unwrap())
        .collect()
}

fn one_hash(b: &[u8]) -> Hash {
    <Hash>::try_from(b).expect("expected exactly 32 bytes")
}

fn unflatten_commitment(cur: &mut Cursor, root_path: &str, params_path: &str) -> Commitment {
    let root = one_hash(&cur.bytes(root_path));
    let params = params_from_bytes(&cur.bytes(params_path));
    Commitment { root, params }
}

fn unflatten_opening(cur: &mut Cursor, paths: &OpeningPaths) -> BatchOpeningProofLigerito {
    let ring_switches: Vec<RingSwitchProof> = cur
        .take_seq(paths.s_hat_v)
        .into_iter()
        .map(|v| match v {
            FlatValue::F128s(s) => RingSwitchProof { s_hat_v: s.clone() },
            other => panic!("s_hat_v: expected F128s, got {other:?}"),
        })
        .collect();
    let initial_root = one_hash(&cur.bytes(paths.initial_root));
    let initial_proof = RecursiveProof {
        opened_rows: cur.rows(paths.initial_rows),
        merkle_proof: bytes_hashes(&cur.bytes(paths.initial_merkle)),
    };
    let recursive_roots = bytes_hashes(&cur.bytes(paths.recursive_roots));
    let mut recursive_proofs = Vec::new();
    while cur.pos < cur.fields.len() && cur.fields[cur.pos].path == paths.recursive_rows {
        let opened_rows = cur.rows(paths.recursive_rows);
        let merkle_proof = bytes_hashes(&cur.bytes(paths.recursive_merkle));
        recursive_proofs.push(RecursiveProof {
            opened_rows,
            merkle_proof,
        });
    }
    let final_proof = FinalProof {
        yr: cur.f128s(paths.final_yr),
        opened_rows: cur.rows(paths.final_rows),
        merkle_proof: bytes_hashes(&cur.bytes(paths.final_merkle)),
    };
    let sumcheck_transcript: Vec<SumcheckMessage> = f128_pairs(cur.f128s(paths.sumcheck))
        .into_iter()
        .map(|(u_0, u_2)| SumcheckMessage { u_0, u_2 })
        .collect();
    let grinding_nonces = cur.u64s(paths.grinding_nonces);
    let ood_values = cur.f128s(paths.ood_values);
    let fold_grinding_nonces = cur.u64s(paths.fold_grinding_nonces);
    let y_g = cur.one_f128(paths.y_g);
    let c_grind_nonce = cur.u64s(paths.c_grind_nonce);
    assert_eq!(c_grind_nonce.len(), 1);
    BatchOpeningProofLigerito {
        ring_switches,
        ligerito: LigeritoProof {
            initial_root,
            initial_proof,
            recursive_roots,
            recursive_proofs,
            final_proof,
            sumcheck_transcript,
            grinding_nonces,
            ood_values,
            fold_grinding_nonces,
        },
        zk_blind: Some(ZkBlindOpening {
            y_g,
            c_grind_nonce: c_grind_nonce[0],
        }),
    }
}

/// Rebuild `(commitment, proof)` from flattened fields. Inverse of
/// [`flatten_a1`]; asserting `unflatten_a1(flatten_a1(c, p)) == (c, p)`
/// proves the flattening loses nothing.
pub fn unflatten_a1(flat: &[FlatField]) -> (Commitment, R1csProofZkA1) {
    let mut cur = Cursor {
        fields: flat,
        pos: 0,
    };
    let commitment = unflatten_commitment(&mut cur, "commitment.root", "commitment.params");
    let comm_p = unflatten_commitment(&mut cur, "comm_p.root", "comm_p.params");
    let comm_q = unflatten_commitment(&mut cur, "comm_q.root", "comm_q.params");
    let comm_s = unflatten_commitment(&mut cur, "comm_s.root", "comm_s.params");
    let comm_s_c = unflatten_commitment(&mut cur, "comm_s_c.root", "comm_s_c.params");
    let comm_s_h = unflatten_commitment(&mut cur, "comm_s_h.root", "comm_s_h.params");

    let zerocheck = ZkZerocheckProof {
        round1_ab: cur.f128s("zerocheck.round1_ab"),
        round1_c: cur.f128s("zerocheck.round1_c"),
        mask_init: cur.one_f128("zerocheck.mask_init"),
        multilinear_rounds: f128_pairs(cur.f128s("zerocheck.multilinear_rounds")),
        final_a_eval: cur.one_f128("zerocheck.final_a_eval"),
        final_b_eval: cur.one_f128("zerocheck.final_b_eval"),
        final_c_eval: cur.one_f128("zerocheck.final_c_eval"),
        final_p_eval: cur.one_f128("zerocheck.final_p_eval"),
        final_q_eval: cur.one_f128("zerocheck.final_q_eval"),
    };
    let mc_at_z = cur.one_f128("zerocheck.mc_at_z");
    let h_at_z = cur.one_f128("zerocheck.h_at_z");
    let sigma_lc = cur.one_f128("lincheck.sigma_lc");
    let lincheck = LincheckProof {
        rounds: f128_pairs(cur.f128s("lincheck.rounds")),
        z_partial: cur.f128s("lincheck.z_partial"),
    };
    let s_eval = cur.one_f128("lincheck.s_eval");
    let open_p = unflatten_opening(&mut cur, &OPEN_P_PATHS);
    let open_q = unflatten_opening(&mut cur, &OPEN_Q_PATHS);
    let open_s = unflatten_opening(&mut cur, &OPEN_S_PATHS);
    let open_s_c = unflatten_opening(&mut cur, &OPEN_SC_PATHS);
    let open_s_h = unflatten_opening(&mut cur, &OPEN_SH_PATHS);
    let pcs_open = unflatten_opening(&mut cur, &PCS_OPEN_PATHS);
    assert_eq!(cur.pos, flat.len(), "unflatten did not consume every field");
    (
        commitment,
        R1csProofZkA1 {
            zerocheck,
            lincheck,
            pcs_open,
            open_p,
            open_q,
            open_s,
            open_s_c,
            open_s_h,
            comm_p,
            comm_q,
            comm_s,
            comm_s_c,
            comm_s_h,
            sigma_lc,
            s_eval,
            mc_at_z,
            h_at_z,
        },
    )
}

// ---------------------------------------------------------------------------
// Manifest, schema hash, and coordinate index
// ---------------------------------------------------------------------------

/// The ordered field manifest: `(path, class, fs_absorbed)` per distinct
/// path, in flatten order. This is the reviewable single source of truth for
/// transcript classification; `manifest_of` extracted from a real proof must
/// equal it exactly.
pub const A1_FIELD_MANIFEST: &[(&str, LeakageClass, bool)] = {
    use LeakageClass::*;
    &[
        ("commitment.root", HiddenHash, true),
        ("commitment.params", Metadata, false),
        ("comm_p.root", HiddenHash, true),
        ("comm_p.params", Metadata, false),
        ("comm_q.root", HiddenHash, true),
        ("comm_q.params", Metadata, false),
        ("comm_s.root", HiddenHash, true),
        ("comm_s.params", Metadata, false),
        ("comm_s_c.root", HiddenHash, true),
        ("comm_s_c.params", Metadata, false),
        ("comm_s_h.root", HiddenHash, true),
        ("comm_s_h.params", Metadata, false),
        ("zerocheck.round1_ab", WitnessDependent, true),
        ("zerocheck.round1_c", WitnessDependent, true),
        ("zerocheck.mask_init", MaskOnly, true),
        ("zerocheck.multilinear_rounds", WitnessDependent, true),
        ("zerocheck.final_a_eval", WitnessDependent, true),
        ("zerocheck.final_b_eval", WitnessDependent, true),
        ("zerocheck.final_c_eval", Derived, false),
        ("zerocheck.final_p_eval", MaskOnly, true),
        ("zerocheck.final_q_eval", MaskOnly, true),
        ("zerocheck.mc_at_z", MaskOnly, false),
        ("zerocheck.h_at_z", MaskOnly, false),
        ("lincheck.sigma_lc", MaskOnly, true),
        ("lincheck.rounds", WitnessDependent, true),
        ("lincheck.z_partial", WitnessDependent, true),
        ("lincheck.s_eval", MaskOnly, false),
        ("open_p.ring_switches.s_hat_v", MaskOnly, true),
        ("open_p.ligerito.initial_root", HiddenHash, false),
        ("open_p.ligerito.initial_proof.opened_rows", MaskOnly, false),
        (
            "open_p.ligerito.initial_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_p.ligerito.recursive_roots", HiddenHash, true),
        (
            "open_p.ligerito.recursive_proofs.opened_rows",
            MaskOnly,
            false,
        ),
        (
            "open_p.ligerito.recursive_proofs.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_p.ligerito.final_proof.yr", MaskOnly, true),
        ("open_p.ligerito.final_proof.opened_rows", MaskOnly, false),
        (
            "open_p.ligerito.final_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_p.ligerito.sumcheck_transcript", MaskOnly, true),
        ("open_p.ligerito.grinding_nonces", Metadata, false),
        ("open_p.ligerito.ood_values", MaskOnly, true),
        ("open_p.ligerito.fold_grinding_nonces", Metadata, false),
        ("open_p.zk_blind.y_g", MaskOnly, true),
        ("open_p.zk_blind.c_grind_nonce", Metadata, false),
        ("open_q.ring_switches.s_hat_v", MaskOnly, true),
        ("open_q.ligerito.initial_root", HiddenHash, false),
        ("open_q.ligerito.initial_proof.opened_rows", MaskOnly, false),
        (
            "open_q.ligerito.initial_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_q.ligerito.recursive_roots", HiddenHash, true),
        (
            "open_q.ligerito.recursive_proofs.opened_rows",
            MaskOnly,
            false,
        ),
        (
            "open_q.ligerito.recursive_proofs.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_q.ligerito.final_proof.yr", MaskOnly, true),
        ("open_q.ligerito.final_proof.opened_rows", MaskOnly, false),
        (
            "open_q.ligerito.final_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_q.ligerito.sumcheck_transcript", MaskOnly, true),
        ("open_q.ligerito.grinding_nonces", Metadata, false),
        ("open_q.ligerito.ood_values", MaskOnly, true),
        ("open_q.ligerito.fold_grinding_nonces", Metadata, false),
        ("open_q.zk_blind.y_g", MaskOnly, true),
        ("open_q.zk_blind.c_grind_nonce", Metadata, false),
        ("open_s.ring_switches.s_hat_v", MaskOnly, true),
        ("open_s.ligerito.initial_root", HiddenHash, false),
        ("open_s.ligerito.initial_proof.opened_rows", MaskOnly, false),
        (
            "open_s.ligerito.initial_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s.ligerito.recursive_roots", HiddenHash, true),
        (
            "open_s.ligerito.recursive_proofs.opened_rows",
            MaskOnly,
            false,
        ),
        (
            "open_s.ligerito.recursive_proofs.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s.ligerito.final_proof.yr", MaskOnly, true),
        ("open_s.ligerito.final_proof.opened_rows", MaskOnly, false),
        (
            "open_s.ligerito.final_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s.ligerito.sumcheck_transcript", MaskOnly, true),
        ("open_s.ligerito.grinding_nonces", Metadata, false),
        ("open_s.ligerito.ood_values", MaskOnly, true),
        ("open_s.ligerito.fold_grinding_nonces", Metadata, false),
        ("open_s.zk_blind.y_g", MaskOnly, true),
        ("open_s.zk_blind.c_grind_nonce", Metadata, false),
        ("open_s_c.ring_switches.s_hat_v", MaskOnly, true),
        ("open_s_c.ligerito.initial_root", HiddenHash, false),
        (
            "open_s_c.ligerito.initial_proof.opened_rows",
            MaskOnly,
            false,
        ),
        (
            "open_s_c.ligerito.initial_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s_c.ligerito.recursive_roots", HiddenHash, true),
        (
            "open_s_c.ligerito.recursive_proofs.opened_rows",
            MaskOnly,
            false,
        ),
        (
            "open_s_c.ligerito.recursive_proofs.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s_c.ligerito.final_proof.yr", MaskOnly, true),
        ("open_s_c.ligerito.final_proof.opened_rows", MaskOnly, false),
        (
            "open_s_c.ligerito.final_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s_c.ligerito.sumcheck_transcript", MaskOnly, true),
        ("open_s_c.ligerito.grinding_nonces", Metadata, false),
        ("open_s_c.ligerito.ood_values", MaskOnly, true),
        ("open_s_c.ligerito.fold_grinding_nonces", Metadata, false),
        ("open_s_c.zk_blind.y_g", MaskOnly, true),
        ("open_s_c.zk_blind.c_grind_nonce", Metadata, false),
        ("open_s_h.ring_switches.s_hat_v", MaskOnly, true),
        ("open_s_h.ligerito.initial_root", HiddenHash, false),
        (
            "open_s_h.ligerito.initial_proof.opened_rows",
            MaskOnly,
            false,
        ),
        (
            "open_s_h.ligerito.initial_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s_h.ligerito.recursive_roots", HiddenHash, true),
        (
            "open_s_h.ligerito.recursive_proofs.opened_rows",
            MaskOnly,
            false,
        ),
        (
            "open_s_h.ligerito.recursive_proofs.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s_h.ligerito.final_proof.yr", MaskOnly, true),
        ("open_s_h.ligerito.final_proof.opened_rows", MaskOnly, false),
        (
            "open_s_h.ligerito.final_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("open_s_h.ligerito.sumcheck_transcript", MaskOnly, true),
        ("open_s_h.ligerito.grinding_nonces", Metadata, false),
        ("open_s_h.ligerito.ood_values", MaskOnly, true),
        ("open_s_h.ligerito.fold_grinding_nonces", Metadata, false),
        ("open_s_h.zk_blind.y_g", MaskOnly, true),
        ("open_s_h.zk_blind.c_grind_nonce", Metadata, false),
        ("pcs_open.ring_switches.s_hat_v", WitnessDependent, true),
        ("pcs_open.ligerito.initial_root", HiddenHash, false),
        (
            "pcs_open.ligerito.initial_proof.opened_rows",
            WitnessDependent,
            false,
        ),
        (
            "pcs_open.ligerito.initial_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        ("pcs_open.ligerito.recursive_roots", HiddenHash, true),
        (
            "pcs_open.ligerito.recursive_proofs.opened_rows",
            WitnessDependent,
            false,
        ),
        (
            "pcs_open.ligerito.recursive_proofs.merkle_proof",
            HiddenHash,
            false,
        ),
        ("pcs_open.ligerito.final_proof.yr", WitnessDependent, true),
        (
            "pcs_open.ligerito.final_proof.opened_rows",
            WitnessDependent,
            false,
        ),
        (
            "pcs_open.ligerito.final_proof.merkle_proof",
            HiddenHash,
            false,
        ),
        (
            "pcs_open.ligerito.sumcheck_transcript",
            WitnessDependent,
            true,
        ),
        ("pcs_open.ligerito.grinding_nonces", Metadata, false),
        ("pcs_open.ligerito.ood_values", WitnessDependent, true),
        ("pcs_open.ligerito.fold_grinding_nonces", Metadata, false),
        ("pcs_open.zk_blind.y_g", MaskOnly, true),
        ("pcs_open.zk_blind.c_grind_nonce", Metadata, false),
    ]
};

/// Extract the `(path, class, fs)` manifest of a flattened proof: distinct
/// paths in first-occurrence order; panics if two instances of one path
/// disagree on classification.
pub fn manifest_of(flat: &[FlatField]) -> Vec<(&'static str, LeakageClass, bool)> {
    let mut out: Vec<(&'static str, LeakageClass, bool)> = Vec::new();
    for f in flat {
        match out.iter().find(|(p, _, _)| *p == f.path) {
            None => out.push((f.path, f.class, f.fs_absorbed)),
            Some((p, c, a)) => {
                assert_eq!(
                    (*c, *a),
                    (f.class, f.fs_absorbed),
                    "inconsistent classification for {p}"
                )
            }
        }
    }
    out
}

/// Hash of the full schema: version + per-field `(path, group, class, fs,
/// unit, len)` in order. Pinned per supported shape; a reshape or
/// reclassification without an intentional pin bump fails the tests.
pub fn schema_hash(flat: &[FlatField]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"flock-a1-transcript-schema");
    h.update(&A1_SCHEMA_VERSION.to_le_bytes());
    for f in flat {
        h.update(f.path.as_bytes());
        h.update(&[0u8]);
        h.update(&(f.group as u64).to_le_bytes());
        h.update(&[f.class as u8, f.fs_absorbed as u8]);
        h.update(f.value.unit().as_bytes());
        h.update(&[0u8]);
        h.update(&(f.value.len_units() as u64).to_le_bytes());
    }
    *h.finalize().as_bytes()
}

/// The algebraic transcript vector: every F128 coordinate of every
/// non-hash, non-metadata field, in flatten order. This is the codomain the
/// joint leakage certificates work in.
pub fn algebraic_vector(flat: &[FlatField]) -> Vec<F128> {
    let mut v = Vec::new();
    for f in flat {
        if matches!(f.class, LeakageClass::HiddenHash | LeakageClass::Metadata) {
            continue;
        }
        match &f.value {
            FlatValue::F128s(x) => v.extend_from_slice(x),
            FlatValue::F128Rows(rows) => {
                for r in rows {
                    v.extend_from_slice(r);
                }
            }
            _ => {}
        }
    }
    v
}

/// Coordinate index over [`algebraic_vector`]: F128 ranges per path pattern.
pub struct SchemaIndex {
    entries: Vec<(&'static str, std::ops::Range<usize>)>,
    total: usize,
}

impl SchemaIndex {
    pub fn build(flat: &[FlatField]) -> Self {
        let mut entries = Vec::new();
        let mut off = 0usize;
        for f in flat {
            if matches!(f.class, LeakageClass::HiddenHash | LeakageClass::Metadata) {
                continue;
            }
            let n = f.value.f128_len();
            if n > 0 {
                entries.push((f.path, off..off + n));
                off += n;
            }
        }
        SchemaIndex {
            entries,
            total: off,
        }
    }
    /// Total F128 coordinates in the algebraic vector.
    pub fn total(&self) -> usize {
        self.total
    }
    /// The coordinate range covering **all** instances of `path`. Panics if
    /// the path is absent or its instances are not contiguous.
    pub fn range(&self, path: &str) -> std::ops::Range<usize> {
        let mut it = self.entries.iter().filter(|(p, _)| *p == path);
        let first = it
            .next()
            .unwrap_or_else(|| panic!("schema path not found: {path}"))
            .1
            .clone();
        let mut end = first.end;
        for (_, r) in it {
            assert_eq!(r.start, end, "non-contiguous instances of {path}");
            end = r.end;
        }
        first.start..end
    }
    /// Ranges of every field whose class matches `class`, in order.
    pub fn ranges_by_class<'a>(
        &'a self,
        flat: &'a [FlatField],
        class: LeakageClass,
    ) -> Vec<(&'static str, std::ops::Range<usize>)> {
        let mut out = Vec::new();
        let mut idx = 0usize;
        for f in flat {
            if matches!(f.class, LeakageClass::HiddenHash | LeakageClass::Metadata) {
                continue;
            }
            let n = f.value.f128_len();
            if n == 0 {
                continue;
            }
            let (path, r) = &self.entries[idx];
            debug_assert_eq!(*path, f.path);
            if f.class == class {
                out.push((*path, r.clone()));
            }
            idx += 1;
        }
        out
    }
}

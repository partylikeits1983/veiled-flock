//! Canonical-transcript-schema tripwires, on the complete A1′ pipeline at
//! the m=15 masked-identity fixture (full pipeline: hiding commits, masked
//! zerocheck, lincheck, hiding witness/P/Q openings).
//!
//! What is being pinned and why:
//! - `manifest`: the ordered `(path, class, fs_absorbed)` classification of
//!   every proof field. New/changed fields fail here (and fail to compile in
//!   `flatten_a1` first).
//! - `bijectivity`: `unflatten(flatten(p)) == p` and byte-exact bundle
//!   re-serialization — no proof byte escapes classification.
//! - `wire order`: the multiset of F128 values the honest prover absorbs
//!   into Fiat–Shamir equals the multiset of flattened values marked
//!   `fs_absorbed` — a field can be neither secretly absorbed nor falsely
//!   marked absorbed. The zerocheck+lincheck prefix is additionally checked
//!   in exact order.

#![cfg(feature = "zk")]

use flock_core::challenger::FsChallenger;
use flock_core::field::F128;
use flock_core::zk::ZkRng;
use flock_prover::proof_io::R1csProofBundleZkA1;
use flock_prover::transcript_schema::{
    A1_FIELD_MANIFEST, SchemaIndex, algebraic_vector, flatten_a1, manifest_of, schema_hash,
    unflatten_a1,
};
use flock_prover::zk_audit_support::{FixtureA1M15, RecordedOp, RecordingChallenger};

struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.next_u64() & 1 == 1).collect()
    }
}

fn prove_fixture(seed: u64) -> (FixtureA1M15, flock_prover::prover::R1csProofZkA1, flock_core::pcs::Commitment) {
    let fx = FixtureA1M15::new();
    let mut rng = Rng(seed);
    let payload = rng.bits(FixtureA1M15::N_PAYLOAD * FixtureA1M15::BLOCKS);
    let u_a = rng.bits(FixtureA1M15::A_BITS);
    let u_b = rng.bits(FixtureA1M15::B_BITS);
    let z = fx.witness(&payload, &u_a, &u_b);
    let mut zk_rng = ZkRng::from_seed([0x5C; 32]);
    let mut ch = FsChallenger::new(b"flock-a1-schema-test");
    let (proof, comm) = fx.prove(z, &mut zk_rng, &mut ch);
    (fx, proof, comm)
}

#[test]
fn a1_schema_manifest_and_bijectivity() {
    let (fx, proof, comm) = prove_fixture(0x5C4E);

    // The proof verifies (sanity that the fixture is honest).
    let mut chv = FsChallenger::new(b"flock-a1-schema-test");
    fx.verify(&proof, &comm, &mut chv).expect("fixture proof must verify");

    let flat = flatten_a1(&comm, &proof);

    // 1. Manifest equality: classification is exactly the reviewed list.
    let m = manifest_of(&flat);
    assert_eq!(
        m.as_slice(),
        A1_FIELD_MANIFEST,
        "transcript field manifest changed — every new/reshaped proof field \
         must be classified in transcript_schema.rs and reviewed"
    );

    // 2. Bijectivity: nothing escapes the flattening.
    let (comm2, proof2) = unflatten_a1(&flat);
    assert_eq!(comm2, comm);
    assert_eq!(proof2, proof);

    // 3. Serialization roundtrip is byte-exact through the parser.
    let bundle = R1csProofBundleZkA1 { commitment: comm.clone(), proof: proof.clone() };
    let bytes = bundle.to_bytes();
    let parsed = R1csProofBundleZkA1::from_bytes(&bytes).expect("parse");
    assert_eq!(parsed, bundle);
    assert_eq!(parsed.to_bytes(), bytes, "re-serialization must be byte-identical");
    // ... and the parsed proof verifies.
    let mut chv2 = FsChallenger::new(b"flock-a1-schema-test");
    fx.verify(&parsed.proof, &parsed.commitment, &mut chv2).expect("parsed proof verifies");

    // 4. Pinned schema hash for this fixture shape. If this fails and the
    //    change is intentional, review the classification diff and update
    //    the constant (printed below).
    let h = schema_hash(&flat);
    let hex: String = h.iter().map(|b| format!("{b:02x}")).collect();
    const PINNED_M15: &str = "6f21208ff17981c878c8cc28cc4ea8dadfef1d026992cedccf69b1f92ae19476";
    assert_eq!(hex, PINNED_M15, "schema hash changed for the m=15 fixture shape");

    // 5. The coordinate index is consistent with the algebraic vector.
    let vec = algebraic_vector(&flat);
    let idx = SchemaIndex::build(&flat);
    assert_eq!(vec.len(), idx.total());
    // Round-pair block sanity: 2·(m−k_skip) F128s.
    let rp = idx.range("zerocheck.multilinear_rounds");
    assert_eq!(rp.len(), 2 * (FixtureA1M15::M - FixtureA1M15::K_SKIP));
    // final_b is its own coordinate (the earlier mixture certificate's blind
    // spot was exactly this value being sliced out of audit subsets).
    let fb = idx.range("zerocheck.final_b_eval");
    assert_eq!(fb.len(), 1);
    assert_eq!(vec[fb.start], proof.zerocheck.final_b_eval);
}

#[test]
fn a1_schema_matches_wire_order() {
    let fx = FixtureA1M15::new();
    let mut rng = Rng(0x11ED);
    let payload = rng.bits(FixtureA1M15::N_PAYLOAD * FixtureA1M15::BLOCKS);
    let u_a = rng.bits(FixtureA1M15::A_BITS);
    let u_b = rng.bits(FixtureA1M15::B_BITS);
    let z = fx.witness(&payload, &u_a, &u_b);
    let mut zk_rng = ZkRng::from_seed([0x7A; 32]);
    let mut rec = RecordingChallenger::new(FsChallenger::new(b"flock-a1-schema-test"));
    let (proof, comm) = fx.prove(z, &mut zk_rng, &mut rec);

    let flat = flatten_a1(&comm, &proof);

    // Every F128 the prover absorbed, across the main channel and the
    // domain-separated P/Q opening forks (clones share the log).
    let observed = rec.observed_f128s();

    // Flattened fs_absorbed F128 values.
    let mut absorbed: Vec<F128> = Vec::new();
    for f in &flat {
        if !f.fs_absorbed {
            continue;
        }
        match &f.value {
            flock_prover::transcript_schema::FlatValue::F128s(v) => absorbed.extend_from_slice(v),
            flock_prover::transcript_schema::FlatValue::F128Rows(rows) => {
                for r in rows {
                    absorbed.extend_from_slice(r);
                }
            }
            _ => {}
        }
    }

    // Multiset comparison (128-bit values: collisions are vanishing, so
    // sorted-diff is an exact multiset check).
    //
    // Two directions:
    //  - `missing` (flattened \ observed) must be EMPTY: every field marked
    //    fs_absorbed really is observed by the honest prover.
    //  - `extras` (observed \ flattened) must consist ONLY of the
    //    verifier-recomputable derived absorptions: each of the three
    //    Ligerito openings re-absorbs its combined sumcheck target
    //    (`ligerito.rs` `observe_f128(claimed_value)`), a value derived from
    //    already-absorbed data and not carried in the proof. Crucially, no
    //    extra may equal ANY value stored in the proof — that would be a
    //    proof field secretly absorbed without schema classification.
    let key = |v: &F128| (v.hi, v.lo);
    let mut obs_sorted = observed.clone();
    let mut abs_sorted = absorbed.clone();
    obs_sorted.sort_unstable_by_key(key);
    abs_sorted.sort_unstable_by_key(key);
    let mut extras: Vec<F128> = Vec::new();
    let mut missing: Vec<F128> = Vec::new();
    {
        let (mut i, mut j) = (0usize, 0usize);
        while i < obs_sorted.len() || j < abs_sorted.len() {
            match (obs_sorted.get(i), abs_sorted.get(j)) {
                (Some(o), Some(a)) if key(o) == key(a) => {
                    i += 1;
                    j += 1;
                }
                (Some(o), Some(a)) if key(o) < key(a) => {
                    extras.push(*o);
                    i += 1;
                }
                (Some(_), Some(a)) => {
                    missing.push(*a);
                    j += 1;
                }
                (Some(o), None) => {
                    extras.push(*o);
                    i += 1;
                }
                (None, Some(a)) => {
                    missing.push(*a);
                    j += 1;
                }
                (None, None) => unreachable!(),
            }
        }
    }
    assert!(
        missing.is_empty(),
        "{} schema fields marked fs_absorbed were never observed (stale flag): {missing:?}",
        missing.len()
    );
    assert_eq!(
        extras.len(),
        3,
        "expected exactly 3 derived absorptions (one combined Ligerito target \
         per opening); anything else is an unclassified absorption: {extras:?}"
    );
    // No extra may be a proof value: collect EVERY F128 in the proof
    // (regardless of class or fs flag) and check disjointness.
    let mut all_proof_values: Vec<F128> = Vec::new();
    for f in &flat {
        match &f.value {
            flock_prover::transcript_schema::FlatValue::F128s(v) => {
                all_proof_values.extend_from_slice(v)
            }
            flock_prover::transcript_schema::FlatValue::F128Rows(rows) => {
                for r in rows {
                    all_proof_values.extend_from_slice(r);
                }
            }
            _ => {}
        }
    }
    for e in &extras {
        assert!(
            !all_proof_values.iter().any(|v| v == e),
            "observed value {e:?} matches a proof field not marked fs_absorbed — \
             hidden absorption of an unclassified proof field"
        );
    }

    // The zerocheck + lincheck prefix must match in exact order (these are
    // main-channel messages the schema lists in wire order).
    let mut prefix: Vec<F128> = Vec::new();
    for f in &flat {
        if !f.fs_absorbed || !(f.path.starts_with("zerocheck.") || f.path.starts_with("lincheck.")) {
            continue;
        }
        if let flock_prover::transcript_schema::FlatValue::F128s(v) = &f.value {
            prefix.extend_from_slice(v);
        }
    }
    assert_eq!(
        &observed[..prefix.len()],
        prefix.as_slice(),
        "zerocheck/lincheck wire order does not match schema order"
    );

    // Every fs_absorbed byte field (roots) must actually be absorbed.
    let observed_bytes = rec.observed_bytes();
    for f in &flat {
        if !f.fs_absorbed {
            continue;
        }
        if let flock_prover::transcript_schema::FlatValue::Bytes(bts) = &f.value {
            if bts.is_empty() {
                continue;
            }
            // Roots are absorbed whole (comm roots) or per-hash (recursion
            // roots) — accept either containment form.
            let whole = observed_bytes.iter().any(|ob| ob == bts);
            let chunked = bts.len() % 32 == 0
                && bts
                    .chunks_exact(32)
                    .all(|c| observed_bytes.iter().any(|ob| ob.as_slice() == c));
            assert!(
                whole || chunked,
                "byte field {} marked fs_absorbed but its bytes were never observed",
                f.path
            );
        }
    }

    // Sanity: the log actually saw the three domain labels of the opening
    // forks (i.e. the clones really share the log).
    let labels: Vec<Vec<u8>> = rec
        .recorded()
        .iter()
        .filter_map(|op| match op {
            RecordedOp::Label(l) => Some(l.clone()),
            _ => None,
        })
        .collect();
    assert!(labels.iter().any(|l| l == b"flock-a1-open-P"));
    assert!(labels.iter().any(|l| l == b"flock-a1-open-Q"));
}

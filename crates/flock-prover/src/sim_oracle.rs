//! **A programmable random oracle**, so the zero-knowledge game is executable
//! rather than only argued.
//!
//! A NIZK simulator in the random-oracle model is allowed to *program* the
//! oracle: it fixes the answers at points of its choosing, then produces a
//! transcript that the verifier — asking the same oracle — accepts. Prose
//! proofs stop there. This module makes the game runnable: the oracle is a
//! real object, the simulator programs entries in it, and the **unmodified
//! verifier** either accepts or does not.
//!
//! ## What is and is not demonstrated
//!
//! Acceptance under a programmed oracle is necessary, not sufficient. It shows
//! the simulator produces a transcript the verifier takes; it does not show
//! the transcript is *distributed* like an honest one, which is the actual
//! zero-knowledge property and has to be measured separately. Nor does a
//! harness like this bound the programming-collision probability — that is the
//! freshness argument, and it lives in the memos.
//!
//! Two controls keep the harness from being self-fulfilling:
//!
//! * an **unprogrammed** oracle must reproduce plain Fiat–Shamir exactly, so
//!   honest proofs verify under it unchanged
//!   ([`ProgrammableOracle::is_empty`], and the tests below);
//! * programming a point the verifier never reaches must change nothing.
//!
//! ## Faithfulness to the model
//!
//! [`OracleChallenger`] is byte-for-byte
//! [`FsChallenger`](flock_core::challenger::FsChallenger) except that each
//! squeeze consults the programmed table first, keyed by the **exact query
//! bytes** (`transcript state ‖ counter`) the honest challenger would have
//! hashed. Absorption, tagging, re-absorption of squeezed bytes, and the PoW
//! grind are unchanged. So an entry programmed at a point some other prefix
//! also reaches is visible there too — as it must be, since a random oracle is
//! a function, and pretending otherwise is exactly the error the freshness
//! argument exists to rule out.
//!
//! The succinct VEIL path uses this oracle for Fiat--Shamir challenges, but
//! not for every PCS and VEIL hash. See `docs/SECURITY.md`.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use flock_core::challenger::Challenger;
use flock_core::field::F128;
use flock_core::ro::{ByteOracle, encode_pow_point};

// Transcript op tags — must match `flock_core::challenger`'s encoding, since
// this challenger has to be byte-identical to the honest one.
const OP_DOMAIN: u8 = 0x01;
const OP_LABEL: u8 = 0x02;
const OP_OBSERVE: u8 = 0x03;
const OP_SQUEEZE: u8 = 0x04;
const OP_BYTES: u8 = 0x05;
const KIND_SCALAR: u8 = 0x01;
const KIND_SLICE: u8 = 0x02;

/// A random oracle with a programmed table. Points not in the table are
/// answered by SHA-256, so an empty table is the honest oracle.
#[derive(Debug, Default)]
pub struct ProgrammableOracle {
    table: HashMap<Vec<u8>, [u8; 32]>,
    /// Every point queried, in order — the query transcript a straightline
    /// extractor would read, and the audit trail for which programmed points
    /// were actually reached.
    queries: Vec<Vec<u8>>,
    seen: HashSet<[u8; 32]>,
    record_roles: Option<Vec<u8>>,
}

impl ProgrammableOracle {
    pub fn new() -> Self {
        Self::default()
    }

    /// Answer at `point`: the programmed value if there is one, else the real
    /// hash. Records the query.
    fn answer(&mut self, point: &[u8]) -> [u8; 32] {
        self.seen.insert(flock_core::ro::hash_point(point));
        if self
            .record_roles
            .as_ref()
            .is_none_or(|roles| point.first().is_some_and(|role| roles.contains(role)))
        {
            self.queries.push(point.to_vec());
        }
        if let Some(v) = self.table.get(point) {
            return *v;
        }
        flock_core::ro::hash_point(point)
    }

    /// Program the oracle at `point`. Returns the previous value if this
    /// point was already programmed — a collision the simulator must not
    /// ignore, since re-programming a point it already used would make its
    /// own earlier transcript inconsistent.
    pub fn program(&mut self, point: Vec<u8>, value: [u8; 32]) -> Option<[u8; 32]> {
        self.table.insert(point, value)
    }

    /// Whether `point` was already *queried* before being programmed. In the
    /// security argument this is the bad event: programming a point the
    /// distinguisher has already seen answered honestly is detectable. The
    /// simulator should assert this is false for every point it programs.
    pub fn was_queried(&self, point: &[u8]) -> bool {
        self.seen.contains(&flock_core::ro::hash_point(point))
    }

    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    pub fn programmed_len(&self) -> usize {
        self.table.len()
    }

    /// Programmed points in deterministic byte order. This is the executable
    /// audit surface for the G4/G5 simulator-game transition.
    pub fn programmed_points(&self) -> Vec<Vec<u8>> {
        let mut points = self.table.keys().cloned().collect::<Vec<_>>();
        points.sort();
        points
    }

    pub fn query_count(&self) -> usize {
        self.queries.len()
    }

    /// The recorded query transcript.
    pub fn queries(&self) -> &[Vec<u8>] {
        &self.queries
    }

    /// Restrict retained query bytes to the listed first-byte roles. Prior
    /// query detection remains active for every role.
    pub fn set_record_roles(&mut self, roles: Option<Vec<u8>>) {
        self.record_roles = roles;
    }

    /// Recorded depth-0 leaf payloads for a commitment channel, keyed by leaf
    /// index. Recording order is intentionally irrelevant under rayon.
    pub fn leaf_queries(&self, channel: flock_core::ro::RoChannel) -> Vec<(u64, Vec<u8>)> {
        let mut leaves = self
            .queries
            .iter()
            .filter_map(|point| {
                if point.len() < 76
                    || point[0] != flock_core::ro::ROLE_LEAF
                    || point[1..8] != flock_core::ro::RO_MAGIC
                    || point[8] != channel.as_u8()
                    || point[9] != 0
                {
                    return None;
                }
                let index = u64::from_le_bytes(point[68..76].try_into().ok()?);
                Some((index, point[76..].to_vec()))
            })
            .collect::<Vec<_>>();
        leaves.sort_unstable_by_key(|(index, _)| *index);
        leaves.dedup_by_key(|(index, _)| *index);
        leaves
    }
}

/// A handle several challengers can share, so prover-side programming and
/// verifier-side querying hit the same oracle.
pub type SharedOracle = Arc<Mutex<ProgrammableOracle>>;

pub fn shared_oracle() -> SharedOracle {
    Arc::new(Mutex::new(ProgrammableOracle::new()))
}

/// Point-oracle adapter sharing the simulator's programmed table and query
/// transcript. Merkle queries and Fiat-Shamir/PoW queries therefore inhabit
/// one oracle, distinguished only by their injective encodings.
#[derive(Clone)]
pub struct ProgrammableByteOracle {
    oracle: SharedOracle,
}

impl ProgrammableByteOracle {
    pub fn new(oracle: SharedOracle) -> Self {
        Self { oracle }
    }
}

impl ByteOracle for ProgrammableByteOracle {
    fn answer(&self, point: &[u8]) -> [u8; 32] {
        self.oracle.lock().expect("oracle poisoned").answer(point)
    }
}

/// Construct a point-oracle context backed by the same programmable oracle
/// used by [`OracleChallenger`].
pub fn ro_context(nonce: [u8; 32], oracle: SharedOracle) -> flock_core::ro::RoContext {
    flock_core::ro::RoContext::external(nonce, Arc::new(ProgrammableByteOracle::new(oracle)))
}

/// Fiat–Shamir over a [`ProgrammableOracle`]. Byte-identical to
/// `FsChallenger` in what it absorbs; the only difference is that squeezes go
/// through the oracle.
/// The absorbed transcript is kept in full rather than as a running hash
/// state. `FsChallenger` squeezes `SHA256(every absorbed byte ‖ ctr)` by
/// cloning its streaming hasher; to be able to *name* that query point — which
/// programming requires — the challenger must be able to reproduce those bytes
/// exactly. Keeping them costs memory a test harness can afford and buys
/// byte-exact faithfulness, which is the whole point of the module.
#[derive(Clone)]
pub struct OracleChallenger {
    absorbed: Vec<u8>,
    oracle: SharedOracle,
}

impl OracleChallenger {
    pub fn new(domain: &[u8], oracle: SharedOracle) -> Self {
        let mut c = Self {
            absorbed: Vec::new(),
            oracle,
        };
        c.absorb(&[OP_DOMAIN]);
        c.absorb(&(domain.len() as u64).to_le_bytes());
        c.absorb(domain);
        c
    }

    pub fn oracle(&self) -> &SharedOracle {
        &self.oracle
    }

    #[inline]
    fn absorb(&mut self, bytes: &[u8]) {
        self.absorbed.extend_from_slice(bytes);
    }

    #[inline]
    fn absorb_f128(&mut self, v: F128) {
        self.absorb(&v.lo.to_le_bytes());
        self.absorb(&v.hi.to_le_bytes());
    }

    /// The exact bytes the honest challenger hashes for squeeze block `ctr`:
    /// the current transcript state followed by the counter. Exposed so a
    /// simulator can compute the point it needs to program *before* querying
    /// it.
    pub fn squeeze_point(&self, ctr: u64) -> Vec<u8> {
        let mut point = Vec::with_capacity(self.absorbed.len() + 8);
        point.extend_from_slice(&self.absorbed);
        point.extend_from_slice(&ctr.to_le_bytes());
        point
    }

    /// One domain-separated proof-of-work query, routed
    /// through the oracle so grind queries appear in its transcript.
    fn pow_answer(&self, state: &[u8; 32], nonce: u64) -> [u8; 32] {
        let point = encode_pow_point(state, nonce);
        self.oracle.lock().expect("oracle poisoned").answer(&point)
    }

    /// The proof-of-work state digest, mirroring `FsChallenger`, but routed
    /// through the programmable oracle so no point query bypasses the game.
    fn pow_state_digest(&self) -> [u8; 32] {
        self.oracle
            .lock()
            .expect("oracle poisoned")
            .answer(&self.absorbed)
    }

    /// Squeeze through the oracle, mirroring `FsChallenger::squeeze_into`.
    fn squeeze_into(&self, out: &mut [u8]) {
        let mut off = 0usize;
        let mut ctr: u64 = 0;
        while off < out.len() {
            let point = self.squeeze_point(ctr);
            let block = self.oracle.lock().expect("oracle poisoned").answer(&point);
            let take = (out.len() - off).min(32);
            out[off..off + take].copy_from_slice(&block[..take]);
            off += take;
            ctr = ctr.wrapping_add(1);
        }
    }

    /// Program the *next* scalar squeeze to `value`, and return the point
    /// programmed. Call immediately before the `sample_f128` it should
    /// govern: the point depends on everything absorbed so far, so ordering
    /// is load-bearing.
    ///
    /// Returns `None` — having programmed nothing — if the point was already
    /// queried, which is the bad event of the security argument. Callers
    /// should treat `None` as a simulation failure rather than continuing.
    /// Program the *next* vector squeeze of length `n` to `values`. Same
    /// contract as [`Self::program_next_scalar`]: call immediately before the
    /// `sample_f128_vec` it governs.
    ///
    /// A vector squeeze spans `ceil(n·16 / 32)` oracle blocks, so this
    /// programs each block of the stream.
    pub fn program_next_vec(&mut self, values: &[F128]) -> Option<Vec<Vec<u8>>> {
        let mut probe = self.clone();
        probe.absorb(&[OP_SQUEEZE, KIND_SLICE]);
        probe.absorb(&(values.len() as u64).to_le_bytes());

        // The byte stream the squeeze must produce.
        let mut stream = Vec::with_capacity(values.len() * 16);
        for v in values {
            stream.extend_from_slice(&v.lo.to_le_bytes());
            stream.extend_from_slice(&v.hi.to_le_bytes());
        }

        let mut points = Vec::new();
        let mut off = 0usize;
        let mut ctr = 0u64;
        while off < stream.len() {
            let point = probe.squeeze_point(ctr);
            let take = (stream.len() - off).min(32);
            let mut block = [0u8; 32];
            block[..take].copy_from_slice(&stream[off..off + take]);
            // Bytes past the requested length are never read by the squeeze,
            // so leaving them zero is harmless.
            {
                let mut oracle = self.oracle.lock().expect("oracle poisoned");
                if oracle.was_queried(&point) {
                    return None;
                }
                oracle.program(point.clone(), block);
            }
            points.push(point);
            off += take;
            ctr = ctr.wrapping_add(1);
        }
        Some(points)
    }

    pub fn program_next_scalar(&mut self, value: F128) -> Option<Vec<u8>> {
        // Mirror what `sample_f128` absorbs before squeezing.
        let mut probe = self.clone();
        probe.absorb(&[OP_SQUEEZE, KIND_SCALAR]);
        let point = probe.squeeze_point(0);
        let mut block = [0u8; 32];
        block[..8].copy_from_slice(&value.lo.to_le_bytes());
        block[8..16].copy_from_slice(&value.hi.to_le_bytes());
        let mut oracle = self.oracle.lock().expect("oracle poisoned");
        if oracle.was_queried(&point) {
            return None;
        }
        oracle.program(point.clone(), block);
        Some(point)
    }
}

impl Challenger for OracleChallenger {
    fn observe_label(&mut self, label: &[u8]) {
        self.absorb(&[OP_LABEL]);
        self.absorb(&(label.len() as u64).to_le_bytes());
        self.absorb(label);
    }

    fn observe_f128(&mut self, value: F128) {
        self.absorb(&[OP_OBSERVE, KIND_SCALAR]);
        self.absorb_f128(value);
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.absorb(&[OP_OBSERVE, KIND_SLICE]);
        self.absorb(&(values.len() as u64).to_le_bytes());
        for v in values {
            self.absorb_f128(*v);
        }
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.absorb(&[OP_BYTES]);
        self.absorb(&(bytes.len() as u64).to_le_bytes());
        self.absorb(bytes);
    }

    fn sample_f128(&mut self) -> F128 {
        self.absorb(&[OP_SQUEEZE, KIND_SCALAR]);
        let mut buf = [0u8; 16];
        self.squeeze_into(&mut buf);
        self.absorb(&buf);
        F128 {
            lo: u64::from_le_bytes(buf[..8].try_into().unwrap()),
            hi: u64::from_le_bytes(buf[8..].try_into().unwrap()),
        }
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.absorb(&[OP_SQUEEZE, KIND_SLICE]);
        self.absorb(&(n as u64).to_le_bytes());
        let mut buf = vec![0u8; n * 16];
        self.squeeze_into(&mut buf);
        self.absorb(&buf);
        buf.chunks_exact(16)
            .map(|c| F128 {
                lo: u64::from_le_bytes(c[..8].try_into().unwrap()),
                hi: u64::from_le_bytes(c[8..].try_into().unwrap()),
            })
            .collect()
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        // Grinding queries the oracle at fresh points, exactly as the honest
        // challenger does. It is NOT programmed: the simulator grinds
        // honestly on its programmed prefix, which is why programming and
        // grinding have to interleave rather than the former completing
        // first.
        let state = self.pow_state_digest();
        let nonce = if bits == 0 {
            // Canonical nonce at zero-bit sites, matching `FsChallenger` —
            // which rejects any other value to keep proofs non-malleable.
            0
        } else {
            let mut n = 0u64;
            loop {
                let out = self.pow_answer(&state, n);
                if leading_zero_bits(&out) >= bits {
                    break n;
                }
                n = n.wrapping_add(1);
            }
        };
        // Absorbed through the TAGGED byte observation, exactly as the honest
        // challenger does — a raw absorb here would silently desynchronize
        // every later challenge.
        self.observe_bytes(&nonce.to_le_bytes());
        nonce
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        let state = self.pow_state_digest();
        let ok = if bits == 0 {
            nonce == 0
        } else {
            leading_zero_bits(&self.pow_answer(&state, nonce)) >= bits
        };
        self.observe_bytes(&nonce.to_le_bytes());
        ok
    }
}

fn leading_zero_bits(digest: &[u8; 32]) -> u32 {
    let mut n = 0u32;
    for b in digest {
        if *b == 0 {
            n += 8;
        } else {
            n += b.leading_zeros();
            break;
        }
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;
    use flock_core::challenger::FsChallenger;

    /// **The control.** With nothing programmed, the oracle challenger must
    /// be indistinguishable from plain Fiat–Shamir — same challenges, same
    /// order. Without this the harness could "verify" simulated proofs simply
    /// by being a different protocol.
    #[test]
    fn unprogrammed_oracle_reproduces_fiat_shamir() {
        let oracle = shared_oracle();
        let mut a = OracleChallenger::new(b"same-domain", oracle);
        let mut b = FsChallenger::new(b"same-domain");

        for i in 0..8u64 {
            let v = F128 { lo: i, hi: i * 7 };
            a.observe_f128(v);
            b.observe_f128(v);
            assert_eq!(a.sample_f128(), b.sample_f128(), "scalar squeeze {i}");
        }
        a.observe_bytes(b"root-bytes");
        b.observe_bytes(b"root-bytes");
        assert_eq!(a.sample_f128_vec(5), b.sample_f128_vec(5));
        a.observe_label(b"a-label");
        b.observe_label(b"a-label");
        assert_eq!(a.sample_f128(), b.sample_f128());
    }

    /// Programming the next challenge makes it come out as chosen, and the
    /// transcript continues consistently from there.
    #[test]
    fn programming_forces_the_next_challenge() {
        let oracle = shared_oracle();
        let mut ch = OracleChallenger::new(b"prog", oracle.clone());
        ch.observe_bytes(b"prefix");

        let chosen = F128 {
            lo: 0xDEAD_BEEF_1234_5678,
            hi: 0x0BAD_C0DE_9999_0001,
        };
        let point = ch
            .program_next_scalar(chosen)
            .expect("point must be fresh before any query");
        assert_eq!(ch.sample_f128(), chosen);
        assert_eq!(oracle.lock().unwrap().programmed_len(), 1);
        assert!(oracle.lock().unwrap().was_queried(&point));
    }

    /// A verifier reading the same oracle sees the same programmed
    /// challenges — which is what makes the simulation game meaningful.
    #[test]
    fn verifier_side_sees_the_programmed_value() {
        let oracle = shared_oracle();
        let chosen = F128 { lo: 42, hi: 43 };
        let mut prover = OracleChallenger::new(b"shared", oracle.clone());
        prover.observe_bytes(b"stmt");
        prover.program_next_scalar(chosen).expect("fresh");
        assert_eq!(prover.sample_f128(), chosen);

        // An independent challenger replaying the same absorptions.
        let mut verifier = OracleChallenger::new(b"shared", oracle);
        verifier.observe_bytes(b"stmt");
        assert_eq!(
            verifier.sample_f128(),
            chosen,
            "the verifier must see the programmed challenge"
        );
    }

    /// The bad event is detected rather than silently allowed: programming a
    /// point already queried returns `None`.
    #[test]
    fn reprogramming_a_queried_point_is_refused() {
        let oracle = shared_oracle();
        let mut ch = OracleChallenger::new(b"collide", oracle.clone());
        ch.observe_bytes(b"p");
        // Query first.
        let mut probe = ch.clone();
        let _ = probe.sample_f128();
        // Now programming that same point must be refused.
        assert!(
            ch.program_next_scalar(F128 { lo: 1, hi: 2 }).is_none(),
            "programming an already-queried point must be refused"
        );
    }

    /// Programming a point nothing reaches changes no challenge.
    #[test]
    fn unreached_programming_is_inert() {
        let oracle = shared_oracle();
        oracle
            .lock()
            .unwrap()
            .program(b"a point no transcript produces".to_vec(), [7u8; 32]);
        let mut a = OracleChallenger::new(b"inert", oracle);
        let mut b = FsChallenger::new(b"inert");
        a.observe_bytes(b"x");
        b.observe_bytes(b"x");
        assert_eq!(a.sample_f128(), b.sample_f128());
    }

    /// PoW points carry their role byte, are recorded by the oracle, and the
    /// unprogrammed result is byte-identical to production Fiat-Shamir.
    #[test]
    fn pow_points_are_framed_and_oracle_visible() {
        let oracle = shared_oracle();
        let mut p = OracleChallenger::new(b"pow", oracle.clone());
        p.observe_bytes(b"state");
        let nonce = p.grind_pow(8);
        let mut honest = FsChallenger::new(b"pow");
        honest.observe_bytes(b"state");
        assert_eq!(nonce, honest.grind_pow(8));
        let queries = oracle.lock().unwrap().queries().to_vec();
        assert!(
            queries
                .iter()
                .any(|point| point.len() == 41 && point[0] == flock_core::ro::ROLE_POW),
            "grinding must expose domain-separated PoW queries"
        );
        let mut v = OracleChallenger::new(b"pow", oracle);
        v.observe_bytes(b"state");
        assert!(v.verify_pow(nonce, 8), "honest grind must verify");
    }

    /// Regression for the former direct-SHA bypass: the bare transcript
    /// prefix is itself an oracle query, and programming it controls the state
    /// embedded in every subsequent PoW point.
    #[test]
    fn oracle_pow_state_digest_is_an_oracle_query() {
        let oracle = shared_oracle();
        let mut ch = OracleChallenger::new(b"pow-state", oracle.clone());
        ch.observe_bytes(b"prefix");
        let state_point = ch.absorbed.clone();
        let programmed_state = [0x5au8; 32];
        oracle
            .lock()
            .unwrap()
            .program(state_point.clone(), programmed_state);

        let _ = ch.grind_pow(2);
        let guard = oracle.lock().unwrap();
        assert!(guard.was_queried(&state_point));
        assert!(guard.queries().iter().any(|point| {
            point.len() == 41
                && point[0] == flock_core::ro::ROLE_POW
                && point[1..33] == programmed_state
        }));
    }
}

//! Verifier-randomness abstraction.
//!
//! A [`Challenger`] is the source of verifier challenges in the protocol.
//! The prover writes its messages into the challenger (`observe_*`) and reads
//! challenges back out (`sample_*`). The verifier mirrors this exactly — as
//! it walks through the proof, it observes each prover message and samples
//! the same challenges, so both sides derive the same randomness in lockstep.
//!
//! Two implementations:
//! - `RandomChallenger` — seeded pseudo-random, ignores observed messages.
//!   Kept around for bench isolation (measure prover cost without FS overhead)
//!   and soundness mutation tests. **Not sound for real proofs**, and to make
//!   that structural it is compiled *only* under `cfg(test)` or the
//!   `unsound-challenger` feature — a normal (real-proof) build has no insecure
//!   challenger to reach for.
//! - [`FsChallenger`] — SHA-256-based Fiat-Shamir. Absorbs observations into a
//!   running hash state; samples by cloning the state and squeezing bytes via a
//!   counter (`SHA256(state || ctr)` for ctr = 0, 1, …, since SHA-256 is not an
//!   XOF), then re-absorbing the squeezed bytes so the next challenge binds to
//!   the previous one (Merlin-style duplex). SHA-256 is also used for the
//!   Merkle commitments, so the whole system rests on a single hash.

use crate::{
    field::F128,
    oracle_budget::{OracleLimitError, OracleQueryBudget, oracle_blocks_for_bytes},
    ro::RoContext,
};
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

// `Send` supertrait: the verifier runs its PIOP/PCS replay inside a dedicated
// single-thread rayon pool (see `verifier::verifier_pool`), so the challenger
// it threads through must be able to cross into that pool. Both concrete
// challengers (`RandomChallenger`, `FsChallenger`) are trivially `Send`.
pub trait Challenger: Send {
    /// Build the SHA-256 context used by PCS and auxiliary commitments.
    /// Simulator challengers override this to share their programmable oracle.
    fn ro_context(&self, nonce: [u8; 32]) -> RoContext {
        RoContext::native(nonce)
    }

    /// Absorb a domain-separation label (e.g. `b"flock-zerocheck"`). Each
    /// protocol entry should call this once on entry so a transcript from
    /// one protocol cannot be replayed as another.
    fn observe_label(&mut self, _label: &[u8]) {
        // default no-op — RandomChallenger inherits this.
    }

    /// Absorb a single F128 prover message.
    fn observe_f128(&mut self, value: F128);

    /// Absorb a slice of F128 prover messages (e.g. the round-1 vector).
    fn observe_f128_slice(&mut self, values: &[F128]) {
        for v in values {
            self.observe_f128(*v);
        }
    }

    /// Absorb arbitrary bytes (e.g. a Merkle root or a statement digest).
    fn observe_bytes(&mut self, _bytes: &[u8]) {
        // default no-op — RandomChallenger inherits this.
    }

    /// Produce one F128 challenge.
    fn sample_f128(&mut self) -> F128;

    /// Fallible form of [`Self::sample_f128`] for budgeted execution.
    fn try_sample_f128(&mut self) -> Result<F128, OracleLimitError> {
        Ok(self.sample_f128())
    }

    /// Produce `n` F128 challenges, in order.
    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sample_f128()).collect()
    }

    /// Fallible form of [`Self::sample_f128_vec`] for budgeted execution.
    fn try_sample_f128_vec(&mut self, n: usize) -> Result<Vec<F128>, OracleLimitError> {
        Ok(self.sample_f128_vec(n))
    }

    /// Prover-side PoW grinding: snapshot the current transcript state,
    /// search for a `u64` nonce such that
    /// `SHA256(ROLE_POW || state || nonce)` has at
    /// least `bits` leading zero bits, then absorb the nonce into the
    /// transcript so subsequent challenges bind to it.
    ///
    /// Default implementation is a no-op (returns 0). Real implementations
    /// — e.g. [`FsChallenger`] — do the actual grind work and absorb the
    /// nonce. `bits = 0` means "no PoW required"; still absorbs the 0 nonce
    /// so the verifier mirror is byte-identical.
    fn grind_pow(&mut self, _bits: u32) -> u64 {
        0
    }

    /// Bounded prover-side PoW grinding. Implementations must try only nonces
    /// in `0..max_trials`, absorb the first successful nonce, and fail closed
    /// without absorbing if no such nonce exists.
    fn grind_pow_bounded(&mut self, bits: u32, _max_trials: u64) -> Result<u64, OracleLimitError> {
        Ok(self.grind_pow(bits))
    }

    /// Verifier-side mirror of [`Self::grind_pow`]: check that `nonce`
    /// satisfies the `bits`-leading-zeros PoW against the current transcript
    /// state, then absorb the nonce so the running state stays in lockstep
    /// with the prover.
    ///
    /// Default implementation accepts unconditionally (no-op). Real
    /// implementations must check the PoW; an honest verifier rejects the
    /// proof if this returns `false`.
    fn verify_pow(&mut self, _nonce: u64, _bits: u32) -> bool {
        true
    }

    /// Bounded verifier-side PoW check. Nonces outside `0..max_trials` are
    /// rejected before the PoW point is queried.
    fn verify_pow_bounded(
        &mut self,
        nonce: u64,
        bits: u32,
        _max_trials: u64,
    ) -> Result<bool, OracleLimitError> {
        Ok(self.verify_pow(nonce, bits))
    }
}

/// Byte length of `n` transcript-encoded `F128` elements.
pub fn f128_vec_byte_len(n: usize) -> Result<usize, OracleLimitError> {
    n.checked_mul(F128::BYTE_LEN)
        .ok_or(OracleLimitError::QueryBudgetExceeded)
}

/// Decode a whole byte stream of `F128` elements in transcript byte order.
pub fn f128_vec_from_le_bytes(bytes: &[u8]) -> Vec<F128> {
    let (chunks, remainder) = bytes.as_chunks::<{ F128::BYTE_LEN }>();
    assert!(
        remainder.is_empty(),
        "F128 byte stream length must be a multiple of 16"
    );
    chunks
        .iter()
        .map(|chunk| F128::from_le_bytes(*chunk))
        .collect()
}

/// Draw `n` scalar challenges, preserving scalar transcript tags.
pub fn sample_f128_scalars<C: Challenger>(
    challenger: &mut C,
    n: usize,
) -> Result<Vec<F128>, OracleLimitError> {
    (0..n).map(|_| challenger.try_sample_f128()).collect()
}

/// Draw a scalar challenge until `predicate` accepts or `max_trials` is exhausted.
pub fn sample_f128_matching<C, P>(
    challenger: &mut C,
    max_trials: usize,
    mut predicate: P,
) -> Result<F128, OracleLimitError>
where
    C: Challenger,
    P: FnMut(F128) -> bool,
{
    for _ in 0..max_trials {
        let value = challenger.try_sample_f128()?;
        if predicate(value) {
            return Ok(value);
        }
    }
    Err(OracleLimitError::RejectionSamplingLimitExceeded)
}

/// Draw vector challenges until `predicate` accepts or `max_trials` is exhausted.
pub fn sample_f128_vec_matching<C, P>(
    challenger: &mut C,
    len: usize,
    max_trials: usize,
    mut predicate: P,
) -> Result<Vec<F128>, OracleLimitError>
where
    C: Challenger,
    P: FnMut(&[F128]) -> bool,
{
    for _ in 0..max_trials {
        let values = challenger.try_sample_f128_vec(len)?;
        if predicate(&values) {
            return Ok(values);
        }
    }
    Err(OracleLimitError::RejectionSamplingLimitExceeded)
}

/// Draw `count` distinct positions in `0..domain`, returning them sorted.
pub fn sample_distinct_positions<C: Challenger>(
    challenger: &mut C,
    domain: usize,
    count: usize,
    max_trials: usize,
) -> Result<Vec<usize>, OracleLimitError> {
    assert!(
        count <= domain,
        "cannot sample {count} distinct positions from a domain of size {domain}"
    );
    if count == 0 {
        return Ok(Vec::new());
    }
    assert!(domain > 0, "position-sampling domain must be non-empty");

    let mut positions = BTreeSet::new();
    for _ in 0..max_trials {
        if positions.len() == count {
            break;
        }
        positions.insert((challenger.try_sample_f128()?.lo as usize) % domain);
    }
    if positions.len() != count {
        return Err(OracleLimitError::PositionSamplingLimitExceeded);
    }
    Ok(positions.into_iter().collect())
}

// ---------------------------------------------------------------------------
// RandomChallenger — seeded SplitMix64 pseudo-random source.
//
// Ignores observed messages (no Fiat-Shamir binding). Keep for bench isolation
// and soundness mutation tests; real proofs MUST use FsChallenger.
//
// Gated behind `cfg(test)` / `feature = "unsound-challenger"`: a real-proof
// build does not compile this type at all, so no production code path can
// accidentally instantiate an unsound challenger. See the module docs.
// ---------------------------------------------------------------------------

#[cfg(any(test, feature = "unsound-challenger"))]
#[derive(Clone, Debug)]
pub struct RandomChallenger {
    state: u64,
}

#[cfg(any(test, feature = "unsound-challenger"))]
impl RandomChallenger {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }
}

#[cfg(any(test, feature = "unsound-challenger"))]
impl Challenger for RandomChallenger {
    #[inline]
    fn observe_f128(&mut self, _value: F128) {
        // intentional no-op: random challenger is independent of prover state
    }

    fn sample_f128(&mut self) -> F128 {
        let lo = splitmix64(&mut self.state);
        let hi = splitmix64(&mut self.state);
        F128 { lo, hi }
    }
}

#[cfg(any(test, feature = "unsound-challenger"))]
#[inline]
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E3779B97F4A7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

// ---------------------------------------------------------------------------
// FsChallenger — SHA-256-based Fiat-Shamir (Merlin-style duplex).
//
// Tag bytes (one-byte op + one-byte kind) encode the operation type so that
// e.g. an `observe_f128_slice` of length 1 cannot collide with `observe_f128`,
// and a slice observation cannot collide with two scalar observations of the
// same total length.
//
// Sampling clones the live hasher, squeezes challenge bytes via SHA256(state
// || ctr) (SHA-256 is not an XOF), and absorbs the squeezed output back into
// the live state. This "duplex" pattern binds each subsequent
// challenge/observation to all prior squeezed output.
// ---------------------------------------------------------------------------

const OP_DOMAIN: u8 = 0x01;
const OP_LABEL: u8 = 0x02;
const OP_OBSERVE: u8 = 0x03;
const OP_SQUEEZE: u8 = 0x04;
const OP_BYTES: u8 = 0x05;

const KIND_SCALAR: u8 = 0x01;
const KIND_SLICE: u8 = 0x02;

/// Global Fiat–Shamir hash counters, enabled with `--features hash-count`.
/// Tracks the SHA-256 squeeze count and the SHA-256 PoW checks; absorbed
/// transcript bytes are tracked via [`FsChallenger::absorbed_bytes`].
#[cfg(feature = "hash-count")]
pub mod fs_count {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

    /// Number of XOF finalizations (one per `sample_f128` /
    /// `sample_f128_vec` / PoW state-digest extraction).
    pub static SQUEEZES: AtomicU64 = AtomicU64::new(0);
    /// Number of SHA-256 PoW evaluations (1 compression each; 41 B input).
    pub static POW_SHA256: AtomicU64 = AtomicU64::new(0);

    pub fn reset() {
        SQUEEZES.store(0, Relaxed);
        POW_SHA256.store(0, Relaxed);
    }

    /// (squeezes, pow_sha256_calls)
    pub fn snapshot() -> (u64, u64) {
        (SQUEEZES.load(Relaxed), POW_SHA256.load(Relaxed))
    }
}

#[derive(Clone)]
pub struct FsChallenger {
    hasher: Sha256,
    budget: Option<OracleQueryBudget>,
    /// Running total of absorbed transcript bytes, for the `hash-count`
    /// instrumentation (read only under that feature).
    #[allow(dead_code)]
    n_absorbed: u64,
}

impl FsChallenger {
    /// New challenger seeded with a domain-separation tag (e.g.
    /// `b"flock-r1cs"`). The domain is length-prefixed before being
    /// absorbed so two domains where one is a prefix of the other cannot
    /// produce the same initial state.
    pub fn new(domain: &[u8]) -> Self {
        let mut c = Self {
            hasher: Sha256::new(),
            budget: None,
            n_absorbed: 0,
        };
        c.absorb(&[OP_DOMAIN]);
        c.absorb(&(domain.len() as u64).to_le_bytes());
        c.absorb(domain);
        c
    }

    pub fn new_budgeted(domain: &[u8], budget: OracleQueryBudget) -> Self {
        let mut c = Self::new(domain);
        c.budget = Some(budget);
        c
    }

    pub fn with_query_budget(mut self, budget: OracleQueryBudget) -> Self {
        self.budget = Some(budget);
        self
    }

    pub fn query_budget(&self) -> Option<OracleQueryBudget> {
        self.budget.clone()
    }

    fn charge_queries(&self, amount: u64) -> Result<(), OracleLimitError> {
        if let Some(budget) = &self.budget {
            budget.try_charge(amount)?;
        }
        Ok(())
    }

    fn try_pow_state_digest(&self) -> Result<[u8; 32], OracleLimitError> {
        self.charge_queries(1)?;
        Ok(fs_pow_state_digest(&self.hasher))
    }

    fn try_pow_candidate(
        &self,
        state_digest: &[u8; 32],
        nonce: u64,
        bits: u32,
    ) -> Result<bool, OracleLimitError> {
        self.charge_queries(1)?;
        Ok(sha256_has_leading_zero_bits(state_digest, nonce, bits))
    }

    /// Absorb bytes into the running transcript state.
    #[inline]
    fn absorb(&mut self, bytes: &[u8]) {
        self.hasher.update(bytes);
        self.n_absorbed = self.n_absorbed.wrapping_add(bytes.len() as u64);
    }

    #[inline]
    fn absorb_f128(&mut self, v: F128) {
        self.absorb(&v.to_le_bytes());
    }

    /// Squeeze `out.len()` pseudorandom bytes from the current transcript
    /// state without mutating it. SHA-256 is not an XOF, so we derive the
    /// stream by hashing `state || ctr` for ctr = 0, 1, … (32 bytes each).
    fn squeeze_into(&self, out: &mut [u8]) {
        let mut off = 0usize;
        let mut ctr: u64 = 0;
        while off < out.len() {
            let mut h = self.hasher.clone();
            h.update(ctr.to_le_bytes());
            let block: [u8; 32] = h.finalize().into();
            let take = (out.len() - off).min(32);
            out[off..off + take].copy_from_slice(&block[..take]);
            off += take;
            ctr = ctr.wrapping_add(1);
        }
    }

    /// Total bytes absorbed into the transcript so far. Used by the
    /// `hash-count` instrumentation to estimate SHA-256 compression calls
    /// (≈ bytes / 64).
    #[cfg(feature = "hash-count")]
    pub fn absorbed_bytes(&self) -> u64 {
        self.n_absorbed
    }
}

impl Challenger for FsChallenger {
    fn ro_context(&self, nonce: [u8; 32]) -> RoContext {
        match &self.budget {
            Some(budget) => RoContext::native_with_budget(nonce, budget.clone()),
            None => RoContext::native(nonce),
        }
    }

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
        self.try_sample_f128()
            .expect("Fiat-Shamir oracle query budget exhausted")
    }

    fn try_sample_f128(&mut self) -> Result<F128, OracleLimitError> {
        self.charge_queries(1)?;
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb(&[OP_SQUEEZE, KIND_SCALAR]);
        let mut buf = [0u8; 16];
        self.squeeze_into(&mut buf);
        // Re-absorb the squeezed bytes so subsequent ops bind to this challenge.
        self.absorb(&buf);
        Ok(F128::from_le_bytes(buf))
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.try_sample_f128_vec(n)
            .expect("Fiat-Shamir oracle query budget exhausted")
    }

    fn try_sample_f128_vec(&mut self, n: usize) -> Result<Vec<F128>, OracleLimitError> {
        let bytes = f128_vec_byte_len(n)?;
        self.charge_queries(oracle_blocks_for_bytes(bytes)?)?;
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb(&[OP_SQUEEZE, KIND_SLICE]);
        self.absorb(&(n as u64).to_le_bytes());
        let mut buf = vec![0u8; bytes];
        self.squeeze_into(&mut buf);
        self.absorb(&buf);
        Ok(f128_vec_from_le_bytes(&buf))
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        let nonce = if bits == 0 {
            0
        } else {
            assert!(
                bits <= 256,
                "PoW grinding bits cannot exceed SHA-256 output length"
            );
            if self.budget.is_none() {
                grind_pow_unbudgeted(&self.hasher, bits)
            } else {
                let state_digest = self
                    .try_pow_state_digest()
                    .expect("Fiat-Shamir oracle query budget exhausted");
                let mut nonce: u64 = 0;
                loop {
                    if self
                        .try_pow_candidate(&state_digest, nonce, bits)
                        .expect("Fiat-Shamir oracle query budget exhausted")
                    {
                        break nonce;
                    }
                    nonce = nonce.wrapping_add(1);
                }
            }
        };
        // Absorb the nonce so subsequent transcript state binds to it.
        // Verifier mirrors via verify_pow.
        self.observe_bytes(&nonce.to_le_bytes());
        nonce
    }

    fn grind_pow_bounded(&mut self, bits: u32, max_trials: u64) -> Result<u64, OracleLimitError> {
        if bits == 0 {
            let nonce = 0u64;
            self.observe_bytes(&nonce.to_le_bytes());
            return Ok(0);
        }
        let state_digest = self.try_pow_state_digest()?;
        let mut found = None;
        for nonce in 0..max_trials {
            if self.try_pow_candidate(&state_digest, nonce, bits)? {
                found = Some(nonce);
                break;
            }
        }
        let nonce = found.ok_or(OracleLimitError::GrindingLimitExceeded)?;
        self.observe_bytes(&nonce.to_le_bytes());
        Ok(nonce)
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        let ok = if bits == 0 {
            // No PoW required here. An honest prover emits the canonical nonce
            // 0 (see `grind_pow`), so reject any non-zero value: it can only be
            // a re-grinding knob, and accepting it would leave proofs malleable
            // (a proof and its nonce-mutated twin would both verify). This
            // closes no soundness gap — when grinding_bits = 0 the query phase
            // already carries the full security target, and the FS soundness
            // accounting assumes free re-grinding regardless — it just keeps
            // proofs canonical / non-malleable at zero-bit grinding sites.
            nonce == 0
        } else {
            let state_digest = self
                .try_pow_state_digest()
                .expect("Fiat-Shamir oracle query budget exhausted");
            self.try_pow_candidate(&state_digest, nonce, bits)
                .expect("Fiat-Shamir oracle query budget exhausted")
        };
        // Absorb regardless of `ok` so the transcript stays byte-identical to
        // the prover's (an honest prover always reaches this with the same
        // nonce); a failed check rejects the proof at the call site anyway.
        self.observe_bytes(&nonce.to_le_bytes());
        ok
    }

    fn verify_pow_bounded(
        &mut self,
        nonce: u64,
        bits: u32,
        max_trials: u64,
    ) -> Result<bool, OracleLimitError> {
        if bits == 0 {
            let ok = nonce == 0;
            self.observe_bytes(&nonce.to_le_bytes());
            return Ok(ok);
        }
        if nonce >= max_trials {
            self.observe_bytes(&nonce.to_le_bytes());
            return Ok(false);
        }
        let state_digest = self.try_pow_state_digest()?;
        let ok = self.try_pow_candidate(&state_digest, nonce, bits)?;
        self.observe_bytes(&nonce.to_le_bytes());
        Ok(ok)
    }
}

/// Extract a 32-byte digest from the current SHA-256 challenger state, to be
/// used as the PoW base. Cloning + finalize gives a state-bound digest without
/// mutating the live hasher.
#[inline]
fn fs_pow_state_digest(hasher: &Sha256) -> [u8; 32] {
    #[cfg(feature = "hash-count")]
    fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    hasher.clone().finalize().into()
}

fn grind_pow_unbudgeted(hasher: &Sha256, bits: u32) -> u64 {
    let state_digest = fs_pow_state_digest(hasher);
    const PARALLEL_GRIND_MIN_HASHES: u64 = 1 << 13;
    if (1u64 << bits.min(63)) < PARALLEL_GRIND_MIN_HASHES {
        let mut nonce: u64 = 0;
        loop {
            if sha256_has_leading_zero_bits(&state_digest, nonce, bits) {
                break nonce;
            }
            nonce = nonce.wrapping_add(1);
        }
    } else {
        let block: u64 = 1 << (bits.min(24) + 1);
        let mut start: u64 = 0;
        loop {
            if let Some(n) = (start..start.saturating_add(block))
                .into_par_iter()
                .find_first(|&n| sha256_has_leading_zero_bits(&state_digest, n, bits))
            {
                break n;
            }
            start = start.saturating_add(block);
        }
    }
}

/// Check whether the domain-separated PoW point has at least `bits` leading
/// zero bits. Uses the same injective framing as external oracle challengers.
#[inline]
fn sha256_has_leading_zero_bits(state_digest: &[u8; 32], nonce: u64, bits: u32) -> bool {
    if bits > 256 {
        return false;
    }
    #[cfg(feature = "hash-count")]
    fs_count::POW_SHA256.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let h: [u8; 32] = Sha256::digest(crate::ro::encode_pow_point(state_digest, nonce)).into();
    let full_bytes = (bits / 8) as usize;
    let extra = bits % 8;
    for &b in h.iter().take(full_bytes) {
        if b != 0 {
            return false;
        }
    }
    if extra > 0 && (h[full_bytes] >> (8 - extra)) != 0 {
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Prover-side PoW grinding produces a nonce that the verifier-side
    /// `verify_pow` accepts at the same transcript position. State binding
    /// is preserved — sampling after PoW gives identical challenges on both
    /// sides.
    #[test]
    fn fs_challenger_pow_roundtrip() {
        for bits in [0u32, 5, 10, 14] {
            let mut prover = FsChallenger::new(b"pow-test");
            prover.observe_label(b"flock-pow-test");
            prover.observe_bytes(b"some root data");
            let nonce = prover.grind_pow(bits);

            let mut verifier = FsChallenger::new(b"pow-test");
            verifier.observe_label(b"flock-pow-test");
            verifier.observe_bytes(b"some root data");
            assert!(
                verifier.verify_pow(nonce, bits),
                "verify failed at bits={bits}"
            );

            // Subsequent challenges must agree.
            for _ in 0..4 {
                assert_eq!(prover.sample_f128(), verifier.sample_f128());
            }
        }
    }

    /// `verify_pow` rejects a wrong nonce when grinding bits > 0.
    #[test]
    fn fs_challenger_pow_rejects_wrong_nonce() {
        let mut prover = FsChallenger::new(b"pow-test");
        prover.observe_bytes(b"root");
        let nonce = prover.grind_pow(10);
        let bad_nonce = nonce.wrapping_add(1);

        let mut verifier = FsChallenger::new(b"pow-test");
        verifier.observe_bytes(b"root");
        assert!(
            !verifier.verify_pow(bad_nonce, 10),
            "should reject wrong nonce"
        );
    }

    /// At a zero-bit grinding site `verify_pow` accepts the canonical nonce 0
    /// (what `grind_pow(0)` emits) but rejects any non-zero nonce, so a proof
    /// can't be made malleable by swapping in an arbitrary nonce.
    #[test]
    fn fs_challenger_pow_zero_bits_requires_canonical_nonce() {
        let mk = || {
            let mut ch = FsChallenger::new(b"pow-test");
            ch.observe_bytes(b"root");
            ch
        };
        assert_eq!(mk().grind_pow(0), 0, "honest zero-bit grind is the 0 nonce");
        assert!(mk().verify_pow(0, 0), "canonical 0 nonce must verify");
        for bad in [1u64, 42, u64::MAX] {
            assert!(
                !mk().verify_pow(bad, 0),
                "non-zero nonce {bad} must be rejected at zero-bit grinding"
            );
        }
    }

    /// Default Challenger impl (RandomChallenger) is a no-op for PoW.
    #[test]
    fn random_challenger_pow_is_noop() {
        let mut ch = RandomChallenger::new(0);
        assert_eq!(ch.grind_pow(16), 0);
        assert!(ch.verify_pow(0, 16));
    }

    #[test]
    fn random_challenger_is_deterministic_per_seed() {
        let mut c1 = RandomChallenger::new(42);
        let mut c2 = RandomChallenger::new(42);
        for _ in 0..16 {
            assert_eq!(c1.sample_f128(), c2.sample_f128());
        }
    }

    #[test]
    fn random_challenger_observe_is_noop() {
        // Observing arbitrary messages does not change the sampled values.
        let mut c1 = RandomChallenger::new(7);
        let mut c2 = RandomChallenger::new(7);
        c2.observe_f128(F128 {
            lo: 0xDEADBEEF,
            hi: 0xCAFEBABE,
        });
        c2.observe_f128_slice(&[F128::ONE, F128::ZERO]);
        c2.observe_label(b"ignored");
        c2.observe_bytes(b"also ignored");
        for _ in 0..8 {
            assert_eq!(c1.sample_f128(), c2.sample_f128());
        }
    }

    #[test]
    fn sample_f128_vec_matches_individual_samples() {
        let mut c1 = RandomChallenger::new(99);
        let mut c2 = RandomChallenger::new(99);
        let batch = c1.sample_f128_vec(5);
        let individual: Vec<F128> = (0..5).map(|_| c2.sample_f128()).collect();
        assert_eq!(batch, individual);
    }

    // ---- FsChallenger ------------------------------------------------------

    #[test]
    fn fs_challenger_identical_scripts_produce_identical_output() {
        let mut c1 = FsChallenger::new(b"flock-test");
        let mut c2 = FsChallenger::new(b"flock-test");
        let msg = F128 {
            lo: 0x1234,
            hi: 0x5678,
        };
        c1.observe_f128(msg);
        c2.observe_f128(msg);
        let r1 = c1.sample_f128_vec(8);
        let r2 = c2.sample_f128_vec(8);
        assert_eq!(r1, r2);
    }

    #[test]
    fn fs_challenger_different_domains_diverge() {
        let mut c1 = FsChallenger::new(b"flock-a");
        let mut c2 = FsChallenger::new(b"flock-b");
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_different_observations_diverge() {
        let mut c1 = FsChallenger::new(b"flock");
        let mut c2 = FsChallenger::new(b"flock");
        c1.observe_f128(F128::ONE);
        c2.observe_f128(F128::ZERO);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_label_changes_output() {
        let mut c1 = FsChallenger::new(b"flock");
        let mut c2 = FsChallenger::new(b"flock");
        c1.observe_label(b"phase-A");
        // c2 omits the label entirely.
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_scalar_vs_slice_dont_collide() {
        // observe_f128_slice(&[v]) must NOT produce the same state as
        // observe_f128(v) — the length prefix and kind tag must defeat this.
        let v = F128 { lo: 0xAB, hi: 0xCD };
        let mut c1 = FsChallenger::new(b"flock");
        let mut c2 = FsChallenger::new(b"flock");
        c1.observe_f128(v);
        c2.observe_f128_slice(&[v]);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_two_scalars_dont_collide_with_one_slice_of_two() {
        let a = F128 { lo: 1, hi: 2 };
        let b = F128 { lo: 3, hi: 4 };
        let mut c1 = FsChallenger::new(b"flock");
        let mut c2 = FsChallenger::new(b"flock");
        c1.observe_f128(a);
        c1.observe_f128(b);
        c2.observe_f128_slice(&[a, b]);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_sample_one_vs_sample_vec_one_differ() {
        // Squeeze tag differs (KIND_SCALAR vs KIND_SLICE+len), so a single
        // sample_f128 must not equal sample_f128_vec(1)[0].
        let mut c1 = FsChallenger::new(b"flock");
        let mut c2 = FsChallenger::new(b"flock");
        assert_ne!(c1.sample_f128(), c2.sample_f128_vec(1)[0]);
    }

    #[test]
    fn fs_challenger_budgeted_vector_charges_exact_blocks() {
        let budget = OracleQueryBudget::new(2);
        let mut challenger = FsChallenger::new_budgeted(b"budget", budget.clone());
        assert!(challenger.try_sample_f128_vec(3).is_ok());
        assert_eq!(budget.used(), 2);
        assert_eq!(
            challenger.try_sample_f128(),
            Err(OracleLimitError::QueryBudgetExceeded)
        );
        assert_eq!(budget.used(), 2);
    }

    #[test]
    fn fs_challenger_bounded_grind_exhausts_exact_trial_cap() {
        let budget = OracleQueryBudget::new(4);
        let mut challenger = FsChallenger::new_budgeted(b"pow-budget", budget.clone());
        challenger.observe_bytes(b"prefix");
        assert_eq!(
            challenger.grind_pow_bounded(257, 3),
            Err(OracleLimitError::GrindingLimitExceeded)
        );
        assert_eq!(budget.used(), 4);
    }

    #[test]
    fn fs_challenger_sample_advances_state() {
        // After a sample, the next observation should not collapse to the
        // pre-sample state (the squeezed bytes are re-absorbed).
        let mut c1 = FsChallenger::new(b"flock");
        let mut c2 = FsChallenger::new(b"flock");
        let _ = c1.sample_f128();
        // c2 skips the sample.
        c1.observe_f128(F128::ONE);
        c2.observe_f128(F128::ONE);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }
}

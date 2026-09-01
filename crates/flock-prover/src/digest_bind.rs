//! **Public-digest binding**: pinning a batch's output regions to a public
//! list of hash digests.
//!
//! This is what turns Flock's BLAKE3 batch statement from
//!
//! > "there exist `2^n` valid compression traces"
//!
//! into the statement applications actually want:
//!
//! > "for the public digests `y_1..y_n`, I know preimages `x_1..x_n` with
//! > `BLAKE3(x_i) = y_i`".
//!
//! ## The mechanism, and why this one
//!
//! The output region (`out_lo`, the 8-word compression output) occupies an
//! aligned `2^region_log`-bit slot of every witness block — the same geometry
//! the hash-chain argument was designed around. So the digest list is exactly
//! a *public* assignment to that slot across instances, and binding it is one
//! multilinear identity:
//!
//! ```text
//!   ẑ_packed(τ_pos, sel=OUT, 0^high, ι)  ==  ŷ(τ_pos, ι)
//! ```
//!
//! where `ŷ` is the multilinear extension of the public digest array over
//! (packed-position-within-slot, instance) and `ι` is a random instance
//! point. Both sides are evaluated at challenges drawn *after* the commitment
//! is bound, so by Schwartz–Zippel a committed slab that differs from the
//! public digests anywhere agrees at the challenge point with probability at
//! most `(n_log + 1)/2^128`.
//!
//! The verifier **computes the target itself** from the public statement
//! (`digest_claim_value`); nothing about it is taken on the prover's word, and
//! it is not a proof field. The claim rides the *existing* batched Ligerito
//! opening as one more [`PackedDirectClaim`] — no extra commitment, no extra
//! sumcheck, no extra opening (contrast the chain argument, whose shift
//! sumcheck exists for the inter-instance glue, which digest binding does not
//! need).
//!
//! ## Why not open at fixed Boolean indices
//!
//! The obvious alternative — "open the witness at the digest bit positions" —
//! leaks. A ring-switched claim at a Boolean point publishes `s_hat_v`, whose
//! entries are then literally the 128 raw bits of the witness word; a
//! packed-direct claim at a Boolean point reveals that whole 128-bit word.
//! Evaluating at a *random* point instead reveals only `ŷ(τ)`, a public
//! function of the public digests. This matters for the zk mode: the value is
//! public, so conditioning the hiding argument on it is legitimate rather than
//! a concession.
//!
//! ## Padding instances
//!
//! The batch is padded to `2^n_log` instances. `digest_slab` fills padding
//! entries with [`PaddingDigest`], which must match what the honest padding
//! trace actually carries in its output slot — that is a property of the
//! encoder's padding witness, asserted by the encoder's own tests, and it is
//! part of the statement encoding (a verifier using the wrong padding rule
//! computes a different target and rejects honest proofs).

#[cfg(not(feature = "std"))]
use std::prelude::v1::*;

use flock_core::challenger::Challenger;
use flock_core::field::F128;
use flock_core::lincheck::build_eq_table;
use flock_core::pcs::{DirectEqInd, LOG_PACKING, PackedDirectClaim};
use flock_core::r1cs::WitnessLayout;

/// Geometry of the output region a digest list binds to. Mirrors the chain
/// layout's output half — the same aligned-slot requirement applies, and for
/// the same reason (the slot selector must be a single bit of the multilinear
/// cube).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DigestLayout {
    /// `log2` of the per-block witness size in bits.
    pub k_log: usize,
    /// `log2` of the aligned slot holding the output region.
    pub region_log: usize,
    /// Real digest bits per instance (≤ `2^region_log`, multiple of 8).
    pub region_bits: usize,
    /// Byte offset of the output slot within a block.
    pub output_byte_off: usize,
}

impl DigestLayout {
    /// Packed positions spanning one region = `region_log − LOG_PACKING`
    /// coordinates.
    #[inline]
    pub fn tau_pos_len(&self) -> usize {
        self.region_log - LOG_PACKING
    }

    /// Index of the aligned slot the output region occupies.
    #[inline]
    pub fn slot_index(&self) -> usize {
        (self.output_byte_off * 8) >> self.region_log
    }

    /// Coordinates between the slot-selector bits and the instance index.
    #[inline]
    pub fn high_coords(&self) -> usize {
        self.k_log - self.region_log
    }

    /// Sanity: the region must be an aligned, byte-contiguous slot that fits.
    pub fn validate(&self) {
        assert!(
            self.region_log >= LOG_PACKING,
            "region must span at least one packed word"
        );
        assert!(self.region_bits <= 1usize << self.region_log);
        assert_eq!(self.region_bits % 8, 0, "region_bits must be a byte count");
        assert_eq!(
            (self.output_byte_off * 8) % (1usize << self.region_log),
            0,
            "output region must be slot-aligned"
        );
        assert!(self.k_log >= self.region_log);
    }
}

/// What a padded (non-statement) instance carries in its output slot. Part of
/// the statement encoding: the verifier must use the same rule the honest
/// prover's padding witness satisfies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaddingDigest {
    /// Padding instances hold an all-zero output region.
    Zero,
    /// Padding instances repeat the digest of the honest padding trace,
    /// supplied by the encoder (e.g. the compression of an all-zero input).
    Constant,
}

/// The public part of a fixed-digest statement: an ordered digest list plus
/// the padding rule. `digests[i]` is instance `i`'s output region in
/// **physical within-slot bit order** (the same order the witness stores it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigestStatement {
    pub layout: DigestLayout,
    /// `n_log` — the batch is `2^n_log` instances.
    pub n_log: usize,
    /// The public digests, one per real instance. `digests.len()` may be less
    /// than `2^n_log`; the remainder is padding.
    pub digests: Vec<Vec<bool>>,
    pub padding: PaddingDigest,
    /// The padding instances' region bits when `padding == Constant`.
    pub padding_bits: Vec<bool>,
}

impl DigestStatement {
    /// Absorb the statement into a transcript hash. Every field that changes
    /// what is being proven is included — the digest list, its order and
    /// length, the padding rule, and the geometry — so a proof cannot be
    /// replayed against a different, reordered, or differently-padded list.
    ///
    /// This is deliberately a *separate* digest from the circuit's
    /// `statement_digest`: the circuit fixes the relation's shape, this fixes
    /// its public inputs.
    pub fn public_digest(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"flock-digest-statement");
        h.update(&(self.layout.k_log as u64).to_le_bytes());
        h.update(&(self.layout.region_log as u64).to_le_bytes());
        h.update(&(self.layout.region_bits as u64).to_le_bytes());
        h.update(&(self.layout.output_byte_off as u64).to_le_bytes());
        h.update(&(self.n_log as u64).to_le_bytes());
        h.update(&(self.digests.len() as u64).to_le_bytes());
        h.update(match self.padding {
            PaddingDigest::Zero => b"pad-zero",
            PaddingDigest::Constant => b"pad-const",
        });
        let pack_bits = |h: &mut blake3::Hasher, bits: &[bool]| {
            h.update(&(bits.len() as u64).to_le_bytes());
            let mut byte = 0u8;
            for (i, b) in bits.iter().enumerate() {
                if *b {
                    byte |= 1 << (i % 8);
                }
                if i % 8 == 7 {
                    h.update(&[byte]);
                    byte = 0;
                }
            }
            if !bits.len().is_multiple_of(8) {
                h.update(&[byte]);
            }
        };
        for d in &self.digests {
            pack_bits(&mut h, d);
        }
        if self.padding == PaddingDigest::Constant {
            pack_bits(&mut h, &self.padding_bits);
        }
        *h.finalize().as_bytes()
    }

    /// The region bits of instance `i`, real or padding.
    fn region_of(&self, i: usize) -> &[bool] {
        match self.digests.get(i) {
            Some(d) => d,
            None => match self.padding {
                PaddingDigest::Zero => &[],
                PaddingDigest::Constant => &self.padding_bits,
            },
        }
    }

    /// Basic well-formedness. Called by both prover and verifier.
    pub fn validate(&self) {
        self.layout.validate();
        assert!(
            self.digests.len() <= 1usize << self.n_log,
            "more digests ({}) than instances (2^{})",
            self.digests.len(),
            self.n_log
        );
        for d in &self.digests {
            assert_eq!(
                d.len(),
                self.layout.region_bits,
                "each digest must be exactly region_bits long"
            );
        }
        if self.padding == PaddingDigest::Constant {
            assert_eq!(self.padding_bits.len(), self.layout.region_bits);
        }
    }
}

/// Fold one public region's physical bits to `Σ_pos eq(τ_pos, pos)·packed[pos]`
/// — the same map the prover's committed witness realizes at that slot.
///
/// Packing is bit `b` of packed word `pos` ↦ coefficient `b` of the `F128` at
/// position `pos`, matching the witness packing; the region's tail up to the
/// slot size is zero, as the layout requires.
fn fold_region(tau_pos: &[F128], eq_tau: &[F128], phys_bits: &[bool]) -> F128 {
    let bits_per_packed = 1usize << LOG_PACKING;
    let n_packed = 1usize << tau_pos.len();
    debug_assert!(phys_bits.len() <= n_packed * bits_per_packed);
    let mut acc = F128::ZERO;
    for (pos, eq) in eq_tau.iter().enumerate().take(n_packed) {
        let mut packed = F128::ZERO;
        for b in 0..bits_per_packed {
            let idx = pos * bits_per_packed + b;
            if idx < phys_bits.len() && phys_bits[idx] {
                if b < 64 {
                    packed.lo |= 1u64 << b;
                } else {
                    packed.hi |= 1u64 << (b - 64);
                }
            }
        }
        acc += *eq * packed;
    }
    acc
}

/// The challenges a digest claim consumes, in transcript order. Sampled
/// identically by prover and verifier.
#[derive(Clone, Debug)]
pub struct DigestChallenges {
    /// Binds the packed position within the output slot.
    pub tau_pos: Vec<F128>,
    /// Binds the instance index.
    pub instance: Vec<F128>,
}

impl DigestChallenges {
    /// Draw the claim's challenges. MUST be called after the commitment (and,
    /// in zk mode, every mask commitment) is bound into the transcript —
    /// otherwise a prover could choose the committed slab to agree with the
    /// public digests only at the point it knew in advance.
    pub fn sample<Ch: Challenger>(stmt: &DigestStatement, challenger: &mut Ch) -> Self {
        challenger.observe_label(b"flock-digest-bind");
        let tau_pos = challenger.sample_f128_vec(stmt.layout.tau_pos_len());
        let instance = challenger.sample_f128_vec(stmt.n_log);
        Self { tau_pos, instance }
    }
}

/// The claim target `ŷ(τ_pos, ι)`: the multilinear extension of the public
/// digest array, evaluated at the sampled point. Public — computed the same
/// way by prover and verifier, never transmitted.
///
/// Cost is `O(2^n_log)` field operations (one fold per instance), which is
/// linear in the batch and negligible beside verification.
pub fn digest_claim_value(stmt: &DigestStatement, ch: &DigestChallenges) -> F128 {
    stmt.validate();
    let eq_tau = build_eq_table(&ch.tau_pos);
    let eq_inst = build_eq_table(&ch.instance);
    let n_inst = 1usize << stmt.n_log;
    let mut acc = F128::ZERO;
    for (i, eq_i) in eq_inst.iter().enumerate().take(n_inst) {
        if *eq_i == F128::ZERO {
            continue;
        }
        acc += *eq_i * fold_region(&ch.tau_pos, &eq_tau, stmt.region_of(i));
    }
    acc
}

/// Build the claim point over `L = m − LOG_PACKING` coordinates.
///
/// The point addresses a *word* index, decomposed by the witness layout:
/// - RowMajor: `word = (inst << (k_log − 7)) | in_block`
///   → `[τ_pos…, slot-selector bits…, instance…]`
/// - BatchMajor: `word = (in_block << n_log) | inst`
///   → `[instance…, τ_pos…, slot-selector bits…]`
///
/// The slot-selector coordinates are pinned to the binary expansion of
/// [`DigestLayout::slot_index`] — exact zeros and ones, which
/// `build_eq_sparse` collapses, so the eq tensor stays small.
pub fn digest_claim_point(
    stmt: &DigestStatement,
    wl: WitnessLayout,
    ch: &DigestChallenges,
) -> Vec<F128> {
    let high = stmt.layout.high_coords();
    let slot = stmt.layout.slot_index();
    assert!(
        slot < (1usize << high),
        "slot index {slot} does not fit in {high} coords"
    );
    let mut in_block: Vec<F128> = Vec::with_capacity(stmt.layout.tau_pos_len() + high);
    in_block.extend_from_slice(&ch.tau_pos);
    for j in 0..high {
        in_block.push(if (slot >> j) & 1 == 1 {
            F128::ONE
        } else {
            F128::ZERO
        });
    }
    let mut point = Vec::with_capacity(in_block.len() + ch.instance.len());
    match wl {
        WitnessLayout::RowMajor => {
            point.extend_from_slice(&in_block);
            point.extend_from_slice(&ch.instance);
        }
        WitnessLayout::BatchMajor => {
            point.extend_from_slice(&ch.instance);
            point.extend_from_slice(&in_block);
        }
    }
    point
}

/// Assemble the prover-side packed-direct claim binding the committed output
/// slab to the public digests.
pub fn digest_claim(
    stmt: &DigestStatement,
    wl: WitnessLayout,
    ch: &DigestChallenges,
) -> PackedDirectClaim {
    let point = digest_claim_point(stmt, wl, ch);
    let value = digest_claim_value(stmt, ch);
    let sparse_eq = flock_core::pcs::ring_switch::build_eq_sparse(&point);
    PackedDirectClaim {
        point,
        value,
        eq_ind: DirectEqInd::Sparse(sparse_eq),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// BLAKE3's I/O-aligned geometry: 256-bit slots, output in slot 1.
    fn blake3_layout() -> DigestLayout {
        DigestLayout {
            k_log: 14,
            region_log: 8,
            region_bits: 256,
            output_byte_off: 32,
        }
    }

    fn stmt_of(digests: Vec<Vec<bool>>, n_log: usize) -> DigestStatement {
        DigestStatement {
            layout: blake3_layout(),
            n_log,
            digests,
            padding: PaddingDigest::Zero,
            padding_bits: Vec::new(),
        }
    }

    fn bits_of(seed: u64, n: usize) -> Vec<bool> {
        let mut s = seed | 1;
        (0..n)
            .map(|_| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                s & 1 == 1
            })
            .collect()
    }

    fn challenges(seed: u64, stmt: &DigestStatement) -> DigestChallenges {
        let mut s = seed | 1;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            let lo = s;
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            F128 { lo, hi: s }
        };
        DigestChallenges {
            tau_pos: (0..stmt.layout.tau_pos_len()).map(|_| next()).collect(),
            instance: (0..stmt.n_log).map(|_| next()).collect(),
        }
    }

    /// The point must select exactly the output slot: the selector coords are
    /// the binary expansion of slot 1, and the τ_pos coords stay free.
    #[test]
    fn claim_point_selects_the_output_slot() {
        let stmt = stmt_of(vec![bits_of(7, 256); 4], 2);
        let ch = challenges(11, &stmt);
        let point = digest_claim_point(&stmt, WitnessLayout::RowMajor, &ch);
        // L = m − 7 where m = k_log + n_log = 16 → 9 coords.
        assert_eq!(point.len(), 9);
        assert_eq!(&point[0..1], &ch.tau_pos[..]);
        // slot_index = (32*8) >> 8 = 1 → selector coords are [1, 0, 0, 0, 0, 0].
        assert_eq!(point[1], F128::ONE);
        for p in point.iter().take(7).skip(2) {
            assert_eq!(*p, F128::ZERO);
        }
        assert_eq!(&point[7..9], &ch.instance[..]);
    }

    /// BatchMajor puts the instance coords first; both layouts address the
    /// same word set.
    #[test]
    fn claim_point_respects_batch_major() {
        let stmt = stmt_of(vec![bits_of(3, 256); 4], 2);
        let ch = challenges(5, &stmt);
        let point = digest_claim_point(&stmt, WitnessLayout::BatchMajor, &ch);
        assert_eq!(&point[0..2], &ch.instance[..]);
        assert_eq!(&point[2..3], &ch.tau_pos[..]);
        assert_eq!(point[3], F128::ONE);
    }

    /// The target is the MLE of the digest array: at a Boolean instance point
    /// it must equal that instance's own folded region.
    #[test]
    fn value_at_boolean_instance_point_is_that_digest() {
        let digests: Vec<Vec<bool>> = (0..4).map(|i| bits_of(100 + i, 256)).collect();
        let stmt = stmt_of(digests.clone(), 2);
        let base = challenges(21, &stmt);
        for (i, digest) in digests.iter().enumerate() {
            let ch = DigestChallenges {
                tau_pos: base.tau_pos.clone(),
                instance: (0..2)
                    .map(|b| {
                        if (i >> b) & 1 == 1 {
                            F128::ONE
                        } else {
                            F128::ZERO
                        }
                    })
                    .collect(),
            };
            let eq_tau = build_eq_table(&ch.tau_pos);
            assert_eq!(
                digest_claim_value(&stmt, &ch),
                fold_region(&ch.tau_pos, &eq_tau, digest),
                "MLE at instance {i} must be that instance's folded digest"
            );
        }
    }

    /// Padding instances contribute their padding rule, not a real digest.
    #[test]
    fn padding_instances_fold_to_the_padding_rule() {
        // Two real digests in a 4-instance batch; instances 2,3 are padding.
        let stmt = stmt_of(vec![bits_of(1, 256), bits_of(2, 256)], 2);
        let base = challenges(33, &stmt);
        for i in 2..4 {
            let ch = DigestChallenges {
                tau_pos: base.tau_pos.clone(),
                instance: (0..2)
                    .map(|b| {
                        if (i >> b) & 1 == 1 {
                            F128::ONE
                        } else {
                            F128::ZERO
                        }
                    })
                    .collect(),
            };
            assert_eq!(
                digest_claim_value(&stmt, &ch),
                F128::ZERO,
                "zero-padding instance {i} must fold to zero"
            );
        }
    }

    /// Different digest lists give different targets at a random point — the
    /// binding is not vacuous.
    #[test]
    fn distinct_digest_lists_give_distinct_targets() {
        let a = stmt_of((0..4).map(|i| bits_of(200 + i, 256)).collect(), 2);
        let mut flipped = a.digests.clone();
        flipped[2][17] = !flipped[2][17];
        let b = stmt_of(flipped, 2);
        let ch = challenges(44, &a);
        assert_ne!(digest_claim_value(&a, &ch), digest_claim_value(&b, &ch));
    }

    /// Reordering the digest list changes the statement hash AND the target.
    #[test]
    fn reordering_changes_statement_and_target() {
        let digests: Vec<Vec<bool>> = (0..4).map(|i| bits_of(300 + i, 256)).collect();
        let a = stmt_of(digests.clone(), 2);
        let mut swapped = digests;
        swapped.swap(0, 3);
        let b = stmt_of(swapped, 2);
        assert_ne!(a.public_digest(), b.public_digest());
        let ch = challenges(55, &a);
        assert_ne!(digest_claim_value(&a, &ch), digest_claim_value(&b, &ch));
    }

    /// Duplicate digests are allowed and produce a well-defined target (the
    /// MLE of a list with repeats) — nothing de-duplicates.
    #[test]
    fn duplicate_digests_are_allowed() {
        let d = bits_of(400, 256);
        let stmt = stmt_of(vec![d.clone(), d.clone(), d.clone(), d], 2);
        let ch = challenges(66, &stmt);
        let eq_tau = build_eq_table(&ch.tau_pos);
        // Every instance carries the same region, so the MLE collapses to it
        // (the eq weights sum to one).
        assert_eq!(
            digest_claim_value(&stmt, &ch),
            fold_region(&ch.tau_pos, &eq_tau, &stmt.digests[0])
        );
    }

    /// A batch whose real-instance count is not a power of two is handled by
    /// the padding rule, and the statement hash records the real count.
    #[test]
    fn non_power_of_two_batch_records_its_length() {
        let three = stmt_of((0..3).map(|i| bits_of(500 + i, 256)).collect(), 2);
        let four = stmt_of((0..4).map(|i| bits_of(500 + i, 256)).collect(), 2);
        assert_ne!(three.public_digest(), four.public_digest());
        let ch = challenges(77, &three);
        // Instance 3 is padding in `three` and a real digest in `four`.
        assert_ne!(
            digest_claim_value(&three, &ch),
            digest_claim_value(&four, &ch)
        );
    }

    /// The padding RULE is part of the statement: the same digests with a
    /// different padding convention are a different statement and a different
    /// target.
    #[test]
    fn padding_rule_is_bound() {
        let digests = vec![bits_of(600, 256), bits_of(601, 256)];
        let zero = stmt_of(digests.clone(), 2);
        let konst = DigestStatement {
            layout: blake3_layout(),
            n_log: 2,
            digests,
            padding: PaddingDigest::Constant,
            padding_bits: bits_of(999, 256),
        };
        assert_ne!(zero.public_digest(), konst.public_digest());
        let ch = challenges(88, &zero);
        assert_ne!(
            digest_claim_value(&zero, &ch),
            digest_claim_value(&konst, &ch)
        );
    }
}

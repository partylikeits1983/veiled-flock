//! The three protocol roles: mask counter, prover, verifier.

use flock_core::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    lincheck::QuirkyPoint,
    pcs::{
        self, Commitment, PreblindedOpening, PreblindedOpeningVerification, ProverData,
        commit_zk_with_ro,
        ring_switch::{claim_check, scale_s_hat_v},
    },
    ro::{RoChannel, RoContext},
    zerocheck::{self, PaddingSpec},
    zk::{MaskSampler, ZkRng},
};
use veil_f128::{
    CircuitBuilder, ConstraintCommitment, ConstraintParameters, LinearCombination,
    certify_constraint_soundness, commit_constraint_inputs, prove_constraints_from_commitment,
    verify_constraints,
};

use crate::challenger::{
    BoundedGrindingChallenger, ligerito_grinding_is_bounded, observe_framed, sample_nonzero,
};
use crate::error::VeilError;
use crate::pcs::{
    BitPcs, MAX_BLIND_GRIND_TRIALS, MAX_LIGERITO_GRIND_TRIALS, RING_WIDTH, claim_weights,
    ring_slices, x_full,
};
use crate::proof::ZkProof;

/// Affine expression in the private mask variables.
pub type Expr = LinearCombination;

/// Handle of a committed bit witness: its index in commitment order. Only
/// `read_oracle` constructs one, so a handle always names a commitment the
/// same context has read; `prove` and `verify` bound-check it anyway.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleId(usize);

impl OracleId {
    pub fn index(self) -> usize {
        self.0
    }
}

const STATEMENT_LABEL: &[u8] = b"veil-examples-statement";
const MASK_ROOT_LABEL: &[u8] = b"veil-examples-mask-root";
const ORACLE_LABEL: &[u8] = b"veil-examples-oracle";
const RING_MASK_LABEL: &[u8] = b"veil-examples-ring-masks";
const BLINDED_RING_LABEL: &[u8] = b"veil-examples-blinded-ring";
const PCS_FORK_LABEL: &[u8] = b"veil-examples-pcs-fork";
const VEIL_FORK_LABEL: &[u8] = b"veil-examples-veil-fork";

/// `sum_i weights[i] * exprs[i]`.
pub fn linear_combination(exprs: &[Expr], weights: &[F128]) -> Expr {
    assert_eq!(exprs.len(), weights.len());
    exprs
        .iter()
        .zip(weights)
        .fold(Expr::zero(), |acc, (expr, weight)| {
            acc.add(&expr.scale(*weight))
        })
}

fn unmask(masked: F128, index: usize) -> Expr {
    Expr::constant(masked).add(&Expr::variable(index))
}

// ============================================================================
// Traits
// ============================================================================

pub trait ConstraintCtx {
    fn assert_zero(&mut self, expr: Expr);

    /// `left * right == output`, with `output` an affine expression. No
    /// witness variable is materialized.
    fn assert_mul(&mut self, left: Expr, right: Expr, output: Expr);

    /// Register the claim that the multilinear extension of the committed
    /// bit witness `oracle` evaluates to `value` at `point`. The claim is
    /// discharged by a ring-switched opening with masked slices.
    fn assert_bit_mle_eval(&mut self, oracle: OracleId, point: QuirkyPoint, value: Expr);
}

/// Reads the transcript and samples challenges. Runs on the verifier, on the
/// prover replay, and on the mask counter.
pub trait ReadingCtx: ConstraintCtx {
    fn read_next(&mut self, count: usize) -> Result<Vec<Expr>, VeilError>;

    fn read_one(&mut self) -> Result<Expr, VeilError> {
        let mut values = self.read_next(1)?;
        values.pop().ok_or(VeilError::TranscriptExhausted)
    }

    /// Read the next commitment to a `2^m`-bit witness.
    fn read_oracle(&mut self, m: usize) -> Result<OracleId, VeilError>;

    /// Absorb a public label at this transcript position.
    fn absorb_label(&mut self, label: &[u8]);

    /// Absorb public bytes (a statement digest) at this transcript position.
    fn absorb_bytes(&mut self, bytes: &[u8]);

    fn sample(&mut self) -> F128;

    fn sample_point(&mut self, dimension: usize) -> Vec<F128> {
        (0..dimension).map(|_| self.sample()).collect()
    }

    /// The zerocheck equality point, rejection sampled exactly as the native
    /// prover does.
    fn sample_eq_point(&mut self, m: usize) -> Result<Vec<F128>, VeilError>;
}

/// Prover side. The context is a [`Challenger`]: every field value observed
/// through it is one-time padded, recorded as a sent message, and absorbed
/// in masked form, so the native FLOCK provers run through it unchanged.
pub trait SendingCtx: ConstraintCtx + Challenger {
    fn send_value(&mut self, value: F128) -> Expr;

    fn send_values(&mut self, values: &[F128]) -> Vec<Expr>;

    /// Commit a packed `2^m`-bit witness with the hiding PCS.
    fn commit_bits(&mut self, packed: Vec<F128>) -> Result<OracleId, VeilError>;
}

// ============================================================================
// Shared pieces
// ============================================================================

struct ClaimRecord {
    oracle: OracleId,
    point: QuirkyPoint,
    value: Expr,
}

fn observe_statement<C: Challenger>(
    challenger: &mut C,
    proof_nonce: &[u8; 32],
    veil_linear_nonce: &[u8; 32],
    veil_hadamard_nonce: &[u8; 32],
    mask_root: &[u8; 32],
) {
    challenger.observe_label(STATEMENT_LABEL);
    challenger.observe_bytes(proof_nonce);
    challenger.observe_bytes(veil_linear_nonce);
    challenger.observe_bytes(veil_hadamard_nonce);
    challenger.observe_label(MASK_ROOT_LABEL);
    challenger.observe_bytes(mask_root);
}

fn observe_oracle<C: Challenger>(challenger: &mut C, nonce: &[u8; 32], commitment: &Commitment) {
    challenger.observe_label(ORACLE_LABEL);
    challenger.observe_bytes(nonce);
    challenger.observe_bytes(&commitment.root);
}

/// Apply packed-field scaling by `scalar` to slice expressions, the affine
/// mirror of `scale_s_hat_v`.
fn scale_ring_expressions(expressions: &[Expr], scalar: F128) -> Vec<Expr> {
    assert_eq!(expressions.len(), RING_WIDTH);
    let mut out = vec![Expr::zero(); RING_WIDTH];
    for (input_bit, expression) in expressions.iter().enumerate() {
        let basis = if input_bit < 64 {
            F128::new(1u64 << input_bit, 0)
        } else {
            F128::new(0, 1u64 << (input_bit - 64))
        };
        let product = scalar * basis;
        for (output_bit, slot) in out.iter_mut().enumerate() {
            let present = if output_bit < 64 {
                (product.lo >> output_bit) & 1
            } else {
                (product.hi >> (output_bit - 64)) & 1
            };
            if present == 1 {
                *slot = slot.add(expression);
            }
        }
    }
    out
}

/// Link one claim to its blinded slices: `q_i = w_i + (c * b)_i` for every
/// slice, and `value = <weights, w>`. Returns the public claim value the PCS
/// opens on the blinded vector.
fn link_ring_claim(
    builder: &mut CircuitBuilder,
    claim: &ClaimRecord,
    witness: &[Expr],
    blind: &[Expr],
    blinded: &[F128],
    challenge: F128,
) -> F128 {
    let scaled_blind = scale_ring_expressions(blind, challenge);
    for ((q, w), b) in blinded.iter().zip(witness).zip(&scaled_blind) {
        builder.assert_zero(&Expr::constant(*q).add(w).add(b));
    }
    let weights = claim_weights(&claim.point);
    builder.assert_zero(&claim.value.add(&linear_combination(witness, &weights)));
    claim_check(&weights, blinded)
}

/// Commitment indices that carry at least one claim, ascending.
fn oracles_with_claims(claims: &[ClaimRecord]) -> Vec<usize> {
    let mut ids: Vec<usize> = claims.iter().map(|claim| claim.oracle.0).collect();
    ids.sort_unstable();
    ids.dedup();
    ids
}

/// One terminal transcript branch per opened commitment. Every branch forks
/// after all claims, the blinding challenge, and the blinded slices are
/// bound, so the openings stay independent exactly as in production, where
/// the PCS opening is the terminal step of its fork.
fn pcs_fork(challenger: &FsChallenger, oracle_index: usize) -> FsChallenger {
    let mut fork = challenger.clone();
    fork.observe_label(PCS_FORK_LABEL);
    fork.observe_bytes(&(oracle_index as u64).to_le_bytes());
    fork
}

fn sample_nonce(rng: &mut ZkRng) -> [u8; 32] {
    let mut words = [0u64; 4];
    rng.fill_u64s(&mut words);
    let mut nonce = [0u8; 32];
    for (chunk, word) in nonce.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    nonce
}

// ============================================================================
// Mask counter
// ============================================================================

/// Dry-run context: counts transcript reads and ring-slice masks so the
/// prover knows how many masks to commit before any challenge.
pub struct MaskCounter {
    count: usize,
    oracles: usize,
    m: Option<usize>,
    challenger: FsChallenger,
}

impl MaskCounter {
    pub fn new(pcs: Option<&BitPcs>) -> Self {
        Self {
            count: 0,
            oracles: 0,
            m: pcs.map(BitPcs::m),
            challenger: FsChallenger::new(b"veil-examples-mask-counter"),
        }
    }

    pub fn count(&self) -> usize {
        self.count
    }
}

/// Run the unified verify body on a counting context and return the number
/// of masks the prover must commit.
pub fn compute_mask_length(
    pcs: Option<&BitPcs>,
    verify: impl FnOnce(&mut MaskCounter) -> Result<(), VeilError>,
) -> Result<usize, VeilError> {
    let mut counter = MaskCounter::new(pcs);
    verify(&mut counter)?;
    Ok(counter.count())
}

impl ConstraintCtx for MaskCounter {
    fn assert_zero(&mut self, _expr: Expr) {}

    fn assert_mul(&mut self, _left: Expr, _right: Expr, _output: Expr) {}

    fn assert_bit_mle_eval(&mut self, _oracle: OracleId, _point: QuirkyPoint, _value: Expr) {
        self.count += 2 * RING_WIDTH;
    }
}

impl ReadingCtx for MaskCounter {
    fn read_next(&mut self, count: usize) -> Result<Vec<Expr>, VeilError> {
        let start = self.count;
        self.count += count;
        Ok((start..self.count).map(Expr::variable).collect())
    }

    fn read_oracle(&mut self, m: usize) -> Result<OracleId, VeilError> {
        let expected = self.m.ok_or(VeilError::ClaimWithoutOracle)?;
        if expected != m {
            return Err(VeilError::OracleShape {
                expected,
                actual: m,
            });
        }
        let id = OracleId(self.oracles);
        self.oracles += 1;
        Ok(id)
    }

    fn absorb_label(&mut self, _label: &[u8]) {}

    fn absorb_bytes(&mut self, _bytes: &[u8]) {}

    fn sample(&mut self) -> F128 {
        self.challenger.sample_f128()
    }

    fn sample_eq_point(&mut self, m: usize) -> Result<Vec<F128>, VeilError> {
        Ok(zerocheck::sample_eq_point(m, &mut self.challenger))
    }
}

// ============================================================================
// Prover
// ============================================================================

struct CommittedBits {
    packed: Vec<F128>,
    nonce: [u8; 32],
    ro: RoContext,
    commitment: Commitment,
    prover_data: ProverData,
}

/// Replays recorded challenges for the prover's verify pass. Observations
/// are ignored, so the real Fiat--Shamir state stays untouched.
struct ReplayChallenger<'a> {
    challenges: &'a [F128],
    cursor: &'a mut usize,
}

impl Challenger for ReplayChallenger<'_> {
    fn observe_f128(&mut self, _value: F128) {}

    fn sample_f128(&mut self) -> F128 {
        let value = self
            .challenges
            .get(*self.cursor)
            .copied()
            .expect("the verify replay asked for more challenges than the prove pass produced");
        *self.cursor += 1;
        value
    }
}

/// Prover context. The prove pass populates the transcript through the
/// [`Challenger`] impl; the [`ReadingCtx`] pass replays it without touching
/// the challenger so the same verify body emits the constraints;
/// [`Self::prove`] discharges them.
pub struct ZkProverCtx {
    challenger: FsChallenger,
    pcs: Option<BitPcs>,
    masks: Vec<F128>,
    sent: Vec<F128>,
    challenges: Vec<F128>,
    oracles: Vec<CommittedBits>,
    claims: Vec<ClaimRecord>,
    builder: CircuitBuilder,
    veil_commitment: ConstraintCommitment,
    veil_rng: ZkRng,
    witness_rng: ZkRng,
    nonce_rng: ZkRng,
    proof_nonce: [u8; 32],
    veil_linear_nonce: [u8; 32],
    veil_hadamard_nonce: [u8; 32],
    veil_hadamard_ro: RoContext,
    read_cursor: usize,
    challenge_cursor: usize,
    oracle_cursor: usize,
}

impl ZkProverCtx {
    /// Production entry: every coin comes from the OS random source.
    pub fn initialize(
        domain: &[u8],
        mask_length: usize,
        pcs: Option<BitPcs>,
    ) -> Result<Self, VeilError> {
        Self::initialize_with_rng(domain, mask_length, pcs, ZkRng::from_entropy())
    }

    /// Deterministic variant for tests and reproducible audits only. A proof
    /// made from a caller-chosen seed is not hiding against that caller.
    #[doc(hidden)]
    pub fn initialize_with_rng(
        domain: &[u8],
        mask_length: usize,
        pcs: Option<BitPcs>,
        mut rng: ZkRng,
    ) -> Result<Self, VeilError> {
        if mask_length == 0 {
            return Err(VeilError::MaskCountMismatch {
                expected: 1,
                actual: 0,
            });
        }
        let mut challenger = FsChallenger::new(domain);
        let mut masks = vec![F128::ZERO; mask_length];
        rng.fork(b"veil-examples-transcript-masks")
            .fill_f128(&mut masks);

        let mut nonce_rng = rng.fork(b"veil-examples-public-nonces");
        let proof_nonce = sample_nonce(&mut nonce_rng);
        let veil_linear_nonce = sample_nonce(&mut nonce_rng);
        let veil_hadamard_nonce = sample_nonce(&mut nonce_rng);
        let veil_linear_ro = challenger.ro_context(veil_linear_nonce);
        let veil_hadamard_ro = challenger.ro_context(veil_hadamard_nonce);

        let mut veil_rng = rng.fork(b"veil-examples-inner-proof");
        let placeholder = CircuitBuilder::new(mask_length).finish();
        let veil_commitment = commit_constraint_inputs(
            &placeholder,
            &masks,
            ConstraintParameters::succinct_flock_secure(),
            &mut veil_rng,
            &veil_linear_ro,
        )?;
        observe_statement(
            &mut challenger,
            &proof_nonce,
            &veil_linear_nonce,
            &veil_hadamard_nonce,
            &veil_commitment.root(),
        );

        Ok(Self {
            challenger,
            pcs,
            masks,
            sent: Vec::with_capacity(mask_length),
            challenges: Vec::new(),
            oracles: Vec::new(),
            claims: Vec::new(),
            builder: CircuitBuilder::new(mask_length),
            veil_commitment,
            veil_rng,
            witness_rng: rng.fork(b"veil-examples-witness-pcs"),
            nonce_rng,
            proof_nonce,
            veil_linear_nonce,
            veil_hadamard_nonce,
            veil_hadamard_ro,
            read_cursor: 0,
            challenge_cursor: 0,
            oracle_cursor: 0,
        })
    }

    pub fn mask_length(&self) -> usize {
        self.masks.len()
    }

    /// Mask the next values with the committed masks, absorb them, and
    /// record them as sent. Returns the masked values.
    fn mask_and_send(&mut self, values: &[F128]) -> Vec<F128> {
        let start = self.sent.len();
        assert!(
            start + values.len() <= self.masks.len(),
            "the prover sends more values than the mask counter reported ({} masks)",
            self.masks.len()
        );
        let masked: Vec<F128> = values
            .iter()
            .zip(&self.masks[start..])
            .map(|(value, mask)| *value + *mask)
            .collect();
        observe_framed(&mut self.challenger, &masked);
        self.sent.extend_from_slice(&masked);
        masked
    }

    /// Discharge the constraints: mask and blind every ring claim, open the
    /// commitments, prove the shifted circuit, and assemble the proof.
    pub fn prove(mut self) -> Result<ZkProof, VeilError> {
        if self.read_cursor != self.sent.len() {
            return Err(VeilError::TranscriptNotConsumed);
        }
        if self.challenge_cursor != self.challenges.len() {
            return Err(VeilError::ChallengeReplayExhausted);
        }
        if self.oracle_cursor != self.oracles.len() {
            return Err(VeilError::OracleNotConsumed);
        }
        let expected_masks = self.sent.len() + 2 * RING_WIDTH * self.claims.len();
        if expected_masks != self.masks.len() {
            return Err(VeilError::MaskCountMismatch {
                expected: self.masks.len(),
                actual: expected_masks,
            });
        }
        if self
            .claims
            .iter()
            .any(|claim| claim.oracle.0 >= self.oracles.len())
        {
            return Err(VeilError::OracleExhausted);
        }

        let mut blind_grind_nonce = 0u64;
        let mut blinded_slices = Vec::with_capacity(self.claims.len());
        let mut pcs_values = Vec::with_capacity(self.claims.len());
        let mut challenge = None;
        if !self.claims.is_empty() {
            let pcs = self.pcs.as_ref().ok_or(VeilError::ClaimWithoutOracle)?;
            let bits = pcs.blind_grinding_bits()?;
            let mut witness_slices = Vec::with_capacity(self.claims.len());
            let mut blind_slices = Vec::with_capacity(self.claims.len());
            let mut witness_exprs = Vec::with_capacity(self.claims.len());
            let mut blind_exprs = Vec::with_capacity(self.claims.len());
            self.challenger.observe_label(RING_MASK_LABEL);
            for index in 0..self.claims.len() {
                let (oracle, point) = {
                    let claim = &self.claims[index];
                    (claim.oracle.0, claim.point.clone())
                };
                let (witness, blind) = {
                    let committed = &self.oracles[oracle];
                    let g_top = &committed.prover_data.zk_blind[committed.packed.len()..];
                    (
                        ring_slices(&committed.packed, &point),
                        ring_slices(g_top, &point),
                    )
                };
                let start = self.sent.len();
                let masked_witness = self.mask_and_send(&witness);
                let masked_blind = self.mask_and_send(&blind);
                witness_exprs.push(
                    masked_witness
                        .iter()
                        .enumerate()
                        .map(|(i, value)| unmask(*value, start + i))
                        .collect::<Vec<_>>(),
                );
                blind_exprs.push(
                    masked_blind
                        .iter()
                        .enumerate()
                        .map(|(i, value)| unmask(*value, start + RING_WIDTH + i))
                        .collect::<Vec<_>>(),
                );
                witness_slices.push(witness);
                blind_slices.push(blind);
            }
            blind_grind_nonce = self.challenger.grind_pow(bits);
            if blind_grind_nonce >= MAX_BLIND_GRIND_TRIALS {
                return Err(VeilError::GrindingLimitExceeded);
            }
            let c = sample_nonzero(&mut self.challenger)
                .ok_or(VeilError::ChallengeSamplingLimitExceeded)?;
            self.challenger.observe_label(BLINDED_RING_LABEL);
            for (witness, blind) in witness_slices.iter().zip(&blind_slices) {
                let blinded: Vec<F128> = witness
                    .iter()
                    .zip(scale_s_hat_v(blind, c))
                    .map(|(w, b)| *w + b)
                    .collect();
                self.challenger.observe_f128_slice(&blinded);
                blinded_slices.push(blinded);
            }
            for (index, claim) in self.claims.iter().enumerate() {
                pcs_values.push(link_ring_claim(
                    &mut self.builder,
                    claim,
                    &witness_exprs[index],
                    &blind_exprs[index],
                    &blinded_slices[index],
                    c,
                ));
            }
            challenge = Some(c);
        }

        let circuit = self.builder.finish();
        let veil_parameters = ConstraintParameters::succinct_flock_secure();
        certify_constraint_soundness(&circuit, veil_parameters)?;

        let mut veil_challenger = self.challenger.clone();
        veil_challenger.observe_label(VEIL_FORK_LABEL);

        let mut pcs_openings = Vec::new();
        if let Some(c) = challenge {
            let pcs = self.pcs.as_ref().ok_or(VeilError::ClaimWithoutOracle)?;
            let padding = PaddingSpec::dense(pcs.m());
            for oracle_index in oracles_with_claims(&self.claims) {
                let mut pcs_challenger = pcs_fork(&self.challenger, oracle_index);
                let mut bounded =
                    BoundedGrindingChallenger::new(&mut pcs_challenger, MAX_LIGERITO_GRIND_TRIALS);
                let committed = &self.oracles[oracle_index];
                let g_top = &committed.prover_data.zk_blind[committed.packed.len()..];
                let q_packed: Vec<F128> = committed
                    .packed
                    .iter()
                    .zip(g_top)
                    .map(|(z, g)| *z + c * *g)
                    .collect();
                let x_fulls: Vec<Vec<F128>> = self
                    .claims
                    .iter()
                    .filter(|claim| claim.oracle.0 == oracle_index)
                    .map(|claim| x_full(&claim.point))
                    .collect();
                let x_refs: Vec<&[F128]> = x_fulls.iter().map(Vec::as_slice).collect();
                let precomputed: Vec<Option<&[F128]>> = self
                    .claims
                    .iter()
                    .zip(&blinded_slices)
                    .filter(|(claim, _)| claim.oracle.0 == oracle_index)
                    .map(|(_, slice)| Some(slice.as_slice()))
                    .collect();
                let opening = pcs::open_batch_mixed_ligerito_preblinded_ro(
                    PreblindedOpening {
                        q_packed,
                        prover_data: &committed.prover_data,
                        commitment: &committed.commitment,
                        challenge: c,
                        x_outers: &x_refs,
                        precomputed_s_hat_v: &precomputed,
                        packed_direct: &[],
                        padding: &padding,
                        lig_config: pcs.prover_config(),
                        ro: &committed.ro,
                        channel: RoChannel::Witness,
                    },
                    &mut bounded,
                );
                if bounded.exhausted || !ligerito_grinding_is_bounded(&opening.ligerito) {
                    return Err(VeilError::GrindingLimitExceeded);
                }
                pcs_openings.push(opening);
            }
        }
        drop(pcs_values);

        let veil = prove_constraints_from_commitment(
            &circuit,
            self.veil_commitment,
            &mut self.veil_rng,
            &mut veil_challenger,
            &self.veil_hadamard_ro,
        )?;

        Ok(ZkProof {
            proof_nonce: self.proof_nonce,
            veil_linear_nonce: self.veil_linear_nonce,
            veil_hadamard_nonce: self.veil_hadamard_nonce,
            oracle_nonces: self.oracles.iter().map(|oracle| oracle.nonce).collect(),
            masked_transcript: self.sent,
            commitments: self
                .oracles
                .iter()
                .map(|oracle| oracle.commitment.clone())
                .collect(),
            blind_grind_nonce,
            blinded_slices,
            pcs_openings,
            veil,
        })
    }
}

impl Challenger for ZkProverCtx {
    fn ro_context(&self, nonce: [u8; 32]) -> RoContext {
        self.challenger.ro_context(nonce)
    }

    fn observe_label(&mut self, label: &[u8]) {
        self.challenger.observe_label(label);
    }

    fn observe_f128(&mut self, value: F128) {
        self.mask_and_send(&[value]);
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.mask_and_send(values);
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.challenger.observe_bytes(bytes);
    }

    fn sample_f128(&mut self) -> F128 {
        let challenge = self.challenger.sample_f128();
        self.challenges.push(challenge);
        challenge
    }

    /// Vector squeezes are one transcript operation on `FsChallenger`, not
    /// `n` scalar squeezes, so they must reach the inner challenger intact.
    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        let challenges = self.challenger.sample_f128_vec(n);
        self.challenges.extend_from_slice(&challenges);
        challenges
    }

    fn grind_pow(&mut self, _bits: u32) -> u64 {
        panic!("the PIOP layer must not grind through the masking context")
    }

    fn verify_pow(&mut self, _nonce: u64, _bits: u32) -> bool {
        panic!("the PIOP layer must not grind through the masking context")
    }
}

impl ConstraintCtx for ZkProverCtx {
    fn assert_zero(&mut self, expr: Expr) {
        self.builder.assert_zero(&expr);
    }

    fn assert_mul(&mut self, left: Expr, right: Expr, output: Expr) {
        self.builder.assert_mul(&left, &right, &output);
    }

    fn assert_bit_mle_eval(&mut self, oracle: OracleId, point: QuirkyPoint, value: Expr) {
        self.claims.push(ClaimRecord {
            oracle,
            point,
            value,
        });
    }
}

impl SendingCtx for ZkProverCtx {
    fn send_value(&mut self, value: F128) -> Expr {
        let mut exprs = self.send_values(&[value]);
        exprs.pop().expect("one expression per sent value")
    }

    fn send_values(&mut self, values: &[F128]) -> Vec<Expr> {
        let start = self.sent.len();
        let masked = self.mask_and_send(values);
        masked
            .into_iter()
            .enumerate()
            .map(|(offset, value)| unmask(value, start + offset))
            .collect()
    }

    fn commit_bits(&mut self, packed: Vec<F128>) -> Result<OracleId, VeilError> {
        let pcs = self.pcs.as_ref().ok_or(VeilError::ClaimWithoutOracle)?;
        if packed.len() != pcs.packed_len() {
            return Err(VeilError::WitnessLength {
                expected: pcs.packed_len(),
                actual: packed.len(),
            });
        }
        let nonce = sample_nonce(&mut self.nonce_rng);
        let ro = self.challenger.ro_context(nonce);
        let (commitment, prover_data) = commit_zk_with_ro(
            &packed,
            pcs.params(),
            &mut self.witness_rng,
            &ro,
            RoChannel::Witness,
        );
        observe_oracle(&mut self.challenger, &nonce, &commitment);
        let id = OracleId(self.oracles.len());
        self.oracles.push(CommittedBits {
            packed,
            nonce,
            ro,
            commitment,
            prover_data,
        });
        Ok(id)
    }
}

/// Replay of the prove pass: expressions come from the recorded masked
/// values, challenges from the recorded samples. The challenger is untouched.
impl ReadingCtx for ZkProverCtx {
    fn read_next(&mut self, count: usize) -> Result<Vec<Expr>, VeilError> {
        let start = self.read_cursor;
        let end = start + count;
        if end > self.sent.len() {
            return Err(VeilError::TranscriptExhausted);
        }
        self.read_cursor = end;
        Ok((start..end)
            .map(|index| unmask(self.sent[index], index))
            .collect())
    }

    fn read_oracle(&mut self, m: usize) -> Result<OracleId, VeilError> {
        let pcs = self.pcs.as_ref().ok_or(VeilError::ClaimWithoutOracle)?;
        if pcs.m() != m {
            return Err(VeilError::OracleShape {
                expected: pcs.m(),
                actual: m,
            });
        }
        if self.oracle_cursor >= self.oracles.len() {
            return Err(VeilError::OracleExhausted);
        }
        let id = OracleId(self.oracle_cursor);
        self.oracle_cursor += 1;
        Ok(id)
    }

    fn absorb_label(&mut self, _label: &[u8]) {}

    fn absorb_bytes(&mut self, _bytes: &[u8]) {}

    fn sample(&mut self) -> F128 {
        let mut replay = ReplayChallenger {
            challenges: &self.challenges,
            cursor: &mut self.challenge_cursor,
        };
        replay.sample_f128()
    }

    fn sample_eq_point(&mut self, m: usize) -> Result<Vec<F128>, VeilError> {
        let mut replay = ReplayChallenger {
            challenges: &self.challenges,
            cursor: &mut self.challenge_cursor,
        };
        Ok(zerocheck::sample_eq_point(m, &mut replay))
    }
}

// ============================================================================
// Verifier
// ============================================================================

/// Verifier context: reads the masked transcript, rebuilds the shifted
/// circuit, and checks the PCS openings and the VEIL proof in [`Self::verify`].
pub struct ZkVerifierCtx {
    challenger: FsChallenger,
    proof: ZkProof,
    pcs: Option<BitPcs>,
    claims: Vec<ClaimRecord>,
    builder: CircuitBuilder,
    read_cursor: usize,
    oracle_cursor: usize,
}

impl ZkVerifierCtx {
    pub fn init(domain: &[u8], proof: ZkProof, pcs: Option<BitPcs>) -> Result<Self, VeilError> {
        let mask_length = proof.masked_transcript.len();
        if mask_length == 0 {
            return Err(VeilError::ProofShape("empty masked transcript"));
        }
        if proof.commitments.len() != proof.oracle_nonces.len() {
            return Err(VeilError::ProofShape("oracle nonce count"));
        }
        match &pcs {
            Some(pcs) => {
                if proof
                    .commitments
                    .iter()
                    .any(|commitment| commitment.params != *pcs.params())
                {
                    return Err(VeilError::PcsParamsMismatch);
                }
            }
            None => {
                if !proof.commitments.is_empty() || !proof.pcs_openings.is_empty() {
                    return Err(VeilError::ClaimWithoutOracle);
                }
            }
        }
        if proof.pcs_openings.len() > proof.commitments.len() {
            return Err(VeilError::ProofShape("opening count"));
        }
        if proof
            .blinded_slices
            .iter()
            .any(|slice| slice.len() != RING_WIDTH)
        {
            return Err(VeilError::ProofShape("ring slice width"));
        }
        if proof.blind_grind_nonce >= MAX_BLIND_GRIND_TRIALS {
            return Err(VeilError::InvalidGrindNonce);
        }
        if proof.veil.parameters != ConstraintParameters::succinct_flock_secure() {
            return Err(VeilError::ProofShape("VEIL parameters"));
        }
        let mut challenger = FsChallenger::new(domain);
        observe_statement(
            &mut challenger,
            &proof.proof_nonce,
            &proof.veil_linear_nonce,
            &proof.veil_hadamard_nonce,
            &proof.veil.linear.commitment,
        );
        Ok(Self {
            challenger,
            proof,
            pcs,
            claims: Vec::new(),
            builder: CircuitBuilder::new(mask_length),
            read_cursor: 0,
            oracle_cursor: 0,
        })
    }

    fn read_masked(&mut self, count: usize) -> Result<(usize, Vec<F128>), VeilError> {
        let start = self.read_cursor;
        let end = start + count;
        if end > self.proof.masked_transcript.len() {
            return Err(VeilError::TranscriptExhausted);
        }
        self.read_cursor = end;
        let masked = self.proof.masked_transcript[start..end].to_vec();
        observe_framed(&mut self.challenger, &masked);
        Ok((start, masked))
    }

    pub fn verify(mut self) -> Result<(), VeilError> {
        if self.oracle_cursor != self.proof.commitments.len() {
            return Err(VeilError::OracleNotConsumed);
        }
        let expected_len = self.read_cursor + 2 * RING_WIDTH * self.claims.len();
        if self.proof.masked_transcript.len() != expected_len {
            return Err(VeilError::TranscriptNotConsumed);
        }
        if self
            .claims
            .iter()
            .any(|claim| claim.oracle.0 >= self.proof.commitments.len())
        {
            return Err(VeilError::OracleExhausted);
        }
        if self.proof.blinded_slices.len() != self.claims.len()
            || self.proof.pcs_openings.len() != oracles_with_claims(&self.claims).len()
        {
            return Err(VeilError::ProofShape("ring claim count"));
        }

        let mut challenge = None;
        let mut pcs_values = Vec::with_capacity(self.claims.len());
        if self.claims.is_empty() {
            if self.proof.blind_grind_nonce != 0 {
                return Err(VeilError::ProofShape("grind nonce without claims"));
            }
        } else {
            let pcs = self.pcs.as_ref().ok_or(VeilError::ClaimWithoutOracle)?;
            let bits = pcs.blind_grinding_bits()?;
            for claim in &self.claims {
                pcs.check_point(&claim.point)?;
            }
            self.challenger.observe_label(RING_MASK_LABEL);
            let mut witness_exprs = Vec::with_capacity(self.claims.len());
            let mut blind_exprs = Vec::with_capacity(self.claims.len());
            for _ in 0..self.claims.len() {
                let (start, witness) = self.read_masked(RING_WIDTH)?;
                let (blind_start, blind) = self.read_masked(RING_WIDTH)?;
                witness_exprs.push(
                    witness
                        .iter()
                        .enumerate()
                        .map(|(i, value)| unmask(*value, start + i))
                        .collect::<Vec<_>>(),
                );
                blind_exprs.push(
                    blind
                        .iter()
                        .enumerate()
                        .map(|(i, value)| unmask(*value, blind_start + i))
                        .collect::<Vec<_>>(),
                );
            }
            if !self
                .challenger
                .verify_pow(self.proof.blind_grind_nonce, bits)
            {
                return Err(VeilError::InvalidGrindNonce);
            }
            let c = sample_nonzero(&mut self.challenger)
                .ok_or(VeilError::ChallengeSamplingLimitExceeded)?;
            self.challenger.observe_label(BLINDED_RING_LABEL);
            for slice in &self.proof.blinded_slices {
                self.challenger.observe_f128_slice(slice);
            }
            for (index, claim) in self.claims.iter().enumerate() {
                pcs_values.push(link_ring_claim(
                    &mut self.builder,
                    claim,
                    &witness_exprs[index],
                    &blind_exprs[index],
                    &self.proof.blinded_slices[index],
                    c,
                ));
            }
            challenge = Some(c);
        }

        let circuit = self.builder.finish();
        let proof = &self.proof;
        certify_constraint_soundness(&circuit, proof.veil.parameters)?;

        let mut veil_challenger = self.challenger.clone();
        veil_challenger.observe_label(VEIL_FORK_LABEL);

        if let Some(c) = challenge {
            let pcs = self.pcs.as_ref().ok_or(VeilError::ClaimWithoutOracle)?;
            for (opening, oracle_index) in proof
                .pcs_openings
                .iter()
                .zip(oracles_with_claims(&self.claims))
            {
                if !ligerito_grinding_is_bounded(&opening.ligerito) {
                    return Err(VeilError::GrindingLimitExceeded);
                }
                let commitment = &proof.commitments[oracle_index];
                let selected: Vec<usize> = (0..self.claims.len())
                    .filter(|&index| self.claims[index].oracle.0 == oracle_index)
                    .collect();
                if opening.ring_switches.len() != selected.len()
                    || selected
                        .iter()
                        .zip(&opening.ring_switches)
                        .any(|(&index, ring)| ring.s_hat_v != proof.blinded_slices[index])
                {
                    return Err(VeilError::ProofShape("opened ring slices"));
                }
                let values: Vec<F128> = selected.iter().map(|&i| pcs_values[i]).collect();
                let z_skips: Vec<F128> = selected
                    .iter()
                    .map(|&i| self.claims[i].point.z_skip)
                    .collect();
                let x_fulls: Vec<Vec<F128>> = selected
                    .iter()
                    .map(|&i| x_full(&self.claims[i].point))
                    .collect();
                let x_refs: Vec<&[F128]> = x_fulls.iter().map(Vec::as_slice).collect();
                let ro = self
                    .challenger
                    .ro_context(proof.oracle_nonces[oracle_index]);
                let mut pcs_challenger = pcs_fork(&self.challenger, oracle_index);
                pcs::verify_opening_batch_ligerito_mixed_preblinded_ro(
                    PreblindedOpeningVerification {
                        commitment,
                        claims: &values,
                        z_skips: &z_skips,
                        x_outers: &x_refs,
                        packed_direct: &[],
                        proof: opening,
                        lig_config: pcs.verifier_config(),
                        challenge: c,
                        ro: &ro,
                        channel: RoChannel::Witness,
                    },
                    &mut pcs_challenger,
                )?;
            }
        }

        let veil_linear_ro = self.challenger.ro_context(proof.veil_linear_nonce);
        let veil_hadamard_ro = self.challenger.ro_context(proof.veil_hadamard_nonce);
        verify_constraints(
            &circuit,
            &proof.veil,
            &mut veil_challenger,
            &veil_linear_ro,
            &veil_hadamard_ro,
        )?;
        Ok(())
    }
}

impl ConstraintCtx for ZkVerifierCtx {
    fn assert_zero(&mut self, expr: Expr) {
        self.builder.assert_zero(&expr);
    }

    fn assert_mul(&mut self, left: Expr, right: Expr, output: Expr) {
        self.builder.assert_mul(&left, &right, &output);
    }

    fn assert_bit_mle_eval(&mut self, oracle: OracleId, point: QuirkyPoint, value: Expr) {
        self.claims.push(ClaimRecord {
            oracle,
            point,
            value,
        });
    }
}

impl ReadingCtx for ZkVerifierCtx {
    fn read_next(&mut self, count: usize) -> Result<Vec<Expr>, VeilError> {
        let (start, masked) = self.read_masked(count)?;
        Ok(masked
            .iter()
            .enumerate()
            .map(|(offset, value)| unmask(*value, start + offset))
            .collect())
    }

    fn read_oracle(&mut self, m: usize) -> Result<OracleId, VeilError> {
        let pcs = self.pcs.as_ref().ok_or(VeilError::ClaimWithoutOracle)?;
        if pcs.m() != m {
            return Err(VeilError::OracleShape {
                expected: pcs.m(),
                actual: m,
            });
        }
        let index = self.oracle_cursor;
        let commitment = self
            .proof
            .commitments
            .get(index)
            .ok_or(VeilError::OracleExhausted)?;
        if commitment.params != *pcs.params() {
            return Err(VeilError::PcsParamsMismatch);
        }
        observe_oracle(
            &mut self.challenger,
            &self.proof.oracle_nonces[index],
            commitment,
        );
        self.oracle_cursor += 1;
        Ok(OracleId(index))
    }

    fn absorb_label(&mut self, label: &[u8]) {
        self.challenger.observe_label(label);
    }

    fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.challenger.observe_bytes(bytes);
    }

    fn sample(&mut self) -> F128 {
        self.challenger.sample_f128()
    }

    fn sample_eq_point(&mut self, m: usize) -> Result<Vec<F128>, VeilError> {
        Ok(zerocheck::sample_eq_point(m, &mut self.challenger))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flock::sample_quirky_point;
    use crate::pcs::bit_mle_eval;

    const M: usize = 22;
    const K_LOG: usize = 6;
    const DOMAIN: &[u8] = b"veil-examples-ctx-test";

    fn packed_bits(rng: &mut ZkRng, pcs: &BitPcs) -> Vec<F128> {
        let mut packed = vec![F128::ZERO; pcs.packed_len()];
        rng.fill_f128(&mut packed);
        packed
    }

    /// Three committed witnesses; `a` and `b` claimed at one point, `c` at
    /// another. Exercises the three-oracle opening order and the per-oracle
    /// forks.
    fn body<C: ReadingCtx>(ctx: &mut C) -> Result<(), VeilError> {
        let a = ctx.read_oracle(M)?;
        let b = ctx.read_oracle(M)?;
        let c = ctx.read_oracle(M)?;
        let shared = sample_quirky_point(ctx, M, K_LOG)?;
        let other = sample_quirky_point(ctx, M, K_LOG)?;
        let evals = ctx.read_next(3)?;
        ctx.assert_bit_mle_eval(a, shared.clone(), evals[0].clone());
        ctx.assert_bit_mle_eval(b, shared, evals[1].clone());
        ctx.assert_bit_mle_eval(c, other, evals[2].clone());
        Ok(())
    }

    fn quirky_point_sending(ctx: &mut ZkProverCtx) -> QuirkyPoint {
        let z_skip = ctx.sample_f128();
        let x_outer = (0..M - K_LOG).map(|_| ctx.sample_f128()).collect();
        QuirkyPoint {
            z_skip,
            x_inner_rest: Vec::new(),
            x_outer,
        }
    }

    fn prove(seed: u8) -> (BitPcs, ZkProof) {
        let pcs = BitPcs::new(M).unwrap();
        let mut rng = ZkRng::from_seed([seed; 32]);
        let mut data_rng = rng.fork(b"data");
        let tables: Vec<Vec<F128>> = (0..3).map(|_| packed_bits(&mut data_rng, &pcs)).collect();
        let mask_length = compute_mask_length(Some(&pcs), body).unwrap();
        assert_eq!(mask_length, 3 + 3 * 2 * RING_WIDTH);
        let mut pctx =
            ZkProverCtx::initialize_with_rng(DOMAIN, mask_length, Some(pcs.clone()), rng).unwrap();
        for table in &tables {
            pctx.commit_bits(table.clone()).unwrap();
        }
        let shared = quirky_point_sending(&mut pctx);
        let other = quirky_point_sending(&mut pctx);
        pctx.send_values(&[
            bit_mle_eval(&tables[0], &shared),
            bit_mle_eval(&tables[1], &shared),
            bit_mle_eval(&tables[2], &other),
        ]);
        body(&mut pctx).unwrap();
        (pcs, pctx.prove().unwrap())
    }

    fn verify(pcs: &BitPcs, proof: ZkProof) -> Result<(), VeilError> {
        let mut vctx = ZkVerifierCtx::init(DOMAIN, proof, Some(pcs.clone()))?;
        body(&mut vctx)?;
        vctx.verify()
    }

    #[test]
    fn three_oracle_roundtrip() {
        let (pcs, proof) = prove(1);
        assert_eq!(proof.commitments.len(), 3);
        assert_eq!(proof.pcs_openings.len(), 3);
        assert_eq!(proof.blinded_slices.len(), 3);
        verify(&pcs, proof).unwrap();
    }

    #[test]
    fn shape_guards_return_exact_errors() {
        let (pcs, proof) = prove(2);

        let mut nonce = proof.clone();
        nonce.blind_grind_nonce += 1;
        assert_eq!(
            verify(&pcs, nonce).unwrap_err(),
            VeilError::InvalidGrindNonce
        );

        let mut huge_nonce = proof.clone();
        huge_nonce.blind_grind_nonce = MAX_BLIND_GRIND_TRIALS;
        assert_eq!(
            verify(&pcs, huge_nonce).unwrap_err(),
            VeilError::InvalidGrindNonce
        );

        let mut short = proof.clone();
        short.masked_transcript.truncate(2);
        assert_eq!(
            verify(&pcs, short).unwrap_err(),
            VeilError::TranscriptExhausted
        );

        let mut partial = proof.clone();
        partial.masked_transcript.truncate(3 + RING_WIDTH);
        assert_eq!(
            verify(&pcs, partial).unwrap_err(),
            VeilError::TranscriptNotConsumed
        );

        let mut extra_slice = proof.clone();
        extra_slice
            .blinded_slices
            .push(vec![F128::ZERO; RING_WIDTH]);
        assert_eq!(
            verify(&pcs, extra_slice).unwrap_err(),
            VeilError::ProofShape("ring claim count")
        );

        let mut narrow_slice = proof.clone();
        narrow_slice.blinded_slices[0].pop();
        assert_eq!(
            verify(&pcs, narrow_slice).unwrap_err(),
            VeilError::ProofShape("ring slice width")
        );

        let mut parameters = proof.clone();
        parameters.veil.parameters.inverse_rate = 4;
        assert_eq!(
            verify(&pcs, parameters).unwrap_err(),
            VeilError::ProofShape("VEIL parameters")
        );

        let mut swapped = proof.clone();
        swapped.pcs_openings.swap(0, 2);
        assert_eq!(
            verify(&pcs, swapped).unwrap_err(),
            VeilError::ProofShape("opened ring slices")
        );

        let mut ring = proof.clone();
        ring.pcs_openings[1].ring_switches[0].s_hat_v[5] += F128::ONE;
        assert_eq!(
            verify(&pcs, ring).unwrap_err(),
            VeilError::ProofShape("opened ring slices")
        );

        let mut fewer_openings = proof.clone();
        fewer_openings.pcs_openings.pop();
        assert_eq!(
            verify(&pcs, fewer_openings).unwrap_err(),
            VeilError::ProofShape("ring claim count")
        );

        let mut grind = proof.clone();
        grind.pcs_openings[0].ligerito.fold_grinding_nonces[0] = MAX_LIGERITO_GRIND_TRIALS;
        assert_eq!(
            verify(&pcs, grind).unwrap_err(),
            VeilError::GrindingLimitExceeded
        );

        let mut params = proof.clone();
        params.commitments[1].params.zk = false;
        assert_eq!(
            verify(&pcs, params).unwrap_err(),
            VeilError::PcsParamsMismatch
        );

        let mut no_oracle = proof.clone();
        no_oracle.commitments.clear();
        no_oracle.oracle_nonces.clear();
        no_oracle.pcs_openings.clear();
        assert_eq!(
            verify(&pcs, no_oracle).unwrap_err(),
            VeilError::OracleExhausted
        );

        let mut nonces = proof;
        nonces.oracle_nonces.pop();
        assert_eq!(
            verify(&pcs, nonces).unwrap_err(),
            VeilError::ProofShape("oracle nonce count")
        );
    }

    #[test]
    fn value_mutations_are_rejected_by_the_constraints() {
        let (pcs, proof) = prove(3);

        // A mutated masked message changes every later challenge. The
        // two-bit blind grind rejects the stale nonce with probability 3/4;
        // otherwise the PCS opening rejects the changed challenge `c`.
        let rejected =
            |error: VeilError| matches!(error, VeilError::InvalidGrindNonce | VeilError::Pcs(_));
        let mut eval = proof.clone();
        eval.masked_transcript[1] += F128::ONE;
        assert!(rejected(verify(&pcs, eval).unwrap_err()));

        let mut mask = proof.clone();
        mask.masked_transcript[3 + 7] += F128::ONE;
        assert!(rejected(verify(&pcs, mask).unwrap_err()));

        let mut blinded = proof;
        blinded.blinded_slices[2][9] += F128::ONE;
        assert!(verify(&pcs, blinded).is_err());
    }

    #[test]
    fn out_of_range_oracle_handle_is_an_error() {
        let (pcs, proof) = prove(4);
        let mut vctx = ZkVerifierCtx::init(DOMAIN, proof, Some(pcs)).unwrap();
        let a = vctx.read_oracle(M).unwrap();
        vctx.read_oracle(M).unwrap();
        vctx.read_oracle(M).unwrap();
        let shared = sample_quirky_point(&mut vctx, M, K_LOG).unwrap();
        let other = sample_quirky_point(&mut vctx, M, K_LOG).unwrap();
        let evals = vctx.read_next(3).unwrap();
        vctx.assert_bit_mle_eval(a, shared.clone(), evals[0].clone());
        vctx.assert_bit_mle_eval(OracleId(7), shared, evals[1].clone());
        vctx.assert_bit_mle_eval(a, other, evals[2].clone());
        assert_eq!(vctx.verify().unwrap_err(), VeilError::OracleExhausted);
    }

    #[test]
    fn verifier_without_pcs_rejects_commitments() {
        let (_, proof) = prove(5);
        let error = ZkVerifierCtx::init(DOMAIN, proof, None).err();
        assert_eq!(error, Some(VeilError::ClaimWithoutOracle));
    }
}

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

/// Handle of a committed bit witness: its index in commitment order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleId(pub usize);

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
pub fn compute_mask_length(pcs: Option<&BitPcs>, verify: impl FnOnce(&mut MaskCounter)) -> usize {
    let mut counter = MaskCounter::new(pcs);
    verify(&mut counter);
    counter.count()
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
        zerocheck::sample_eq_point_bounded(m, &mut self.challenger)
            .ok_or(VeilError::ChallengeSamplingLimitExceeded)
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
            blind_grind_nonce = self
                .challenger
                .grind_pow_bounded(bits, MAX_BLIND_GRIND_TRIALS)
                .ok_or(VeilError::GrindingLimitExceeded)?;
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

    fn grind_pow_bounded(&mut self, _bits: u32, _max_attempts: u64) -> Option<u64> {
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
        zerocheck::sample_eq_point_bounded(m, &mut replay)
            .ok_or(VeilError::ChallengeSamplingLimitExceeded)
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
        if self.proof.blinded_slices.len() != self.claims.len()
            || self.proof.pcs_openings.len() != oracles_with_claims(&self.claims).len()
            || self
                .proof
                .blinded_slices
                .iter()
                .any(|slice| slice.len() != RING_WIDTH)
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
            if self.proof.blind_grind_nonce >= MAX_BLIND_GRIND_TRIALS
                || !self
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
        if proof.veil.parameters != ConstraintParameters::succinct_flock_secure() {
            return Err(VeilError::ProofShape("VEIL parameters"));
        }
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
                if commitment.params != *pcs.params() {
                    return Err(VeilError::PcsParamsMismatch);
                }
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
        zerocheck::sample_eq_point_bounded(m, &mut self.challenger)
            .ok_or(VeilError::ChallengeSamplingLimitExceeded)
    }
}

//! Succinct VEIL compilation for FLOCK's algebraic transcript.
//!
//! VEIL masks the zerocheck and lincheck messages and the terminal ring-switch
//! slices. A non-zero transcript challenge combines the witness with the
//! committed uniform PCS blinder before ring switching. The VEIL circuit
//! checks the FLOCK transcript, its terminal claims, and the characteristic-two
//! linear map relating the masked slices to the blinded PCS opening.
//!
//! For a ring-switch slice map `S` and packed-field multiplication map `M_c`,
//! `S(z + c·g) = S(z) + M_c(S(g))`. Every masked slice is bound before `c` is
//! sampled, and `M_c` is invertible for non-zero `c`.

use flock_core::{
    challenger::Challenger,
    field::F128,
    lincheck::{self, LincheckCircuit, LincheckProof},
    pcs::{self, Commitment, PcsParams},
    proof::{ZClaim, bind_statement},
    r1cs::BlockR1cs,
    ro::{RoChannel, RoContext},
    zerocheck::{self, ZerocheckProof},
    zk::{MaskSampler, ZkRng},
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use veil_f128::{
    ArithmeticCircuit, CircuitBuilder, ConstraintError, ConstraintParameters, ConstraintProof,
    ConstraintSoundnessBound, LinearCombination, certify_constraint_soundness,
    commit_constraint_inputs, prove_constraints_from_commitment, verify_constraints,
};

use crate::prover::quirky_x_outer_full;

const MASK_ROOT_LABEL: &[u8] = b"veil-flock-mask-root";
const RING_MASK_LABEL: &[u8] = b"veil-flock-ring-masks";
const PCS_BLIND_LABEL: &[u8] = b"veil-flock-public-pcs-blind";
const BLINDED_RING_LABEL: &[u8] = b"veil-flock-blinded-ring";
const PCS_FORK_LABEL: &[u8] = b"veil-flock-pcs-fork";
const VEIL_FORK_LABEL: &[u8] = b"veil-flock-inner-fork";
const TREE_NONCES_LABEL: &[u8] = b"veil-flock-tree-nonces";
const RING_CLAIM_COUNT: usize = 2;
const PUBLIC_DIRECT_CLAIM_COUNT: usize = 1;
const RING_WIDTH: usize = 1 << pcs::LOG_PACKING;

#[derive(Clone, Copy)]
struct SupportedBlake3R1csShape {
    digest: [u8; 32],
    r1cs_m: usize,
    mask_count: usize,
}

/// Pinned BLAKE3-preimage circuit digests and mask counts accepted by full ZK.
/// Entries correspond to 256, 512, 1024, and 2048 slots.
const SUPPORTED_BLAKE3_R1CS_SHAPES: [SupportedBlake3R1csShape; 4] = [
    SupportedBlake3R1csShape {
        digest: [
            0x33, 0xcb, 0x2a, 0x40, 0x4f, 0x1b, 0x19, 0x77, 0x5e, 0x0c, 0x38, 0x11, 0x89, 0xd1,
            0x4e, 0xc9, 0x0d, 0x00, 0xf9, 0xcd, 0x75, 0xa9, 0x68, 0x5d, 0x1f, 0xc0, 0x1c, 0x6b,
            0x72, 0x58, 0x2d, 0x4f,
        ],
        r1cs_m: 22,
        mask_count: 754,
    },
    SupportedBlake3R1csShape {
        digest: [
            0xd0, 0xa0, 0x54, 0x97, 0x0d, 0xce, 0xc1, 0x72, 0x7d, 0xdb, 0x8c, 0x49, 0x61, 0x53,
            0x95, 0x92, 0xd2, 0x84, 0xf0, 0x75, 0xfa, 0xb5, 0xd3, 0x9b, 0xc3, 0x1b, 0xcd, 0x35,
            0x01, 0x89, 0x0a, 0x4b,
        ],
        r1cs_m: 23,
        mask_count: 756,
    },
    SupportedBlake3R1csShape {
        digest: [
            0xc2, 0x65, 0x34, 0xe7, 0x42, 0x6c, 0xd4, 0x2b, 0x19, 0x13, 0xf4, 0x21, 0x70, 0xf2,
            0x39, 0xd1, 0x55, 0x30, 0x94, 0xef, 0x3e, 0x98, 0xc3, 0x8b, 0x5a, 0xed, 0x9d, 0x31,
            0x6b, 0xb3, 0xa2, 0x23,
        ],
        r1cs_m: 24,
        mask_count: 758,
    },
    SupportedBlake3R1csShape {
        digest: [
            0x51, 0x6b, 0x46, 0xd4, 0x88, 0x0e, 0x7f, 0xa8, 0x42, 0xe1, 0x4a, 0x39, 0x61, 0xeb,
            0xbc, 0x15, 0x2d, 0xef, 0x5f, 0x6a, 0x6f, 0x75, 0x47, 0xcc, 0xa8, 0xff, 0x50, 0x5a,
            0x3d, 0x22, 0xc6, 0x7c,
        ],
        r1cs_m: 25,
        mask_count: 760,
    },
];
/// ZK doubles the committed dimension, so supported outer blinding is <=5 bits.
/// A 4096-trial fail-closed cap charges at most `(31/32)^4096 < 2^-187`.
pub const MAX_BLIND_GRINDING_BITS: u32 = 5;
pub const MAX_BLIND_GRIND_TRIALS: u64 = 4096;
/// Every Ligerito query/fold grind is bounded for the same reason. The cap
/// permits a five-bit live fold grind, whose 4096-trial tail is below `2^-187`.
pub const MAX_LIGERITO_GRINDING_BITS: usize = 5;
pub const MAX_LIGERITO_GRIND_TRIALS: u64 = 4096;
pub const MAX_LIGERITO_GRIND_SITES: u64 = 16;

fn supported_blake3_r1cs_shape(r1cs: &BlockR1cs) -> Option<SupportedBlake3R1csShape> {
    let digest = r1cs.statement_digest();
    SUPPORTED_BLAKE3_R1CS_SHAPES
        .iter()
        .copied()
        .find(|shape| shape.digest == digest && shape.r1cs_m == r1cs.m)
}

fn supported_mask_count(r1cs: &BlockR1cs) -> Option<usize> {
    supported_blake3_r1cs_shape(r1cs).map(|shape| shape.mask_count)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SuccinctVeilProof {
    pub proof_nonce: [u8; 32],
    pub tree_nonces: InitialTreeNonces,
    /// Exactly the zerocheck values observed by Fiat--Shamir, each one-time
    /// padded.
    pub masked_zerocheck: MaskedZerocheckProof,
    pub masked_lincheck: LincheckProof,
    /// Masked slice evaluations for the witness and the PCS blinder at the
    /// two terminal FLOCK points.
    pub masked_ring_claims: Vec<MaskedRingClaim>,
    /// Evaluations of the uniform PCS blinder at packed-direct claim bases.
    /// They are bound before the non-zero witness-blinding challenge.
    pub public_direct_blind_values: Vec<F128>,
    pub blind_grind_nonce: u64,
    pub pcs_open: pcs::BatchOpeningProofLigerito,
    pub veil: ConstraintProof,
}

/// Independent public freshness domains for every initial
/// witness-dependent Merkle tree in the full-ZK protocol.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InitialTreeNonces {
    pub outer: [u8; 32],
    pub veil_linear: [u8; 32],
    pub veil_hadamard: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MaskedRingClaim {
    pub witness: Vec<F128>,
    pub blind: Vec<F128>,
}

/// Audit marker for a packed functional whose claimed value is derived only
/// from the public statement. The succinct full-view-ZK entry point is crate
/// private and accepts direct claims only through this wrapper: a relation
/// adapter must explicitly attest the kernel condition
/// `L(witness_0 - witness_1) = 0` for equal public statements.
pub(crate) struct PublicPackedDirectClaim(pcs::PackedDirectClaim);

impl PublicPackedDirectClaim {
    pub(crate) fn from_public_statement(claim: pcs::PackedDirectClaim) -> Self {
        Self(claim)
    }
}

/// Verifier-side form of [`PublicPackedDirectClaim`].
pub(crate) struct PublicPackedDirectClaimValue {
    point: Vec<F128>,
    value: F128,
}

impl PublicPackedDirectClaimValue {
    pub(crate) fn from_public_statement(point: Vec<F128>, value: F128) -> Self {
        Self { point, value }
    }
}

fn sample_nonce(rng: &mut impl MaskSampler) -> [u8; 32] {
    let mut words = [0u64; 4];
    rng.fill_u64s(&mut words);
    let mut nonce = [0u8; 32];
    for (chunk, word) in nonce.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    nonce
}

fn observe_tree_nonces<Ch: Challenger>(challenger: &mut Ch, nonces: &InitialTreeNonces) {
    challenger.observe_label(TREE_NONCES_LABEL);
    challenger.observe_bytes(&nonces.outer);
    challenger.observe_bytes(&nonces.veil_linear);
    challenger.observe_bytes(&nonces.veil_hadamard);
}

/// Masked zerocheck wire format for succinct VEIL. This intentionally differs
/// from [`ZerocheckProof`]: the ordinary proof's derived `final_c_eval` is not
/// observed by Fiat--Shamir and therefore does not belong in the masked wire.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MaskedZerocheckProof {
    pub round1_ab: Vec<F128>,
    pub round1_c: Vec<F128>,
    pub multilinear_rounds: Vec<(F128, F128)>,
    pub final_a_eval: F128,
    pub final_b_eval: F128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SuccinctVeilError {
    InvalidParameters,
    InvalidShape(&'static str),
    Veil(ConstraintError),
    Pcs(pcs::VerifyError),
    DegenerateSimulation,
    ProgrammingCollision,
    GrindingLimitExceeded,
}

pub struct SuccinctZerocheckInputs<'a> {
    pub a_packed: &'a [u8],
    pub b_packed: &'a [u8],
    pub c_packed: &'a [u8],
    pub m: usize,
    pub padding: &'a zerocheck::PaddingSpec,
}

/// Simulator seam for the standard (unmasked) zerocheck. Implementations
/// emit the masked wire messages directly into `challenger`; the downstream
/// lincheck, PCS opening, and VEIL certificate remain the production path.
pub trait SuccinctZerocheckSource<Ch: Challenger> {
    fn emit(
        &mut self,
        inputs: SuccinctZerocheckInputs<'_>,
        masks: &[F128],
        challenger: &mut Ch,
    ) -> Result<(ZerocheckProof, zerocheck::ZerocheckClaim, Option<Vec<F128>>), SuccinctVeilError>;
}

/// Public-witness-free ROM zerocheck simulator. It samples a transcript and
/// solves its final quadratic coefficient so the verifier lands on the true
/// evaluations of the caller's public-fiber representative.
pub struct RomZerocheckSimulator {
    rng: ZkRng,
    z: F128,
    rhos: Vec<F128>,
}

impl RomZerocheckSimulator {
    pub fn new(m: usize, mut rng: ZkRng) -> Self {
        let mut z_value = [F128::ZERO; 1];
        rng.fill_f128(&mut z_value);
        let mut rhos = vec![F128::ZERO; m - zerocheck::K_SKIP];
        rng.fill_f128(&mut rhos);
        Self {
            rng,
            z: z_value[0],
            rhos,
        }
    }

    fn random_vec(&mut self, length: usize) -> Vec<F128> {
        let mut values = vec![F128::ZERO; length];
        self.rng.fill_f128(&mut values);
        values
    }
}

fn solve_sumcheck_messages(
    running: F128,
    target: F128,
    r_eq: F128,
    rho: F128,
    random_g1: F128,
    random_g_inf: F128,
) -> Result<(F128, F128), SuccinctVeilError> {
    let denominator = F128::ONE + r_eq;
    if denominator.is_zero() {
        return Err(SuccinctVeilError::DegenerateSimulation);
    }
    let inverse_eq = denominator.inv();
    let one_plus_rho = F128::ONE + rho;
    let running_weight = one_plus_rho * inverse_eq;
    let one_weight = (r_eq + rho) * inverse_eq;
    let infinity_weight = rho * one_plus_rho;
    if !infinity_weight.is_zero() {
        let g_inf =
            (target + running_weight * running + one_weight * random_g1) * infinity_weight.inv();
        Ok((random_g1, g_inf))
    } else if !one_weight.is_zero() {
        let g1 =
            (target + running_weight * running + infinity_weight * random_g_inf) * one_weight.inv();
        Ok((g1, random_g_inf))
    } else {
        Err(SuccinctVeilError::DegenerateSimulation)
    }
}

impl SuccinctZerocheckSource<crate::sim_oracle::OracleChallenger> for RomZerocheckSimulator {
    fn emit(
        &mut self,
        inputs: SuccinctZerocheckInputs<'_>,
        masks: &[F128],
        challenger: &mut crate::sim_oracle::OracleChallenger,
    ) -> Result<(ZerocheckProof, zerocheck::ZerocheckClaim, Option<Vec<F128>>), SuccinctVeilError>
    {
        let ell = 1usize << zerocheck::K_SKIP;
        let n_mlv = inputs.m - zerocheck::K_SKIP;
        let expected_masks = 2 * ell + 2 * n_mlv + 2;
        if masks.len() < expected_masks || self.rhos.len() != n_mlv {
            return Err(SuccinctVeilError::InvalidShape(
                "simulator zerocheck mask geometry",
            ));
        }

        challenger.observe_label(b"flock-zerocheck");
        let r = zerocheck::sample_eq_point(inputs.m, challenger);

        // Reuse the shipped terminal evaluator with zero mask channels; only
        // its a/b/c outputs are relevant to the standard zerocheck.
        let zero_p = vec![F128::ZERO; zerocheck::SmallMaskSpec::default().d(inputs.m)];
        let zeros = vec![0u8; (1usize << inputs.m) / 8];
        let terminal = zerocheck::evaluate_zk_terminals_packed_padded(
            inputs.a_packed,
            inputs.b_packed,
            inputs.c_packed,
            &zero_p,
            &zeros,
            &zeros,
            inputs.m,
            inputs.padding,
            &r,
            self.z,
            &self.rhos,
        );

        let mut round1_ab = self.random_vec(ell);
        let mut round1_c = self.random_vec(ell);
        let c_weights =
            zerocheck::multilinear::lagrange_weights_lambda_naive(zerocheck::K_SKIP, self.z);
        let pivot = c_weights
            .iter()
            .position(|weight| !weight.is_zero())
            .ok_or(SuccinctVeilError::DegenerateSimulation)?;
        let partial_c = c_weights
            .iter()
            .zip(&round1_c)
            .enumerate()
            .filter(|(index, _)| *index != pivot)
            .fold(F128::ZERO, |acc, (_, (weight, value))| {
                acc + *weight * *value
            });
        round1_c[pivot] = (terminal.c_eval + partial_c) * c_weights[pivot].inv();

        // Normally one non-identity recursive round is used to solve the
        // terminal constraint. If every `(rho, r_eq)` pair is `(0, 0)`, all
        // recursive rounds are the identity. Cover that honest-support event
        // exactly by solving one initial AB coefficient instead of aborting or
        // conditioning the challenges.
        let solve_round = (0..n_mlv)
            .rev()
            .find(|&i| !(self.rhos[i].is_zero() && r[zerocheck::K_SKIP + i].is_zero()));
        let target = terminal.a_eval * terminal.b_eval;
        if solve_round.is_none() {
            let weights = zerocheck::multilinear::interpolate_at_z_combined_weights(
                zerocheck::K_SKIP,
                self.z,
            );
            let pivot = weights
                .iter()
                .position(|weight| !weight.is_zero())
                .ok_or(SuccinctVeilError::DegenerateSimulation)?;
            let partial = weights
                .iter()
                .zip(round1_ab.iter().zip(&round1_c))
                .enumerate()
                .filter(|(index, _)| *index != pivot)
                .fold(F128::ZERO, |acc, (_, (weight, (ab, c)))| {
                    acc + *weight * (*ab + *c)
                });
            round1_ab[pivot] =
                (target + terminal.c_eval + partial) * weights[pivot].inv() + round1_c[pivot];
        }

        let mut mask_cursor = 0usize;
        let masked_ab = round1_ab
            .iter()
            .map(|value| {
                let masked = *value + masks[mask_cursor];
                mask_cursor += 1;
                masked
            })
            .collect::<Vec<_>>();
        let masked_c = round1_c
            .iter()
            .map(|value| {
                let masked = *value + masks[mask_cursor];
                mask_cursor += 1;
                masked
            })
            .collect::<Vec<_>>();
        challenger.observe_f128_slice(&masked_ab);
        challenger.observe_f128_slice(&masked_c);
        if challenger.program_next_scalar(self.z).is_none() {
            return Err(SuccinctVeilError::ProgrammingCollision);
        }
        let z = challenger.sample_f128();

        let combined = round1_ab
            .iter()
            .zip(&round1_c)
            .map(|(ab, c)| *ab + *c)
            .collect::<Vec<_>>();
        let mut running =
            zerocheck::multilinear::interpolate_at_z_combined(&combined, zerocheck::K_SKIP, z)
                + terminal.c_eval;
        // A round with `(rho, r_eq) = (0, 0)` is the identity on `running`
        // regardless of its two messages. Otherwise solve at the last
        // non-identity round and let any identity suffix pass through. This
        // handles rho=0 and rho=1 without conditioning the uniform challenge
        // law.
        let mut rounds = Vec::with_capacity(n_mlv);
        for i in 0..n_mlv {
            let rho = self.rhos[i];
            let one_plus_rho = F128::ONE + rho;
            let r_eq = r[zerocheck::K_SKIP + i];
            let one_plus_r_eq = F128::ONE + r_eq;
            if one_plus_r_eq.is_zero() {
                return Err(SuccinctVeilError::DegenerateSimulation);
            }
            let inverse_eq = one_plus_r_eq.inv();
            let (g1, g_inf) = if solve_round == Some(i) {
                solve_sumcheck_messages(
                    running,
                    target,
                    r_eq,
                    rho,
                    self.random_vec(1)[0],
                    self.random_vec(1)[0],
                )?
            } else {
                (self.random_vec(1)[0], self.random_vec(1)[0])
            };
            let g0 = (running + r_eq * g1) * inverse_eq;
            rounds.push((g1, g_inf));
            challenger.observe_f128(g1 + masks[mask_cursor]);
            mask_cursor += 1;
            challenger.observe_f128(g_inf + masks[mask_cursor]);
            mask_cursor += 1;
            if challenger.program_next_scalar(rho).is_none() {
                return Err(SuccinctVeilError::ProgrammingCollision);
            }
            let sampled = challenger.sample_f128();
            running = g0 * one_plus_rho + g1 * rho + g_inf * rho * one_plus_rho;
            debug_assert_eq!(sampled, rho);
        }
        if running != target {
            return Err(SuccinctVeilError::DegenerateSimulation);
        }
        challenger.observe_f128(terminal.a_eval + masks[mask_cursor]);
        mask_cursor += 1;
        challenger.observe_f128(terminal.b_eval + masks[mask_cursor]);
        mask_cursor += 1;
        if mask_cursor != expected_masks {
            return Err(SuccinctVeilError::InvalidShape(
                "simulator zerocheck observation count",
            ));
        }
        Ok((
            ZerocheckProof {
                round1_ab: std::mem::take(&mut round1_ab),
                round1_c: std::mem::take(&mut round1_c),
                multilinear_rounds: rounds,
                final_a_eval: terminal.a_eval,
                final_b_eval: terminal.b_eval,
                final_c_eval: terminal.c_eval,
            },
            zerocheck::ZerocheckClaim {
                z,
                mlv_challenges: self.rhos.clone(),
                r_rest: r[zerocheck::K_SKIP..].to_vec(),
                a_eval: terminal.a_eval,
                b_eval: terminal.b_eval,
                c_eval: terminal.c_eval,
            },
            None,
        ))
    }
}

impl From<ConstraintError> for SuccinctVeilError {
    fn from(value: ConstraintError) -> Self {
        Self::Veil(value)
    }
}

impl From<pcs::VerifyError> for SuccinctVeilError {
    fn from(value: pcs::VerifyError) -> Self {
        Self::Pcs(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MaskLayout {
    ell: usize,
    zc_rounds: usize,
    lc_rounds: usize,
    z_partial: usize,
}

/// Exact constraint inventory for the shifted FLOCK verifier circuit before
/// VEIL adds its two standard Hadamard-masking products.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShiftedCircuitCertificate {
    pub private_inputs: usize,
    pub flock_multiplications: usize,
    pub lincheck_linear_constraints: usize,
    pub ring_scale_linear_constraints: usize,
    pub ring_claim_linear_constraints: usize,
}

/// Additive algebraic soundness ledger for the FLOCK PIOP and its batched
/// linkage to the single witness PCS opening. This is separate from both the
/// VEIL constraint binding bound and the recursive Ligerito PCS bound.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FlockPiopSoundnessBound {
    pub friendly_coordinate_rank_f2: usize,
    pub zerocheck_relation_probability: f64,
    pub zerocheck_univariate_probability: f64,
    pub zerocheck_sumcheck_probability: f64,
    pub lincheck_claim_batch_probability: f64,
    pub constant_pin_probability: f64,
    pub lincheck_sumcheck_probability: f64,
    pub lincheck_skip_probability: f64,
    pub ring_switch_probability: f64,
    pub pcs_claim_batch_probability: f64,
}

impl FlockPiopSoundnessBound {
    pub fn probability(self) -> f64 {
        self.zerocheck_relation_probability
            + self.zerocheck_univariate_probability
            + self.zerocheck_sumcheck_probability
            + self.lincheck_claim_batch_probability
            + self.constant_pin_probability
            + self.lincheck_sumcheck_probability
            + self.lincheck_skip_probability
            + self.ring_switch_probability
            + self.pcs_claim_batch_probability
    }

    pub fn bits(self) -> f64 {
        -self.probability().log2()
    }
}

/// Certify every Schwartz--Zippel term in the active fixed-shape FLOCK PIOP.
/// All challenges counted here are sampled after the polynomial/message they
/// bind. The seven implementation-fixed zerocheck coordinates are checked for
/// full F2 rank; the remaining `m-7` coordinates are uniform F128 values.
pub fn certify_flock_piop_soundness(
    r1cs: &BlockR1cs,
    lincheck_circuit: &dyn LincheckCircuit,
) -> Result<FlockPiopSoundnessBound, SuccinctVeilError> {
    if supported_mask_count(r1cs).is_none() {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    let layout = MaskLayout::new(r1cs)?;
    let friendly = zerocheck::univariate_skip_optimized::small_challenges_ghash()
        .into_iter()
        .chain(zerocheck::univariate_skip_optimized::medium_challenges_ghash());
    let mut rows = friendly
        .map(|value| (u128::from(value.hi) << 64) | u128::from(value.lo))
        .collect::<Vec<_>>();
    let friendly_coordinate_rank_f2 = binary_rank(&mut rows);
    if friendly_coordinate_rank_f2 != zerocheck::N_INNER
        || r1cs.m < zerocheck::N_INNER
        || layout.ell != 1usize << zerocheck::K_SKIP
    {
        return Err(SuccinctVeilError::InvalidParameters);
    }

    let q = 2f64.powi(128);
    let bound = FlockPiopSoundnessBound {
        friendly_coordinate_rank_f2,
        // MLE identity/collision at the partially fixed equality point.
        zerocheck_relation_probability: (r1cs.m - zerocheck::N_INNER) as f64 / q,
        // The round-one AB+C polynomial has degree < 2*ell.
        zerocheck_univariate_probability: (2 * layout.ell - 1) as f64 / q,
        // Every remaining compressed sumcheck polynomial is quadratic.
        zerocheck_sumcheck_probability: (2 * layout.zc_rounds) as f64 / q,
        // alpha batches the two terminal A/B claims.
        lincheck_claim_batch_probability: 1.0 / q,
        // beta pins the public constant column when the live circuit has one.
        constant_pin_probability: if lincheck_circuit.const_pin_col().is_some() {
            1.0 / q
        } else {
            0.0
        },
        lincheck_sumcheck_probability: (2 * layout.lc_rounds) as f64 / q,
        // The final phi8/Lagrange polynomial has degree < ell.
        lincheck_skip_probability: (layout.ell - 1) as f64 / q,
        // Each of the two ring-switch tables is tested at LOG_PACKING fresh
        // multilinear coordinates before its batch coefficient is sampled.
        ring_switch_probability: (RING_CLAIM_COUNT * pcs::LOG_PACKING) as f64 / q,
        // Independent coefficients batch both ring claims and the one public
        // packed-direct claim into the single Ligerito opening.
        pcs_claim_batch_probability: 1.0 / q,
    };
    if !bound.bits().is_finite() || bound.bits() < 110.0 {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    Ok(bound)
}

/// Compute the VEIL binding ledger from the exact production circuit
/// inventory. Runtime proving and verification separately validate that the
/// challenge-instantiated circuit has precisely this shape.
pub fn certify_shifted_veil_soundness(
    r1cs: &BlockR1cs,
) -> Result<ConstraintSoundnessBound, SuccinctVeilError> {
    if supported_mask_count(r1cs).is_none() {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    let layout = MaskLayout::new(r1cs)?;
    let inventory = layout.shifted_circuit_certificate(true);
    let mut builder = CircuitBuilder::new(inventory.private_inputs);
    let zero = builder.constant(F128::ZERO);
    for _ in 0..inventory.flock_multiplications {
        builder.assert_mul(&zero, &zero, &zero);
    }
    for _ in 0..inventory.linear_constraints() {
        builder.assert_zero(&zero);
    }
    let circuit = builder.finish();
    inventory.validate(&circuit)?;
    Ok(certify_constraint_soundness(
        &circuit,
        ConstraintParameters::succinct_flock_secure(),
    )?)
}

fn binary_rank(rows: &mut [u128]) -> usize {
    let mut rank = 0usize;
    for column in (0..128).rev() {
        let Some(pivot) = (rank..rows.len()).find(|&row| ((rows[row] >> column) & 1) == 1) else {
            continue;
        };
        rows.swap(rank, pivot);
        for row in 0..rows.len() {
            if row != rank && ((rows[row] >> column) & 1) == 1 {
                rows[row] ^= rows[rank];
            }
        }
        rank += 1;
    }
    rank
}

impl ShiftedCircuitCertificate {
    pub fn linear_constraints(self) -> usize {
        self.lincheck_linear_constraints
            + self.ring_scale_linear_constraints
            + self.ring_claim_linear_constraints
    }

    fn validate(self, circuit: &ArithmeticCircuit) -> Result<(), SuccinctVeilError> {
        if circuit.num_inputs() != self.private_inputs
            || circuit.num_variables() != self.private_inputs
            || circuit.num_multiplications() != self.flock_multiplications
            || circuit.num_linear_constraints() != self.linear_constraints()
        {
            return Err(SuccinctVeilError::InvalidShape(
                "shifted verifier constraint inventory",
            ));
        }
        Ok(())
    }
}

impl MaskLayout {
    fn new(r1cs: &BlockR1cs) -> Result<Self, SuccinctVeilError> {
        let k = r1cs.k();
        if r1cs.k_skip != zerocheck::K_SKIP
            || r1cs.m < zerocheck::K_SKIP + zerocheck::N_INNER
            || r1cs.k_log < r1cs.k_skip
            || !r1cs.c0_is_identity()
            || r1cs.a_0.num_rows != k
            || r1cs.a_0.num_cols != k
            || r1cs.b_0.num_rows != k
            || r1cs.b_0.num_cols != k
        {
            return Err(SuccinctVeilError::InvalidShape("R1CS mask geometry"));
        }
        Ok(Self {
            ell: 1usize << zerocheck::K_SKIP,
            zc_rounds: r1cs.m - zerocheck::K_SKIP,
            lc_rounds: r1cs.k_log - r1cs.k_skip,
            z_partial: 1usize << r1cs.k_skip,
        })
    }

    fn piop_count(self) -> usize {
        2 * self.ell + 2 * self.zc_rounds + 2 + 2 * self.lc_rounds + self.z_partial
    }

    fn observed_count(self) -> usize {
        self.piop_count() + 2 * RING_CLAIM_COUNT * RING_WIDTH
    }

    fn shifted_circuit_certificate(self, with_ring_link: bool) -> ShiftedCircuitCertificate {
        ShiftedCircuitCertificate {
            private_inputs: if with_ring_link {
                self.observed_count()
            } else {
                self.piop_count()
            },
            flock_multiplications: 1,
            lincheck_linear_constraints: 1,
            ring_scale_linear_constraints: if with_ring_link {
                RING_CLAIM_COUNT * RING_WIDTH
            } else {
                0
            },
            ring_claim_linear_constraints: if with_ring_link { RING_CLAIM_COUNT } else { 0 },
        }
    }
}

fn validate_succinct_parameters(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
) -> Result<MaskLayout, SuccinctVeilError> {
    if !pcs_params.zk
        || r1cs.zk.is_none()
        || pcs_params.m != r1cs.m
        || pcs_params.log_inv_rate != 1
        || pcs_params.log_batch_size != 6
        || pcs_params.profile != pcs::ligerito::LigeritoProfile::Secure
    {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    let Some(supported_shape) = supported_blake3_r1cs_shape(r1cs) else {
        return Err(SuccinctVeilError::InvalidParameters);
    };
    let layout = MaskLayout::new(r1cs)?;
    if layout.observed_count() != supported_shape.mask_count {
        return Err(SuccinctVeilError::InvalidShape(
            "global mask identity cover",
        ));
    }
    Ok(layout)
}

fn validate_l0_hiding_budget(
    pcs_params: &PcsParams,
    queries: &[usize],
) -> Result<(), SuccinctVeilError> {
    let Some(&opened_positions) = queries.first() else {
        return Err(SuccinctVeilError::InvalidShape("missing L0 query budget"));
    };
    let mask_symbols_per_lane =
        (1usize << pcs_params.witness_log_msg_len()) / pcs_params.num_ntts();
    if opened_positions > mask_symbols_per_lane {
        return Err(SuccinctVeilError::InvalidShape("L0 hiding query budget"));
    }
    Ok(())
}

/// Fold rounds per Ligerito level: L0 uses `initial_k`, later levels use `recursive_ks`.
/// The prover grinds once per round of a level with positive fold grind.
fn fold_rounds_of(initial_k: usize, recursive_ks: &[usize]) -> Vec<usize> {
    std::iter::once(initial_k)
        .chain(recursive_ks.iter().copied())
        .collect()
}

fn validate_batch_opening(
    pcs_params: &PcsParams,
    queries: &[usize],
    grinding_bits: &[usize],
    fold_grinding_bits: &[usize],
    fold_rounds: &[usize],
) -> Result<(), SuccinctVeilError> {
    validate_l0_hiding_budget(pcs_params, queries)?;
    // Count one site per positive-grind fold round, not one per level.
    // This matches `ligerito_grinding_is_bounded` on emitted nonces.
    let positive_fold_sites: usize = fold_grinding_bits
        .iter()
        .zip(fold_rounds)
        .filter(|(bits, _)| **bits > 0)
        .map(|(_, rounds)| *rounds)
        .sum();
    if grinding_bits.iter().any(|bits| *bits != 0)
        || fold_grinding_bits.len() != fold_rounds.len()
        || fold_grinding_bits
            .iter()
            .any(|bits| *bits > MAX_LIGERITO_GRINDING_BITS)
        || positive_fold_sites > MAX_LIGERITO_GRIND_SITES as usize
    {
        return Err(SuccinctVeilError::InvalidShape("bounded grinding schedule"));
    }
    let blind_grinding_bits = pcs::ligerito::l0_derived_grind_bits(fold_grinding_bits);
    if queries[0] == 0 || !(1..=MAX_BLIND_GRINDING_BITS).contains(&blind_grinding_bits) {
        return Err(SuccinctVeilError::InvalidShape("batch opening certificate"));
    }
    Ok(())
}

fn ligerito_grinding_is_bounded(proof: &pcs::ligerito::LigeritoProof) -> bool {
    proof
        .grinding_nonces
        .iter()
        .chain(&proof.fold_grinding_nonces)
        .all(|nonce| *nonce < MAX_LIGERITO_GRIND_TRIALS)
        && proof.fold_grinding_nonces.len() <= MAX_LIGERITO_GRIND_SITES as usize
}

/// Challenger adapter used only while producing zerocheck and lincheck. It
/// forwards exactly the masked values to the real Fiat--Shamir transcript,
/// preserving scalar-vs-slice framing.
struct MaskingChallenger<'a, C> {
    inner: &'a mut C,
    masks: &'a [F128],
    cursor: usize,
}

impl<'a, C> MaskingChallenger<'a, C> {
    fn new(inner: &'a mut C, masks: &'a [F128]) -> Self {
        Self {
            inner,
            masks,
            cursor: 0,
        }
    }

    fn take_mask(&mut self) -> F128 {
        let mask = self.masks[self.cursor];
        self.cursor += 1;
        mask
    }
}

impl<C: Challenger> Challenger for MaskingChallenger<'_, C> {
    fn ro_context(&self, nonce: [u8; 32]) -> RoContext {
        self.inner.ro_context(nonce)
    }

    fn observe_label(&mut self, label: &[u8]) {
        self.inner.observe_label(label);
    }

    fn observe_f128(&mut self, value: F128) {
        let masked = value + self.take_mask();
        self.inner.observe_f128(masked);
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        let masked = values
            .iter()
            .map(|value| *value + self.take_mask())
            .collect::<Vec<_>>();
        self.inner.observe_f128_slice(&masked);
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.inner.observe_bytes(bytes);
    }

    fn sample_f128(&mut self) -> F128 {
        self.inner.sample_f128()
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.inner.sample_f128_vec(n)
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        self.inner.grind_pow(bits)
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.inner.verify_pow(nonce, bits)
    }
}

fn mask_proofs(
    zc: &ZerocheckProof,
    lc: &LincheckProof,
    masks: &[F128],
) -> (MaskedZerocheckProof, LincheckProof) {
    let mut cursor = 0;
    let mut next = |value: F128| {
        let result = value + masks[cursor];
        cursor += 1;
        result
    };
    let masked_zc = MaskedZerocheckProof {
        round1_ab: zc.round1_ab.iter().map(|v| next(*v)).collect(),
        round1_c: zc.round1_c.iter().map(|v| next(*v)).collect(),
        multilinear_rounds: zc
            .multilinear_rounds
            .iter()
            .map(|(a, b)| (next(*a), next(*b)))
            .collect(),
        final_a_eval: next(zc.final_a_eval),
        final_b_eval: next(zc.final_b_eval),
    };
    let masked_lc = LincheckProof {
        rounds: lc
            .rounds
            .iter()
            .map(|(a, b)| (next(*a), next(*b)))
            .collect(),
        z_partial: lc.z_partial.iter().map(|v| next(*v)).collect(),
    };
    assert_eq!(cursor, masks.len());
    (masked_zc, masked_lc)
}

struct ExpressionCursor {
    masks: usize,
    cursor: usize,
}

impl ExpressionCursor {
    fn new(masks: usize) -> Self {
        Self { masks, cursor: 0 }
    }

    fn unmask(&mut self, value: F128) -> LinearCombination {
        assert!(self.cursor < self.masks);
        let result =
            LinearCombination::constant(value).add(&LinearCombination::variable(self.cursor));
        self.cursor += 1;
        result
    }
}

fn dot(expressions: &[LinearCombination], coefficients: &[F128]) -> LinearCombination {
    assert_eq!(expressions.len(), coefficients.len());
    expressions.iter().zip(coefficients).fold(
        LinearCombination::zero(),
        |acc, (expression, coefficient)| acc.add(&expression.scale(*coefficient)),
    )
}

fn mask_ring_claims(
    witness: &[Vec<F128>],
    blind: &[Vec<F128>],
    masks: &[F128],
) -> Vec<MaskedRingClaim> {
    assert_eq!(witness.len(), RING_CLAIM_COUNT);
    assert_eq!(blind.len(), RING_CLAIM_COUNT);
    assert_eq!(masks.len(), 2 * RING_CLAIM_COUNT * RING_WIDTH);
    let mut cursor = 0;
    witness
        .iter()
        .zip(blind)
        .map(|(witness, blind)| {
            assert_eq!(witness.len(), RING_WIDTH);
            assert_eq!(blind.len(), RING_WIDTH);
            let witness = witness
                .iter()
                .map(|value| {
                    let masked = *value + masks[cursor];
                    cursor += 1;
                    masked
                })
                .collect();
            let blind = blind
                .iter()
                .map(|value| {
                    let masked = *value + masks[cursor];
                    cursor += 1;
                    masked
                })
                .collect();
            MaskedRingClaim { witness, blind }
        })
        .collect()
}

fn observe_masked_ring_claims<C: Challenger>(challenger: &mut C, claims: &[MaskedRingClaim]) {
    challenger.observe_label(RING_MASK_LABEL);
    for claim in claims {
        challenger.observe_f128_slice(&claim.witness);
        challenger.observe_f128_slice(&claim.blind);
    }
}

fn observe_direct_blinds<C: Challenger>(challenger: &mut C, values: &[F128]) {
    challenger.observe_label(PCS_BLIND_LABEL);
    challenger.observe_f128_slice(values);
}

fn observe_blinded_ring_claims<C: Challenger>(challenger: &mut C, slices: &[Vec<F128>]) {
    challenger.observe_label(BLINDED_RING_LABEL);
    for slice in slices {
        challenger.observe_f128_slice(slice);
    }
}

fn sample_nonzero<C: Challenger>(challenger: &mut C) -> F128 {
    loop {
        let value = challenger.sample_f128();
        if !value.is_zero() {
            return value;
        }
    }
}

fn scale_ring_expressions(
    expressions: &[LinearCombination],
    scalar: F128,
) -> Vec<LinearCombination> {
    assert_eq!(expressions.len(), RING_WIDTH);
    let mut out = vec![LinearCombination::zero(); RING_WIDTH];
    for (input_bit, expression) in expressions.iter().enumerate() {
        let basis = if input_bit < 64 {
            F128::new(1u64 << input_bit, 0)
        } else {
            F128::new(0, 1u64 << (input_bit - 64))
        };
        let product = scalar * basis;
        for output_bit in 0..RING_WIDTH {
            let present = if output_bit < 64 {
                (product.lo >> output_bit) & 1
            } else {
                (product.hi >> (output_bit - 64)) & 1
            };
            if present == 1 {
                out[output_bit] = out[output_bit].add(expression);
            }
        }
    }
    out
}

struct RingLink<'a> {
    masked: &'a [MaskedRingClaim],
    q_slices: &'a [Vec<F128>],
    challenge: F128,
}

/// Replay the public, masked PIOP transcript and construct
/// `C'(h) = C(masked + h)`. When ring linkage is present, the returned claims
/// are evaluations of the blinded witness at the two terminal FLOCK points.
fn shifted_verifier_circuit<C: Challenger>(
    r1cs: &BlockR1cs,
    zc: &MaskedZerocheckProof,
    lc: &LincheckProof,
    ring_link: Option<RingLink<'_>>,
    lincheck_circuit: &dyn LincheckCircuit,
    challenger: &mut C,
) -> Result<(ArithmeticCircuit, ZClaim, ZClaim), SuccinctVeilError> {
    let layout = MaskLayout::new(r1cs)?;
    let with_ring_link = ring_link.is_some();
    if zc.round1_ab.len() != layout.ell
        || zc.round1_c.len() != layout.ell
        || zc.multilinear_rounds.len() != layout.zc_rounds
        || lc.rounds.len() != layout.lc_rounds
        || lc.z_partial.len() != layout.z_partial
    {
        return Err(SuccinctVeilError::InvalidShape("PIOP proof geometry"));
    }

    let mask_count = if ring_link.is_some() {
        layout.observed_count()
    } else {
        layout.piop_count()
    };
    let mut builder = CircuitBuilder::new(mask_count);
    let mut expressions = ExpressionCursor::new(mask_count);

    challenger.observe_label(b"flock-zerocheck");
    let r = zerocheck::sample_eq_point(r1cs.m, challenger);

    let round1_ab = zc
        .round1_ab
        .iter()
        .map(|value| expressions.unmask(*value))
        .collect::<Vec<_>>();
    let round1_c = zc
        .round1_c
        .iter()
        .map(|value| expressions.unmask(*value))
        .collect::<Vec<_>>();
    challenger.observe_f128_slice(&zc.round1_ab);
    challenger.observe_f128_slice(&zc.round1_c);
    let z = challenger.sample_f128();

    let c_weights = zerocheck::multilinear::lagrange_weights_lambda_naive(zerocheck::K_SKIP, z);
    let computed_c = dot(&round1_c, &c_weights);

    let combined_weights =
        zerocheck::multilinear::interpolate_at_z_combined_weights(zerocheck::K_SKIP, z);
    let combined = round1_ab
        .iter()
        .zip(&round1_c)
        .map(|(ab, c)| ab.add(c))
        .collect::<Vec<_>>();
    let mut running = dot(&combined, &combined_weights).add(&computed_c);
    let mut mlv_challenges = Vec::with_capacity(layout.zc_rounds);
    for (i, (masked_1, masked_inf)) in zc.multilinear_rounds.iter().enumerate() {
        let msg_1 = expressions.unmask(*masked_1);
        let msg_inf = expressions.unmask(*masked_inf);
        let r_eq = r[zerocheck::K_SKIP + i];

        challenger.observe_f128(*masked_1);
        challenger.observe_f128(*masked_inf);
        let rho = challenger.sample_f128();
        mlv_challenges.push(rho);
        let [running_weight, one_weight, infinity_weight] =
            zerocheck::sumcheck_round_weights(r_eq, rho).ok_or(SuccinctVeilError::InvalidShape(
                "degenerate zerocheck challenge",
            ))?;
        running = running
            .scale(running_weight)
            .add(&msg_1.scale(one_weight))
            .add(&msg_inf.scale(infinity_weight));
    }
    let final_a = expressions.unmask(zc.final_a_eval);
    let final_b = expressions.unmask(zc.final_b_eval);
    builder.assert_mul(&final_a, &final_b, &running);
    challenger.observe_f128(zc.final_a_eval);
    challenger.observe_f128(zc.final_b_eval);

    let x_ab = r1cs.x_ab_from_mlv(z, &mlv_challenges);
    challenger.observe_label(b"flock-lincheck");
    let alpha = challenger.sample_f128();
    let eq_inner = lincheck::build_quirky_eq_table(x_ab.z_skip, &x_ab.x_inner_rest, r1cs.k_skip);
    let mut comb_vec = lincheck_circuit.fold_alpha_batched(alpha, &eq_inner);
    let mut lc_running = final_a.scale(alpha).add(&final_b);
    if let Some(column) = lincheck_circuit.const_pin_col() {
        let beta = challenger.sample_f128();
        comb_vec[column] += beta;
        lc_running = lc_running.add(&LinearCombination::constant(beta));
    }

    let mut lc_challenges = Vec::with_capacity(layout.lc_rounds);
    for (masked_1, masked_inf) in &lc.rounds {
        let e1 = expressions.unmask(*masked_1);
        let einf = expressions.unmask(*masked_inf);
        challenger.observe_f128(*masked_1);
        challenger.observe_f128(*masked_inf);
        let rho = challenger.sample_f128();
        let e0 = lc_running.add(&e1);
        let c1 = e0.add(&e1).add(&einf);
        lc_running = einf.scale(rho * rho).add(&c1.scale(rho)).add(&e0);
        lincheck::sumcheck_bind_top_in_place_par_pub(&mut comb_vec, rho);
        lc_challenges.push(rho);
    }
    let z_partial = lc
        .z_partial
        .iter()
        .map(|value| expressions.unmask(*value))
        .collect::<Vec<_>>();
    challenger.observe_f128_slice(&lc.z_partial);
    builder.assert_zero(&lc_running.add(&dot(&z_partial, &comb_vec)));

    let r_inner_skip = challenger.sample_f128();
    let lambda = lincheck::build_quirky_eq_table(r_inner_skip, &[], r1cs.k_skip);
    let w = dot(&z_partial, &lambda);

    lc_challenges.reverse();
    let ab_point = r1cs.ab_claim_point(r_inner_skip, &lc_challenges, &x_ab.x_outer);
    let c_point = r1cs.c_claim_point(z, &r[zerocheck::K_SKIP..]);
    let mut values = [F128::ZERO; RING_CLAIM_COUNT];

    if let Some(link) = ring_link {
        if link.masked.len() != RING_CLAIM_COUNT
            || link.q_slices.len() != RING_CLAIM_COUNT
            || link.challenge.is_zero()
        {
            return Err(SuccinctVeilError::InvalidShape("ring claim geometry"));
        }
        let points = [&ab_point, &c_point];
        for (index, ((masked, q_slice), point)) in link
            .masked
            .iter()
            .zip(link.q_slices)
            .zip(points)
            .enumerate()
        {
            if masked.witness.len() != RING_WIDTH
                || masked.blind.len() != RING_WIDTH
                || q_slice.len() != RING_WIDTH
            {
                return Err(SuccinctVeilError::InvalidShape("ring claim width"));
            }
            let witness = masked
                .witness
                .iter()
                .map(|value| expressions.unmask(*value))
                .collect::<Vec<_>>();
            let blind = masked
                .blind
                .iter()
                .map(|value| expressions.unmask(*value))
                .collect::<Vec<_>>();
            let scaled_blind = scale_ring_expressions(&blind, link.challenge);
            for ((q, witness), blind) in q_slice.iter().zip(&witness).zip(&scaled_blind) {
                builder.assert_zero(&LinearCombination::constant(*q).add(witness).add(blind));
            }
            let x_outer = quirky_x_outer_full(point);
            let weights = pcs::ring_switch::build_claim_weights(point.z_skip, x_outer[0]);
            let witness_value = dot(&witness, &weights);
            if index == 0 {
                builder.assert_zero(&w.add(&witness_value));
            } else {
                builder.assert_zero(&computed_c.add(&witness_value));
            }
            values[index] = pcs::ring_switch::claim_check(&weights, q_slice);
        }
    }
    if expressions.cursor != mask_count {
        return Err(SuccinctVeilError::InvalidShape("mask expression cursor"));
    }

    let ab = ZClaim {
        point: ab_point,
        value: values[0],
    };
    let c = ZClaim {
        point: c_point,
        value: values[1],
    };
    let circuit = builder.finish();
    layout
        .shifted_circuit_certificate(with_ring_link)
        .validate(&circuit)?;
    Ok((circuit, ab, c))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_succinct_veil_r1cs<Ch: Challenger + Clone + Send>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed: Vec<F128>,
    b_packed: Vec<F128>,
    z_lincheck: Vec<u8>,
    lincheck_circuit: &dyn LincheckCircuit,
    lig_config: &pcs::ligerito::ProverConfig,
    rng: &mut ZkRng,
    public_packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<PublicPackedDirectClaim>,
    zerocheck_source: Option<&mut dyn SuccinctZerocheckSource<Ch>>,
    challenger: &mut Ch,
) -> Result<(SuccinctVeilProof, Commitment), SuccinctVeilError> {
    let layout = validate_succinct_parameters(r1cs, pcs_params)?;
    certify_flock_piop_soundness(r1cs, lincheck_circuit)?;
    validate_batch_opening(
        pcs_params,
        &lig_config.queries,
        &lig_config.grinding_bits,
        &lig_config.fold_grinding_bits,
        &fold_rounds_of(lig_config.initial_k, &lig_config.recursive_ks),
    )?;
    let mut masks = vec![F128::ZERO; layout.observed_count()];
    let mut mask_rng = rng.fork(b"succinct-veil-transcript-masks");
    mask_rng.fill_f128(&mut masks);

    let mut nonce_rng = rng.fork(b"succinct-veil-public-nonces");
    let proof_nonce = sample_nonce(&mut nonce_rng);
    let tree_nonces = InitialTreeNonces {
        outer: sample_nonce(&mut nonce_rng),
        veil_linear: sample_nonce(&mut nonce_rng),
        veil_hadamard: sample_nonce(&mut nonce_rng),
    };
    let outer_ro = challenger.ro_context(tree_nonces.outer);
    let veil_linear_ro = challenger.ro_context(tree_nonces.veil_linear);
    let veil_hadamard_ro = challenger.ro_context(tree_nonces.veil_hadamard);

    let placeholder = CircuitBuilder::new(layout.observed_count()).finish();
    let veil_parameters = ConstraintParameters::succinct_flock_secure();
    let mut veil_rng = rng.fork(b"succinct-veil-inner-proof");
    let veil_commitment = commit_constraint_inputs(
        &placeholder,
        &masks,
        veil_parameters,
        &mut veil_rng,
        &veil_linear_ro,
    )?;
    let mut witness_rng = rng.fork(b"succinct-veil-witness-pcs");
    let (commitment, prover_data) = pcs::commit::commit_zk_with_ro(
        &z_packed,
        pcs_params,
        &mut witness_rng,
        &outer_ro,
        RoChannel::Witness,
    );

    bind_statement(challenger, r1cs, &commitment, &proof_nonce);
    observe_tree_nonces(challenger, &tree_nonces);
    challenger.observe_label(MASK_ROOT_LABEL);
    challenger.observe_bytes(&veil_commitment.root());
    let circuit_start = challenger.clone();

    let padding = r1cs.padding_spec();
    let (honest_zc, zc_claim, s_hat_v_c) = {
        let a_bytes = unsafe {
            std::slice::from_raw_parts(
                a_packed.as_ptr() as *const u8,
                std::mem::size_of_val(a_packed.as_slice()),
            )
        };
        let b_bytes = unsafe {
            std::slice::from_raw_parts(
                b_packed.as_ptr() as *const u8,
                std::mem::size_of_val(b_packed.as_slice()),
            )
        };
        let z_bytes = unsafe {
            std::slice::from_raw_parts(
                z_packed.as_ptr() as *const u8,
                std::mem::size_of_val(z_packed.as_slice()),
            )
        };
        match zerocheck_source {
            Some(source) => source.emit(
                SuccinctZerocheckInputs {
                    a_packed: a_bytes,
                    b_packed: b_bytes,
                    c_packed: z_bytes,
                    m: r1cs.m,
                    padding: &padding,
                },
                &masks,
                challenger,
            )?,
            None => {
                let mut masking = MaskingChallenger::new(challenger, &masks);
                let (proof, claim, s_hat_v_c) = zerocheck::prove_packed_padded_capture_s_hat_v_c(
                    a_bytes,
                    b_bytes,
                    z_bytes,
                    r1cs.m,
                    &padding,
                    &mut masking,
                );
                if masking.cursor != 2 * layout.ell + 2 * layout.zc_rounds + 2 {
                    return Err(SuccinctVeilError::InvalidShape(
                        "zerocheck mask observation count",
                    ));
                }
                (proof, claim, Some(s_hat_v_c))
            }
        }
    };
    flock_core::scratch::give_f128(a_packed);
    flock_core::scratch::give_f128(b_packed);

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);
    let zc_mask_count = 2 * layout.ell + 2 * layout.zc_rounds + 2;
    let (honest_lc, lc_claim, z_vec) = {
        let mut masking = MaskingChallenger {
            inner: challenger,
            masks: &masks,
            cursor: zc_mask_count,
        };
        let result = lincheck::prove_padded_capture_z_vec(
            &z_lincheck,
            r1cs.m,
            r1cs.k_log,
            r1cs.k_skip,
            r1cs.useful_bits,
            lincheck_circuit,
            &x_ab,
            &mut masking,
        );
        if masking.cursor != layout.piop_count() {
            return Err(SuccinctVeilError::InvalidShape(
                "lincheck mask observation count",
            ));
        }
        result
    };
    drop(z_lincheck);

    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };
    let (masked_zerocheck, masked_lincheck) =
        mask_proofs(&honest_zc, &honest_lc, &masks[..layout.piop_count()]);

    let points = [&ab.point, &c.point];
    let x_fulls = points
        .iter()
        .map(|point| quirky_x_outer_full(point))
        .collect::<Vec<_>>();
    let s_hat_v_ab = if r1cs.k_log >= pcs::LOG_PACKING {
        Some(pcs::ring_switch::s_hat_v_from_z_vec(
            &z_vec,
            &lc_claim.r_inner_rest[1..],
        ))
    } else {
        None
    };
    let witness_slices = vec![
        s_hat_v_ab.unwrap_or_else(|| pcs::ring_switch::s_hat_v_at_point(&z_packed, &x_fulls[0])),
        s_hat_v_c.unwrap_or_else(|| pcs::ring_switch::s_hat_v_at_point(&z_packed, &x_fulls[1])),
    ];
    let witness_len = z_packed.len();
    let g_top = &prover_data.zk_blind[witness_len..];
    let blind_slices = x_fulls
        .iter()
        .map(|point| pcs::ring_switch::s_hat_v_at_point(g_top, point))
        .collect::<Vec<_>>();
    let masked_ring_claims = mask_ring_claims(
        &witness_slices,
        &blind_slices,
        &masks[layout.piop_count()..],
    );
    observe_masked_ring_claims(challenger, &masked_ring_claims);

    let mut pd = public_packed_direct(challenger)
        .into_iter()
        .map(|claim| claim.0)
        .collect::<Vec<_>>();
    if pd.len() != PUBLIC_DIRECT_CLAIM_COUNT {
        return Err(SuccinctVeilError::InvalidShape(
            "public packed-direct claim count",
        ));
    }
    let public_direct_blind_values = pd
        .iter()
        .map(|claim| claim.evaluate(g_top))
        .collect::<Vec<_>>();
    observe_direct_blinds(challenger, &public_direct_blind_values);
    let blind_bits = pcs::ligerito::l0_derived_grind_bits(&lig_config.fold_grinding_bits);
    if !(1..=MAX_BLIND_GRINDING_BITS).contains(&blind_bits) {
        return Err(SuccinctVeilError::InvalidShape("blind grinding bits"));
    }
    let blind_grind_nonce = challenger.grind_pow(blind_bits);
    if blind_grind_nonce >= MAX_BLIND_GRIND_TRIALS {
        return Err(SuccinctVeilError::GrindingLimitExceeded);
    }
    let blind_challenge = sample_nonzero(challenger);

    let q_slices = witness_slices
        .iter()
        .zip(&blind_slices)
        .map(|(witness, blind)| {
            let scaled = pcs::ring_switch::scale_s_hat_v(blind, blind_challenge);
            witness
                .iter()
                .zip(scaled)
                .map(|(witness, blind)| *witness + blind)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    observe_blinded_ring_claims(challenger, &q_slices);
    for (claim, blind_value) in pd.iter_mut().zip(&public_direct_blind_values) {
        claim.value += blind_challenge * *blind_value;
    }
    let mut q_packed = z_packed;
    q_packed
        .par_iter_mut()
        .zip(g_top.par_iter())
        .for_each(|(witness, blind)| *witness += blind_challenge * *blind);

    let mut circuit_challenger = circuit_start;
    let (circuit, circuit_ab, circuit_c) = shifted_verifier_circuit(
        r1cs,
        &masked_zerocheck,
        &masked_lincheck,
        Some(RingLink {
            masked: &masked_ring_claims,
            q_slices: &q_slices,
            challenge: blind_challenge,
        }),
        lincheck_circuit,
        &mut circuit_challenger,
    )?;
    if circuit_ab.point != ab.point || circuit_c.point != c.point {
        return Err(SuccinctVeilError::InvalidShape(
            "shifted verifier output points",
        ));
    }
    certify_constraint_soundness(&circuit, veil_parameters)?;

    // The VEIL constraint proof and the PCS opening use independent terminal
    // transcript branches after their shared linkage data is bound.
    let mut pcs_challenger = challenger.clone();
    pcs_challenger.observe_label(PCS_FORK_LABEL);
    let mut veil_challenger = challenger.clone();
    veil_challenger.observe_label(VEIL_FORK_LABEL);
    let x_refs = x_fulls.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let precomputed = q_slices
        .iter()
        .map(|slice| Some(slice.as_slice()))
        .collect::<Vec<_>>();
    let (pcs_open, veil) = rayon::join(
        || {
            pcs::open_batch_mixed_ligerito_preblinded_ro(
                pcs::PreblindedOpening {
                    q_packed,
                    prover_data: &prover_data,
                    commitment: &commitment,
                    challenge: blind_challenge,
                    x_outers: &x_refs,
                    precomputed_s_hat_v: &precomputed,
                    packed_direct: &pd,
                    padding: &padding,
                    lig_config,
                    ro: &outer_ro,
                    channel: RoChannel::Witness,
                },
                &mut pcs_challenger,
            )
        },
        || {
            prove_constraints_from_commitment(
                &circuit,
                veil_commitment,
                &mut veil_rng,
                &mut veil_challenger,
                &veil_hadamard_ro,
            )
        },
    );
    if !ligerito_grinding_is_bounded(&pcs_open.ligerito) {
        return Err(SuccinctVeilError::GrindingLimitExceeded);
    }
    let veil = veil?;
    Ok((
        SuccinctVeilProof {
            proof_nonce,
            tree_nonces,
            masked_zerocheck,
            masked_lincheck,
            masked_ring_claims,
            public_direct_blind_values,
            blind_grind_nonce,
            pcs_open,
            veil,
        },
        commitment,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_succinct_veil_r1cs<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &SuccinctVeilProof,
    commitment: &Commitment,
    lincheck_circuit: &dyn LincheckCircuit,
    lig_config: &pcs::ligerito::VerifierConfig,
    public_packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<PublicPackedDirectClaimValue>,
    challenger: &mut Ch,
) -> Result<(), SuccinctVeilError> {
    validate_succinct_parameters(r1cs, pcs_params)?;
    certify_flock_piop_soundness(r1cs, lincheck_circuit)?;
    validate_batch_opening(
        pcs_params,
        &lig_config.queries,
        &lig_config.grinding_bits,
        &lig_config.fold_grinding_bits,
        &fold_rounds_of(lig_config.initial_k, &lig_config.recursive_ks),
    )?;
    if commitment.params != *pcs_params
        || proof.veil.parameters != ConstraintParameters::succinct_flock_secure()
    {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    let outer_ro = challenger.ro_context(proof.tree_nonces.outer);
    let veil_linear_ro = challenger.ro_context(proof.tree_nonces.veil_linear);
    let veil_hadamard_ro = challenger.ro_context(proof.tree_nonces.veil_hadamard);
    bind_statement(challenger, r1cs, commitment, &proof.proof_nonce);
    observe_tree_nonces(challenger, &proof.tree_nonces);
    challenger.observe_label(MASK_ROOT_LABEL);
    challenger.observe_bytes(&proof.veil.linear.commitment);
    let circuit_start = challenger.clone();
    let (_, preliminary_ab, preliminary_c) = shifted_verifier_circuit(
        r1cs,
        &proof.masked_zerocheck,
        &proof.masked_lincheck,
        None,
        lincheck_circuit,
        challenger,
    )?;

    if proof.masked_ring_claims.len() != RING_CLAIM_COUNT
        || proof.pcs_open.ring_switches.len() != RING_CLAIM_COUNT
    {
        return Err(SuccinctVeilError::InvalidShape("ring claim count"));
    }
    observe_masked_ring_claims(challenger, &proof.masked_ring_claims);
    let pd = public_packed_direct(challenger);
    if pd.len() != PUBLIC_DIRECT_CLAIM_COUNT
        || proof.public_direct_blind_values.len() != PUBLIC_DIRECT_CLAIM_COUNT
    {
        return Err(SuccinctVeilError::InvalidShape(
            "packed-direct blind values",
        ));
    }
    observe_direct_blinds(challenger, &proof.public_direct_blind_values);
    let blind_bits = pcs::ligerito::l0_derived_grind_bits(&lig_config.fold_grinding_bits);
    if !(1..=MAX_BLIND_GRINDING_BITS).contains(&blind_bits)
        || proof.blind_grind_nonce >= MAX_BLIND_GRIND_TRIALS
        || !challenger.verify_pow(proof.blind_grind_nonce, blind_bits)
    {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    let blind_challenge = sample_nonzero(challenger);

    let q_slices = proof
        .pcs_open
        .ring_switches
        .iter()
        .map(|ring| ring.s_hat_v.clone())
        .collect::<Vec<_>>();
    observe_blinded_ring_claims(challenger, &q_slices);
    let mut circuit_challenger = circuit_start;
    let (circuit, ab, c) = shifted_verifier_circuit(
        r1cs,
        &proof.masked_zerocheck,
        &proof.masked_lincheck,
        Some(RingLink {
            masked: &proof.masked_ring_claims,
            q_slices: &q_slices,
            challenge: blind_challenge,
        }),
        lincheck_circuit,
        &mut circuit_challenger,
    )?;
    if ab.point != preliminary_ab.point || c.point != preliminary_c.point {
        return Err(SuccinctVeilError::InvalidShape(
            "shifted verifier output points",
        ));
    }
    certify_constraint_soundness(&circuit, proof.veil.parameters)?;

    let mut pcs_challenger = challenger.clone();
    pcs_challenger.observe_label(PCS_FORK_LABEL);
    let mut veil_challenger = challenger.clone();
    veil_challenger.observe_label(VEIL_FORK_LABEL);
    let pd_refs = pd
        .iter()
        .zip(&proof.public_direct_blind_values)
        .map(|(claim, blind)| pcs::PackedDirectClaimRef {
            point: claim.point.as_slice(),
            value: claim.value + blind_challenge * *blind,
        })
        .collect::<Vec<_>>();
    if !ligerito_grinding_is_bounded(&proof.pcs_open.ligerito) {
        return Err(SuccinctVeilError::GrindingLimitExceeded);
    }
    flock_core::verifier::verify_claims_ligerito_with_config_pd_preblinded_ro(
        flock_core::verifier::PreblindedClaimVerification {
            commitment,
            claims: &[ab, c],
            packed_direct: &pd_refs,
            pcs_open: &proof.pcs_open,
            pcs_params,
            lig_v_config: lig_config,
            challenge: blind_challenge,
            ro: &outer_ro,
            channel: RoChannel::Witness,
        },
        &mut pcs_challenger,
    )?;
    verify_constraints(
        &circuit,
        &proof.veil,
        &mut veil_challenger,
        &veil_linear_ro,
        &veil_hadamard_ro,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests;

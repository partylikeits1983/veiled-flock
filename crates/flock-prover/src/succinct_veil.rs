//! Succinct experimental VEIL compilation for FLOCK's algebraic transcript.
//!
//! The witness stays in FLOCK's hiding Ligerito commitment. Only the
//! zerocheck/lincheck messages are additively masked. A small VEIL circuit
//! proves that subtracting those masks (addition in characteristic two)
//! yields an accepting FLOCK verifier transcript whose two output claims are
//! the claims opened by Ligerito.

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
use serde::{Deserialize, Serialize};
use veil_f128::{
    ArithmeticCircuit, CircuitBuilder, ConstraintError, ConstraintParameters, ConstraintProof,
    LinearCombination, commit_constraint_inputs, prove_constraints_from_commitment,
    verify_constraints,
};

use crate::prover::open_claims_with_precomputed_ligerito_pd_ro;

const MASK_ROOT_LABEL: &[u8] = b"veil-flock-mask-root";
const CLAIMS_LABEL: &[u8] = b"veil-flock-output-claims";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SuccinctVeilProof {
    pub proof_nonce: [u8; 32],
    /// Exactly the zerocheck values observed by Fiat--Shamir, each one-time
    /// padded. The derived C evaluation is carried once in `c_value`.
    pub masked_zerocheck: MaskedZerocheckProof,
    pub masked_lincheck: LincheckProof,
    /// The two values checked by the hiding PCS. Randomizer rows in the ZK
    /// circuit make these evaluation claims witness-independent.
    pub ab_value: F128,
    pub c_value: F128,
    pub pcs_open: pcs::BatchOpeningProofLigerito,
    pub veil: ConstraintProof,
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
/// evaluations of the caller's committed pseudo-witness.
pub struct RomZerocheckSimulator {
    rng: ZkRng,
    z: F128,
    rhos: Vec<F128>,
}

impl RomZerocheckSimulator {
    pub fn new(m: usize, seed: [u8; 32]) -> Self {
        let mut rng = ZkRng::from_seed(seed);
        let mut z_value = [F128::ZERO; 1];
        rng.fill_f128(&mut z_value);
        let mut rhos = vec![F128::ZERO; m - zerocheck::K_SKIP];
        rng.fill_f128(&mut rhos);
        while rhos
            .last()
            .is_some_and(|rho| rho.is_zero() || *rho == F128::ONE)
        {
            rng.fill_f128(rhos.last_mut().map(std::slice::from_mut).unwrap());
        }
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
        let target = terminal.a_eval * terminal.b_eval;
        let mut rounds = Vec::with_capacity(n_mlv);
        for i in 0..n_mlv {
            let rho = self.rhos[i];
            let one_plus_rho = F128::ONE + rho;
            let r_eq = r[zerocheck::K_SKIP + i];
            let one_plus_r_eq = F128::ONE + r_eq;
            let g1 = self.random_vec(1)[0];
            let g0 = (running + r_eq * g1) * one_plus_r_eq.inv();
            let g_inf = if i + 1 == n_mlv {
                let denominator = rho * one_plus_rho;
                if denominator.is_zero() {
                    return Err(SuccinctVeilError::DegenerateSimulation);
                }
                (target + g0 * one_plus_rho + g1 * rho) * denominator.inv()
            } else {
                self.random_vec(1)[0]
            };
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

#[derive(Clone, Copy, Debug)]
struct MaskLayout {
    ell: usize,
    zc_rounds: usize,
    lc_rounds: usize,
    z_partial: usize,
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

    fn observed_count(self) -> usize {
        2 * self.ell + 2 * self.zc_rounds + 2 + 2 * self.lc_rounds + self.z_partial
    }
}

fn validate_succinct_parameters(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
) -> Result<MaskLayout, SuccinctVeilError> {
    if !pcs_params.zk || r1cs.zk.is_none() || pcs_params.m != r1cs.m {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    MaskLayout::new(r1cs)
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

fn observe_claims<C: Challenger>(challenger: &mut C, ab: F128, c: F128) {
    challenger.observe_label(CLAIMS_LABEL);
    challenger.observe_f128(ab);
    challenger.observe_f128(c);
}

/// Replay the public, masked PIOP transcript and construct
/// `C'(h) = C(masked + h)`. The returned points are public; the returned
/// values are the two explicit PCS claim values supplied by the proof.
fn shifted_verifier_circuit<C: Challenger>(
    r1cs: &BlockR1cs,
    zc: &MaskedZerocheckProof,
    lc: &LincheckProof,
    ab_value: F128,
    c_value: F128,
    lincheck_circuit: &dyn LincheckCircuit,
    challenger: &mut C,
) -> Result<(ArithmeticCircuit, ZClaim, ZClaim), SuccinctVeilError> {
    let layout = MaskLayout::new(r1cs)?;
    if zc.round1_ab.len() != layout.ell
        || zc.round1_c.len() != layout.ell
        || zc.multilinear_rounds.len() != layout.zc_rounds
        || lc.rounds.len() != layout.lc_rounds
        || lc.z_partial.len() != layout.z_partial
    {
        return Err(SuccinctVeilError::InvalidShape("PIOP proof geometry"));
    }

    let mut builder = CircuitBuilder::new(layout.observed_count());
    let mut expressions = ExpressionCursor::new(layout.observed_count());

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
    builder.assert_zero(&computed_c.add(&LinearCombination::constant(c_value)));

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
    builder.assert_zero(&w.add(&LinearCombination::constant(ab_value)));
    if expressions.cursor != layout.observed_count() {
        return Err(SuccinctVeilError::InvalidShape("mask expression cursor"));
    }

    lc_challenges.reverse();
    let ab = ZClaim {
        point: r1cs.ab_claim_point(r_inner_skip, &lc_challenges, &x_ab.x_outer),
        value: ab_value,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(z, &r[zerocheck::K_SKIP..]),
        value: c_value,
    };
    Ok((builder.finish(), ab, c))
}

#[allow(clippy::too_many_arguments)]
pub fn prove_succinct_veil_r1cs<Ch: Challenger + Clone + Send>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed: Vec<F128>,
    b_packed: Vec<F128>,
    z_lincheck: Vec<u8>,
    lincheck_circuit: &dyn LincheckCircuit,
    lig_config: &pcs::ligerito::ProverConfig,
    rng: &mut ZkRng,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<pcs::PackedDirectClaim>,
    zerocheck_source: Option<&mut dyn SuccinctZerocheckSource<Ch>>,
    challenger: &mut Ch,
) -> Result<(SuccinctVeilProof, Commitment), SuccinctVeilError> {
    let layout = validate_succinct_parameters(r1cs, pcs_params)?;
    let mut masks = vec![F128::ZERO; layout.observed_count()];
    let mut mask_rng = rng.fork(b"succinct-veil-transcript-masks");
    mask_rng.fill_f128(&mut masks);

    let mut nonce_rng = rng.fork(b"succinct-veil-proof-nonce");
    let mut nonce_words = [0u64; 4];
    nonce_rng.fill_u64s(&mut nonce_words);
    let mut proof_nonce = [0u8; 32];
    for (chunk, word) in proof_nonce
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip(nonce_words)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    let ro = challenger.ro_context(proof_nonce);

    let placeholder = CircuitBuilder::new(layout.observed_count()).finish();
    let veil_parameters = ConstraintParameters::succinct_flock_experimental();
    let mut veil_rng = rng.fork(b"succinct-veil-inner-proof");
    let veil_commitment =
        commit_constraint_inputs(&placeholder, &masks, veil_parameters, &mut veil_rng, &ro)?;
    let mut witness_rng = rng.fork(b"succinct-veil-witness-pcs");
    let (commitment, prover_data) = pcs::commit::commit_zk_with_ro(
        &z_packed,
        pcs_params,
        &mut witness_rng,
        &ro,
        RoChannel::Witness,
    );

    bind_statement(challenger, r1cs, &commitment, &proof_nonce);
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
        if masking.cursor != masks.len() {
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
    let (masked_zerocheck, masked_lincheck) = mask_proofs(&honest_zc, &honest_lc, &masks);

    let mut circuit_challenger = circuit_start;
    let (circuit, circuit_ab, circuit_c) = shifted_verifier_circuit(
        r1cs,
        &masked_zerocheck,
        &masked_lincheck,
        ab.value,
        c.value,
        lincheck_circuit,
        &mut circuit_challenger,
    )?;
    if circuit_ab != ab {
        return Err(SuccinctVeilError::InvalidShape(
            "shifted verifier AB output claim",
        ));
    }
    if circuit_c != c {
        return Err(SuccinctVeilError::InvalidShape(
            "shifted verifier C output claim",
        ));
    }

    observe_claims(challenger, ab.value, c.value);
    let pd = packed_direct(challenger);
    // Ligerito's prover and verifier historically did not need to preserve a
    // byte-identical transcript state after the terminal opening. Fork the
    // inner VEIL transcript here, after all linkage data is bound but before
    // entering that terminal protocol.
    let mut veil_challenger = challenger.clone();
    veil_challenger.observe_label(b"veil-flock-inner-fork");
    let s_hat_v_ab = if r1cs.k_log >= pcs::LOG_PACKING {
        Some(pcs::ring_switch::s_hat_v_from_z_vec(
            &z_vec,
            &lc_claim.r_inner_rest[1..],
        ))
    } else {
        None
    };
    // The terminal proofs use independent transcripts and randomness.
    let (pcs_open, veil) = rayon::join(
        || {
            open_claims_with_precomputed_ligerito_pd_ro(
                z_packed,
                &prover_data,
                &commitment,
                &[ab.clone(), c.clone()],
                &[s_hat_v_ab.as_deref(), s_hat_v_c.as_deref()],
                &pd,
                &padding,
                lig_config,
                &ro,
                RoChannel::Witness,
                challenger,
            )
        },
        || {
            prove_constraints_from_commitment(
                &circuit,
                veil_commitment,
                &mut veil_rng,
                &mut veil_challenger,
                &ro,
            )
        },
    );
    let veil = veil?;
    Ok((
        SuccinctVeilProof {
            proof_nonce,
            masked_zerocheck,
            masked_lincheck,
            ab_value: ab.value,
            c_value: c.value,
            pcs_open,
            veil,
        },
        commitment,
    ))
}

#[allow(clippy::too_many_arguments)]
pub fn verify_succinct_veil_r1cs<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &SuccinctVeilProof,
    commitment: &Commitment,
    lincheck_circuit: &dyn LincheckCircuit,
    lig_config: &pcs::ligerito::VerifierConfig,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<(Vec<F128>, F128)>,
    challenger: &mut Ch,
) -> Result<(), SuccinctVeilError> {
    validate_succinct_parameters(r1cs, pcs_params)?;
    if commitment.params != *pcs_params
        || proof.veil.parameters != ConstraintParameters::succinct_flock_experimental()
    {
        return Err(SuccinctVeilError::InvalidParameters);
    }
    let ro = challenger.ro_context(proof.proof_nonce);
    bind_statement(challenger, r1cs, commitment, &proof.proof_nonce);
    challenger.observe_label(MASK_ROOT_LABEL);
    challenger.observe_bytes(&proof.veil.linear.commitment);
    let (circuit, ab, c) = shifted_verifier_circuit(
        r1cs,
        &proof.masked_zerocheck,
        &proof.masked_lincheck,
        proof.ab_value,
        proof.c_value,
        lincheck_circuit,
        challenger,
    )?;
    observe_claims(challenger, proof.ab_value, proof.c_value);
    let pd = packed_direct(challenger);
    let mut veil_challenger = challenger.clone();
    veil_challenger.observe_label(b"veil-flock-inner-fork");
    let pd_refs = pd
        .iter()
        .map(|(point, value)| pcs::PackedDirectClaimRef {
            point: point.as_slice(),
            value: *value,
        })
        .collect::<Vec<_>>();
    flock_core::verifier::verify_claims_ligerito_with_config_pd_ro(
        commitment,
        &[ab, c],
        &pd_refs,
        &proof.pcs_open,
        pcs_params,
        lig_config,
        &ro,
        RoChannel::Witness,
        challenger,
    )?;
    verify_constraints(&circuit, &proof.veil, &mut veil_challenger, &ro)?;
    Ok(())
}

#[cfg(test)]
mod tests;

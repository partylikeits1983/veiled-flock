//! VEIL's inner arithmetic-constraint compiler over `F128`.
//!
//! Transcript masks form a private witness vector. Two dummy products mask
//! the three Hadamard dot claims, following VEIL's R1CS compiler: for random
//! `r,s,t` we append
//! `(r,s,rs)` and `(r+1,t,(r+1)t)`. Their two product rows make every exposed
//! multiplication claim witness-independent, while the linear relation
//! `r + (r+1) + 1 = 0` ties the padding together.
//! Linear constraints are batched into one ZK dot-product proof. Multiplicative
//! constraints are batched into one ZK Hadamard-plus-dot proof, and the three
//! resulting dot claims are linked back to the same witness vector by three
//! additional linear constraints.

use flock_core::{
    challenger::Challenger,
    field::F128,
    ro::{RoChannel, RoContext},
    zk::MaskSampler,
};
use serde::{Deserialize, Serialize};

use crate::{
    dot_product::{
        DotProductError, DotProductProof, VectorParameters, commit_vectors, prove_dot_product,
        sample_not_zero_or_one, verify_dot_product,
    },
    hadamard::{
        HadamardError, HadamardProof, commit_hadamard, prove_hadamard_and_dots,
        verify_hadamard_and_dots,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinearCombination {
    pub constant: F128,
    pub terms: Vec<(usize, F128)>,
}

impl LinearCombination {
    pub fn zero() -> Self {
        Self {
            constant: F128::ZERO,
            terms: Vec::new(),
        }
    }

    pub fn constant(value: F128) -> Self {
        Self {
            constant: value,
            terms: Vec::new(),
        }
    }

    pub fn variable(index: usize) -> Self {
        Self {
            constant: F128::ZERO,
            terms: vec![(index, F128::ONE)],
        }
    }

    pub fn evaluate(&self, witness: &[F128]) -> Result<F128, ConstraintError> {
        let mut value = self.constant;
        for &(index, coefficient) in &self.terms {
            let variable = witness
                .get(index)
                .ok_or(ConstraintError::InvalidVariable(index))?;
            value += coefficient * *variable;
        }
        Ok(value)
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.constant += other.constant;
        result.terms.extend_from_slice(&other.terms);
        result.normalize();
        result
    }

    pub fn scale(&self, scalar: F128) -> Self {
        if scalar.is_zero() {
            return Self::zero();
        }
        let mut result = self.clone();
        result.constant *= scalar;
        for (_, coefficient) in &mut result.terms {
            *coefficient *= scalar;
        }
        result.normalize();
        result
    }

    fn normalize(&mut self) {
        self.terms.sort_unstable_by_key(|(index, _)| *index);
        let mut merged: Vec<(usize, F128)> = Vec::with_capacity(self.terms.len());
        for (index, coefficient) in self.terms.drain(..) {
            if coefficient.is_zero() {
                continue;
            }
            if let Some((last_index, last_coefficient)) = merged.last_mut()
                && *last_index == index
            {
                *last_coefficient += coefficient;
                if last_coefficient.is_zero() {
                    merged.pop();
                }
                continue;
            }
            merged.push((index, coefficient));
        }
        self.terms = merged;
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct MultiplicationGate {
    left: LinearCombination,
    right: LinearCombination,
    output: LinearCombination,
    materialized_output: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticCircuit {
    num_inputs: usize,
    num_variables: usize,
    multiplications: Vec<MultiplicationGate>,
    linear_constraints: Vec<LinearCombination>,
}

impl ArithmeticCircuit {
    pub fn num_inputs(&self) -> usize {
        self.num_inputs
    }

    pub fn num_variables(&self) -> usize {
        self.num_variables
    }

    pub fn num_multiplications(&self) -> usize {
        self.multiplications.len()
    }

    pub fn num_linear_constraints(&self) -> usize {
        self.linear_constraints.len()
    }

    pub fn complete_witness(&self, inputs: &[F128]) -> Result<Vec<F128>, ConstraintError> {
        if inputs.len() != self.num_inputs {
            return Err(ConstraintError::WrongInputLength {
                expected: self.num_inputs,
                actual: inputs.len(),
            });
        }
        let mut witness = inputs.to_vec();
        witness.reserve(self.multiplications.len());
        for gate in &self.multiplications {
            if let Some(output) = gate.materialized_output {
                if output != witness.len() {
                    return Err(ConstraintError::MalformedCircuit);
                }
                let value = gate.left.evaluate(&witness)? * gate.right.evaluate(&witness)?;
                witness.push(value);
            }
        }
        if witness.len() != self.num_variables {
            return Err(ConstraintError::MalformedCircuit);
        }
        Ok(witness)
    }

    pub fn is_satisfied(&self, witness: &[F128]) -> Result<bool, ConstraintError> {
        if witness.len() != self.num_variables {
            return Err(ConstraintError::WrongWitnessLength {
                expected: self.num_variables,
                actual: witness.len(),
            });
        }
        for gate in &self.multiplications {
            if gate.left.evaluate(witness)? * gate.right.evaluate(witness)?
                != gate.output.evaluate(witness)?
            {
                return Ok(false);
            }
        }
        for constraint in &self.linear_constraints {
            if !constraint.evaluate(witness)?.is_zero() {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[derive(Clone, Debug)]
pub struct CircuitBuilder {
    num_inputs: usize,
    num_variables: usize,
    multiplications: Vec<MultiplicationGate>,
    linear_constraints: Vec<LinearCombination>,
}

impl CircuitBuilder {
    pub fn new(num_inputs: usize) -> Self {
        assert!(
            num_inputs > 0,
            "VEIL circuit needs at least one masked input"
        );
        Self {
            num_inputs,
            num_variables: num_inputs,
            multiplications: Vec::new(),
            linear_constraints: Vec::new(),
        }
    }

    pub fn input(&self, index: usize) -> LinearCombination {
        assert!(index < self.num_inputs);
        LinearCombination::variable(index)
    }

    pub fn constant(&self, value: F128) -> LinearCombination {
        LinearCombination::constant(value)
    }

    pub fn add(&self, left: &LinearCombination, right: &LinearCombination) -> LinearCombination {
        left.add(right)
    }

    pub fn scale(&self, value: &LinearCombination, scalar: F128) -> LinearCombination {
        value.scale(scalar)
    }

    pub fn mul(
        &mut self,
        left: &LinearCombination,
        right: &LinearCombination,
    ) -> LinearCombination {
        let output = self.num_variables;
        self.num_variables += 1;
        self.multiplications.push(MultiplicationGate {
            left: left.clone(),
            right: right.clone(),
            output: LinearCombination::variable(output),
            materialized_output: Some(output),
        });
        LinearCombination::variable(output)
    }

    /// Assert a multiplication whose output is already represented by a
    /// linear expression. Unlike [`Self::mul`], this allocates no witness
    /// variable. FLOCK's `C = I` R1CS uses this path for every circuit row.
    pub fn assert_mul(
        &mut self,
        left: &LinearCombination,
        right: &LinearCombination,
        output: &LinearCombination,
    ) {
        self.multiplications.push(MultiplicationGate {
            left: left.clone(),
            right: right.clone(),
            output: output.clone(),
            materialized_output: None,
        });
    }

    pub fn assert_zero(&mut self, value: &LinearCombination) {
        self.linear_constraints.push(value.clone());
    }

    pub fn finish(self) -> ArithmeticCircuit {
        ArithmeticCircuit {
            num_inputs: self.num_inputs,
            num_variables: self.num_variables,
            multiplications: self.multiplications,
            linear_constraints: self.linear_constraints,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintProof {
    pub parameters: ConstraintParameters,
    pub num_variables: usize,
    pub num_multiplications: usize,
    pub hadamard: HadamardProof,
    pub linear: DotProductProof,
}

/// First phase of the VEIL compilation. The caller may bind [`Self::root`]
/// into an outer Fiat--Shamir transcript before that transcript derives the
/// challenges used to construct the shifted verifier circuit. This breaks
/// the otherwise-circular dependency between the mask commitment and those
/// challenges.
pub struct ConstraintCommitment {
    circuit_inputs: usize,
    padded_witness: Vec<F128>,
    linear_data: crate::dot_product::DotProductProverData,
    parameters: ConstraintParameters,
}

impl ConstraintCommitment {
    pub fn root(&self) -> flock_core::merkle::Hash {
        self.linear_data.root()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintParameters {
    pub linear_padding: usize,
    pub hadamard_padding: usize,
    pub inverse_rate: usize,
}

impl ConstraintParameters {
    /// Fail-closed profile for the succinct FLOCK transcript compiler.
    ///
    /// The active caller must additionally run [`certify_constraint_soundness`]
    /// against the exact shifted circuit. The certificate uses the actual
    /// operand and product-code dimensions, the finite-length unique-decoding
    /// backoff, and additive (rather than minimum-per-round) error composition.
    pub const fn succinct_flock_secure() -> Self {
        Self {
            linear_padding: 160,
            hadamard_padding: 160,
            inverse_rate: 8,
        }
    }

    fn validate(self) -> Result<Self, ConstraintError> {
        if self.linear_padding == 0
            || self.hadamard_padding == 0
            || self.inverse_rate < 2
            || !self.inverse_rate.is_power_of_two()
        {
            return Err(ConstraintError::InvalidParameters);
        }
        Ok(self)
    }
}

impl Default for ConstraintParameters {
    fn default() -> Self {
        Self::succinct_flock_secure()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstraintError {
    InvalidParameters,
    WrongInputLength { expected: usize, actual: usize },
    WrongWitnessLength { expected: usize, actual: usize },
    InvalidVariable(usize),
    MalformedCircuit,
    UnsatisfiedCircuit,
    WrongProofShape,
    LinearClaimMismatch,
    ChallengeSamplingLimitExceeded,
    InsufficientSoundness,
    Dot(DotProductError),
    Hadamard(HadamardError),
}

/// Minimum soundness floor accepted by the production succinct compiler.
/// The exact active profile currently clears this floor without treating
/// concrete SHA-256 as an information-theoretic primitive.
pub const SUCCINCT_FLOCK_MIN_SOUNDNESS_BITS: f64 = 100.0;

/// Executable additive soundness ledger for the live VEIL constraint layer.
///
/// The dot-product term follows VEIL Lemma 3.4:
/// `eps_pg + (1-gamma)^queries`. The Hadamard term follows its binding theorem:
/// `eps_pg + eps_pg_product + eps_linear_bias +
/// (1-gamma_product)^queries`. The remaining two terms bind the Hadamard rows
/// to the shifted circuit and batch all resulting linear constraints.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ConstraintSoundnessBound {
    pub linear_code_length: usize,
    pub linear_dimension: usize,
    pub linear_gamma: f64,
    pub hadamard_code_length: usize,
    pub hadamard_dimension: usize,
    pub hadamard_gamma: f64,
    pub product_dimension: usize,
    pub product_gamma: f64,
    pub query_count: usize,
    pub linear_proximity_probability: f64,
    pub linear_query_probability: f64,
    pub hadamard_operand_proximity_probability: f64,
    pub hadamard_product_proximity_probability: f64,
    pub hadamard_product_query_probability: f64,
    pub hadamard_reduction_probability: f64,
    pub hadamard_link_probability: f64,
    pub constraint_batch_probability: f64,
}

impl ConstraintSoundnessBound {
    pub fn probability(self) -> f64 {
        self.linear_proximity_probability
            + self.linear_query_probability
            + self.hadamard_operand_proximity_probability
            + self.hadamard_product_proximity_probability
            + self.hadamard_product_query_probability
            + self.hadamard_reduction_probability
            + self.hadamard_link_probability
            + self.constraint_batch_probability
    }

    pub fn bits(self) -> f64 {
        -self.probability().log2()
    }
}

/// Certify the exact finite-length RS geometry and additive VEIL binding error
/// of `circuit` under `parameters`.
///
/// For an `RS[N,K]` (or a fixed non-zero multiplier thereof), use the
/// conservative relative distance `delta = 1-K/N` and the largest radius in
/// the proved unique-decoding interval,
/// `gamma = delta/2 - 3/(delta*N)`. A binary fold has at most
/// `floor(gamma*N+1)` bad non-zero scalars. We upper-bound division by
/// `2^128-1` and `2^128-2` with division by `2^127`, avoiding any unsound
/// floating-point approximation of those denominators.
pub fn certify_constraint_soundness(
    circuit: &ArithmeticCircuit,
    parameters: ConstraintParameters,
) -> Result<ConstraintSoundnessBound, ConstraintError> {
    let parameters = parameters.validate()?;
    if circuit.num_variables != circuit.num_inputs
        || circuit
            .multiplications
            .iter()
            .any(|gate| gate.materialized_output.is_some())
    {
        return Err(ConstraintError::MalformedCircuit);
    }
    let padded = padded_circuit(circuit);
    let linear_dimension = padded
        .num_variables
        .checked_add(parameters.linear_padding)
        .ok_or(ConstraintError::InvalidParameters)?;
    let hadamard_dimension = padded
        .multiplications
        .len()
        .checked_add(parameters.hadamard_padding)
        .ok_or(ConstraintError::InvalidParameters)?;
    let linear_code_length = linear_dimension
        .next_power_of_two()
        .checked_mul(parameters.inverse_rate)
        .ok_or(ConstraintError::InvalidParameters)?;
    let hadamard_code_length = hadamard_dimension
        .next_power_of_two()
        .checked_mul(parameters.inverse_rate)
        .ok_or(ConstraintError::InvalidParameters)?;
    let product_dimension = 2 * hadamard_dimension.next_power_of_two() - 1;
    let linear_gamma = unique_decoding_radius(linear_code_length, linear_dimension)?;
    let hadamard_gamma = unique_decoding_radius(hadamard_code_length, hadamard_dimension)?;
    let product_gamma = unique_decoding_radius(hadamard_code_length, product_dimension)?;
    let query_count = parameters.linear_padding;
    if parameters.hadamard_padding != query_count {
        // The current theorem/ledger intentionally fixes one common query
        // budget. A future asymmetric profile needs its own explicit ledger.
        return Err(ConstraintError::InvalidParameters);
    }

    let nonzero_denominator = 2f64.powi(127);
    let field_size = 2f64.powi(128);
    let binary_pg =
        |gamma: f64, length: usize| (gamma * length as f64 + 1.0).floor() / nonzero_denominator;
    let linear_proximity_probability = binary_pg(linear_gamma, linear_code_length);
    // Four operand rows are Horner-folded by one non-zero scalar. A union
    // over its three binary folds is valid without assuming independence.
    let hadamard_operand_proximity_probability =
        3.0 * binary_pg(hadamard_gamma, hadamard_code_length);
    let hadamard_product_proximity_probability = binary_pg(product_gamma, hadamard_code_length);

    let hadamard_multiplications = padded.multiplications.len();
    let hadamard_reduction_probability =
        hadamard_multiplications.saturating_sub(1) as f64 / field_size;
    // The shared F\{0,1} challenge links all three Hadamard rows. If any row
    // is false, acceptance requires one non-zero polynomial of this degree to
    // vanish; no extra factor of three is needed.
    let hadamard_link_probability =
        hadamard_multiplications.saturating_sub(1) as f64 / nonzero_denominator;
    // padded_circuit adds one constraint and Hadamard linkage adds three.
    let combined_constraints = padded.linear_constraints.len() + 3;
    let constraint_batch_probability = combined_constraints.saturating_sub(1) as f64 / field_size;

    let bound = ConstraintSoundnessBound {
        linear_code_length,
        linear_dimension,
        linear_gamma,
        hadamard_code_length,
        hadamard_dimension,
        hadamard_gamma,
        product_dimension,
        product_gamma,
        query_count,
        linear_proximity_probability,
        linear_query_probability: (1.0 - linear_gamma).powi(query_count as i32),
        hadamard_operand_proximity_probability,
        hadamard_product_proximity_probability,
        hadamard_product_query_probability: (1.0 - product_gamma).powi(query_count as i32),
        hadamard_reduction_probability,
        hadamard_link_probability,
        constraint_batch_probability,
    };
    if !bound.bits().is_finite() || bound.bits() < SUCCINCT_FLOCK_MIN_SOUNDNESS_BITS {
        return Err(ConstraintError::InsufficientSoundness);
    }
    Ok(bound)
}

fn unique_decoding_radius(code_length: usize, dimension: usize) -> Result<f64, ConstraintError> {
    if dimension == 0 || dimension >= code_length {
        return Err(ConstraintError::InvalidParameters);
    }
    let n = code_length as f64;
    let delta = 1.0 - dimension as f64 / n;
    let gamma = delta / 2.0 - 3.0 / (delta * n);
    let size_floor = 3.0 * 2.0f64.sqrt() / n.sqrt();
    if delta < size_floor || gamma < delta / 3.0 || gamma <= 0.0 {
        return Err(ConstraintError::InsufficientSoundness);
    }
    Ok(gamma)
}

impl From<DotProductError> for ConstraintError {
    fn from(value: DotProductError) -> Self {
        Self::Dot(value)
    }
}

impl From<HadamardError> for ConstraintError {
    fn from(value: HadamardError) -> Self {
        Self::Hadamard(value)
    }
}

pub fn prove_constraints<C: Challenger, R: MaskSampler + ?Sized>(
    circuit: &ArithmeticCircuit,
    inputs: &[F128],
    rng: &mut R,
    challenger: &mut C,
    ro: &RoContext,
) -> Result<ConstraintProof, ConstraintError> {
    prove_constraints_with_parameters(
        circuit,
        inputs,
        ConstraintParameters::default(),
        rng,
        challenger,
        ro,
    )
}

pub fn prove_constraints_with_parameters<C: Challenger, R: MaskSampler + ?Sized>(
    circuit: &ArithmeticCircuit,
    inputs: &[F128],
    parameters: ConstraintParameters,
    rng: &mut R,
    challenger: &mut C,
    ro: &RoContext,
) -> Result<ConstraintProof, ConstraintError> {
    certify_constraint_soundness(circuit, parameters)?;
    let commitment = commit_constraint_inputs(circuit, inputs, parameters, rng, ro)?;
    prove_constraints_from_commitment(circuit, commitment, rng, challenger, ro)
}

/// Commit to the shifted-circuit inputs before the outer protocol samples
/// challenges. Circuits used with this two-phase API must not materialize
/// multiplication outputs: verifier checks in FLOCK use only linear
/// expressions plus asserted products, so this restriction loses nothing and
/// keeps the precommitment independent of later challenges.
pub fn commit_constraint_inputs<R: MaskSampler + ?Sized>(
    circuit: &ArithmeticCircuit,
    inputs: &[F128],
    parameters: ConstraintParameters,
    rng: &mut R,
    ro: &RoContext,
) -> Result<ConstraintCommitment, ConstraintError> {
    let parameters = parameters.validate()?;
    if circuit.num_variables != circuit.num_inputs
        || circuit
            .multiplications
            .iter()
            .any(|gate| gate.materialized_output.is_some())
    {
        return Err(ConstraintError::MalformedCircuit);
    }
    if inputs.len() != circuit.num_inputs {
        return Err(ConstraintError::WrongInputLength {
            expected: circuit.num_inputs,
            actual: inputs.len(),
        });
    }

    let mut random = [F128::ZERO; 3];
    rng.fill_f128(&mut random);
    let [r, s, t] = random;
    let r_plus_one = r + F128::ONE;
    let mut padded_witness = Vec::with_capacity(inputs.len() + 6);
    padded_witness.extend_from_slice(inputs);
    padded_witness.extend_from_slice(&[r, s, r * s, r_plus_one, t, r_plus_one * t]);
    let linear_parameters = VectorParameters::with_security(
        padded_witness.len(),
        1,
        parameters.linear_padding,
        parameters.inverse_rate,
    )?;
    let linear_data = commit_vectors(
        std::slice::from_ref(&padded_witness),
        linear_parameters,
        rng,
        ro,
        RoChannel::VeilLinear,
    )?;
    Ok(ConstraintCommitment {
        circuit_inputs: circuit.num_inputs,
        padded_witness,
        linear_data,
        parameters,
    })
}

/// Finish a two-phase proof using an input commitment made before the outer
/// protocol derived the verifier-circuit challenges.
pub fn prove_constraints_from_commitment<C: Challenger, R: MaskSampler + ?Sized>(
    circuit: &ArithmeticCircuit,
    commitment: ConstraintCommitment,
    rng: &mut R,
    challenger: &mut C,
    ro: &RoContext,
) -> Result<ConstraintProof, ConstraintError> {
    certify_constraint_soundness(circuit, commitment.parameters)?;
    if circuit.num_variables != circuit.num_inputs
        || circuit.num_inputs != commitment.circuit_inputs
        || circuit
            .multiplications
            .iter()
            .any(|gate| gate.materialized_output.is_some())
    {
        return Err(ConstraintError::MalformedCircuit);
    }
    let inputs = &commitment.padded_witness[..commitment.circuit_inputs];
    if !circuit.is_satisfied(inputs)? {
        return Err(ConstraintError::UnsatisfiedCircuit);
    }
    let padded = padded_circuit(circuit);
    if !padded.is_satisfied(&commitment.padded_witness)? {
        return Err(ConstraintError::UnsatisfiedCircuit);
    }

    let ConstraintCommitment {
        padded_witness,
        linear_data,
        parameters,
        ..
    } = commitment;
    let linear_root = linear_data.root();
    let mut constraints = padded.linear_constraints.clone();
    challenger.observe_label(b"veil-f128-constraint-system");
    challenger.observe_bytes(&linear_root);

    // The padded circuit always has the two masking products, even when the
    // shifted verifier decision itself is linear.
    let hadamard = {
        let (a, b, c) = multiplication_vectors(&padded, &padded_witness)?;
        let hadamard_parameters = VectorParameters::with_security(
            padded.multiplications.len(),
            3,
            parameters.hadamard_padding,
            parameters.inverse_rate,
        )?;
        let hadamard_data = commit_hadamard(
            &a,
            &b,
            &c,
            hadamard_parameters,
            rng,
            ro,
            RoChannel::VeilHadamard,
        )?;
        challenger.observe_bytes(&hadamard_data.root());
        let multiplication_rlc = sample_not_zero_or_one(challenger)
            .ok_or(ConstraintError::ChallengeSamplingLimitExceeded)?;
        let dot_vector = powers(multiplication_rlc, padded.multiplications.len());
        let proof = prove_hadamard_and_dots(&dot_vector, hadamard_data, challenger)?;
        append_multiplication_link_constraints(&padded, &dot_vector, &proof, &mut constraints);
        proof
    };

    let constraint_rlc = challenger.sample_f128();
    let (dot_vector, expected_dot) =
        combine_linear_constraints(padded.num_variables, &constraints, constraint_rlc)?;
    let linear = prove_dot_product(&dot_vector, linear_data, challenger)?;
    if linear.claimed_dot_products.as_slice() != [expected_dot] {
        return Err(ConstraintError::LinearClaimMismatch);
    }

    Ok(ConstraintProof {
        parameters,
        num_variables: padded.num_variables,
        num_multiplications: padded.multiplications.len(),
        hadamard,
        linear,
    })
}

pub fn verify_constraints<C: Challenger>(
    circuit: &ArithmeticCircuit,
    proof: &ConstraintProof,
    challenger: &mut C,
    linear_ro: &RoContext,
    hadamard_ro: &RoContext,
) -> Result<(), ConstraintError> {
    let parameters = proof.parameters.validate()?;
    certify_constraint_soundness(circuit, parameters)?;
    if circuit.num_variables != circuit.num_inputs
        || circuit
            .multiplications
            .iter()
            .any(|gate| gate.materialized_output.is_some())
    {
        return Err(ConstraintError::MalformedCircuit);
    }
    let padded = padded_circuit(circuit);
    if proof.num_variables != padded.num_variables
        || proof.num_multiplications != padded.multiplications.len()
        || proof.linear.parameters.vector_length != padded.num_variables
        || proof.linear.parameters.num_vectors != 1
        || proof.linear.parameters.padding_length != parameters.linear_padding
        || proof.hadamard.parameters.padding_length != parameters.hadamard_padding
        || proof.hadamard.parameters.vector_length != padded.multiplications.len()
        || proof.hadamard.parameters.code_length
            != (padded.multiplications.len() + parameters.hadamard_padding).next_power_of_two()
                * parameters.inverse_rate
        || proof.linear.parameters.code_length
            != (padded.num_variables + parameters.linear_padding).next_power_of_two()
                * parameters.inverse_rate
    {
        return Err(ConstraintError::WrongProofShape);
    }

    let mut constraints = padded.linear_constraints.clone();
    challenger.observe_label(b"veil-f128-constraint-system");
    challenger.observe_bytes(&proof.linear.commitment);
    challenger.observe_bytes(&proof.hadamard.commitment);
    let multiplication_rlc = sample_not_zero_or_one(challenger)
        .ok_or(ConstraintError::ChallengeSamplingLimitExceeded)?;
    let dot_vector = powers(multiplication_rlc, padded.multiplications.len());
    verify_hadamard_and_dots(
        &dot_vector,
        &proof.hadamard,
        challenger,
        hadamard_ro,
        RoChannel::VeilHadamard,
    )?;
    append_multiplication_link_constraints(&padded, &dot_vector, &proof.hadamard, &mut constraints);

    let constraint_rlc = challenger.sample_f128();
    let (dot_vector, expected_dot) =
        combine_linear_constraints(padded.num_variables, &constraints, constraint_rlc)?;
    if proof.linear.claimed_dot_products.as_slice() != [expected_dot] {
        return Err(ConstraintError::LinearClaimMismatch);
    }
    verify_dot_product(
        &dot_vector,
        &proof.linear,
        challenger,
        linear_ro,
        RoChannel::VeilLinear,
    )?;
    Ok(())
}

fn padded_circuit(circuit: &ArithmeticCircuit) -> ArithmeticCircuit {
    let n = circuit.num_variables;
    let r = LinearCombination::variable(n);
    let s = LinearCombination::variable(n + 1);
    let rs = LinearCombination::variable(n + 2);
    let r_plus_one = LinearCombination::variable(n + 3);
    let t = LinearCombination::variable(n + 4);
    let r_plus_one_t = LinearCombination::variable(n + 5);

    let mut multiplications = circuit.multiplications.clone();
    multiplications.push(MultiplicationGate {
        left: r.clone(),
        right: s,
        output: rs,
        materialized_output: None,
    });
    multiplications.push(MultiplicationGate {
        left: r_plus_one.clone(),
        right: t,
        output: r_plus_one_t,
        materialized_output: None,
    });
    let mut linear_constraints = circuit.linear_constraints.clone();
    linear_constraints.push(
        r.add(&r_plus_one)
            .add(&LinearCombination::constant(F128::ONE)),
    );
    ArithmeticCircuit {
        num_inputs: n + 6,
        num_variables: n + 6,
        multiplications,
        linear_constraints,
    }
}

fn multiplication_vectors(
    circuit: &ArithmeticCircuit,
    witness: &[F128],
) -> Result<(Vec<F128>, Vec<F128>, Vec<F128>), ConstraintError> {
    let mut a = Vec::with_capacity(circuit.multiplications.len());
    let mut b = Vec::with_capacity(circuit.multiplications.len());
    let mut c = Vec::with_capacity(circuit.multiplications.len());
    for gate in &circuit.multiplications {
        a.push(gate.left.evaluate(witness)?);
        b.push(gate.right.evaluate(witness)?);
        c.push(gate.output.evaluate(witness)?);
    }
    Ok((a, b, c))
}

fn append_multiplication_link_constraints(
    circuit: &ArithmeticCircuit,
    dot_vector: &[F128],
    proof: &HadamardProof,
    constraints: &mut Vec<LinearCombination>,
) {
    for side in 0..3 {
        let mut linked = LinearCombination::constant(proof.claimed_dot_products[side]);
        for (gate, coefficient) in circuit.multiplications.iter().zip(dot_vector) {
            let expression = match side {
                0 => gate.left.clone(),
                1 => gate.right.clone(),
                2 => gate.output.clone(),
                _ => unreachable!(),
            };
            linked = linked.add(&expression.scale(*coefficient));
        }
        constraints.push(linked);
    }
}

fn combine_linear_constraints(
    num_variables: usize,
    constraints: &[LinearCombination],
    rlc: F128,
) -> Result<(Vec<F128>, F128), ConstraintError> {
    if constraints.is_empty() {
        return Ok((vec![F128::ZERO; num_variables], F128::ZERO));
    }
    let coefficients = powers(rlc, constraints.len());
    let mut dot_vector = vec![F128::ZERO; num_variables];
    let mut expected = F128::ZERO;
    for (constraint, challenge) in constraints.iter().zip(coefficients) {
        expected += challenge * constraint.constant;
        for &(index, coefficient) in &constraint.terms {
            let slot = dot_vector
                .get_mut(index)
                .ok_or(ConstraintError::InvalidVariable(index))?;
            *slot += challenge * coefficient;
        }
    }
    // In characteristic two, -constant = constant.
    Ok((dot_vector, expected))
}

fn powers(base: F128, length: usize) -> Vec<F128> {
    let mut current = F128::ONE;
    (0..length)
        .map(|_| {
            let value = current;
            current *= base;
            value
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use flock_core::{challenger::FsChallenger, ro::RoContext, zk::ZkRng};

    use super::*;

    fn root_circuit(public_constant: F128, masked: F128) -> ArithmeticCircuit {
        // The private input is h. Reconstruct v = masked + h and prove
        // v^2 + v + public_constant = 0. This is the intermediate VEIL shift
        // C'(h) = C(masked - h); subtraction is addition in characteristic 2.
        let mut builder = CircuitBuilder::new(1);
        let h = builder.input(0);
        let v = builder.add(&builder.constant(masked), &h);
        // v² + v + c = 0 is equivalent to v² = v + c. Expressing the
        // product with a linear output keeps the circuit compatible with the
        // two-phase precommitment API (no challenge-dependent materialized
        // witness variables).
        let output = builder.add(&v, &builder.constant(public_constant));
        builder.assert_mul(&v, &v, &output);
        builder.finish()
    }

    #[test]
    fn shifted_circuit_proves_and_verifies() {
        let secret = F128::new(0x1234, 0x5678);
        let mask = F128::new(0xaaaa, 0xbbbb);
        let masked = secret + mask;
        let public_constant = secret * secret + secret;
        let circuit = root_circuit(public_constant, masked);
        let mut rng = ZkRng::from_seed([31; 32]);
        let ro = RoContext::native([31; 32]);
        let mut prover_challenger = FsChallenger::new(b"veil-f128-constraints-test");
        let proof =
            prove_constraints(&circuit, &[mask], &mut rng, &mut prover_challenger, &ro).unwrap();
        let mut verifier_challenger = FsChallenger::new(b"veil-f128-constraints-test");
        verify_constraints(&circuit, &proof, &mut verifier_challenger, &ro, &ro).unwrap();
    }

    #[test]
    fn unsatisfied_shifted_circuit_is_not_provable() {
        let secret = F128::new(0x1234, 0x5678);
        let mask = F128::new(0xaaaa, 0xbbbb);
        let masked = secret + mask;
        let circuit = root_circuit(secret * secret + secret + F128::ONE, masked);
        let mut rng = ZkRng::from_seed([32; 32]);
        let ro = RoContext::native([32; 32]);
        let mut challenger = FsChallenger::new(b"veil-f128-constraints-false");
        assert_eq!(
            prove_constraints(&circuit, &[mask], &mut rng, &mut challenger, &ro),
            Err(ConstraintError::UnsatisfiedCircuit)
        );
    }

    #[test]
    fn linear_only_circuit_roundtrip() {
        let mut builder = CircuitBuilder::new(2);
        let check = builder.add(&builder.input(0), &builder.input(1));
        builder.assert_zero(&check);
        let circuit = builder.finish();
        let value = F128::new(7, 9);
        let mut rng = ZkRng::from_seed([33; 32]);
        let ro = RoContext::native([33; 32]);
        let mut prover_challenger = FsChallenger::new(b"veil-f128-linear-test");
        let proof = prove_constraints(
            &circuit,
            &[value, value],
            &mut rng,
            &mut prover_challenger,
            &ro,
        )
        .unwrap();
        let mut verifier_challenger = FsChallenger::new(b"veil-f128-linear-test");
        verify_constraints(&circuit, &proof, &mut verifier_challenger, &ro, &ro).unwrap();
    }

    #[test]
    fn succinct_flock_profile_has_a_concrete_additive_soundness_bound() {
        // Exact production shifted-circuit shape: 754 independently masked
        // inputs, one live multiplication, and 259 linear constraints.
        let mut builder = CircuitBuilder::new(754);
        let zero = builder.constant(F128::ZERO);
        builder.assert_mul(&zero, &zero, &zero);
        for _ in 0..259 {
            builder.assert_zero(&zero);
        }
        let circuit = builder.finish();
        let bound =
            certify_constraint_soundness(&circuit, ConstraintParameters::succinct_flock_secure())
                .unwrap();

        assert_eq!(bound.linear_dimension, 920);
        assert_eq!(bound.linear_code_length, 8192);
        assert_eq!(bound.hadamard_dimension, 163);
        assert_eq!(bound.hadamard_code_length, 2048);
        assert_eq!(bound.product_dimension, 511);
        assert_eq!(bound.query_count, 160);
        assert!(bound.bits() > SUCCINCT_FLOCK_MIN_SOUNDNESS_BITS);
        assert!(bound.bits() < 110.0);
    }

    #[test]
    fn succinct_soundness_certificate_rejects_an_underqueried_profile() {
        let mut builder = CircuitBuilder::new(754);
        let zero = builder.constant(F128::ZERO);
        builder.assert_mul(&zero, &zero, &zero);
        builder.assert_zero(&zero);
        let circuit = builder.finish();
        let weak = ConstraintParameters {
            linear_padding: 32,
            hadamard_padding: 32,
            inverse_rate: 8,
        };
        assert_eq!(
            certify_constraint_soundness(&circuit, weak),
            Err(ConstraintError::InsufficientSoundness)
        );
    }
}

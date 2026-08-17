//! VEIL's inner arithmetic-constraint compiler over `F128`.
//!
//! Transcript masks and materialized products form a private witness vector.
//! Linear constraints are batched into one ZK dot-product proof. Multiplicative
//! constraints are batched into one ZK Hadamard-plus-dot proof, and the three
//! resulting dot claims are linked back to the same witness vector by three
//! additional linear constraints.

use flock_core::{challenger::Challenger, field::F128, zk::MaskSampler};
use serde::{Deserialize, Serialize};

use crate::{
    dot_product::{
        DotProductError, DotProductProof, VectorParameters, commit_vectors, prove_dot_product,
        verify_dot_product,
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
    pub hadamard: Option<HadamardProof>,
    pub linear: DotProductProof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintParameters {
    pub linear_padding: usize,
    pub hadamard_padding: usize,
    pub inverse_rate: usize,
}

impl ConstraintParameters {
    pub const fn conservative() -> Self {
        Self {
            linear_padding: 112,
            hadamard_padding: 128,
            inverse_rate: 16,
        }
    }

    /// Memory-oriented profile for the direct FLOCK R1CS experiment. At
    /// rate 1/2, 128 queries contribute roughly 53 bits in the basic
    /// unique-decoding proximity term; this is not a 100-bit profile.
    pub const fn flock_experimental() -> Self {
        Self {
            linear_padding: 128,
            hadamard_padding: 128,
            inverse_rate: 2,
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
        Self::conservative()
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
    Dot(DotProductError),
    Hadamard(HadamardError),
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
) -> Result<ConstraintProof, ConstraintError> {
    prove_constraints_with_parameters(
        circuit,
        inputs,
        ConstraintParameters::default(),
        rng,
        challenger,
    )
}

pub fn prove_constraints_with_parameters<C: Challenger, R: MaskSampler + ?Sized>(
    circuit: &ArithmeticCircuit,
    inputs: &[F128],
    parameters: ConstraintParameters,
    rng: &mut R,
    challenger: &mut C,
) -> Result<ConstraintProof, ConstraintError> {
    let parameters = parameters.validate()?;
    let witness = circuit.complete_witness(inputs)?;
    if !circuit.is_satisfied(&witness)? {
        return Err(ConstraintError::UnsatisfiedCircuit);
    }

    let linear_parameters = VectorParameters::with_security(
        circuit.num_variables,
        1,
        parameters.linear_padding,
        parameters.inverse_rate,
    )?;
    let linear_data = commit_vectors(std::slice::from_ref(&witness), linear_parameters, rng)?;
    let linear_root = linear_data.root();

    let mut constraints = circuit.linear_constraints.clone();
    challenger.observe_label(b"veil-f128-constraint-system-v0");
    challenger.observe_bytes(&linear_root);

    let hadamard = if circuit.multiplications.is_empty() {
        None
    } else {
        let (a, b, c) = multiplication_vectors(circuit, &witness)?;
        let hadamard_parameters = VectorParameters::with_security(
            circuit.multiplications.len(),
            3,
            parameters.hadamard_padding,
            parameters.inverse_rate,
        )?;
        let hadamard_data = commit_hadamard(&a, &b, &c, hadamard_parameters, rng)?;
        challenger.observe_bytes(&hadamard_data.root());
        let multiplication_rlc = challenger.sample_f128();
        let dot_vector = powers(multiplication_rlc, circuit.multiplications.len());
        let proof = prove_hadamard_and_dots(&dot_vector, hadamard_data, challenger)?;
        append_multiplication_link_constraints(circuit, &dot_vector, &proof, &mut constraints);
        Some(proof)
    };

    let constraint_rlc = challenger.sample_f128();
    let (dot_vector, expected_dot) =
        combine_linear_constraints(circuit.num_variables, &constraints, constraint_rlc)?;
    let linear = prove_dot_product(&dot_vector, linear_data, challenger)?;
    if linear.claimed_dot_products.as_slice() != [expected_dot] {
        return Err(ConstraintError::LinearClaimMismatch);
    }

    Ok(ConstraintProof {
        parameters,
        num_variables: circuit.num_variables,
        num_multiplications: circuit.multiplications.len(),
        hadamard,
        linear,
    })
}

pub fn verify_constraints<C: Challenger>(
    circuit: &ArithmeticCircuit,
    proof: &ConstraintProof,
    challenger: &mut C,
) -> Result<(), ConstraintError> {
    let parameters = proof.parameters.validate()?;
    if proof.num_variables != circuit.num_variables
        || proof.num_multiplications != circuit.multiplications.len()
        || proof.linear.parameters.vector_length != circuit.num_variables
        || proof.linear.parameters.num_vectors != 1
        || proof.hadamard.is_some() != !circuit.multiplications.is_empty()
        || proof.linear.parameters.padding_length != parameters.linear_padding
        || proof.linear.parameters.code_length
            != (circuit.num_variables + parameters.linear_padding).next_power_of_two()
                * parameters.inverse_rate
    {
        return Err(ConstraintError::WrongProofShape);
    }

    let mut constraints = circuit.linear_constraints.clone();
    challenger.observe_label(b"veil-f128-constraint-system-v0");
    challenger.observe_bytes(&proof.linear.commitment);
    if let Some(hadamard) = &proof.hadamard {
        if hadamard.parameters.padding_length != parameters.hadamard_padding
            || hadamard.parameters.code_length
                != (circuit.multiplications.len() + parameters.hadamard_padding).next_power_of_two()
                    * parameters.inverse_rate
        {
            return Err(ConstraintError::WrongProofShape);
        }
        challenger.observe_bytes(&hadamard.commitment);
        let multiplication_rlc = challenger.sample_f128();
        let dot_vector = powers(multiplication_rlc, circuit.multiplications.len());
        verify_hadamard_and_dots(&dot_vector, hadamard, challenger)?;
        append_multiplication_link_constraints(circuit, &dot_vector, hadamard, &mut constraints);
    }

    let constraint_rlc = challenger.sample_f128();
    let (dot_vector, expected_dot) =
        combine_linear_constraints(circuit.num_variables, &constraints, constraint_rlc)?;
    if proof.linear.claimed_dot_products.as_slice() != [expected_dot] {
        return Err(ConstraintError::LinearClaimMismatch);
    }
    verify_dot_product(&dot_vector, &proof.linear, challenger)?;
    Ok(())
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
    use flock_core::{challenger::FsChallenger, zk::ZkRng};

    use super::*;

    fn root_circuit(public_constant: F128, masked: F128) -> ArithmeticCircuit {
        // The private input is h. Reconstruct v = masked + h and prove
        // v^2 + v + public_constant = 0. This is the intermediate VEIL shift
        // C'(h) = C(masked - h); subtraction is addition in characteristic 2.
        let mut builder = CircuitBuilder::new(1);
        let h = builder.input(0);
        let v = builder.add(&builder.constant(masked), &h);
        let square = builder.mul(&v, &v);
        let check = builder.add(
            &builder.add(&square, &v),
            &builder.constant(public_constant),
        );
        builder.assert_zero(&check);
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
        let mut prover_challenger = FsChallenger::new(b"veil-f128-constraints-test");
        let proof = prove_constraints(&circuit, &[mask], &mut rng, &mut prover_challenger).unwrap();
        let mut verifier_challenger = FsChallenger::new(b"veil-f128-constraints-test");
        verify_constraints(&circuit, &proof, &mut verifier_challenger).unwrap();
    }

    #[test]
    fn unsatisfied_shifted_circuit_is_not_provable() {
        let secret = F128::new(0x1234, 0x5678);
        let mask = F128::new(0xaaaa, 0xbbbb);
        let masked = secret + mask;
        let circuit = root_circuit(secret * secret + secret + F128::ONE, masked);
        let mut rng = ZkRng::from_seed([32; 32]);
        let mut challenger = FsChallenger::new(b"veil-f128-constraints-false");
        assert_eq!(
            prove_constraints(&circuit, &[mask], &mut rng, &mut challenger),
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
        let mut prover_challenger = FsChallenger::new(b"veil-f128-linear-test");
        let proof =
            prove_constraints(&circuit, &[value, value], &mut rng, &mut prover_challenger).unwrap();
        assert!(proof.hadamard.is_none());
        let mut verifier_challenger = FsChallenger::new(b"veil-f128-linear-test");
        verify_constraints(&circuit, &proof, &mut verifier_challenger).unwrap();
    }
}

//! Straight-line honest-verifier simulator for the native VEIL block-R1CS.
//!
//! The simulator receives only the public relation and public equalities. It
//! samples the algebraic transcript from the distributions induced by VEIL's
//! masks, then programs only fresh, domain-separated Merkle oracle points so
//! those sampled rows authenticate to the previously sampled random roots.

use flock_core::{
    challenger::Challenger,
    field::F128,
    merkle::{Hash, merkle_multi_proof},
    r1cs::BlockR1cs,
    ro::{ROLE_LEAF, ROLE_NODE, RoChannel, encode_header, encode_point},
    zk::MaskSampler,
};

use crate::{
    block_r1cs::{
        BlockR1csError, BlockR1csParameters, BlockR1csProof, PublicEquality, build_link_claim,
        powers, validate_public, vector_parameters,
    },
    code::{AdditiveRsCode, CodeError, CodeParameters},
    commitment::MerkleMatrixOpening,
    dot_product::{DotProductProof, VectorParameters, dot_product, sample_unique_positions},
    hadamard::HadamardProof,
};

/// Minimal programming interface required by the simulator. Implementations
/// must reject a point queried or programmed before this call.
pub trait OracleProgrammer {
    fn program_fresh(&self, point: Vec<u8>, value: Hash) -> Result<(), OracleProgrammingError>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleProgrammingError;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimulationError {
    InvalidRelation(BlockR1csError),
    DegenerateChallenge,
    ProgrammingCollision,
    Code(CodeError),
}

impl From<BlockR1csError> for SimulationError {
    fn from(value: BlockR1csError) -> Self {
        Self::InvalidRelation(value)
    }
}

impl From<CodeError> for SimulationError {
    fn from(value: CodeError) -> Self {
        Self::Code(value)
    }
}

/// Simulate an accepting block-R1CS proof without a witness.
pub fn simulate_block_r1cs<C: Challenger, R: MaskSampler + ?Sized>(
    r1cs: &BlockR1cs,
    public: &[PublicEquality],
    parameters: BlockR1csParameters,
    nonce: &[u8; 32],
    rng: &mut R,
    challenger: &mut C,
    programmer: &dyn OracleProgrammer,
) -> Result<BlockR1csProof, SimulationError> {
    validate_public(r1cs, public)?;
    let n = r1cs.n();
    let witness_parameters = vector_parameters(n + 6, 1, parameters)?;
    let hadamard_parameters = vector_parameters(2 * n + 2, 3, parameters)?;
    let witness_root = random_hash(rng);
    let hadamard_root = random_hash(rng);

    challenger.observe_label(b"veil-f128-flock-block-r1cs-v0");
    challenger.observe_bytes(&witness_root);
    challenger.observe_bytes(&hadamard_root);
    let multiplication_rlc = challenger.sample_f128();
    // The six private padding values give a bijection except at these two
    // field points (the statistical bad event in VEIL's simulator).
    if multiplication_rlc.is_zero() || multiplication_rlc == F128::ONE {
        return Err(SimulationError::DegenerateChallenge);
    }
    let dot_vector = powers(multiplication_rlc, 2 * n + 2);
    let hadamard = simulate_hadamard(
        &dot_vector,
        hadamard_parameters,
        hadamard_root,
        nonce,
        rng,
        challenger,
        programmer,
    )?;

    let link_rlc = challenger.sample_f128();
    let (link_vector, expected_dot) = build_link_claim(
        r1cs,
        public,
        &dot_vector,
        hadamard.claimed_dot_products,
        link_rlc,
    )?;
    let witness = simulate_dot_product(
        &link_vector,
        vec![expected_dot],
        witness_parameters,
        witness_root,
        nonce,
        RoChannel::Witness,
        rng,
        challenger,
        programmer,
    )?;

    Ok(BlockR1csProof {
        parameters,
        witness_length: n,
        hadamard,
        witness,
    })
}

#[allow(clippy::too_many_arguments)]
fn simulate_dot_product<C: Challenger, R: MaskSampler + ?Sized>(
    dot_vector: &[F128],
    claimed_dot_products: Vec<F128>,
    parameters: VectorParameters,
    root: Hash,
    nonce: &[u8; 32],
    channel: RoChannel,
    rng: &mut R,
    challenger: &mut C,
    programmer: &dyn OracleProgrammer,
) -> Result<DotProductProof, SimulationError> {
    let mask_dot_product = random_field(rng);
    challenger.observe_label(b"veil-f128-dot-product-v0");
    challenger.observe_f128_slice(dot_vector);
    challenger.observe_f128_slice(&claimed_dot_products);
    challenger.observe_f128(mask_dot_product);
    challenger.observe_bytes(&root);
    let rho = challenger.sample_f128();
    if rho.is_zero() {
        return Err(SimulationError::DegenerateChallenge);
    }

    let target = claimed_dot_products
        .iter()
        .chain(std::iter::once(&mask_dot_product))
        .rev()
        .fold(F128::ZERO, |accumulator, value| *value + rho * accumulator);
    let rlc_vector = random_conditioned_vector(dot_vector, target, rng)?;
    let rlc_padding = random_vector(parameters.padding_length, rng);
    challenger.observe_f128_slice(&rlc_vector);
    challenger.observe_f128_slice(&rlc_padding);
    let positions = sample_unique_positions(
        challenger,
        parameters.code_length,
        parameters.padding_length,
    );

    let code = code_for(parameters)?;
    let mut message = rlc_vector.clone();
    message.extend_from_slice(&rlc_padding);
    let encoded = code.encode(&message)?;
    let width = parameters.commitment_width();
    let highest_coefficient = power(rho, width - 1);
    let mut rows = Vec::with_capacity(positions.len() * width);
    for &position in &positions {
        let mut row = random_vector(width, rng);
        let actual = row
            .iter()
            .rev()
            .fold(F128::ZERO, |accumulator, value| *value + rho * accumulator);
        row[width - 1] += (actual + encoded[position]) * highest_coefficient.inv();
        rows.extend(row);
    }
    let opening = program_opening(
        parameters.code_length,
        width,
        root,
        positions,
        rows,
        nonce,
        channel,
        rng,
        programmer,
    )?;
    Ok(DotProductProof {
        parameters,
        commitment: root,
        claimed_dot_products,
        mask_dot_product,
        rlc_vector,
        rlc_padding,
        opening,
    })
}

#[allow(clippy::too_many_arguments)]
fn simulate_hadamard<C: Challenger, R: MaskSampler + ?Sized>(
    dot_vector: &[F128],
    parameters: VectorParameters,
    root: Hash,
    nonce: &[u8; 32],
    rng: &mut R,
    challenger: &mut C,
    programmer: &dyn OracleProgrammer,
) -> Result<HadamardProof, SimulationError> {
    let code = code_for(parameters)?;
    challenger.observe_label(b"veil-f128-hadamard-v0");
    challenger.observe_bytes(&root);
    let evaluation_point = challenger.sample_f128();
    let gamma = random_field(rng);
    challenger.observe_f128(gamma);
    let product_mask_coefficient = challenger.sample_f128();
    if product_mask_coefficient.is_zero() {
        return Err(SimulationError::DegenerateChallenge);
    }

    let phi_length = 2 * parameters.message_length().next_power_of_two();
    let reduction_weights = powers(evaluation_point, parameters.vector_length);
    let phi_target = product_mask_coefficient * gamma;
    let mut phi = random_vector(phi_length, rng);
    condition_prefix(&mut phi, &reduction_weights, phi_target)?;
    challenger.observe_f128_slice(&phi);

    let claimed_dot_products = [random_field(rng), random_field(rng), random_field(rng)];
    let mask_dot_product = random_field(rng);
    challenger.observe_f128_slice(dot_vector);
    challenger.observe_f128_slice(&claimed_dot_products);
    challenger.observe_f128(mask_dot_product);
    challenger.observe_bytes(&root);
    let rho = challenger.sample_f128();
    if rho.is_zero() {
        return Err(SimulationError::DegenerateChallenge);
    }
    let target = claimed_dot_products
        .iter()
        .chain(std::iter::once(&mask_dot_product))
        .rev()
        .fold(F128::ZERO, |accumulator, value| *value + rho * accumulator);
    let rlc_vector = random_conditioned_vector(dot_vector, target, rng)?;
    let rlc_padding = random_vector(parameters.padding_length, rng);
    challenger.observe_f128_slice(&rlc_vector);
    challenger.observe_f128_slice(&rlc_padding);
    let positions = sample_unique_positions(
        challenger,
        parameters.code_length,
        parameters.padding_length,
    );

    let phi_codeword = code.encode_square(&phi)?;
    let mut rlc_message = rlc_vector.clone();
    rlc_message.extend_from_slice(&rlc_padding);
    let rlc_codeword = code.encode(&rlc_message)?;
    let rho_squared = rho * rho;
    let inverse_rho_squared = rho_squared.inv();
    let inverse_product_mask = product_mask_coefficient.inv();
    let mut rows = Vec::with_capacity(positions.len() * 5);
    for &position in &positions {
        let row_0 = random_field(rng);
        let row_1 = random_field(rng);
        let row_3 = random_field(rng);
        let row_2 = (rlc_codeword[position] + row_0 + rho * row_1 + rho_squared * rho * row_3)
            * inverse_rho_squared;
        let row_4 = (phi_codeword[position] + row_0 * row_1 + row_2) * inverse_product_mask;
        rows.extend_from_slice(&[row_0, row_1, row_2, row_3, row_4]);
    }
    let opening = program_opening(
        parameters.code_length,
        5,
        root,
        positions,
        rows,
        nonce,
        RoChannel::MaskP,
        rng,
        programmer,
    )?;
    Ok(HadamardProof {
        parameters,
        commitment: root,
        gamma,
        phi,
        claimed_dot_products,
        mask_dot_product,
        rlc_vector,
        rlc_padding,
        opening,
    })
}

#[allow(clippy::too_many_arguments)]
fn program_opening<R: MaskSampler + ?Sized>(
    num_rows: usize,
    num_columns: usize,
    root: Hash,
    positions: Vec<usize>,
    rows: Vec<F128>,
    nonce: &[u8; 32],
    channel: RoChannel,
    rng: &mut R,
    programmer: &dyn OracleProgrammer,
) -> Result<MerkleMatrixOpening, SimulationError> {
    let mut tree = (0..2 * num_rows - 1)
        .map(|_| random_hash(rng))
        .collect::<Vec<_>>();
    *tree.last_mut().expect("non-empty Merkle tree") = root;
    let leaf_level = num_rows.trailing_zeros();
    let leaf_header = encode_header(ROLE_LEAF, channel, 0, nonce, (num_columns * 16) as u64);
    for (&position, row) in positions.iter().zip(rows.chunks_exact(num_columns)) {
        let point = encode_point(&leaf_header, leaf_level, position as u64, &field_bytes(row));
        programmer
            .program_fresh(point, tree[position])
            .map_err(|_| SimulationError::ProgrammingCollision)?;
    }

    let node_header = encode_header(ROLE_NODE, channel, 0, nonce, 64);
    let mut active = positions.clone();
    let mut level_start = 0usize;
    let mut level_len = num_rows;
    let mut node_level = leaf_level;
    while level_len > 1 {
        node_level -= 1;
        let next_start = level_start + level_len;
        let mut parents = active
            .iter()
            .map(|position| position >> 1)
            .collect::<Vec<_>>();
        parents.sort_unstable();
        parents.dedup();
        for &parent in &parents {
            let left = tree[level_start + 2 * parent];
            let right = tree[level_start + 2 * parent + 1];
            let mut payload = [0u8; 64];
            payload[..32].copy_from_slice(&left);
            payload[32..].copy_from_slice(&right);
            let point = encode_point(&node_header, node_level, parent as u64, &payload);
            programmer
                .program_fresh(point, tree[next_start + parent])
                .map_err(|_| SimulationError::ProgrammingCollision)?;
        }
        active = parents;
        level_start = next_start;
        level_len >>= 1;
    }
    let siblings = merkle_multi_proof(&tree, num_rows, &positions);
    Ok(MerkleMatrixOpening {
        positions,
        rows,
        siblings,
    })
}

fn random_conditioned_vector<R: MaskSampler + ?Sized>(
    weights: &[F128],
    target: F128,
    rng: &mut R,
) -> Result<Vec<F128>, SimulationError> {
    let mut values = random_vector(weights.len(), rng);
    condition_prefix(&mut values, weights, target)?;
    Ok(values)
}

fn condition_prefix(
    values: &mut [F128],
    weights: &[F128],
    target: F128,
) -> Result<(), SimulationError> {
    let Some(pivot) = weights.iter().position(|weight| !weight.is_zero()) else {
        return Err(SimulationError::DegenerateChallenge);
    };
    let actual = dot_product(&values[..weights.len()], weights);
    values[pivot] += (actual + target) * weights[pivot].inv();
    Ok(())
}

fn code_for(parameters: VectorParameters) -> Result<AdditiveRsCode, CodeError> {
    Ok(AdditiveRsCode::new(CodeParameters::new(
        parameters.message_length(),
        parameters.code_length,
    )?))
}

fn random_vector<R: MaskSampler + ?Sized>(length: usize, rng: &mut R) -> Vec<F128> {
    let mut values = vec![F128::ZERO; length];
    rng.fill_f128(&mut values);
    values
}

fn random_field<R: MaskSampler + ?Sized>(rng: &mut R) -> F128 {
    let mut value = [F128::ZERO];
    rng.fill_f128(&mut value);
    value[0]
}

fn random_hash<R: MaskSampler + ?Sized>(rng: &mut R) -> Hash {
    let values = [random_field(rng), random_field(rng)];
    let mut hash = [0u8; 32];
    hash[..8].copy_from_slice(&values[0].lo.to_le_bytes());
    hash[8..16].copy_from_slice(&values[0].hi.to_le_bytes());
    hash[16..24].copy_from_slice(&values[1].lo.to_le_bytes());
    hash[24..].copy_from_slice(&values[1].hi.to_le_bytes());
    hash
}

fn field_bytes(values: &[F128]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(values.len() * 16);
    for value in values {
        bytes.extend_from_slice(&value.lo.to_le_bytes());
        bytes.extend_from_slice(&value.hi.to_le_bytes());
    }
    bytes
}

fn power(base: F128, exponent: usize) -> F128 {
    (0..exponent).fold(F128::ONE, |value, _| value * base)
}

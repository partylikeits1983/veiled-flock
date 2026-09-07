//! Typed transcript-schema audit for the current succinct VEIL proof.
//!
//! This is not a wire format. `proof_io` owns serialization. The purpose here
//! is narrower: give tests a bijective flatten/rebuild pass over every typed
//! proof field, and make field additions fail closed by destructuring without
//! wildcard matches.

use flock_core::{
    field::F128,
    lincheck::LincheckProof,
    pcs::{
        self, BatchOpeningProofLigerito, Commitment, PcsParams, ZkBlindOpening,
        ligerito::{FinalProof, LigeritoProof, RecursiveProof, SumcheckMessage},
    },
};
use sha2::{Digest, Sha256};
use veil_f128::{
    ConstraintParameters, ConstraintProof, DotProductProof, HadamardProof, MerkleMatrixOpening,
    VectorParameters,
};

use crate::succinct_veil::{
    InitialTreeNonces, MaskedRingClaim, MaskedZerocheckProof, SuccinctVeilProof,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptField {
    pub path: String,
    pub value: TranscriptValue,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptValue {
    Bytes(Vec<Vec<u8>>),
    Scalars(Vec<F128>),
    ScalarRows(Vec<Vec<F128>>),
    U64s(Vec<u64>),
    Usizes(Vec<usize>),
    Bool(bool),
    LigeritoProfile(pcs::ligerito::LigeritoProfile),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptSchemaError {
    MissingField {
        expected: String,
    },
    WrongPath {
        expected: String,
        got: String,
    },
    WrongKind {
        path: String,
        expected: &'static str,
        got: &'static str,
    },
    WrongLength {
        path: String,
        expected: usize,
        got: usize,
    },
    TrailingFields {
        remaining: usize,
    },
}

impl std::fmt::Display for TranscriptSchemaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingField { expected } => write!(f, "missing transcript field {expected}"),
            Self::WrongPath { expected, got } => {
                write!(f, "expected transcript field {expected}, got {got}")
            }
            Self::WrongKind {
                path,
                expected,
                got,
            } => write!(
                f,
                "transcript field {path} has kind {got}, expected {expected}"
            ),
            Self::WrongLength {
                path,
                expected,
                got,
            } => write!(
                f,
                "transcript field {path} has length {got}, expected {expected}"
            ),
            Self::TrailingFields { remaining } => {
                write!(f, "{remaining} trailing transcript fields")
            }
        }
    }
}

impl std::error::Error for TranscriptSchemaError {}

impl TranscriptValue {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Bytes(_) => "bytes",
            Self::Scalars(_) => "scalars",
            Self::ScalarRows(_) => "scalar_rows",
            Self::U64s(_) => "u64s",
            Self::Usizes(_) => "usizes",
            Self::Bool(_) => "bool",
            Self::LigeritoProfile(_) => "ligerito_profile",
        }
    }

    fn shape_words(&self) -> Vec<usize> {
        match self {
            Self::Bytes(values) => values.iter().map(Vec::len).collect(),
            Self::Scalars(values) => vec![values.len()],
            Self::ScalarRows(rows) => rows.iter().map(Vec::len).collect(),
            Self::U64s(values) => vec![values.len()],
            Self::Usizes(values) => vec![values.len()],
            Self::Bool(_) | Self::LigeritoProfile(_) => Vec::new(),
        }
    }
}

pub fn flatten_veil_flock_proof(
    commitment: &Commitment,
    proof: &SuccinctVeilProof,
) -> Vec<TranscriptField> {
    let mut out = Vec::new();
    flatten_commitment(&mut out, "commitment", commitment);

    let SuccinctVeilProof {
        proof_nonce,
        tree_nonces,
        masked_zerocheck,
        masked_lincheck,
        masked_ring_claims,
        public_direct_blind_values,
        blind_grind_nonce,
        pcs_open,
        veil,
    } = proof;

    bytes_one(&mut out, "proof.proof_nonce", proof_nonce);
    flatten_initial_tree_nonces(&mut out, "proof.tree_nonces", tree_nonces);
    flatten_masked_zerocheck(&mut out, "proof.masked_zerocheck", masked_zerocheck);
    flatten_lincheck(&mut out, "proof.masked_lincheck", masked_lincheck);
    usizes_one(
        &mut out,
        "proof.masked_ring_claims.len",
        masked_ring_claims.len(),
    );
    for (i, claim) in masked_ring_claims.iter().enumerate() {
        flatten_masked_ring_claim(&mut out, &format!("proof.masked_ring_claims.{i}"), claim);
    }
    scalars(
        &mut out,
        "proof.public_direct_blind_values",
        public_direct_blind_values.clone(),
    );
    u64s_one(&mut out, "proof.blind_grind_nonce", *blind_grind_nonce);
    flatten_batch_opening(&mut out, "proof.pcs_open", pcs_open);
    flatten_constraint_proof(&mut out, "proof.veil", veil);
    out
}

pub fn rebuild_veil_flock_proof(
    fields: &[TranscriptField],
) -> Result<(Commitment, SuccinctVeilProof), TranscriptSchemaError> {
    let mut reader = FieldReader { fields, cursor: 0 };
    let commitment = rebuild_commitment(&mut reader, "commitment")?;
    let proof = SuccinctVeilProof {
        proof_nonce: reader.take_bytes32("proof.proof_nonce")?,
        tree_nonces: rebuild_initial_tree_nonces(&mut reader, "proof.tree_nonces")?,
        masked_zerocheck: rebuild_masked_zerocheck(&mut reader, "proof.masked_zerocheck")?,
        masked_lincheck: rebuild_lincheck(&mut reader, "proof.masked_lincheck")?,
        masked_ring_claims: {
            let len = reader.take_usize_one("proof.masked_ring_claims.len")?;
            (0..len)
                .map(|i| {
                    rebuild_masked_ring_claim(&mut reader, &format!("proof.masked_ring_claims.{i}"))
                })
                .collect::<Result<Vec<_>, _>>()?
        },
        public_direct_blind_values: reader.take_scalars("proof.public_direct_blind_values")?,
        blind_grind_nonce: reader.take_u64_one("proof.blind_grind_nonce")?,
        pcs_open: rebuild_batch_opening(&mut reader, "proof.pcs_open")?,
        veil: rebuild_constraint_proof(&mut reader, "proof.veil")?,
    };
    reader.finish()?;
    Ok((commitment, proof))
}

/// Path-only manifest for schema comparisons where randomized opening shapes
/// may legitimately differ.
pub fn schema_paths(fields: &[TranscriptField]) -> Vec<String> {
    fields.iter().map(|field| field.path.clone()).collect()
}

/// Hash of path, value kind, and container shape. This intentionally excludes
/// field values.
pub fn schema_shape_digest(fields: &[TranscriptField]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for field in fields {
        hasher.update(field.path.as_bytes());
        hasher.update([0]);
        hasher.update(field.value.kind().as_bytes());
        hasher.update([0]);
        let shape = field.value.shape_words();
        hasher.update((shape.len() as u64).to_le_bytes());
        for word in shape {
            hasher.update((word as u64).to_le_bytes());
        }
    }
    hasher.finalize().into()
}

/// Field elements appearing in transcript order. Byte fields are omitted
/// because hashes and Merkle proofs have randomized, challenge-dependent
/// structure that is not meaningfully compared as algebraic PIOP payload.
pub fn algebraic_values(fields: &[TranscriptField]) -> Vec<F128> {
    let mut out = Vec::new();
    for field in fields {
        match &field.value {
            TranscriptValue::Scalars(values) => out.extend_from_slice(values),
            TranscriptValue::ScalarRows(rows) => {
                for row in rows {
                    out.extend_from_slice(row);
                }
            }
            TranscriptValue::Bytes(_)
            | TranscriptValue::U64s(_)
            | TranscriptValue::Usizes(_)
            | TranscriptValue::Bool(_)
            | TranscriptValue::LigeritoProfile(_) => {}
        }
    }
    out
}

fn field(out: &mut Vec<TranscriptField>, path: impl Into<String>, value: TranscriptValue) {
    out.push(TranscriptField {
        path: path.into(),
        value,
    });
}

fn bytes_one(out: &mut Vec<TranscriptField>, path: impl Into<String>, value: &[u8]) {
    field(out, path, TranscriptValue::Bytes(vec![value.to_vec()]));
}

fn bytes_many<const N: usize>(
    out: &mut Vec<TranscriptField>,
    path: impl Into<String>,
    values: &[[u8; N]],
) {
    field(
        out,
        path,
        TranscriptValue::Bytes(values.iter().map(|value| value.to_vec()).collect()),
    );
}

fn scalars(out: &mut Vec<TranscriptField>, path: impl Into<String>, values: Vec<F128>) {
    field(out, path, TranscriptValue::Scalars(values));
}

fn scalar_rows(out: &mut Vec<TranscriptField>, path: impl Into<String>, rows: Vec<Vec<F128>>) {
    field(out, path, TranscriptValue::ScalarRows(rows));
}

fn u64s(out: &mut Vec<TranscriptField>, path: impl Into<String>, values: Vec<u64>) {
    field(out, path, TranscriptValue::U64s(values));
}

fn u64s_one(out: &mut Vec<TranscriptField>, path: impl Into<String>, value: u64) {
    u64s(out, path, vec![value]);
}

fn usizes(out: &mut Vec<TranscriptField>, path: impl Into<String>, values: Vec<usize>) {
    field(out, path, TranscriptValue::Usizes(values));
}

fn usizes_one(out: &mut Vec<TranscriptField>, path: impl Into<String>, value: usize) {
    usizes(out, path, vec![value]);
}

fn flatten_commitment(out: &mut Vec<TranscriptField>, path: &str, commitment: &Commitment) {
    let Commitment { root, params } = commitment;
    bytes_one(out, format!("{path}.root"), root);
    flatten_pcs_params(out, &format!("{path}.params"), params);
}

fn flatten_pcs_params(out: &mut Vec<TranscriptField>, path: &str, params: &PcsParams) {
    let PcsParams {
        m,
        log_inv_rate,
        log_batch_size,
        profile,
        zk,
    } = params;
    usizes_one(out, format!("{path}.m"), *m);
    usizes_one(out, format!("{path}.log_inv_rate"), *log_inv_rate);
    usizes_one(out, format!("{path}.log_batch_size"), *log_batch_size);
    field(
        out,
        format!("{path}.profile"),
        TranscriptValue::LigeritoProfile(*profile),
    );
    field(out, format!("{path}.zk"), TranscriptValue::Bool(*zk));
}

fn flatten_initial_tree_nonces(
    out: &mut Vec<TranscriptField>,
    path: &str,
    nonces: &InitialTreeNonces,
) {
    let InitialTreeNonces {
        outer,
        veil_linear,
        veil_hadamard,
    } = nonces;
    bytes_one(out, format!("{path}.outer"), outer);
    bytes_one(out, format!("{path}.veil_linear"), veil_linear);
    bytes_one(out, format!("{path}.veil_hadamard"), veil_hadamard);
}

fn flatten_masked_zerocheck(
    out: &mut Vec<TranscriptField>,
    path: &str,
    proof: &MaskedZerocheckProof,
) {
    let MaskedZerocheckProof {
        round1_ab,
        round1_c,
        multilinear_rounds,
        final_a_eval,
        final_b_eval,
    } = proof;
    scalars(out, format!("{path}.round1_ab"), round1_ab.clone());
    scalars(out, format!("{path}.round1_c"), round1_c.clone());
    scalars(
        out,
        format!("{path}.multilinear_rounds"),
        flatten_pairs(multilinear_rounds),
    );
    scalars(out, format!("{path}.final_a_eval"), vec![*final_a_eval]);
    scalars(out, format!("{path}.final_b_eval"), vec![*final_b_eval]);
}

fn flatten_lincheck(out: &mut Vec<TranscriptField>, path: &str, proof: &LincheckProof) {
    let LincheckProof { rounds, z_partial } = proof;
    scalars(out, format!("{path}.rounds"), flatten_pairs(rounds));
    scalars(out, format!("{path}.z_partial"), z_partial.clone());
}

fn flatten_masked_ring_claim(out: &mut Vec<TranscriptField>, path: &str, claim: &MaskedRingClaim) {
    let MaskedRingClaim { witness, blind } = claim;
    scalars(out, format!("{path}.witness"), witness.clone());
    scalars(out, format!("{path}.blind"), blind.clone());
}

fn flatten_batch_opening(
    out: &mut Vec<TranscriptField>,
    path: &str,
    proof: &BatchOpeningProofLigerito,
) {
    let BatchOpeningProofLigerito {
        ring_switches,
        ligerito,
        zk_blind,
    } = proof;
    usizes_one(
        out,
        format!("{path}.ring_switches.len"),
        ring_switches.len(),
    );
    for (i, ring) in ring_switches.iter().enumerate() {
        let pcs::RingSwitchProof { s_hat_v } = ring;
        scalars(
            out,
            format!("{path}.ring_switches.{i}.s_hat_v"),
            s_hat_v.clone(),
        );
    }
    flatten_ligerito(out, &format!("{path}.ligerito"), ligerito);
    field(
        out,
        format!("{path}.zk_blind.present"),
        TranscriptValue::Bool(zk_blind.is_some()),
    );
    if let Some(zk_blind) = zk_blind {
        let ZkBlindOpening { y_g, c_grind_nonce } = zk_blind;
        scalars(out, format!("{path}.zk_blind.y_g"), vec![*y_g]);
        u64s_one(
            out,
            format!("{path}.zk_blind.c_grind_nonce"),
            *c_grind_nonce,
        );
    }
}

fn flatten_ligerito(out: &mut Vec<TranscriptField>, path: &str, proof: &LigeritoProof) {
    let LigeritoProof {
        initial_root,
        initial_proof,
        recursive_roots,
        recursive_proofs,
        final_proof,
        sumcheck_transcript,
        grinding_nonces,
        ood_values,
        fold_grinding_nonces,
    } = proof;
    bytes_one(out, format!("{path}.initial_root"), initial_root);
    flatten_recursive_proof(out, &format!("{path}.initial_proof"), initial_proof);
    bytes_many(out, format!("{path}.recursive_roots"), recursive_roots);
    usizes_one(
        out,
        format!("{path}.recursive_proofs.len"),
        recursive_proofs.len(),
    );
    for (i, recursive) in recursive_proofs.iter().enumerate() {
        flatten_recursive_proof(out, &format!("{path}.recursive_proofs.{i}"), recursive);
    }
    flatten_final_proof(out, &format!("{path}.final_proof"), final_proof);
    scalars(
        out,
        format!("{path}.sumcheck_transcript"),
        sumcheck_transcript
            .iter()
            .flat_map(|msg| {
                let SumcheckMessage { u_0, u_2 } = msg;
                [*u_0, *u_2]
            })
            .collect(),
    );
    u64s(
        out,
        format!("{path}.grinding_nonces"),
        grinding_nonces.clone(),
    );
    scalars(out, format!("{path}.ood_values"), ood_values.clone());
    u64s(
        out,
        format!("{path}.fold_grinding_nonces"),
        fold_grinding_nonces.clone(),
    );
}

fn flatten_recursive_proof(out: &mut Vec<TranscriptField>, path: &str, proof: &RecursiveProof) {
    let RecursiveProof {
        opened_rows,
        leaf_salts,
        merkle_proof,
    } = proof;
    scalar_rows(out, format!("{path}.opened_rows"), opened_rows.clone());
    bytes_many(out, format!("{path}.leaf_salts"), leaf_salts);
    bytes_many(out, format!("{path}.merkle_proof"), merkle_proof);
}

fn flatten_final_proof(out: &mut Vec<TranscriptField>, path: &str, proof: &FinalProof) {
    let FinalProof {
        yr,
        opened_rows,
        merkle_proof,
    } = proof;
    scalars(out, format!("{path}.yr"), yr.clone());
    scalar_rows(out, format!("{path}.opened_rows"), opened_rows.clone());
    bytes_many(out, format!("{path}.merkle_proof"), merkle_proof);
}

fn flatten_constraint_proof(out: &mut Vec<TranscriptField>, path: &str, proof: &ConstraintProof) {
    let ConstraintProof {
        parameters,
        num_variables,
        num_multiplications,
        hadamard,
        linear,
    } = proof;
    flatten_constraint_parameters(out, &format!("{path}.parameters"), parameters);
    usizes_one(out, format!("{path}.num_variables"), *num_variables);
    usizes_one(
        out,
        format!("{path}.num_multiplications"),
        *num_multiplications,
    );
    flatten_hadamard_proof(out, &format!("{path}.hadamard"), hadamard);
    flatten_dot_product_proof(out, &format!("{path}.linear"), linear);
}

fn flatten_constraint_parameters(
    out: &mut Vec<TranscriptField>,
    path: &str,
    params: &ConstraintParameters,
) {
    let ConstraintParameters {
        linear_padding,
        hadamard_padding,
        inverse_rate,
    } = params;
    usizes_one(out, format!("{path}.linear_padding"), *linear_padding);
    usizes_one(out, format!("{path}.hadamard_padding"), *hadamard_padding);
    usizes_one(out, format!("{path}.inverse_rate"), *inverse_rate);
}

fn flatten_vector_parameters(
    out: &mut Vec<TranscriptField>,
    path: &str,
    params: &VectorParameters,
) {
    let VectorParameters {
        vector_length,
        padding_length,
        code_length,
        num_vectors,
    } = params;
    usizes_one(out, format!("{path}.vector_length"), *vector_length);
    usizes_one(out, format!("{path}.padding_length"), *padding_length);
    usizes_one(out, format!("{path}.code_length"), *code_length);
    usizes_one(out, format!("{path}.num_vectors"), *num_vectors);
}

fn flatten_hadamard_proof(out: &mut Vec<TranscriptField>, path: &str, proof: &HadamardProof) {
    let HadamardProof {
        parameters,
        commitment,
        gamma,
        phi,
        claimed_dot_products,
        mask_dot_product,
        rlc_vector,
        rlc_padding,
        opening,
    } = proof;
    flatten_vector_parameters(out, &format!("{path}.parameters"), parameters);
    bytes_one(out, format!("{path}.commitment"), commitment);
    scalars(out, format!("{path}.gamma"), vec![*gamma]);
    scalars(out, format!("{path}.phi"), phi.clone());
    scalars(
        out,
        format!("{path}.claimed_dot_products"),
        claimed_dot_products.to_vec(),
    );
    scalars(
        out,
        format!("{path}.mask_dot_product"),
        vec![*mask_dot_product],
    );
    scalars(out, format!("{path}.rlc_vector"), rlc_vector.clone());
    scalars(out, format!("{path}.rlc_padding"), rlc_padding.clone());
    flatten_merkle_matrix_opening(out, &format!("{path}.opening"), opening);
}

fn flatten_dot_product_proof(out: &mut Vec<TranscriptField>, path: &str, proof: &DotProductProof) {
    let DotProductProof {
        parameters,
        commitment,
        claimed_dot_products,
        mask_dot_product,
        rlc_vector,
        rlc_padding,
        opening,
    } = proof;
    flatten_vector_parameters(out, &format!("{path}.parameters"), parameters);
    bytes_one(out, format!("{path}.commitment"), commitment);
    scalars(
        out,
        format!("{path}.claimed_dot_products"),
        claimed_dot_products.clone(),
    );
    scalars(
        out,
        format!("{path}.mask_dot_product"),
        vec![*mask_dot_product],
    );
    scalars(out, format!("{path}.rlc_vector"), rlc_vector.clone());
    scalars(out, format!("{path}.rlc_padding"), rlc_padding.clone());
    flatten_merkle_matrix_opening(out, &format!("{path}.opening"), opening);
}

fn flatten_merkle_matrix_opening(
    out: &mut Vec<TranscriptField>,
    path: &str,
    opening: &MerkleMatrixOpening,
) {
    let MerkleMatrixOpening {
        positions,
        rows,
        salts,
        siblings,
    } = opening;
    usizes(out, format!("{path}.positions"), positions.clone());
    scalars(out, format!("{path}.rows"), rows.clone());
    bytes_many(out, format!("{path}.salts"), salts);
    bytes_many(out, format!("{path}.siblings"), siblings);
}

fn flatten_pairs(pairs: &[(F128, F128)]) -> Vec<F128> {
    pairs.iter().flat_map(|(a, b)| [*a, *b]).collect()
}

struct FieldReader<'a> {
    fields: &'a [TranscriptField],
    cursor: usize,
}

impl<'a> FieldReader<'a> {
    fn take(&mut self, path: &str) -> Result<&'a TranscriptValue, TranscriptSchemaError> {
        let Some(field) = self.fields.get(self.cursor) else {
            return Err(TranscriptSchemaError::MissingField {
                expected: path.to_string(),
            });
        };
        if field.path != path {
            return Err(TranscriptSchemaError::WrongPath {
                expected: path.to_string(),
                got: field.path.clone(),
            });
        }
        self.cursor += 1;
        Ok(&field.value)
    }

    fn take_bytes(&mut self, path: &str) -> Result<Vec<Vec<u8>>, TranscriptSchemaError> {
        match self.take(path)? {
            TranscriptValue::Bytes(values) => Ok(values.clone()),
            value => Err(TranscriptSchemaError::WrongKind {
                path: path.to_string(),
                expected: "bytes",
                got: value.kind(),
            }),
        }
    }

    fn take_bytes32(&mut self, path: &str) -> Result<[u8; 32], TranscriptSchemaError> {
        let values = self.take_bytes(path)?;
        if values.len() != 1 {
            return Err(TranscriptSchemaError::WrongLength {
                path: path.to_string(),
                expected: 1,
                got: values.len(),
            });
        }
        bytes32(path, &values[0])
    }

    fn take_bytes32_many(&mut self, path: &str) -> Result<Vec<[u8; 32]>, TranscriptSchemaError> {
        self.take_bytes(path)?
            .iter()
            .map(|value| bytes32(path, value))
            .collect()
    }

    fn take_scalars(&mut self, path: &str) -> Result<Vec<F128>, TranscriptSchemaError> {
        match self.take(path)? {
            TranscriptValue::Scalars(values) => Ok(values.clone()),
            value => Err(TranscriptSchemaError::WrongKind {
                path: path.to_string(),
                expected: "scalars",
                got: value.kind(),
            }),
        }
    }

    fn take_scalar_one(&mut self, path: &str) -> Result<F128, TranscriptSchemaError> {
        let values = self.take_scalars(path)?;
        if values.len() != 1 {
            return Err(TranscriptSchemaError::WrongLength {
                path: path.to_string(),
                expected: 1,
                got: values.len(),
            });
        }
        Ok(values[0])
    }

    fn take_scalar_rows(&mut self, path: &str) -> Result<Vec<Vec<F128>>, TranscriptSchemaError> {
        match self.take(path)? {
            TranscriptValue::ScalarRows(rows) => Ok(rows.clone()),
            value => Err(TranscriptSchemaError::WrongKind {
                path: path.to_string(),
                expected: "scalar_rows",
                got: value.kind(),
            }),
        }
    }

    fn take_u64s(&mut self, path: &str) -> Result<Vec<u64>, TranscriptSchemaError> {
        match self.take(path)? {
            TranscriptValue::U64s(values) => Ok(values.clone()),
            value => Err(TranscriptSchemaError::WrongKind {
                path: path.to_string(),
                expected: "u64s",
                got: value.kind(),
            }),
        }
    }

    fn take_u64_one(&mut self, path: &str) -> Result<u64, TranscriptSchemaError> {
        let values = self.take_u64s(path)?;
        if values.len() != 1 {
            return Err(TranscriptSchemaError::WrongLength {
                path: path.to_string(),
                expected: 1,
                got: values.len(),
            });
        }
        Ok(values[0])
    }

    fn take_usizes(&mut self, path: &str) -> Result<Vec<usize>, TranscriptSchemaError> {
        match self.take(path)? {
            TranscriptValue::Usizes(values) => Ok(values.clone()),
            value => Err(TranscriptSchemaError::WrongKind {
                path: path.to_string(),
                expected: "usizes",
                got: value.kind(),
            }),
        }
    }

    fn take_usize_one(&mut self, path: &str) -> Result<usize, TranscriptSchemaError> {
        let values = self.take_usizes(path)?;
        if values.len() != 1 {
            return Err(TranscriptSchemaError::WrongLength {
                path: path.to_string(),
                expected: 1,
                got: values.len(),
            });
        }
        Ok(values[0])
    }

    fn take_bool(&mut self, path: &str) -> Result<bool, TranscriptSchemaError> {
        match self.take(path)? {
            TranscriptValue::Bool(value) => Ok(*value),
            value => Err(TranscriptSchemaError::WrongKind {
                path: path.to_string(),
                expected: "bool",
                got: value.kind(),
            }),
        }
    }

    fn take_profile(
        &mut self,
        path: &str,
    ) -> Result<pcs::ligerito::LigeritoProfile, TranscriptSchemaError> {
        match self.take(path)? {
            TranscriptValue::LigeritoProfile(value) => Ok(*value),
            value => Err(TranscriptSchemaError::WrongKind {
                path: path.to_string(),
                expected: "ligerito_profile",
                got: value.kind(),
            }),
        }
    }

    fn finish(&self) -> Result<(), TranscriptSchemaError> {
        if self.cursor == self.fields.len() {
            Ok(())
        } else {
            Err(TranscriptSchemaError::TrailingFields {
                remaining: self.fields.len() - self.cursor,
            })
        }
    }
}

fn bytes32(path: &str, value: &[u8]) -> Result<[u8; 32], TranscriptSchemaError> {
    value
        .try_into()
        .map_err(|_| TranscriptSchemaError::WrongLength {
            path: path.to_string(),
            expected: 32,
            got: value.len(),
        })
}

fn rebuild_commitment(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<Commitment, TranscriptSchemaError> {
    Ok(Commitment {
        root: reader.take_bytes32(&format!("{path}.root"))?,
        params: rebuild_pcs_params(reader, &format!("{path}.params"))?,
    })
}

fn rebuild_pcs_params(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<PcsParams, TranscriptSchemaError> {
    Ok(PcsParams {
        m: reader.take_usize_one(&format!("{path}.m"))?,
        log_inv_rate: reader.take_usize_one(&format!("{path}.log_inv_rate"))?,
        log_batch_size: reader.take_usize_one(&format!("{path}.log_batch_size"))?,
        profile: reader.take_profile(&format!("{path}.profile"))?,
        zk: reader.take_bool(&format!("{path}.zk"))?,
    })
}

fn rebuild_initial_tree_nonces(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<InitialTreeNonces, TranscriptSchemaError> {
    Ok(InitialTreeNonces {
        outer: reader.take_bytes32(&format!("{path}.outer"))?,
        veil_linear: reader.take_bytes32(&format!("{path}.veil_linear"))?,
        veil_hadamard: reader.take_bytes32(&format!("{path}.veil_hadamard"))?,
    })
}

fn rebuild_masked_zerocheck(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<MaskedZerocheckProof, TranscriptSchemaError> {
    Ok(MaskedZerocheckProof {
        round1_ab: reader.take_scalars(&format!("{path}.round1_ab"))?,
        round1_c: reader.take_scalars(&format!("{path}.round1_c"))?,
        multilinear_rounds: rebuild_pairs(
            &format!("{path}.multilinear_rounds"),
            reader.take_scalars(&format!("{path}.multilinear_rounds"))?,
        )?,
        final_a_eval: reader.take_scalar_one(&format!("{path}.final_a_eval"))?,
        final_b_eval: reader.take_scalar_one(&format!("{path}.final_b_eval"))?,
    })
}

fn rebuild_lincheck(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<LincheckProof, TranscriptSchemaError> {
    Ok(LincheckProof {
        rounds: rebuild_pairs(
            &format!("{path}.rounds"),
            reader.take_scalars(&format!("{path}.rounds"))?,
        )?,
        z_partial: reader.take_scalars(&format!("{path}.z_partial"))?,
    })
}

fn rebuild_masked_ring_claim(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<MaskedRingClaim, TranscriptSchemaError> {
    Ok(MaskedRingClaim {
        witness: reader.take_scalars(&format!("{path}.witness"))?,
        blind: reader.take_scalars(&format!("{path}.blind"))?,
    })
}

fn rebuild_batch_opening(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<BatchOpeningProofLigerito, TranscriptSchemaError> {
    let ring_switch_len = reader.take_usize_one(&format!("{path}.ring_switches.len"))?;
    let ring_switches = (0..ring_switch_len)
        .map(|i| {
            Ok(pcs::RingSwitchProof {
                s_hat_v: reader.take_scalars(&format!("{path}.ring_switches.{i}.s_hat_v"))?,
            })
        })
        .collect::<Result<Vec<_>, TranscriptSchemaError>>()?;
    let ligerito = rebuild_ligerito(reader, &format!("{path}.ligerito"))?;
    let zk_blind = if reader.take_bool(&format!("{path}.zk_blind.present"))? {
        Some(ZkBlindOpening {
            y_g: reader.take_scalar_one(&format!("{path}.zk_blind.y_g"))?,
            c_grind_nonce: reader.take_u64_one(&format!("{path}.zk_blind.c_grind_nonce"))?,
        })
    } else {
        None
    };
    Ok(BatchOpeningProofLigerito {
        ring_switches,
        ligerito,
        zk_blind,
    })
}

fn rebuild_ligerito(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<LigeritoProof, TranscriptSchemaError> {
    let initial_root = reader.take_bytes32(&format!("{path}.initial_root"))?;
    let initial_proof = rebuild_recursive_proof(reader, &format!("{path}.initial_proof"))?;
    let recursive_roots = reader.take_bytes32_many(&format!("{path}.recursive_roots"))?;
    let recursive_proof_len = reader.take_usize_one(&format!("{path}.recursive_proofs.len"))?;
    let recursive_proofs = (0..recursive_proof_len)
        .map(|i| rebuild_recursive_proof(reader, &format!("{path}.recursive_proofs.{i}")))
        .collect::<Result<Vec<_>, _>>()?;
    let final_proof = rebuild_final_proof(reader, &format!("{path}.final_proof"))?;
    let sumcheck_scalars = reader.take_scalars(&format!("{path}.sumcheck_transcript"))?;
    Ok(LigeritoProof {
        initial_root,
        initial_proof,
        recursive_roots,
        recursive_proofs,
        final_proof,
        sumcheck_transcript: rebuild_sumcheck_messages(
            &format!("{path}.sumcheck_transcript"),
            sumcheck_scalars,
        )?,
        grinding_nonces: reader.take_u64s(&format!("{path}.grinding_nonces"))?,
        ood_values: reader.take_scalars(&format!("{path}.ood_values"))?,
        fold_grinding_nonces: reader.take_u64s(&format!("{path}.fold_grinding_nonces"))?,
    })
}

fn rebuild_recursive_proof(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<RecursiveProof, TranscriptSchemaError> {
    Ok(RecursiveProof {
        opened_rows: reader.take_scalar_rows(&format!("{path}.opened_rows"))?,
        leaf_salts: reader.take_bytes32_many(&format!("{path}.leaf_salts"))?,
        merkle_proof: reader.take_bytes32_many(&format!("{path}.merkle_proof"))?,
    })
}

fn rebuild_final_proof(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<FinalProof, TranscriptSchemaError> {
    Ok(FinalProof {
        yr: reader.take_scalars(&format!("{path}.yr"))?,
        opened_rows: reader.take_scalar_rows(&format!("{path}.opened_rows"))?,
        merkle_proof: reader.take_bytes32_many(&format!("{path}.merkle_proof"))?,
    })
}

fn rebuild_constraint_proof(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<ConstraintProof, TranscriptSchemaError> {
    Ok(ConstraintProof {
        parameters: rebuild_constraint_parameters(reader, &format!("{path}.parameters"))?,
        num_variables: reader.take_usize_one(&format!("{path}.num_variables"))?,
        num_multiplications: reader.take_usize_one(&format!("{path}.num_multiplications"))?,
        hadamard: rebuild_hadamard_proof(reader, &format!("{path}.hadamard"))?,
        linear: rebuild_dot_product_proof(reader, &format!("{path}.linear"))?,
    })
}

fn rebuild_constraint_parameters(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<ConstraintParameters, TranscriptSchemaError> {
    Ok(ConstraintParameters {
        linear_padding: reader.take_usize_one(&format!("{path}.linear_padding"))?,
        hadamard_padding: reader.take_usize_one(&format!("{path}.hadamard_padding"))?,
        inverse_rate: reader.take_usize_one(&format!("{path}.inverse_rate"))?,
    })
}

fn rebuild_vector_parameters(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<VectorParameters, TranscriptSchemaError> {
    Ok(VectorParameters {
        vector_length: reader.take_usize_one(&format!("{path}.vector_length"))?,
        padding_length: reader.take_usize_one(&format!("{path}.padding_length"))?,
        code_length: reader.take_usize_one(&format!("{path}.code_length"))?,
        num_vectors: reader.take_usize_one(&format!("{path}.num_vectors"))?,
    })
}

fn rebuild_hadamard_proof(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<HadamardProof, TranscriptSchemaError> {
    let parameters = rebuild_vector_parameters(reader, &format!("{path}.parameters"))?;
    let commitment = reader.take_bytes32(&format!("{path}.commitment"))?;
    let gamma = reader.take_scalar_one(&format!("{path}.gamma"))?;
    let phi = reader.take_scalars(&format!("{path}.phi"))?;
    let claimed_dot_products = reader.take_scalars(&format!("{path}.claimed_dot_products"))?;
    let claimed_dot_products = claimed_dot_products
        .try_into()
        .map_err(|values: Vec<F128>| TranscriptSchemaError::WrongLength {
            path: format!("{path}.claimed_dot_products"),
            expected: 3,
            got: values.len(),
        })?;
    Ok(HadamardProof {
        parameters,
        commitment,
        gamma,
        phi,
        claimed_dot_products,
        mask_dot_product: reader.take_scalar_one(&format!("{path}.mask_dot_product"))?,
        rlc_vector: reader.take_scalars(&format!("{path}.rlc_vector"))?,
        rlc_padding: reader.take_scalars(&format!("{path}.rlc_padding"))?,
        opening: rebuild_merkle_matrix_opening(reader, &format!("{path}.opening"))?,
    })
}

fn rebuild_dot_product_proof(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<DotProductProof, TranscriptSchemaError> {
    Ok(DotProductProof {
        parameters: rebuild_vector_parameters(reader, &format!("{path}.parameters"))?,
        commitment: reader.take_bytes32(&format!("{path}.commitment"))?,
        claimed_dot_products: reader.take_scalars(&format!("{path}.claimed_dot_products"))?,
        mask_dot_product: reader.take_scalar_one(&format!("{path}.mask_dot_product"))?,
        rlc_vector: reader.take_scalars(&format!("{path}.rlc_vector"))?,
        rlc_padding: reader.take_scalars(&format!("{path}.rlc_padding"))?,
        opening: rebuild_merkle_matrix_opening(reader, &format!("{path}.opening"))?,
    })
}

fn rebuild_merkle_matrix_opening(
    reader: &mut FieldReader<'_>,
    path: &str,
) -> Result<MerkleMatrixOpening, TranscriptSchemaError> {
    Ok(MerkleMatrixOpening {
        positions: reader.take_usizes(&format!("{path}.positions"))?,
        rows: reader.take_scalars(&format!("{path}.rows"))?,
        salts: reader.take_bytes32_many(&format!("{path}.salts"))?,
        siblings: reader.take_bytes32_many(&format!("{path}.siblings"))?,
    })
}

fn rebuild_pairs(
    path: &str,
    values: Vec<F128>,
) -> Result<Vec<(F128, F128)>, TranscriptSchemaError> {
    if !values.len().is_multiple_of(2) {
        return Err(TranscriptSchemaError::WrongLength {
            path: path.to_string(),
            expected: values.len() + 1,
            got: values.len(),
        });
    }
    let (pairs, remainder) = values.as_chunks::<2>();
    debug_assert!(remainder.is_empty());
    Ok(pairs.iter().map(|[left, right]| (*left, *right)).collect())
}

fn rebuild_sumcheck_messages(
    path: &str,
    values: Vec<F128>,
) -> Result<Vec<SumcheckMessage>, TranscriptSchemaError> {
    Ok(rebuild_pairs(path, values)?
        .into_iter()
        .map(|(u_0, u_2)| SumcheckMessage { u_0, u_2 })
        .collect())
}

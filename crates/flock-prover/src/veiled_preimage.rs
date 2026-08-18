//! End-to-end VEIL mode for FLOCK's fixed-digest BLAKE3 relation.
//!
//! This experimental path proves FLOCK's native Boolean block R1CS with the
//! characteristic-two VEIL code in `veil-f128`.  It uses FLOCK's optimized
//! BLAKE3 witness generator and keeps the substituted sparse matrices native;
//! expanding those matrices into a generic arithmetic circuit would require
//! more than ten gigabytes even for one compression.

use flock_core::{
    challenger::Challenger,
    field::F128,
    pcs::unpack_witness,
    r1cs::BlockR1cs,
    ro::RoContext,
    zk::{MaskSampler, ZkRng},
};
use serde::{Deserialize, Serialize};
use veil_f128::{
    BlockR1csError, BlockR1csParameters, BlockR1csProof, OracleProgrammer, OracleProgrammingError,
    PublicEquality, SimulationError, prove_block_r1cs_framed, simulate_block_r1cs,
    verify_block_r1cs_framed,
};

use crate::r1cs_hashes::{
    blake3::{
        K, OUT_LO_BASE, ParamPinning, Z_CONST_POS, build_block_r1cs_veil_pinned,
        generate_witness_with_ab_packed,
    },
    blake3_preimage::{DIGEST_BYTES, MESSAGE_BYTES, PreimageError, message_compression},
};
use crate::sim_oracle::{SharedOracle, ro_context};

const TRANSCRIPT_LABEL: &[u8] = b"veiled-flock-blake3-preimage-direct-v1";

#[derive(Clone, Debug)]
pub struct VeiledBlake3Setup {
    n_blocks: usize,
    r1cs: BlockR1cs,
    parameters: BlockR1csParameters,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VeiledBlake3Proof {
    pub version: u32,
    pub n_blocks: usize,
    pub r1cs_digest: [u8; 32],
    pub commitment_nonce: [u8; 32],
    pub r1cs: BlockR1csProof,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VeiledPreimageError {
    Preimage(PreimageError),
    Veil(BlockR1csError),
    Simulation(SimulationError),
    WrongProofShape,
    Decode,
}

impl From<PreimageError> for VeiledPreimageError {
    fn from(value: PreimageError) -> Self {
        Self::Preimage(value)
    }
}

impl From<BlockR1csError> for VeiledPreimageError {
    fn from(value: BlockR1csError) -> Self {
        Self::Veil(value)
    }
}

impl From<SimulationError> for VeiledPreimageError {
    fn from(value: SimulationError) -> Self {
        Self::Simulation(value)
    }
}

struct SharedOracleProgrammer(SharedOracle);

impl OracleProgrammer for SharedOracleProgrammer {
    fn program_fresh(&self, point: Vec<u8>, value: [u8; 32]) -> Result<(), OracleProgrammingError> {
        let mut oracle = self.0.lock().map_err(|_| OracleProgrammingError)?;
        if oracle.was_queried(&point) || oracle.program(point, value).is_some() {
            return Err(OracleProgrammingError);
        }
        Ok(())
    }
}

impl VeiledBlake3Setup {
    pub fn new(n_blocks: usize) -> Self {
        assert!(n_blocks > 0, "n_blocks must be non-zero");
        let n_log = n_blocks.next_power_of_two().trailing_zeros() as usize;
        Self {
            n_blocks,
            r1cs: build_block_r1cs_veil_pinned(n_log, ParamPinning::RootHash64),
            parameters: BlockR1csParameters::experimental(),
        }
    }

    pub fn n_blocks(&self) -> usize {
        self.n_blocks
    }

    pub fn parameters(&self) -> BlockR1csParameters {
        self.parameters
    }

    pub fn prove<C: Challenger>(
        &self,
        messages: &[[u8; MESSAGE_BYTES]],
        digests: &[[u8; DIGEST_BYTES]],
        rng: &mut ZkRng,
        challenger: &mut C,
    ) -> Result<VeiledBlake3Proof, VeiledPreimageError> {
        validate_witness(self.n_blocks, messages, digests)?;
        let mut compressions: Vec<_> = messages.iter().map(message_compression).collect();
        compressions.resize(
            self.r1cs.n_outer(),
            ParamPinning::RootHash64.padding_compression(),
        );
        let (z_packed, a_packed, b_packed) =
            generate_witness_with_ab_packed(&compressions, self.r1cs.n_log());
        let z = unpack_as_field(&z_packed, self.r1cs.m);
        let a = unpack_as_field(&a_packed, self.r1cs.m);
        let b = unpack_as_field(&b_packed, self.r1cs.m);
        let public = public_equalities(&self.r1cs, self.n_blocks, digests)?;

        let r1cs_digest = self.r1cs.statement_digest();
        let mut nonce_fields = [F128::ZERO; 2];
        rng.fill_f128(&mut nonce_fields);
        let commitment_nonce = fields_to_nonce(nonce_fields);
        let ro = RoContext::native(commitment_nonce);
        absorb_statement(
            challenger,
            self.n_blocks,
            &r1cs_digest,
            &commitment_nonce,
            digests,
        );
        let r1cs = prove_block_r1cs_framed(
            &self.r1cs,
            &z,
            &a,
            &b,
            &public,
            self.parameters,
            rng,
            challenger,
            &ro,
        )?;
        Ok(VeiledBlake3Proof {
            version: 1,
            n_blocks: self.n_blocks,
            r1cs_digest,
            commitment_nonce,
            r1cs,
        })
    }

    pub fn verify<C: Challenger>(
        &self,
        proof: &VeiledBlake3Proof,
        digests: &[[u8; DIGEST_BYTES]],
        challenger: &mut C,
    ) -> Result<(), VeiledPreimageError> {
        if proof.version != 1
            || proof.n_blocks != self.n_blocks
            || proof.r1cs_digest != self.r1cs.statement_digest()
            || proof.r1cs.parameters != self.parameters
            || digests.len() != self.n_blocks
        {
            return Err(VeiledPreimageError::WrongProofShape);
        }
        let public = public_equalities(&self.r1cs, self.n_blocks, digests)?;
        absorb_statement(
            challenger,
            self.n_blocks,
            &proof.r1cs_digest,
            &proof.commitment_nonce,
            digests,
        );
        let ro = RoContext::native(proof.commitment_nonce);
        verify_block_r1cs_framed(&self.r1cs, &public, &proof.r1cs, challenger, &ro)?;
        Ok(())
    }

    /// Produce an accepting ROM transcript from the public digests alone.
    /// No preimage or witness is accepted by this API.
    pub fn simulate<C: Challenger>(
        &self,
        digests: &[[u8; DIGEST_BYTES]],
        rng: &mut ZkRng,
        challenger: &mut C,
        oracle: SharedOracle,
    ) -> Result<VeiledBlake3Proof, VeiledPreimageError> {
        if digests.len() != self.n_blocks {
            return Err(VeiledPreimageError::WrongProofShape);
        }
        let public = public_equalities(&self.r1cs, self.n_blocks, digests)?;
        let r1cs_digest = self.r1cs.statement_digest();
        let mut nonce_fields = [F128::ZERO; 2];
        rng.fill_f128(&mut nonce_fields);
        let commitment_nonce = fields_to_nonce(nonce_fields);
        absorb_statement(
            challenger,
            self.n_blocks,
            &r1cs_digest,
            &commitment_nonce,
            digests,
        );
        let programmer = SharedOracleProgrammer(oracle);
        let r1cs = simulate_block_r1cs(
            &self.r1cs,
            &public,
            self.parameters,
            &commitment_nonce,
            rng,
            challenger,
            &programmer,
        )?;
        Ok(VeiledBlake3Proof {
            version: 1,
            n_blocks: self.n_blocks,
            r1cs_digest,
            commitment_nonce,
            r1cs,
        })
    }

    /// Verify through a caller-supplied random oracle. Honest proofs work
    /// against an empty table; simulated proofs use the table programmed by
    /// [`Self::simulate`]. The algebraic verifier is otherwise identical.
    pub fn verify_with_oracle<C: Challenger>(
        &self,
        proof: &VeiledBlake3Proof,
        digests: &[[u8; DIGEST_BYTES]],
        challenger: &mut C,
        oracle: SharedOracle,
    ) -> Result<(), VeiledPreimageError> {
        if proof.version != 1
            || proof.n_blocks != self.n_blocks
            || proof.r1cs_digest != self.r1cs.statement_digest()
            || proof.r1cs.parameters != self.parameters
            || digests.len() != self.n_blocks
        {
            return Err(VeiledPreimageError::WrongProofShape);
        }
        let public = public_equalities(&self.r1cs, self.n_blocks, digests)?;
        absorb_statement(
            challenger,
            self.n_blocks,
            &proof.r1cs_digest,
            &proof.commitment_nonce,
            digests,
        );
        let ro = ro_context(proof.commitment_nonce, oracle);
        verify_block_r1cs_framed(&self.r1cs, &public, &proof.r1cs, challenger, &ro)?;
        Ok(())
    }
}

impl VeiledBlake3Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("veiled proof serialization")
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, VeiledPreimageError> {
        let proof: Self = bincode::deserialize(bytes).map_err(|_| VeiledPreimageError::Decode)?;
        if bincode::serialize(&proof).map_err(|_| VeiledPreimageError::Decode)? != bytes {
            return Err(VeiledPreimageError::Decode);
        }
        Ok(proof)
    }
}

fn validate_witness(
    n_blocks: usize,
    messages: &[[u8; MESSAGE_BYTES]],
    digests: &[[u8; DIGEST_BYTES]],
) -> Result<(), PreimageError> {
    if messages.len() != n_blocks || digests.len() != n_blocks {
        return Err(PreimageError::BatchSizeMismatch {
            expected: n_blocks,
            got: messages.len().max(digests.len()),
        });
    }
    for (index, (message, digest)) in messages.iter().zip(digests).enumerate() {
        if ::blake3::hash(message).as_bytes() != digest {
            return Err(PreimageError::DigestMismatch { index });
        }
    }
    Ok(())
}

fn unpack_as_field(packed: &[F128], m: usize) -> Vec<F128> {
    unpack_witness(packed, m)
        .into_iter()
        .map(|bit| if bit { F128::ONE } else { F128::ZERO })
        .collect()
}

fn fields_to_nonce(fields: [F128; 2]) -> [u8; 32] {
    let mut nonce = [0u8; 32];
    nonce[..8].copy_from_slice(&fields[0].lo.to_le_bytes());
    nonce[8..16].copy_from_slice(&fields[0].hi.to_le_bytes());
    nonce[16..24].copy_from_slice(&fields[1].lo.to_le_bytes());
    nonce[24..].copy_from_slice(&fields[1].hi.to_le_bytes());
    nonce
}

fn public_equalities(
    r1cs: &BlockR1cs,
    n_blocks: usize,
    digests: &[[u8; DIGEST_BYTES]],
) -> Result<Vec<PublicEquality>, VeiledPreimageError> {
    if digests.len() != n_blocks || n_blocks > r1cs.n_outer() {
        return Err(VeiledPreimageError::WrongProofShape);
    }
    let padding_digest = *::blake3::hash(&[0u8; MESSAGE_BYTES]).as_bytes();
    let mut equalities = Vec::with_capacity(r1cs.n_outer() * (1 + DIGEST_BYTES * 8));
    for block in 0..r1cs.n_outer() {
        let base = block * K;
        equalities.push(PublicEquality {
            index: base + Z_CONST_POS,
            value: F128::ONE,
        });
        let digest = if block < n_blocks {
            digests[block]
        } else {
            padding_digest
        };
        for bit in 0..DIGEST_BYTES * 8 {
            equalities.push(PublicEquality {
                index: base + OUT_LO_BASE + bit,
                value: if (digest[bit / 8] >> (bit % 8)) & 1 == 1 {
                    F128::ONE
                } else {
                    F128::ZERO
                },
            });
        }
    }
    Ok(equalities)
}

fn absorb_statement<C: Challenger>(
    challenger: &mut C,
    n_blocks: usize,
    r1cs_digest: &[u8; 32],
    commitment_nonce: &[u8; 32],
    digests: &[[u8; DIGEST_BYTES]],
) {
    challenger.observe_label(TRANSCRIPT_LABEL);
    challenger.observe_bytes(&(n_blocks as u64).to_le_bytes());
    challenger.observe_bytes(r1cs_digest);
    challenger.observe_bytes(commitment_nonce);
    for digest in digests {
        challenger.observe_bytes(digest);
    }
}

#[cfg(test)]
mod tests {
    use flock_core::challenger::FsChallenger;

    use super::*;
    use crate::sim_oracle::{OracleChallenger, shared_oracle};

    fn messages(n: usize) -> Vec<[u8; MESSAGE_BYTES]> {
        (0..n)
            .map(|index| std::array::from_fn(|byte| (index * 17 + byte) as u8))
            .collect()
    }

    #[test]
    fn generated_flock_witness_satisfies_native_relation_digest_and_padding() {
        let setup = VeiledBlake3Setup::new(3);
        let messages = messages(3);
        let digests = messages
            .iter()
            .map(|message| *::blake3::hash(message).as_bytes())
            .collect::<Vec<_>>();
        let mut compressions: Vec<_> = messages.iter().map(message_compression).collect();
        compressions.resize(
            setup.r1cs.n_outer(),
            ParamPinning::RootHash64.padding_compression(),
        );
        let (z_packed, a_packed, b_packed) =
            generate_witness_with_ab_packed(&compressions, setup.r1cs.n_log());
        let z = unpack_as_field(&z_packed, setup.r1cs.m);
        let a = unpack_as_field(&a_packed, setup.r1cs.m);
        let b = unpack_as_field(&b_packed, setup.r1cs.m);
        assert!(
            z.iter()
                .zip(&a)
                .zip(&b)
                .all(|((z, a), b)| *z * *z == *z && *a * *b == *z)
        );
        for equality in public_equalities(&setup.r1cs, 3, &digests).unwrap() {
            assert_eq!(z[equality.index], equality.value);
        }
    }

    #[test]
    #[ignore = "full native VEIL proof; run in release mode"]
    fn veiled_preimage_proof_roundtrip() {
        let setup = VeiledBlake3Setup::new(2);
        let messages = messages(2);
        let digests = messages
            .iter()
            .map(|message| *::blake3::hash(message).as_bytes())
            .collect::<Vec<_>>();
        let mut rng = ZkRng::from_seed([73; 32]);
        let mut prover = FsChallenger::new(b"veiled-flock-e2e-test");
        let proof = setup
            .prove(&messages, &digests, &mut rng, &mut prover)
            .unwrap();
        let bytes = proof.to_bytes();
        for message in &messages {
            assert!(
                !bytes.windows(MESSAGE_BYTES).any(|window| window == message),
                "a serialized proof must not contain a raw preimage"
            );
        }
        let decoded = VeiledBlake3Proof::from_bytes(&bytes).unwrap();
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(VeiledBlake3Proof::from_bytes(&trailing).is_err());
        let mut verifier = FsChallenger::new(b"veiled-flock-e2e-test");
        setup.verify(&decoded, &digests, &mut verifier).unwrap();
        let oracle = shared_oracle();
        let mut verifier = OracleChallenger::new(b"veiled-flock-e2e-test", oracle.clone());
        setup
            .verify_with_oracle(&decoded, &digests, &mut verifier, oracle.clone())
            .unwrap();
        assert!(oracle.lock().unwrap().is_empty());

        let mut wrong_digests = digests.clone();
        wrong_digests[0][0] ^= 1;
        let mut verifier = FsChallenger::new(b"veiled-flock-e2e-test");
        assert!(
            setup
                .verify(&decoded, &wrong_digests, &mut verifier)
                .is_err()
        );

        let mut bad_gamma = decoded.clone();
        bad_gamma.r1cs.hadamard.gamma += F128::ONE;
        let mut verifier = FsChallenger::new(b"veiled-flock-e2e-test");
        assert!(setup.verify(&bad_gamma, &digests, &mut verifier).is_err());

        let mut bad_opening = decoded.clone();
        bad_opening.r1cs.witness.opening.rows[0] += F128::ONE;
        let mut verifier = FsChallenger::new(b"veiled-flock-e2e-test");
        assert!(setup.verify(&bad_opening, &digests, &mut verifier).is_err());

        let mut bad_nonce = decoded.clone();
        bad_nonce.commitment_nonce[0] ^= 1;
        let mut verifier = FsChallenger::new(b"veiled-flock-e2e-test");
        assert!(setup.verify(&bad_nonce, &digests, &mut verifier).is_err());
        eprintln!("veiled FLOCK proof bytes: {}", bytes.len());
    }

    #[test]
    #[ignore = "full statement-only simulator; run in release mode"]
    fn statement_only_simulator_is_accepted_by_programmed_oracle() {
        let setup = VeiledBlake3Setup::new(2);
        // The simulator receives this digest, never the message that produced it.
        let hidden_messages = [[0xa7u8; MESSAGE_BYTES], [0x3cu8; MESSAGE_BYTES]];
        let digests = hidden_messages
            .iter()
            .map(|message| *::blake3::hash(message).as_bytes())
            .collect::<Vec<_>>();

        let oracle = shared_oracle();
        let mut rng = ZkRng::from_seed([91; 32]);
        let mut simulator = OracleChallenger::new(b"veiled-flock-simulator-test", oracle.clone());
        let proof = setup
            .simulate(&digests, &mut rng, &mut simulator, oracle.clone())
            .unwrap();
        let proof = VeiledBlake3Proof::from_bytes(&proof.to_bytes()).unwrap();

        let mut verifier = OracleChallenger::new(b"veiled-flock-simulator-test", oracle.clone());
        setup
            .verify_with_oracle(&proof, &digests, &mut verifier, oracle.clone())
            .unwrap();
        assert!(oracle.lock().unwrap().programmed_len() > 0);

        // The same transcript is not a real-hash forgery: its acceptance is
        // specifically the ROM simulator game.
        let mut native = FsChallenger::new(b"veiled-flock-simulator-test");
        assert!(setup.verify(&proof, &digests, &mut native).is_err());

        let mut wrong = digests.clone();
        wrong[0][0] ^= 1;
        let mut verifier = OracleChallenger::new(b"veiled-flock-simulator-test", oracle.clone());
        assert!(
            setup
                .verify_with_oracle(&proof, &wrong, &mut verifier, oracle)
                .is_err()
        );
    }
}

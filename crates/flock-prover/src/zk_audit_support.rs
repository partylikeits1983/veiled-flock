//! Shared support for the ZK audit/certificate suites.
//!
//! Everything here is measurement plumbing for the leakage certificates and
//! transcript-schema tests: a transcript-recording challenger wrapper, small
//! hand-built Ligerito configs for fixture shapes outside the production
//! ladder, and the m=15 "masked identity" fixture that runs the complete A1′
//! pipeline at certificate-probeable size.
//!
//! Nothing in this module weakens the proving API: [`RecordingChallenger`]
//! wraps a real challenger and only *records* what flows through it.

use std::sync::{Arc, Mutex};

use flock_core::challenger::Challenger;
use flock_core::field::F128;
use flock_core::lincheck::pack_z_lincheck_from_packed;
use flock_core::pcs::ligerito::{ProverConfig, VerifierConfig};
use flock_core::pcs::{self, Commitment, PcsParams};
use flock_core::r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout};
use flock_core::verifier::VerifyError;
use flock_core::zk::ZkRng;

use crate::prover::{
    R1csProofZkA1, prove_r1cs_zk_a1_with_config, verify_r1cs_zk_a1_with_config,
};

// ---------------------------------------------------------------------------
// Recording challenger
// ---------------------------------------------------------------------------

/// One recorded transcript operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedOp {
    Label(Vec<u8>),
    F128(F128),
    Bytes(Vec<u8>),
    Sample(F128),
}

/// Challenger wrapper that records every observation and sample flowing
/// through it while forwarding to the wrapped challenger unchanged.
///
/// Clones share the same log (`Arc`), so the domain-separated challenger
/// forks the A1′ prover makes for the P/Q openings append to one sequential
/// record — the prover is sequential, so the combined order is
/// deterministic.
pub struct RecordingChallenger<C> {
    pub inner: C,
    pub log: Arc<Mutex<Vec<RecordedOp>>>,
}

impl<C> RecordingChallenger<C> {
    pub fn new(inner: C) -> Self {
        Self { inner, log: Arc::new(Mutex::new(Vec::new())) }
    }
    /// Snapshot of the recorded operations.
    pub fn recorded(&self) -> Vec<RecordedOp> {
        self.log.lock().unwrap().clone()
    }
    /// The recorded F128 *observations* (samples and labels excluded).
    pub fn observed_f128s(&self) -> Vec<F128> {
        self.log
            .lock()
            .unwrap()
            .iter()
            .filter_map(|op| match op {
                RecordedOp::F128(v) => Some(*v),
                _ => None,
            })
            .collect()
    }
    /// The recorded byte observations.
    pub fn observed_bytes(&self) -> Vec<Vec<u8>> {
        self.log
            .lock()
            .unwrap()
            .iter()
            .filter_map(|op| match op {
                RecordedOp::Bytes(b) => Some(b.clone()),
                _ => None,
            })
            .collect()
    }
    /// The recorded challenge samples, in order.
    pub fn sampled_f128s(&self) -> Vec<F128> {
        self.log
            .lock()
            .unwrap()
            .iter()
            .filter_map(|op| match op {
                RecordedOp::Sample(v) => Some(*v),
                _ => None,
            })
            .collect()
    }
}

impl<C: Clone> Clone for RecordingChallenger<C> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone(), log: Arc::clone(&self.log) }
    }
}

impl<C: Challenger> Challenger for RecordingChallenger<C> {
    fn observe_label(&mut self, label: &[u8]) {
        self.log.lock().unwrap().push(RecordedOp::Label(label.to_vec()));
        self.inner.observe_label(label);
    }
    fn observe_f128(&mut self, value: F128) {
        self.log.lock().unwrap().push(RecordedOp::F128(value));
        self.inner.observe_f128(value);
    }
    fn observe_f128_slice(&mut self, values: &[F128]) {
        {
            let mut log = self.log.lock().unwrap();
            log.extend(values.iter().map(|v| RecordedOp::F128(*v)));
        }
        // Forward the slice form: FsChallenger tags slices differently from
        // per-element observes, so the wrapper must not re-shape the call.
        self.inner.observe_f128_slice(values);
    }
    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.log.lock().unwrap().push(RecordedOp::Bytes(bytes.to_vec()));
        self.inner.observe_bytes(bytes);
    }
    fn sample_f128(&mut self) -> F128 {
        let v = self.inner.sample_f128();
        self.log.lock().unwrap().push(RecordedOp::Sample(v));
        v
    }
    fn grind_pow(&mut self, bits: u32) -> u64 {
        self.inner.grind_pow(bits)
    }
    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.inner.verify_pow(nonce, bits)
    }
}

// ---------------------------------------------------------------------------
// Tiny Ligerito configs
// ---------------------------------------------------------------------------

/// Hand-built Ligerito config pair for audit fixtures whose committed shape
/// (`log_n = log_msg_len`) is below the production config ladder. Mirrors
/// the m=13 `tiny_zk_configs` used by the PCS zk roundtrip tests:
/// `initial_k = 2` (so `PcsParams.log_batch_size` must be 2), two recursive
/// k=2 steps, small query counts, no grinding/OOD. Security level is
/// irrelevant here — these shapes exist to make exact certificates cheap,
/// not to be sound against adversaries.
pub fn tiny_zk_configs_for(log_n: usize) -> (ProverConfig, VerifierConfig) {
    assert!(log_n >= 7, "tiny config needs log_n >= 7");
    let recursive_ks = vec![2usize, 2];
    let log_inv_rates = vec![1usize, 2, 3];
    let queries = vec![6usize, 4, 4];
    let n_levels = log_inv_rates.len();
    let p = ProverConfig {
        log_inv_rates: log_inv_rates.clone(),
        recursive_steps: recursive_ks.len(),
        initial_log_msg_cols: log_n - 2,
        initial_log_num_interleaved: 2,
        initial_k: 2,
        recursive_log_msg_cols: vec![log_n - 4, log_n - 6],
        recursive_ks: recursive_ks.clone(),
        queries: queries.clone(),
        grinding_bits: vec![0; n_levels],
        fold_grinding_bits: vec![0; n_levels],
        ood_samples: vec![0; n_levels],
    };
    let v = VerifierConfig {
        log_inv_rates,
        recursive_steps: recursive_ks.len(),
        initial_log_msg_cols: log_n - 2,
        initial_log_num_interleaved: 2,
        initial_k: 2,
        recursive_log_msg_cols: vec![log_n - 4, log_n - 6],
        recursive_ks,
        queries,
        grinding_bits: vec![0; n_levels],
        fold_grinding_bits: vec![0; n_levels],
        ood_samples: vec![0; n_levels],
    };
    (p, v)
}

// ---------------------------------------------------------------------------
// The m=15 masked-identity fixture (full A1′ pipeline at certificate size)
// ---------------------------------------------------------------------------

/// The m=15 "masked identity" statement used by the PIOP leakage
/// certificates, packaged to run the **complete** A1′ pipeline
/// (hiding commits, masked zerocheck, lincheck, hiding witness/P/Q
/// openings) rather than the zerocheck layer alone.
///
/// Layout per 2^12-slot block: slot 0 = constant one; 64 payload bits;
/// 16 product rows (`payload[2i]·payload[2i+1]`); 24×128 A-type randomizer
/// bits (`u·1 = u`); 2×128 B-type randomizer bits (`1·u = u`). 8 blocks.
pub struct FixtureA1M15 {
    pub r1cs: BlockR1cs,
    pub pcs_params: PcsParams,
    pub lig_prover: ProverConfig,
    pub lig_verifier: VerifierConfig,
}

impl FixtureA1M15 {
    pub const M: usize = 15;
    pub const K_LOG: usize = 12;
    pub const K_SKIP: usize = 6;
    pub const BLOCKS: usize = 1 << (Self::M - Self::K_LOG);
    pub const PAYLOAD_BASE: usize = 1;
    pub const N_PAYLOAD: usize = 64;
    pub const PROD_BASE: usize = Self::PAYLOAD_BASE + Self::N_PAYLOAD;
    pub const N_PROD: usize = 16;
    pub const A_RAND_BASE: usize = 128;
    pub const N_A_RAND: usize = 24 * 128;
    pub const B_RAND_BASE: usize = Self::A_RAND_BASE + Self::N_A_RAND;
    pub const N_B_RAND: usize = 2 * 128;
    pub const USEFUL: usize = Self::B_RAND_BASE + Self::N_B_RAND;
    pub const A_BITS: usize = Self::N_A_RAND * Self::BLOCKS;
    pub const B_BITS: usize = Self::N_B_RAND * Self::BLOCKS;

    pub fn new() -> Self {
        let k = 1usize << Self::K_LOG;
        let mut a_rows: Vec<Vec<usize>> = vec![Vec::new(); k];
        let mut b_rows: Vec<Vec<usize>> = vec![Vec::new(); k];
        a_rows[0] = vec![0];
        b_rows[0] = vec![0];
        for s in Self::PAYLOAD_BASE..Self::PAYLOAD_BASE + Self::N_PAYLOAD {
            a_rows[s] = vec![s];
            b_rows[s] = vec![0];
        }
        for i in 0..Self::N_PROD {
            let s = Self::PROD_BASE + i;
            a_rows[s] = vec![Self::PAYLOAD_BASE + 2 * i];
            b_rows[s] = vec![Self::PAYLOAD_BASE + 2 * i + 1];
        }
        for s in Self::A_RAND_BASE..Self::A_RAND_BASE + Self::N_A_RAND {
            a_rows[s] = vec![s];
            b_rows[s] = vec![0];
        }
        for s in Self::B_RAND_BASE..Self::B_RAND_BASE + Self::N_B_RAND {
            a_rows[s] = vec![0];
            b_rows[s] = vec![s];
        }
        let identity = SparseBinaryMatrix {
            num_rows: k,
            num_cols: k,
            rows: (0..k).map(|i| vec![i]).collect(),
        };
        let r1cs = BlockR1cs {
            m: Self::M,
            k_log: Self::K_LOG,
            k_skip: Self::K_SKIP,
            useful_bits: Self::USEFUL,
            a_0: SparseBinaryMatrix { num_rows: k, num_cols: k, rows: a_rows },
            b_0: SparseBinaryMatrix { num_rows: k, num_cols: k, rows: b_rows },
            c_0: identity,
            layout: WitnessLayout::RowMajor,
            const_pin: None,
            zk: None, // randomizer rows are hand-rolled above, not layout-derived
            digest_cache: std::sync::OnceLock::new(),
            csc_cache: std::sync::OnceLock::new(),
        };
        let pcs_params = PcsParams {
            m: Self::M,
            log_inv_rate: 1,
            log_batch_size: 2,
            profile: Default::default(),
            zk: true,
        };
        let (lig_prover, lig_verifier) = tiny_zk_configs_for(pcs_params.log_msg_len());
        FixtureA1M15 { r1cs, pcs_params, lig_prover, lig_verifier }
    }

    /// Build the packed witness from payload + randomizer bit-vectors.
    pub fn witness(&self, payload: &[bool], u_a: &[bool], u_b: &[bool]) -> Vec<F128> {
        assert_eq!(payload.len(), Self::N_PAYLOAD * Self::BLOCKS);
        assert_eq!(u_a.len(), Self::A_BITS);
        assert_eq!(u_b.len(), Self::B_BITS);
        let k = 1usize << Self::K_LOG;
        let mut z = vec![false; 1 << Self::M];
        for blk in 0..Self::BLOCKS {
            let base = blk * k;
            z[base] = true;
            for j in 0..Self::N_PAYLOAD {
                z[base + Self::PAYLOAD_BASE + j] = payload[blk * Self::N_PAYLOAD + j];
            }
            for i in 0..Self::N_PROD {
                z[base + Self::PROD_BASE + i] = z[base + Self::PAYLOAD_BASE + 2 * i]
                    & z[base + Self::PAYLOAD_BASE + 2 * i + 1];
            }
            for j in 0..Self::N_A_RAND {
                z[base + Self::A_RAND_BASE + j] = u_a[blk * Self::N_A_RAND + j];
            }
            for j in 0..Self::N_B_RAND {
                z[base + Self::B_RAND_BASE + j] = u_b[blk * Self::N_B_RAND + j];
            }
        }
        pcs::pack_witness(&z, Self::M)
    }

    /// Run the complete A1′ prover on this fixture.
    pub fn prove<Ch: Challenger + Clone>(
        &self,
        z_packed: Vec<F128>,
        zk_rng: &mut ZkRng,
        challenger: &mut Ch,
    ) -> (R1csProofZkA1, Commitment) {
        let a_packed = self.r1cs.apply_a_packed(&z_packed);
        let b_packed = self.r1cs.apply_b_packed(&z_packed);
        let stripe = pack_z_lincheck_from_packed(&z_packed, Self::M, Self::K_LOG);
        let circuit = self.r1cs.sparse_lincheck_circuit();
        prove_r1cs_zk_a1_with_config(
            &self.r1cs,
            &self.pcs_params,
            z_packed,
            a_packed,
            b_packed,
            stripe,
            &circuit,
            &self.lig_prover,
            zk_rng,
            challenger,
        )
    }

    /// Verify a proof from [`Self::prove`].
    pub fn verify<Ch: Challenger + Clone>(
        &self,
        proof: &R1csProofZkA1,
        commitment: &Commitment,
        challenger: &mut Ch,
    ) -> Result<(), VerifyError> {
        let circuit = self.r1cs.sparse_lincheck_circuit();
        verify_r1cs_zk_a1_with_config(
            &self.r1cs,
            &self.pcs_params,
            proof,
            commitment,
            &circuit,
            &self.lig_verifier,
            challenger,
        )
    }
}

impl Default for FixtureA1M15 {
    fn default() -> Self {
        Self::new()
    }
}

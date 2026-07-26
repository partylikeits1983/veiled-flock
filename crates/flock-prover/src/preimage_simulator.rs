//! **The fixed-digest simulator**: an accepting proof from the public digests
//! alone, with no preimage anywhere.
//!
//! This is the object the zero-knowledge property is *about*. Everything else
//! in the zk work — the mask channels, the coverage certificates, the Lean
//! coset-uniformity theorems — exists to make the distribution this produces
//! match an honest prover's. What this module supplies is the construction.
//!
//! ## Why the old simulator does not port
//!
//! For the unbound batch statement, the simulator is the honest prover on a
//! witness it picks itself. That is legitimate only because nothing constrains
//! the witness. Here the digests are pinned, so a self-chosen message hashes
//! to the wrong thing, and a simulator that could produce a witness for a
//! *given* digest would be inverting BLAKE3. Witness-indistinguishability —
//! what every certificate in this repository measures — is also vacuous here,
//! because the preimage is essentially unique. So the simulator has to be
//! built, not inherited.
//!
//! ## The construction
//!
//! Take the verifier's checks as the specification and satisfy them by
//! construction, choosing every free coordinate and solving for the dependent
//! ones. Concretely:
//!
//! 1. **Choose the challenges.** In the ROM the simulator programs the oracle,
//!    so the challenges are inputs rather than outputs. They are drawn from the
//!    honest distribution (uniform).
//! 2. **Sample the mask cubes honestly.** `P`, `Q`, `S`, `S_c`, `S_h` carry no
//!    witness, so the simulator draws and commits them exactly as the prover
//!    does — and their opened evaluations are then true evaluations of
//!    committed data, not fabrications.
//! 3. **Fill the zerocheck backwards.** Round-1 vectors are free; the C-side
//!    evaluation is *determined* by the verifier's own interpolation; the
//!    multilinear rounds are free except that the last round's `G(∞)` is solved
//!    so the telescoped claim lands exactly on `â(ρ)b̂(ρ) + γ·P(ρ)Q(ρ)`.
//! 4. **Fill the lincheck backwards.** Round messages are free; `z_partial` is
//!    free except for one coordinate solved to hit the final inner product
//!    against the verifier's own `comb_vec`.
//! 5. **Solve a pseudo-witness.** The three evaluation claims the PCS will
//!    check — the lincheck's output claim, the zerocheck's c-claim, and the
//!    public digest claim — are affine conditions on the committed vector.
//!    Solve them. **No R1CS validity is required**, which is exactly why no
//!    preimage is needed: the zerocheck that would have demanded it was
//!    filled in step 3.
//! 6. **Open honestly.** Commit the pseudo-witness and run the unmodified
//!    opening code. Every structural relation inside the opening — codeword
//!    parity, fold linkage, the residual, `y_g` — then holds because it is
//!    *computed*, not sampled. Sampling those coordinates instead is the
//!    mistake that makes a naive "sample the whole transcript" simulator
//!    distinguishable: at deep recursion levels the opened rows satisfy public
//!    code-parity relations the verifier never checks but a distinguisher can.
//!
//! ## What this establishes, and what it does not
//!
//! It establishes that an accepting transcript exists without a witness, and —
//! run against the *unmodified* verifier through a programmable oracle — that
//! the construction is complete rather than merely plausible.
//!
//! It does **not** by itself establish indistinguishability. That is a
//! statement about distributions and needs the coverage results (restated in
//! claim-kernel form for this relation) plus the obligations listed in
//! `docs/memos/interactive-simulator-design.md`. A simulator whose output
//! verifies but is distributed differently is a real possibility and this
//! module cannot rule it out on its own.

use crate::sim_oracle::OracleChallenger;
use flock_core::challenger::Challenger;
use flock_core::field::F128;
use flock_core::pcs::{self, Commitment, PcsParams};
use flock_core::r1cs::BlockR1cs;
use flock_core::zerocheck::{self, K_SKIP, ZkZerocheckProof};

use crate::digest_bind::{DigestChallenges, DigestStatement, digest_claim};
use crate::prover::R1csProofZkA1;

/// Number of inner coordinates the zerocheck pins to protocol constants.
const N_INNER: usize = 7;

/// A deterministic sampler for the simulator's own coins. The simulator is a
/// PPT algorithm with its own randomness; this keeps runs reproducible.
pub struct SimRng(u64);

impl SimRng {
    pub fn new(seed: u64) -> Self {
        Self(seed | 1)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn f128(&mut self) -> F128 {
        F128 {
            lo: self.next_u64(),
            hi: self.next_u64(),
        }
    }
    pub fn f128_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.f128()).collect()
    }
    pub fn bits(&mut self, n: usize) -> Vec<bool> {
        let mut out = Vec::with_capacity(n);
        while out.len() < n {
            let w = self.next_u64();
            for b in 0..64 {
                if out.len() == n {
                    break;
                }
                out.push((w >> b) & 1 == 1);
            }
        }
        out
    }
}

/// The challenge tuple the simulator fixes up front and later programs into
/// the oracle. Named in transcript order.
#[derive(Clone, Debug)]
pub struct ChosenChallenges {
    /// Zerocheck: the univariate-skip coordinates.
    pub r_skip: Vec<F128>,
    /// Zerocheck: the outer coordinates.
    pub r_outer: Vec<F128>,
    /// Zerocheck: the round-1 evaluation point.
    pub z: F128,
    /// Zerocheck: the mask-batching challenge.
    pub gamma: F128,
    /// Zerocheck: one per multilinear round.
    pub rho: Vec<F128>,
    /// Lincheck: the A/B batching challenge.
    pub alpha: F128,
    /// Lincheck: the constant-wire pin challenge.
    pub beta: F128,
    /// Lincheck: the mask-batching challenge.
    pub gamma_lc: F128,
    /// Lincheck: one per sumcheck round.
    pub lc_r: Vec<F128>,
    /// Lincheck: the final φ8 coordinate.
    pub r_inner_skip: F128,
}

impl ChosenChallenges {
    /// Draw a challenge tuple from the honest distribution.
    pub fn sample(m: usize, k_log: usize, rng: &mut SimRng) -> Self {
        let n_mlv = m - K_SKIP;
        let inner_rest = k_log - K_SKIP;
        Self {
            r_skip: rng.f128_vec(K_SKIP),
            r_outer: rng.f128_vec(m - K_SKIP - N_INNER),
            z: rng.f128(),
            gamma: rng.f128(),
            rho: rng.f128_vec(n_mlv),
            alpha: rng.f128(),
            beta: rng.f128(),
            gamma_lc: rng.f128(),
            lc_r: rng.f128_vec(inner_rest),
            r_inner_skip: rng.f128(),
        }
    }
}

/// Why a simulation attempt failed. Each is a genuine (negligible-probability)
/// degeneracy of the chosen challenges, not a bug: the simulator's contract is
/// to resample, and the cases are named so a failure is diagnosable rather
/// than a silent wrong answer.
#[derive(Debug, PartialEq, Eq)]
pub enum SimError {
    /// The final multilinear round's solve divides by `ρ(1+ρ)`, which vanishes
    /// at `ρ ∈ {0, 1}`.
    DegenerateRho,
    /// The lincheck's final coordinate solve needs a nonzero `comb` entry.
    DegenerateComb,
    /// Programming hit a point the oracle had already answered — the bad event
    /// of the freshness argument.
    ProgrammingCollision,
    /// The terminal identity could not be closed. Only reachable when the
    /// emitter runs without programming, where the solve is unavailable by
    /// construction (see `SimZerocheckSource`).
    TerminalIdentityUnclosed,
}

impl std::fmt::Display for SimError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DegenerateRho => write!(f, "degenerate ρ (0 or 1); resample"),
            Self::DegenerateComb => write!(f, "degenerate comb vector; resample"),
            Self::ProgrammingCollision => {
                write!(f, "oracle point already queried; resample")
            }
            Self::TerminalIdentityUnclosed => write!(
                f,
                "terminal identity unclosed — the emitter needs a programmable oracle"
            ),
        }
    }
}

impl std::error::Error for SimError {}

/// The zerocheck messages a simulator emits in place of the honest ones.
///
/// ## What has to be faked, and what does not
///
/// Only the zerocheck. The simulator starts from a **patched witness**: an
/// honest witness for messages of its own choosing, with the output region
/// overwritten by the public digests. That vector is a perfectly good input
/// to the lincheck, the commitments and the openings — they speak about
/// whatever was committed — and it satisfies the public digest claim by
/// construction. The one thing it is not is a satisfying R1CS assignment, and
/// the zerocheck is exactly the sub-proof that would notice.
///
/// So the simulator computes the *true* terminal evaluations of the patched
/// vector (by running the honest zerocheck on a throwaway transcript), then
/// emits its own round messages that telescope to those evaluations. The
/// lincheck downstream receives true `v_a`, `v_b` for the committed vector and
/// runs honestly; the PCS opens honestly. Nothing else is fabricated.
///
/// ## How the messages are chosen
///
/// The verifier's chain fixes what is free:
///
/// * `final_c_eval` is **recomputed** by the verifier as the interpolation of
///   `round1_c` at `z`, so `round1_c` must interpolate to the true c-value —
///   one linear condition on a 64-vector, solved in one coordinate;
/// * `round1_ab` is free;
/// * the AB initial claim is then whatever the reconstruction yields — the
///   simulator does not need it to be the honest one;
/// * each multilinear round is free, except the last `G(∞)`, which is solved
///   so the telescoped claim lands exactly on `â(ρ)b̂(ρ) + γ·P(ρ)Q(ρ)`.
///
/// That last solve is the crux: it is what lets a transcript with no valid
/// witness behind it satisfy the verifier's terminal identity.
pub struct SimZerocheckSource {
    /// True terminal evaluations of the patched (committed) vector.
    pub true_a_eval: F128,
    pub true_b_eval: F128,
    pub true_c_eval: F128,
    /// True evaluations of the committed mask polynomials at ρ.
    pub true_p_eval: F128,
    pub true_q_eval: F128,
    /// The A3 round-1 mask transcript of the committed mask cubes.
    pub mc_at_z: F128,
    pub h_at_z: F128,
    /// The mask sum the honest prover would have claimed.
    pub mask_init: F128,
    /// A `round1_c` solved so its interpolation at the programmed `z` equals
    /// the committed vector's true C-side evaluation. `None` lets the emitter
    /// pick freely (then the c-claim will not match the commitment).
    pub round1_c: Option<Vec<F128>>,
    /// The challenge tuple the emitter programs.
    pub challenges: ChosenChallenges,
    /// Simulator coins.
    pub rng: SimRng,
    /// Set when a degenerate challenge made the solve impossible.
    pub failure: Option<SimError>,
}

/// The simulator programs the oracle, so it is specialised to
/// [`OracleChallenger`] rather than generic over challengers. That is not a
/// limitation but the point: a simulator that worked against a plain
/// Fiat–Shamir challenger would be claiming something false, since without
/// programming the last round's `G(∞)` would have to be chosen before the
/// challenge it is solved against.
impl crate::prover::ZerocheckSource<OracleChallenger> for SimZerocheckSource {
    fn emit(
        &mut self,
        m: usize,
        challenger: &mut OracleChallenger,
        _honest: &mut dyn FnMut(
            &mut OracleChallenger,
        ) -> (
            ZkZerocheckProof,
            zerocheck::ZerocheckClaim,
            zerocheck::Round1MaskTranscript,
        ),
    ) -> (
        ZkZerocheckProof,
        zerocheck::ZerocheckClaim,
        zerocheck::Round1MaskTranscript,
    ) {
        let ell = 1usize << K_SKIP;
        let n_mlv = m - K_SKIP;
        let ch = self.challenges.clone();

        // Mirror the verifier's transcript walk, programming each challenge to
        // the value fixed in advance.
        // `r_skip` and `r_outer` are NOT programmed. They weight the
        // zerocheck's sum, but the terminal evaluations the simulator has to
        // match depend only on the fold point `(z, ρ)` — so leaving them
        // honest costs nothing and keeps the programmed set as small as
        // possible.
        challenger.observe_label(b"flock-zerocheck-zk-v0");
        let r_skip = challenger.sample_f128_vec(K_SKIP);
        let r_outer = challenger.sample_f128_vec(m - K_SKIP - N_INNER);

        let mut r = vec![F128::ZERO; m];
        r[..K_SKIP].copy_from_slice(&r_skip);
        for (i, v) in flock_core::zerocheck::univariate_skip_optimized::small_challenges_ghash()
            .iter()
            .enumerate()
        {
            r[K_SKIP + i] = *v;
        }
        for (i, v) in flock_core::zerocheck::univariate_skip_optimized::medium_challenges_ghash()
            .iter()
            .enumerate()
        {
            r[K_SKIP + 3 + i] = *v;
        }
        r[K_SKIP + N_INNER..].copy_from_slice(&r_outer);

        // Round-1 vectors are free; the verifier RECOMPUTES the C-side
        // evaluation from `round1_c`, so that value is determined rather than
        // claimed, and it is what the caller must have read back from the
        // committed vector.
        let round1_ab = self.rng.f128_vec(ell);
        let round1_c = self
            .round1_c
            .clone()
            .unwrap_or_else(|| self.rng.f128_vec(ell));
        challenger.observe_f128_slice(&round1_ab);
        challenger.observe_f128_slice(&round1_c);
        if challenger.program_next_scalar(ch.z).is_none() {
            self.failure = Some(SimError::ProgrammingCollision);
        }
        let z = challenger.sample_f128();

        let final_c_eval =
            flock_core::zerocheck::multilinear::interpolate_at_z_on_lambda(&round1_c, K_SKIP, z);

        let combined_at_lambda: Vec<F128> = round1_ab
            .iter()
            .zip(&round1_c)
            .map(|(x, y)| *x + *y)
            .collect();
        let combined_at_z = flock_core::zerocheck::multilinear::interpolate_at_z_combined(
            &combined_at_lambda,
            K_SKIP,
            z,
        );
        let p_c_at_z =
            flock_core::zerocheck::multilinear::interpolate_at_z_on_lambda(&round1_c, K_SKIP, z);
        let ab_init = combined_at_z
            + p_c_at_z
            + self.mc_at_z
            + flock_core::zerocheck::multilinear::vanishing_s_at(K_SKIP, z) * self.h_at_z;

        challenger.observe_f128(self.mask_init);
        if challenger.program_next_scalar(ch.gamma).is_none() {
            self.failure = Some(SimError::ProgrammingCollision);
        }
        let gamma = challenger.sample_f128();

        // The identity the verifier will check at the end. Every term is
        // already fixed: `a`,`b` are the committed vector's true evaluations
        // (the lincheck will prove them consistent), `P(ρ)`,`Q(ρ)` are true
        // evaluations of committed mask cubes, and γ has just been programmed.
        let target =
            self.true_a_eval * self.true_b_eval + gamma * self.true_p_eval * self.true_q_eval;

        let mut running = ab_init + gamma * self.mask_init;
        let mut rounds: Vec<(F128, F128)> = Vec::with_capacity(n_mlv);
        let mut rhos: Vec<F128> = Vec::with_capacity(n_mlv);
        for i in 0..n_mlv {
            let r_eq = r[K_SKIP + i];
            let one_plus_r_eq = F128::ONE + r_eq;
            let rho = ch.rho[i];
            let one_plus_rho = F128::ONE + rho;
            let g1 = self.rng.f128();
            let g0 = (running + r_eq * g1) * one_plus_r_eq.inv();

            // Because ρ is programmed, it is known BEFORE the message that
            // precedes it is emitted — which is exactly what makes the final
            // solve possible.
            let g_inf = if i + 1 == n_mlv {
                let denom = rho * one_plus_rho;
                if denom == F128::ZERO {
                    self.failure = Some(SimError::DegenerateRho);
                    self.rng.f128()
                } else {
                    (target + g0 * one_plus_rho + g1 * rho) * denom.inv()
                }
            } else {
                self.rng.f128()
            };

            rounds.push((g1, g_inf));
            challenger.observe_f128(g1);
            challenger.observe_f128(g_inf);
            if challenger.program_next_scalar(rho).is_none() {
                self.failure = Some(SimError::ProgrammingCollision);
            }
            let got = challenger.sample_f128();
            debug_assert_eq!(got, rho, "programmed ρ must come back");
            rhos.push(got);
            running = g0 * one_plus_rho + g1 * rho + g_inf * rho * one_plus_rho;
        }

        if running != target {
            self.failure = Some(SimError::TerminalIdentityUnclosed);
        }

        challenger.observe_f128(self.true_a_eval);
        challenger.observe_f128(self.true_b_eval);
        challenger.observe_f128(self.true_p_eval);
        challenger.observe_f128(self.true_q_eval);

        let claim = zerocheck::ZerocheckClaim {
            z,
            mlv_challenges: rhos,
            r_rest: r[K_SKIP..].to_vec(),
            a_eval: self.true_a_eval,
            b_eval: self.true_b_eval,
            c_eval: final_c_eval + self.mc_at_z,
        };
        (
            ZkZerocheckProof {
                round1_ab,
                round1_c,
                multilinear_rounds: rounds,
                mask_init: self.mask_init,
                final_a_eval: self.true_a_eval,
                final_b_eval: self.true_b_eval,
                final_c_eval,
                final_p_eval: self.true_p_eval,
                final_q_eval: self.true_q_eval,
            },
            claim,
            zerocheck::Round1MaskTranscript {
                mc_at_z: self.mc_at_z,
                h_at_z: self.h_at_z,
            },
        )
    }
}

/// Pass 1's source: run the honest zerocheck and *record* the claim, so the
/// simulator learns the challenge tuple and the committed vector's true
/// terminal evaluations. It changes nothing about the proof.
struct RecordingSource {
    claim: Option<zerocheck::ZerocheckClaim>,
}

impl crate::prover::ZerocheckSource<OracleChallenger> for RecordingSource {
    fn emit(
        &mut self,
        _m: usize,
        challenger: &mut OracleChallenger,
        honest: &mut dyn FnMut(
            &mut OracleChallenger,
        ) -> (
            ZkZerocheckProof,
            zerocheck::ZerocheckClaim,
            zerocheck::Round1MaskTranscript,
        ),
    ) -> (
        ZkZerocheckProof,
        zerocheck::ZerocheckClaim,
        zerocheck::Round1MaskTranscript,
    ) {
        let (p, c, mk) = honest(challenger);
        self.claim = Some(c.clone());
        (p, c, mk)
    }
}

// ---------------------------------------------------------------------------
// The driver
// ---------------------------------------------------------------------------

/// A simulated proof, plus how many oracle points had to be programmed.
pub struct SimulatedProof {
    pub proof: R1csProofZkA1,
    pub commitment: Commitment,
    /// Bounded by the number of PIOP challenges — reported so a reader can see
    /// the programming is a fixed, small set rather than unbounded.
    pub programmed: usize,
}

/// Simulate a fixed-digest proof: accepting, and built without any preimage.
///
/// Two passes over the honest prover, because the simulator must know the
/// committed vector's *true* terminal evaluations before it can emit messages
/// that telescope to them, and those evaluations depend on challenges that
/// only exist inside a run:
///
/// 1. **Measure.** Run the unmodified prover on the patched vector against a
///    throwaway oracle programmed to the chosen challenges, and read off the
///    true evaluations, the mask-cube evaluations, and the A3 transcript.
/// 2. **Emit.** Run the unmodified prover again, on the real oracle, with the
///    zerocheck supplied by [`SimZerocheckSource`] and everything else — the
///    six commitments, the masked lincheck, the batched opening — untouched.
///
/// The patched vector is an honest witness for messages the simulator chose,
/// with the output region overwritten by the *public* digests and `a`, `b`
/// recomputed. It satisfies the digest claim by construction and is not a
/// satisfying R1CS assignment — which is precisely what the emitted zerocheck
/// covers for.
pub fn simulate<F>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    lincheck_circuit: &dyn flock_core::lincheck::LincheckCircuit,
    statement: &DigestStatement,
    witness_for_own_messages: F,
    patch_digest_words: &dyn Fn(&mut [F128]),
    seed: u64,
    oracle: &crate::sim_oracle::SharedOracle,
    domain: &[u8],
) -> Result<SimulatedProof, SimError>
where
    F: Fn() -> (Vec<F128>, Vec<u8>),
{
    let m = r1cs.m;
    let mut rng = SimRng::new(seed);

    // --- the patched vector ------------------------------------------------
    let (mut z_packed, _stripe) = witness_for_own_messages();
    patch_digest_words(&mut z_packed);
    let a_packed = r1cs.apply_a_packed(&z_packed);
    let b_packed = r1cs.apply_b_packed(&z_packed);
    let stripe = flock_core::lincheck::pack_z_lincheck_from_packed(&z_packed, m, r1cs.k_log);

    let lig_config = pcs::ligerito::prover_config_for(
        pcs_params.log_msg_len(),
        pcs_params.log_batch_size,
        pcs_params.profile,
    )
    .expect("Ligerito prover config");

    // --- pass 1: measure ---------------------------------------------------
    let probe_oracle = crate::sim_oracle::shared_oracle();
    let mut probe_ch = crate::sim_oracle::OracleChallenger::new(domain, probe_oracle);
    // The verifier absorbs the public statement before anything else, so both
    // passes must too — otherwise every challenge diverges from the one the
    // verifier will derive.
    crate::r1cs_hashes::blake3_preimage::absorb_statement(&mut probe_ch, statement);
    let mut probe_rng = flock_core::zk::ZkRng::from_seed([seed as u8; 32]);
    let mut probe_forks = crate::prover::A1MaskForks::from_rng(&mut probe_rng);
    let mut recorder = RecordingSource { claim: None };
    let (probe_proof, _pc, _) = crate::prover::prove_r1cs_zk_a1_with_masks_pd(
        r1cs,
        pcs_params,
        z_packed.clone(),
        a_packed.clone(),
        b_packed.clone(),
        stripe.clone(),
        lincheck_circuit,
        &lig_config,
        probe_forks.sources(),
        &mut |_: &mut crate::sim_oracle::OracleChallenger| Vec::new(),
        Some(&mut recorder),
        None,
        &mut probe_ch,
    );

    // Pass 1 ran honestly, so the challenges it produced are uniform. The
    // simulator adopts them as its own chosen tuple — a simulator is free to
    // draw its challenges however it likes, and drawing them this way means
    // the evaluations just measured are the ones pass 2 has to match.
    let probe_claim = recorder.claim.expect("pass 1 records its zerocheck claim");
    let challenges = ChosenChallenges {
        r_skip: Vec::new(),
        r_outer: Vec::new(),
        z: probe_claim.z,
        gamma: rng.f128(),
        rho: probe_claim.mlv_challenges.clone(),
        alpha: F128::ZERO,
        beta: F128::ZERO,
        gamma_lc: F128::ZERO,
        lc_r: Vec::new(),
        r_inner_skip: F128::ZERO,
    };

    // --- pass 2: emit ------------------------------------------------------
    // `round1_c` is not free: the verifier recomputes the C-side evaluation
    // from it, and the PCS will check that value against the committed vector.
    // Solve one coordinate so the interpolation at the (programmed) `z` lands
    // on the true value pass 1 measured.
    let ell = 1usize << K_SKIP;
    let weights =
        flock_core::zerocheck::multilinear::lagrange_weights_lambda_naive(K_SKIP, challenges.z);
    let pivot = weights
        .iter()
        .position(|w| *w != F128::ZERO)
        .ok_or(SimError::DegenerateComb)?;
    let mut round1_c = rng.f128_vec(ell);
    let mut acc = F128::ZERO;
    for (i, w) in weights.iter().enumerate() {
        if i != pivot {
            acc += *w * round1_c[i];
        }
    }
    round1_c[pivot] = (probe_proof.zerocheck.final_c_eval + acc) * weights[pivot].inv();

    let mut source = SimZerocheckSource {
        true_a_eval: probe_proof.zerocheck.final_a_eval,
        true_b_eval: probe_proof.zerocheck.final_b_eval,
        true_c_eval: probe_proof.zerocheck.final_c_eval,
        true_p_eval: probe_proof.zerocheck.final_p_eval,
        true_q_eval: probe_proof.zerocheck.final_q_eval,
        mc_at_z: probe_proof.mc_at_z,
        h_at_z: probe_proof.h_at_z,
        mask_init: probe_proof.zerocheck.mask_init,
        round1_c: Some(round1_c),
        challenges: challenges.clone(),
        rng: SimRng::new(seed ^ 0xA5A5_A5A5),
        failure: None,
    };

    let mut ch = crate::sim_oracle::OracleChallenger::new(domain, oracle.clone());
    crate::r1cs_hashes::blake3_preimage::absorb_statement(&mut ch, statement);
    let mut rng2 = flock_core::zk::ZkRng::from_seed([seed as u8; 32]);
    let mut forks = crate::prover::A1MaskForks::from_rng(&mut rng2);
    let stmt = statement.clone();
    let layout_kind = r1cs.layout;
    let (proof, commitment, _) = crate::prover::prove_r1cs_zk_a1_with_masks_pd(
        r1cs,
        pcs_params,
        z_packed,
        a_packed,
        b_packed,
        stripe,
        lincheck_circuit,
        &lig_config,
        forks.sources(),
        &mut |c: &mut crate::sim_oracle::OracleChallenger| {
            let dch = DigestChallenges::sample(&stmt, c);
            vec![digest_claim(&stmt, layout_kind, &dch)]
        },
        Some(&mut source),
        None,
        &mut ch,
    );
    if let Some(e) = source.failure {
        return Err(e);
    }
    let programmed = oracle.lock().expect("oracle poisoned").programmed_len();
    Ok(SimulatedProof {
        proof,
        commitment,
        programmed,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The simulator's coins are reproducible, which is what makes a failing
    /// simulation debuggable.
    #[test]
    fn sim_rng_is_deterministic() {
        let a: Vec<F128> = SimRng::new(7).f128_vec(8);
        let b: Vec<F128> = SimRng::new(7).f128_vec(8);
        assert_eq!(a, b);
        let c: Vec<F128> = SimRng::new(8).f128_vec(8);
        assert_ne!(a, c);
    }

    /// The chosen-challenge tuple has one entry per challenge the zerocheck
    /// and lincheck consume, so programming it covers the whole PIOP.
    #[test]
    fn chosen_challenges_have_the_right_shape() {
        let mut rng = SimRng::new(11);
        let (m, k_log) = (22usize, 14usize);
        let ch = ChosenChallenges::sample(m, k_log, &mut rng);
        assert_eq!(ch.r_skip.len(), K_SKIP);
        assert_eq!(ch.r_outer.len(), m - K_SKIP - N_INNER);
        assert_eq!(ch.rho.len(), m - K_SKIP);
        assert_eq!(ch.lc_r.len(), k_log - K_SKIP);
    }
}

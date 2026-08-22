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
//! 2. **Sample the masks honestly.** `P`, `S`, `S_c`, and `S_h` carry no
//!    witness, so the simulator draws and commits them exactly as the prover
//!    does — and their opened evaluations are then true evaluations of
//!    committed data, not fabrications.
//! 3. **Fill the zerocheck backwards.** Round-1 vectors are free; the C-side
//!    evaluation is *determined* by the verifier's own interpolation; the
//!    multilinear rounds are free except that the last round's `G(∞)` is solved
//!    so the telescoped claim lands exactly on `â(ρ)b̂(ρ) + γ·P(ρ)Q*(ρ)`.
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
//! Acceptance does not establish indistinguishability; real and simulated
//! proofs may have different distributions.

use crate::sim_oracle::OracleChallenger;
use crate::sim_seal::{SealedStatement, SimCoins};
use flock_core::challenger::Challenger;
use flock_core::field::F128;
use flock_core::pcs::{self, Commitment};
use flock_core::zerocheck::{self, K_SKIP, ZkZerocheckProof};

use crate::digest_bind::{DigestChallenges, digest_claim};
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

    pub fn byte(&mut self) -> u8 {
        self.next_u64() as u8
    }
}

/// Expand the full simulator seed into the DRBG seed. Hashing the complete
/// little-endian `u64` avoids the former 8-bit seed truncation.
fn zk_seed(seed: u64) -> [u8; 32] {
    *::blake3::hash(&seed.to_le_bytes()).as_bytes()
}

/// The challenge tuple the simulator fixes up front and later programs into
/// the oracle. Named in transcript order.
#[derive(Clone, Debug)]
pub struct ChosenChallenges {
    /// Zerocheck: the round-1 evaluation point.
    pub z: F128,
    /// Zerocheck: the mask-batching challenge.
    pub gamma: F128,
    /// Zerocheck: one per multilinear round.
    pub rho: Vec<F128>,
}

impl ChosenChallenges {
    /// Draw the challenges the zerocheck simulator must program, before any
    /// transcript exists. Lincheck runs honestly, so its uniform challenges
    /// are deliberately not part of this tuple.
    pub fn sample(m: usize, rng: &mut SimRng) -> Self {
        let n_mlv = m - K_SKIP;
        Self {
            z: rng.f128(),
            gamma: rng.f128(),
            rho: rng.f128_vec(n_mlv),
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
///   so the telescoped claim lands exactly on `â(ρ)b̂(ρ) + γ·P(ρ)Q*(ρ)`.
///
/// That last solve is the crux: it is what lets a transcript with no valid
/// witness behind it satisfy the verifier's terminal identity.
pub struct SimZerocheckSource {
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
        inputs: crate::prover::ZerocheckSourceInputs<'_>,
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
        challenger.observe_label(b"flock-zerocheck-zk-v1");
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

        let terminal = zerocheck::evaluate_zk_terminals_packed_padded(
            inputs.a_packed,
            inputs.b_packed,
            inputs.c_packed,
            inputs.p_small,
            inputs.s_c_packed,
            inputs.s_h_packed,
            m,
            inputs.padding,
            &r,
            ch.z,
            &ch.rho,
        );

        // Round-1 vectors are free except that the C vector must interpolate
        // to the masked value whose un-shift is the committed C evaluation.
        let round1_ab = self.rng.f128_vec(ell);
        let weights =
            flock_core::zerocheck::multilinear::lagrange_weights_lambda_naive(K_SKIP, ch.z);
        let pivot = weights.iter().position(|w| *w != F128::ZERO);
        let mut round1_c = self.rng.f128_vec(ell);
        if let Some(pivot) = pivot {
            let mut acc = F128::ZERO;
            for (i, w) in weights.iter().enumerate() {
                if i != pivot {
                    acc += *w * round1_c[i];
                }
            }
            let masked_c = terminal.c_eval + terminal.mc_at_z;
            round1_c[pivot] = (masked_c + acc) * weights[pivot].inv();
        } else {
            self.failure = Some(SimError::DegenerateComb);
        }
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
            + terminal.mc_at_z
            + flock_core::zerocheck::multilinear::vanishing_s_at(K_SKIP, z) * terminal.h_at_z;

        challenger.observe_f128(terminal.mask_init);
        if challenger.program_next_scalar(ch.gamma).is_none() {
            self.failure = Some(SimError::ProgrammingCollision);
        }
        let gamma = challenger.sample_f128();

        // The identity the verifier will check at the end. Every term is
        // already fixed: `a`,`b` are the committed vector's true evaluations
        // (the lincheck will prove them consistent), `P(ρ)` is the true
        // evaluation of the committed mask and Q-star is public.
        let target = terminal.a_eval * terminal.b_eval
            + gamma * terminal.p_eval * zerocheck::SmallMaskSpec::default().q_star_at(&ch.rho);

        let mut running = ab_init + gamma * terminal.mask_init;
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

        challenger.observe_f128(terminal.a_eval);
        challenger.observe_f128(terminal.b_eval);
        challenger.observe_f128(terminal.p_eval);

        let claim = zerocheck::ZerocheckClaim {
            z,
            mlv_challenges: rhos,
            r_rest: r[K_SKIP..].to_vec(),
            a_eval: terminal.a_eval,
            b_eval: terminal.b_eval,
            c_eval: final_c_eval + terminal.mc_at_z,
        };
        (
            ZkZerocheckProof {
                round1_ab,
                round1_c,
                multilinear_rounds: rounds,
                mask_init: terminal.mask_init,
                final_a_eval: terminal.a_eval,
                final_b_eval: terminal.b_eval,
                final_c_eval,
                final_p_eval: terminal.p_eval,
            },
            claim,
            zerocheck::Round1MaskTranscript {
                mc_at_z: terminal.mc_at_z,
                h_at_z: terminal.h_at_z,
            },
        )
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

/// Simulate a fixed-digest proof from a sealed public statement. The function
/// generates its own unrelated messages, patches only the public digest
/// region, and performs the one-pass terminal solve. No witness-bearing type
/// is present in this API.
pub fn simulate(
    sealed: &SealedStatement<'_>,
    coins: SimCoins,
    oracle: &crate::sim_oracle::SharedOracle,
    domain: &[u8],
) -> Result<SimulatedProof, SimError> {
    use crate::r1cs_hashes::blake3::{
        ParamPinning, generate_witness_with_ab_packed_and_lincheck_zk_pinned,
    };
    use crate::r1cs_hashes::blake3_preimage::{MESSAGE_BYTES, message_compression};
    use flock_core::zk::MaskSampler;

    let setup = sealed.setup();
    let r1cs = &setup.r1cs;
    let pcs_params = &setup.pcs_params;
    let lincheck_circuit = setup.r1cs.csc_lincheck_circuit();
    let statement = sealed.statement();
    let seed = coins.seed();
    let m = r1cs.m;
    let mut rng = SimRng::new(seed);

    // --- the patched vector ------------------------------------------------
    let own_messages = (0..setup.n_blocks)
        .map(|_| std::array::from_fn::<_, MESSAGE_BYTES, _>(|_| rng.byte()))
        .collect::<Vec<_>>();
    let blocks = own_messages
        .iter()
        .map(message_compression)
        .collect::<Vec<_>>();
    let layout = r1cs.zk.expect("zk simulator requires randomizer layout");
    let mut randomizer_words =
        vec![
            0u64;
            setup.n_block_slots() * crate::r1cs_hashes::common::zk_rand_words_per_block(&layout)
        ];
    let mut trace_rng = flock_core::zk::ZkRng::from_seed(zk_seed(seed ^ 0x7472_6163_652d_7a6b));
    trace_rng.fill_u64s(&mut randomizer_words);
    let (mut z_packed, _a, _b, _stripe) = generate_witness_with_ab_packed_and_lincheck_zk_pinned(
        &blocks,
        setup.n_blocks_log(),
        &layout,
        &randomizer_words,
        ParamPinning::RootHash64,
    );
    let words_per_block = (1usize << r1cs.k_log) / 128;
    for (instance, digest) in sealed.digests().iter().enumerate() {
        for half in 0..2usize {
            let mut packed = F128::ZERO;
            for bit_in_half in 0..128usize {
                let bit = half * 128 + bit_in_half;
                if (digest[bit / 8] >> (bit % 8)) & 1 == 1 {
                    if bit_in_half < 64 {
                        packed.lo |= 1u64 << bit_in_half;
                    } else {
                        packed.hi |= 1u64 << (bit_in_half - 64);
                    }
                }
            }
            z_packed[instance * words_per_block + 2 + half] = packed;
        }
    }
    let a_packed = r1cs.apply_a_packed(&z_packed);
    let b_packed = r1cs.apply_b_packed(&z_packed);
    let stripe = flock_core::lincheck::pack_z_lincheck_from_packed(&z_packed, m, r1cs.k_log);

    let lig_config = pcs::ligerito::prover_config_for(
        pcs_params.log_msg_len(),
        pcs_params.log_batch_size,
        pcs_params.profile,
    )
    .expect("Ligerito prover config");

    // The simulator fixes every challenge it needs before any transcript
    // exists. Terminal values are evaluated inside the source from the actual
    // committed vectors and masks, so no measurement pass is required.
    let challenges = ChosenChallenges::sample(m, &mut rng);
    let mut source = SimZerocheckSource {
        challenges: challenges.clone(),
        rng: SimRng::new(seed ^ 0xA5A5_A5A5),
        failure: None,
    };

    let mut ch = crate::sim_oracle::OracleChallenger::new(domain, oracle.clone());
    crate::r1cs_hashes::blake3_preimage::absorb_statement(&mut ch, statement);
    let mut rng2 = flock_core::zk::ZkRng::from_seed(zk_seed(seed));
    let mut forks = crate::prover::A1MaskForks::from_rng(&mut rng2);
    let proof_nonce = forks.proof_nonce;
    let ro = crate::sim_oracle::ro_context(proof_nonce, oracle.clone());
    let stmt = statement.clone();
    let layout_kind = r1cs.layout;
    let (proof, commitment, _) = crate::prover::prove_r1cs_zk_a1_with_masks_pd_nonce_ro(
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
        proof_nonce,
        &ro,
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

const _: for<'a> fn(
    &SealedStatement<'a>,
    SimCoins,
    &crate::sim_oracle::SharedOracle,
    &[u8],
) -> Result<SimulatedProof, SimError> = simulate;

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

    /// The chosen tuple contains exactly the zerocheck challenges that are
    /// programmed; lincheck challenges stay honestly sampled.
    #[test]
    fn chosen_challenges_have_the_right_shape() {
        let mut rng = SimRng::new(11);
        let m = 22usize;
        let ch = ChosenChallenges::sample(m, &mut rng);
        assert_eq!(ch.rho.len(), m - K_SKIP);
    }

    #[test]
    fn simulator_challenges_are_sampled_before_transcript() {
        let a = ChosenChallenges::sample(22, &mut SimRng::new(17));
        let b = ChosenChallenges::sample(22, &mut SimRng::new(17));
        let c = ChosenChallenges::sample(22, &mut SimRng::new(18));
        assert_eq!(a.z, b.z);
        assert_eq!(a.gamma, b.gamma);
        assert_eq!(a.rho, b.rho);
        assert_ne!((a.z, a.gamma, &a.rho), (c.z, c.gamma, &c.rho));
    }

    #[test]
    fn simulator_seed_uses_all_64_bits() {
        assert_ne!(zk_seed(1), zk_seed(257));
        assert_ne!(zk_seed(7), zk_seed(7 + (1u64 << 40)));
    }
}

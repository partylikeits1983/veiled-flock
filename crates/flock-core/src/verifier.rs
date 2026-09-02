//! Top-level R1CS verifier: walks the challenger in lockstep with the
//! prover, runs `zerocheck::verify` and `lincheck::verify`, derives the two
//! ZClaims, and verifies the PCS openings at those points against the
//! witness commitment.

use crate::challenger::Challenger;
use crate::field::F128;
use crate::lincheck;
use crate::pcs::{self, Commitment, PcsParams};
use crate::proof::{R1csClaim, R1csProofLigerito, ZClaim};
use crate::r1cs::BlockR1cs;
use crate::ro::{RoChannel, RoContext};
use crate::zerocheck;
use std::sync::OnceLock;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Zerocheck(zerocheck::VerifyError),
    Lincheck(lincheck::VerifyError),
    PcsAb(pcs::VerifyError),
    PcsC(pcs::VerifyError),
}

/// Dedicated single-thread rayon pool that the verifier runs inside.
///
/// The verifier is intentionally single-threaded — matching the convention of
/// comparable provers (binius64, plonky3, hashcaster all ship serial
/// verifiers) and keeping reported verify times honest single-core numbers.
/// The verify path shares several `par_*` helpers with the (multi-threaded)
/// prover — e.g. `lincheck::fold_alpha_batched`, `sumcheck_bind_top_in_place_par`,
/// and the Ligerito residual eval — so rather than fork every shared helper, the
/// reusable verify cores (`verify_core`, `verify_claims_ligerito`)
/// run their body via `verifier_pool().install(..)`. Any `par_iter` reached from
/// there uses this 1-thread pool and collapses onto a single worker, without
/// touching the prover's use of the global pool.
fn verifier_pool() -> &'static rayon::ThreadPool {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            // The whole verify body runs on this worker — including the deep
            // recursive Ligerito verifier — so give it an ample stack. A rayon
            // worker otherwise defaults to ~2 MiB (vs the 8 MiB main thread),
            // which the recursion overflows.
            .stack_size(64 * 1024 * 1024)
            .thread_name(|_| "flock-verify".to_string())
            .build()
            .expect("build single-thread verifier pool")
    })
}

/// Run a complete verifier wrapper under the repository's single-thread
/// verification convention. Higher-level protocol variants must use this for
/// work performed before they enter the shared PCS verification helpers.
pub fn run_serial<R: Send>(op: impl FnOnce() -> R + Send) -> R {
    verifier_pool().install(op)
}

/// Verify an R1CS proof: replay zerocheck + lincheck → the two base z-claims,
/// then verify the batched Ligerito PCS opening covering both.
pub fn verify_ligerito<Ch: Challenger>(
    r1cs: &BlockR1cs,
    commitment: &Commitment,
    proof: &R1csProofLigerito,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    pcs_params: &crate::pcs::PcsParams,
    challenger: &mut Ch,
) -> Result<R1csClaim, VerifyError> {
    let (ab, c) = verify_core(
        r1cs,
        &proof.zerocheck,
        &proof.lincheck,
        commitment,
        lincheck_circuit,
        challenger,
    )?;
    verify_claims_ligerito(
        commitment,
        &[ab.clone(), c.clone()],
        &proof.pcs_open,
        pcs_params,
        challenger,
    )
    .map_err(VerifyError::PcsAb)?;
    Ok(R1csClaim { ab, c })
}

/// Verify a batched PCS opening over an arbitrary list of `ẑ`-claims — the
/// mirror of `flock_prover::prover::open_claims_with_precomputed_ligerito`.
/// Relation wrappers (e.g. the hash chain) reuse this with their own appended
/// claims. Must run at the same transcript position as the prover's open.
pub fn verify_claims_ligerito<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[ZClaim],
    pcs_open: &pcs::BatchOpeningProofLigerito,
    pcs_params: &crate::pcs::PcsParams,
    challenger: &mut Ch,
) -> Result<(), pcs::VerifyError> {
    let ro = crate::ro::RoContext::plain();
    // Verification is single-threaded; run the body on the dedicated 1-thread pool.
    verifier_pool().install(move || {
        verify_claims_ligerito_inner(
            commitment,
            claims,
            &[],
            pcs_open,
            pcs_params,
            None,
            &ro,
            crate::ro::RoChannel::Witness,
            challenger,
        )
    })
}

/// [`verify_claims_ligerito`] with an explicit Ligerito verifier config, for
/// audit fixtures at shapes outside the production config ladder. Production callers use
/// [`verify_claims_ligerito`], which derives the config from `pcs_params`.
pub fn verify_claims_ligerito_with_config<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[ZClaim],
    pcs_open: &pcs::BatchOpeningProofLigerito,
    pcs_params: &crate::pcs::PcsParams,
    lig_v_config: &crate::pcs::ligerito::VerifierConfig,
    challenger: &mut Ch,
) -> Result<(), pcs::VerifyError> {
    let ro = crate::ro::RoContext::plain();
    verify_claims_ligerito_with_config_ro(
        commitment,
        claims,
        pcs_open,
        pcs_params,
        lig_v_config,
        &ro,
        crate::ro::RoChannel::Witness,
        challenger,
    )
}

/// Configured claim verification with an explicit point-oracle context.
#[allow(clippy::too_many_arguments)]
pub fn verify_claims_ligerito_with_config_ro<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[ZClaim],
    pcs_open: &pcs::BatchOpeningProofLigerito,
    pcs_params: &crate::pcs::PcsParams,
    lig_v_config: &crate::pcs::ligerito::VerifierConfig,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> Result<(), pcs::VerifyError> {
    verify_claims_ligerito_with_config_pd_ro(
        commitment,
        claims,
        &[],
        pcs_open,
        pcs_params,
        lig_v_config,
        ro,
        channel,
        challenger,
    )
}

/// [`verify_claims_ligerito_with_config`] plus **packed-direct** claims —
/// public evaluation claims on the committed witness that ride the same
/// batched opening (see `pcs::PackedDirectClaim`).
///
/// The values of packed-direct claims are the verifier's own: it recomputes
/// each target from public data rather than reading it from the proof, so a
/// prover cannot move them. Used to bind public hash digests to the witness's
/// output region.
#[allow(clippy::too_many_arguments)]
pub fn verify_claims_ligerito_with_config_pd<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[ZClaim],
    packed_direct: &[pcs::PackedDirectClaimRef<'_>],
    pcs_open: &pcs::BatchOpeningProofLigerito,
    pcs_params: &crate::pcs::PcsParams,
    lig_v_config: &crate::pcs::ligerito::VerifierConfig,
    challenger: &mut Ch,
) -> Result<(), pcs::VerifyError> {
    let ro = crate::ro::RoContext::plain();
    verify_claims_ligerito_with_config_pd_ro(
        commitment,
        claims,
        packed_direct,
        pcs_open,
        pcs_params,
        lig_v_config,
        &ro,
        crate::ro::RoChannel::Witness,
        challenger,
    )
}

/// Packed-direct configured verification with an explicit point-oracle context.
#[allow(clippy::too_many_arguments)]
pub fn verify_claims_ligerito_with_config_pd_ro<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[ZClaim],
    packed_direct: &[pcs::PackedDirectClaimRef<'_>],
    pcs_open: &pcs::BatchOpeningProofLigerito,
    pcs_params: &crate::pcs::PcsParams,
    lig_v_config: &crate::pcs::ligerito::VerifierConfig,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> Result<(), pcs::VerifyError> {
    verifier_pool().install(move || {
        verify_claims_ligerito_inner(
            commitment,
            claims,
            packed_direct,
            pcs_open,
            pcs_params,
            Some(lig_v_config),
            ro,
            channel,
            challenger,
        )
    })
}

/// Verify claims on the uniformly blinded witness `q = z + c·g_top`.
pub struct PreblindedClaimVerification<'a> {
    pub commitment: &'a Commitment,
    pub claims: &'a [ZClaim],
    pub packed_direct: &'a [pcs::PackedDirectClaimRef<'a>],
    pub pcs_open: &'a pcs::BatchOpeningProofLigerito,
    pub pcs_params: &'a PcsParams,
    pub lig_v_config: &'a pcs::ligerito::VerifierConfig,
    pub challenge: F128,
    pub ro: &'a RoContext,
    pub channel: RoChannel,
}

pub fn verify_claims_ligerito_with_config_pd_preblinded_ro<Ch: Challenger>(
    verification: PreblindedClaimVerification<'_>,
    challenger: &mut Ch,
) -> Result<(), pcs::VerifyError> {
    let PreblindedClaimVerification {
        commitment,
        claims,
        packed_direct,
        pcs_open,
        pcs_params,
        lig_v_config,
        challenge,
        ro,
        channel,
    } = verification;
    verifier_pool().install(move || {
        if commitment.params != *pcs_params {
            return Err(pcs::VerifyError::Ligerito);
        }
        let z_skips: Vec<F128> = claims.iter().map(|claim| claim.point.z_skip).collect();
        let values: Vec<F128> = claims.iter().map(|claim| claim.value).collect();
        let x_fulls: Vec<Vec<F128>> = claims
            .iter()
            .map(|claim| {
                let mut point = claim.point.x_inner_rest.clone();
                point.extend_from_slice(&claim.point.x_outer);
                point
            })
            .collect();
        let x_refs: Vec<&[F128]> = x_fulls.iter().map(Vec::as_slice).collect();
        pcs::verify_opening_batch_ligerito_mixed_preblinded_ro(
            pcs::PreblindedOpeningVerification {
                commitment,
                claims: &values,
                z_skips: &z_skips,
                x_outers: &x_refs,
                packed_direct,
                proof: pcs_open,
                lig_config: lig_v_config,
                challenge,
                ro,
                channel,
            },
            challenger,
        )
    })
}

fn verify_claims_ligerito_inner<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[ZClaim],
    packed_direct: &[pcs::PackedDirectClaimRef<'_>],
    pcs_open: &pcs::BatchOpeningProofLigerito,
    pcs_params: &crate::pcs::PcsParams,
    lig_v_config: Option<&crate::pcs::ligerito::VerifierConfig>,
    ro: &crate::ro::RoContext,
    channel: crate::ro::RoChannel,
    challenger: &mut Ch,
) -> Result<(), pcs::VerifyError> {
    // The commitment carries a params copy for shape bookkeeping, but the
    // verification circuit (config ladder, query counts, zk branch) must be
    // keyed by the verifier's own params — a mismatch is a reject, not a
    // shape accident downstream.
    if commitment.params != *pcs_params {
        return Err(pcs::VerifyError::Ligerito);
    }
    let z_skips: Vec<F128> = claims.iter().map(|c| c.point.z_skip).collect();
    let values: Vec<F128> = claims.iter().map(|c| c.value).collect();
    let x_fulls: Vec<Vec<F128>> = claims
        .iter()
        .map(|c| {
            let mut v = c.point.x_inner_rest.clone();
            v.extend_from_slice(&c.point.x_outer);
            v
        })
        .collect();
    let x_refs: Vec<&[F128]> = x_fulls.iter().map(|v| v.as_slice()).collect();
    // zk mode commits one extra dimension (mask half) — key the ladder on
    // the committed length.
    let derived;
    let lig_v_config = match lig_v_config {
        Some(cfg) => cfg,
        None => {
            derived = crate::pcs::ligerito::verifier_config_for_pcs_params(pcs_params)
                .expect("Ligerito verifier config for PCS parameters");
            &derived
        }
    };
    pcs::verify_opening_batch_ligerito_mixed_ro(
        commitment,
        &values,
        &z_skips,
        &x_refs,
        packed_direct,
        pcs_open,
        lig_v_config,
        ro,
        channel,
        challenger,
    )
}

/// Replay bind → zerocheck → lincheck and reconstruct the two base z-claims
/// (`ab`, `c`), stopping before the PCS open. Mirror of
/// `flock_prover::prover::prove_fast_core`; relation wrappers reuse this then call
/// [`verify_claims_ligerito`] over `[ab, c, …]`.
pub fn verify_core<Ch: Challenger>(
    r1cs: &BlockR1cs,
    zerocheck_proof: &zerocheck::ZerocheckProof,
    lincheck_proof: &lincheck::LincheckProof,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    challenger: &mut Ch,
) -> Result<(ZClaim, ZClaim), VerifyError> {
    // Verification is single-threaded; run the body on the dedicated 1-thread pool.
    verifier_pool().install(move || {
        verify_core_inner(
            r1cs,
            zerocheck_proof,
            lincheck_proof,
            commitment,
            lincheck_circuit,
            challenger,
        )
    })
}

fn verify_core_inner<Ch: Challenger>(
    r1cs: &BlockR1cs,
    zerocheck_proof: &zerocheck::ZerocheckProof,
    lincheck_proof: &lincheck::LincheckProof,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    challenger: &mut Ch,
) -> Result<(ZClaim, ZClaim), VerifyError> {
    let trace = std::env::var("VERIFY_TRACE").is_ok();
    let fmt = |s: f64| -> String {
        let ms = s * 1000.0;
        if ms < 1.0 {
            format!("{:>8.2} µs", s * 1e6)
        } else {
            format!("{:>8.2} ms", ms)
        }
    };

    // ---- Bind FS transcript to the statement (mirrors prover::prove).
    let t = std::time::Instant::now();
    crate::proof::bind_statement(challenger, r1cs, commitment, &[0u8; 32]);
    if trace {
        eprintln!(
            "      [vco] bind_statement: {}",
            fmt(t.elapsed().as_secs_f64())
        );
    }

    // ---- Zerocheck.
    let t = std::time::Instant::now();
    let zc_claim =
        zerocheck::verify(r1cs.m, zerocheck_proof, challenger).map_err(VerifyError::Zerocheck)?;
    if trace {
        eprintln!(
            "      [vco] zerocheck::verify: {}",
            fmt(t.elapsed().as_secs_f64())
        );
    }

    // ---- Build lincheck's shared quirky point from the zerocheck output
    // (layout-aware: the mlv challenges are address-ordered).
    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);

    // ---- Lincheck. v_a, v_b come from the zerocheck's final â, b̂ evals.
    let t = std::time::Instant::now();
    let lc_claim = lincheck::verify(
        r1cs.m,
        r1cs.k_log,
        r1cs.k_skip,
        lincheck_circuit,
        &x_ab,
        zc_claim.a_eval,
        zc_claim.b_eval,
        lincheck_proof,
        challenger,
    )
    .map_err(VerifyError::Lincheck)?;
    if trace {
        eprintln!(
            "      [vco] lincheck::verify: {}",
            fmt(t.elapsed().as_secs_f64())
        );
    }

    // ---- Build the two z-claims (must match what `prove` returned).
    // Layout-aware: the ZClaim points are address-ordered for the PCS.
    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    // c-claim is already a z-claim since `C = I` ⇒ ĉ = ẑ.
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };

    Ok((ab, c))
}

#[cfg(test)]
mod tests {
    /// The verifier is intentionally single-threaded: every `par_*` reached
    /// from a verify core must collapse onto the one-thread `verifier_pool`.
    /// Guard the invariant so a future `ThreadPoolBuilder` tweak can't silently
    /// re-parallelize verification.
    ///
    /// (The end-to-end prove → verify roundtrip and tamper-rejection tests live
    /// in `flock-prover`'s `tests/verifier_roundtrip.rs`, since they need the
    /// prove path.)
    #[test]
    fn verifier_pool_is_single_threaded() {
        let n = super::verifier_pool().install(rayon::current_num_threads);
        assert_eq!(n, 1, "verifier_pool must have exactly one worker thread");
    }
}

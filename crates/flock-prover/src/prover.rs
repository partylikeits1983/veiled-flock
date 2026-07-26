//! Top-level R1CS prover: composes zerocheck + lincheck for block-diagonal
//! circuit R1CS instances. Outputs **two** z-claims at different quirky
//! points that the PCS layer (when it lands) will verify against `z`'s
//! commitment.
//!
//! Flow:
//! ```text
//!     witness z ──► pack ──► a = A·z, b = B·z, c = z (since C=I)
//!         │
//!         │       ┌─────────────┐
//!         │       │  zerocheck  │  reduces a·b ⊕ c = 0 to MLE claims:
//!         │       │             │  • â(z, mlv_challenges) = v_a
//!         │       │             │  • b̂(z, mlv_challenges) = v_b
//!         │       │             │  • ĉ(z, r_rest)         = v_c  ← directly a z-claim
//!         │       └─────────────┘
//!         │
//!         │       ┌─────────────┐
//!         │ ─► z ─►  lincheck   │  reduces â, b̂ claims (same point) to a
//!         │       │             │  single z-claim at (r_inner_skip,
//!         │       │             │                      r_inner_rest,
//!         │       │             │                      x_ab.x_outer).
//!         │       └─────────────┘
//!         │
//!         ▼
//!     R1csClaim { ab: z-claim from lincheck,  c: z-claim from extract_c }
//! ```

use flock_core::challenger::Challenger;
use flock_core::field::F128;
use flock_core::lincheck::{self, QuirkyPoint, pack_z_lincheck_from_packed};
use flock_core::pcs::{self, Commitment, PcsParams};
use flock_core::proof::{R1csClaim, R1csProofLigerito, ZClaim, bind_statement};
use flock_core::r1cs::BlockR1cs;
use flock_core::zerocheck;

/// Construct a multilinear `x_outer_full` of length `m − k_skip` from a
/// QuirkyPoint: concatenate `x_inner_rest` and `x_outer`. This is the format
/// the PCS expects (k_skip = 6 absorbed via `z_skip`; everything else is
/// multilinear).
pub(crate) fn quirky_x_outer_full(point: &QuirkyPoint) -> Vec<F128> {
    let mut v = Vec::with_capacity(point.x_inner_rest.len() + point.x_outer.len());
    v.extend_from_slice(&point.x_inner_rest);
    v.extend_from_slice(&point.x_outer);
    v
}

/// Batched PCS open over an arbitrary list of `ẑ`-evaluation claims. This is
/// the generic seam: the base R1CS proof opens `[ab, c]`; relation wrappers
/// (e.g. the hash chain) append their own claims and open `[ab, c, …]`.
/// Per-claim optional precomputed `s_hat_v` is passed through to ring-switch:
/// when `Some(v)`, the claim skips `fold_1b_rows` and uses `v` directly.
/// Caller responsibility: each `Some(v)` MUST equal what `fold_1b_rows` would
/// produce on `z_packed` against the claim's suffix — see
/// [`pcs::ring_switch::s_hat_v_from_z_vec`] for the AB-claim derivation.
///
/// Must be called at the same transcript position as the verifier's
/// [`flock_core::verifier::verify_claims_ligerito`].
pub(crate) fn open_claims_with_precomputed_ligerito<Ch: Challenger>(
    z_packed: Vec<F128>,
    prover_data: &pcs::ProverData,
    commitment: &Commitment,
    claims: &[ZClaim],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &zerocheck::PaddingSpec,
    lig_config: &pcs::ligerito::ProverConfig,
    challenger: &mut Ch,
) -> pcs::BatchOpeningProofLigerito {
    let x_fulls: Vec<Vec<F128>> = claims
        .iter()
        .map(|c| quirky_x_outer_full(&c.point))
        .collect();
    let x_refs: Vec<&[F128]> = x_fulls.iter().map(|v| v.as_slice()).collect();
    pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v(
        z_packed,
        prover_data,
        commitment,
        &x_refs,
        precomputed_s_hat_v,
        &[],
        padding,
        lig_config,
        challenger,
    )
}

/// Run the full R1CS proof on an F_{2^128}-packed witness.
///
/// The witness is in the canonical packed form (polynomial basis: bit `r` of
/// `z_packed[i]` = logical bit `i·128 + r`), length `2^(m - 7)`. The prover
/// never unpacks; downstream R1CS/zerocheck/lincheck/PCS all consume packed
/// representations.
///
/// Returns the proof bundle, the witness commitment, and the two claims (which
/// the verifier needs to know to check the openings).
pub fn prove_ligerito<Ch: Challenger>(
    r1cs: &BlockR1cs,
    z_packed: Vec<F128>,
    pcs_params: &PcsParams,
    challenger: &mut Ch,
) -> (R1csProofLigerito, Commitment, R1csClaim) {
    prove_ligerito_impl(r1cs, z_packed, pcs_params, None, challenger)
}

/// zk variant of [`prove_ligerito`]: hiding commitment fed by `zk_rng`
/// (a prover-secret mask sampler, independent of the FS transcript).
/// `pcs_params.zk` must be set; the witness is expected to already carry its
/// randomizer rows (`r1cs.zk`).
///
/// **Warning:** this entry does not check `r1cs.zk`. A statement without
/// randomizer rows yields a hiding commitment over an **unmasked PIOP
/// transcript** (the PCS-only tests rely on this seam). Full zero-knowledge
/// needs both mask species — use an encoder entry point like
/// `Blake3Setup::prove_fast_zk`, which builds the statement with its
/// randomizer layout.
pub fn prove_ligerito_zk<Ch: Challenger>(
    r1cs: &BlockR1cs,
    z_packed: Vec<F128>,
    pcs_params: &PcsParams,
    zk_rng: &mut dyn flock_core::zk::MaskSampler,
    challenger: &mut Ch,
) -> (R1csProofLigerito, Commitment, R1csClaim) {
    assert!(pcs_params.zk, "prove_ligerito_zk requires PcsParams.zk");
    prove_ligerito_impl(r1cs, z_packed, pcs_params, Some(zk_rng), challenger)
}

/// Commit dispatch shared by the prove paths: hiding commit in zk mode (mask
/// sampler required; any prefaulted buffer is recycled back to the scratch
/// pool since `commit_zk` sizes its own), plain commit otherwise.
fn commit_dispatch(
    z_packed: &[F128],
    pcs_params: &PcsParams,
    prefaulted_codeword: Option<Vec<F128>>,
    zk_rng: Option<&mut dyn flock_core::zk::MaskSampler>,
) -> (Commitment, pcs::ProverData) {
    if pcs_params.zk {
        #[cfg(feature = "zk")]
        {
            let rng = zk_rng
                .expect("zk PcsParams require a mask sampler — use a *_zk prove entry point");
            if let Some(buf) = prefaulted_codeword {
                flock_core::scratch::give_f128(buf);
            }
            return pcs::commit::commit_zk(z_packed, pcs_params, rng);
        }
        #[cfg(not(feature = "zk"))]
        panic!("PcsParams.zk requires the `zk` cargo feature");
    }
    let _ = zk_rng;
    match prefaulted_codeword {
        Some(buf) => pcs::commit_into(z_packed, pcs_params, buf),
        None => pcs::commit(z_packed, pcs_params),
    }
}

fn prove_ligerito_impl<Ch: Challenger>(
    r1cs: &BlockR1cs,
    z_packed: Vec<F128>,
    pcs_params: &PcsParams,
    zk_rng: Option<&mut dyn flock_core::zk::MaskSampler>,
    challenger: &mut Ch,
) -> (R1csProofLigerito, Commitment, R1csClaim) {
    assert_eq!(
        r1cs.layout,
        flock_core::r1cs::WitnessLayout::RowMajor,
        "the generic matrix-driven provers assume the row-major layout \
         (block-diagonal apply + lincheck stripe packing); batch-major \
         setups must use the per-hash prove_fast paths"
    );
    assert_eq!(z_packed.len(), 1usize << (r1cs.m - 7));
    assert_eq!(pcs_params.m, r1cs.m);

    // In zk mode the committed message is one dimension larger (mask half),
    // so the ladder is keyed on the committed length — the (m+1) config.
    let log_n = pcs_params.log_msg_len();
    let lig_config =
        pcs::ligerito::prover_config_for(log_n, pcs_params.log_batch_size, pcs_params.profile)
            .expect("Ligerito default config; bump m for tiny instances");

    let (commitment, prover_data) = commit_dispatch(&z_packed, pcs_params, None, zk_rng);
    bind_statement(challenger, r1cs, &commitment);

    // a = A·z, b = B·z; for the C = I convention c aliases z.
    let a_packed_f128 = r1cs.apply_a_packed(&z_packed);
    let b_packed_f128 = r1cs.apply_b_packed(&z_packed);
    let c_packed_f128: Vec<F128> = if r1cs.c0_is_identity() {
        Vec::new()
    } else {
        r1cs.apply_c_packed(&z_packed)
    };
    let cast = |v: &[F128]| -> &[u8] {
        unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
    };
    let a_packed: &[u8] = cast(&a_packed_f128);
    let b_packed: &[u8] = cast(&b_packed_f128);
    let c_packed: &[u8] = if c_packed_f128.is_empty() {
        cast(&z_packed)
    } else {
        cast(&c_packed_f128)
    };
    let z_packed_lincheck = pack_z_lincheck_from_packed(&z_packed, r1cs.m, r1cs.k_log);

    let padding = r1cs.padding_spec();
    let (zc_proof, zc_claim, s_hat_v_c) = zerocheck::prove_packed_padded_capture_s_hat_v_c(
        a_packed, b_packed, c_packed, r1cs.m, &padding, challenger,
    );

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);

    let lc_circuit =
        lincheck::SparseMatrixCircuit::new(&r1cs.a_0, &r1cs.b_0).with_const_pin(r1cs.const_pin);
    let (lc_proof, lc_claim, z_vec_pre) = lincheck::prove_padded_capture_z_vec(
        &z_packed_lincheck,
        r1cs.m,
        r1cs.k_log,
        r1cs.k_skip,
        r1cs.useful_bits,
        &lc_circuit,
        &x_ab,
        challenger,
    );

    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };

    let s_hat_v_ab = if r1cs.k_log >= pcs::LOG_PACKING {
        Some(pcs::ring_switch::s_hat_v_from_z_vec(
            &z_vec_pre,
            &lc_claim.r_inner_rest[1..],
        ))
    } else {
        None
    };
    let pre_ab: Option<&[F128]> = s_hat_v_ab.as_deref();
    let pre_c: Option<&[F128]> = Some(s_hat_v_c.as_slice());
    let pcs_open = open_claims_with_precomputed_ligerito(
        z_packed,
        &prover_data,
        &commitment,
        &[ab.clone(), c.clone()],
        &[pre_ab, pre_c],
        &padding,
        &lig_config,
        challenger,
    );

    let proof = R1csProofLigerito {
        zerocheck: zc_proof,
        lincheck: lc_proof,
        pcs_open,
    };
    let claim = R1csClaim { ab, c };
    (proof, commitment, claim)
}

/// Shared `prove_fast` pipeline for the monolithic hash R1CS modules. Takes
/// the four packed buffers produced by the per-hash
/// `generate_witness_with_ab_packed_and_lincheck` and runs commit → zerocheck
/// → lincheck → PCS-open. Uses the c-aliasing trick (`C = I` → `c == z`
/// byte-for-byte). Used by per-hash modules' `prove_fast_ligerito` methods.
pub fn prove_fast_ligerito_from_witness<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    prefaulted_codeword: Option<Vec<F128>>,
    challenger: &mut Ch,
) -> (R1csProofLigerito, Commitment, R1csClaim) {
    prove_fast_ligerito_from_witness_impl(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        prefaulted_codeword,
        None,
        challenger,
    )
}

/// zk variant of [`prove_fast_ligerito_from_witness`] (hiding commitment fed
/// by `zk_rng`). The witness must already carry its randomizer rows.
#[allow(clippy::too_many_arguments)]
pub fn prove_fast_ligerito_from_witness_zk<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    zk_rng: &mut dyn flock_core::zk::MaskSampler,
    challenger: &mut Ch,
) -> (R1csProofLigerito, Commitment, R1csClaim) {
    assert!(pcs_params.zk, "zk prove entry requires PcsParams.zk");
    prove_fast_ligerito_from_witness_impl(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        None,
        Some(zk_rng),
        challenger,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_fast_ligerito_from_witness_impl<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    prefaulted_codeword: Option<Vec<F128>>,
    zk_rng: Option<&mut dyn flock_core::zk::MaskSampler>,
    challenger: &mut Ch,
) -> (R1csProofLigerito, Commitment, R1csClaim) {
    let log_n = pcs_params.log_msg_len();
    let lig_config =
        pcs::ligerito::prover_config_for(log_n, pcs_params.log_batch_size, pcs_params.profile)
            .expect("Ligerito default config; bump m for tiny instances");

    let ProveCore {
        zc_proof,
        lc_proof,
        ab,
        c,
        commitment,
        prover_data,
        z_packed,
        s_hat_v_ab,
        s_hat_v_c,
    } = prove_fast_core_impl(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        prefaulted_codeword,
        zk_rng,
        challenger,
    );

    let padding = r1cs.padding_spec();
    let pre_ab: Option<&[F128]> = s_hat_v_ab.as_deref();
    let pre_c: Option<&[F128]> = Some(s_hat_v_c.as_slice());
    let pcs_open = open_claims_with_precomputed_ligerito(
        z_packed,
        &prover_data,
        &commitment,
        &[ab.clone(), c.clone()],
        &[pre_ab, pre_c],
        &padding,
        &lig_config,
        challenger,
    );

    let proof = R1csProofLigerito {
        zerocheck: zc_proof,
        lincheck: lc_proof,
        pcs_open,
    };
    let claim = R1csClaim { ab, c };
    (proof, commitment, claim)
}

/// Everything the prover produces *before* the PCS open: the zerocheck +
/// lincheck sub-proofs, the two base z-claims (`ab`, `c`), and the retained
/// commitment / prover-data / packed witness needed to open more claims.
///
/// The generic seam: `prove_fast_ligerito_from_witness` = `prove_fast_core` +
/// `open_claims([ab, c])`; a relation wrapper (e.g. the hash chain) runs the
/// same core, derives extra z-claims, and calls `open_claims([ab, c, …])`.
pub struct ProveCore {
    pub zc_proof: zerocheck::ZerocheckProof,
    pub lc_proof: lincheck::LincheckProof,
    pub ab: ZClaim,
    pub c: ZClaim,
    pub commitment: Commitment,
    pub prover_data: pcs::ProverData,
    pub z_packed: Vec<F128>,
    /// Precomputed `s_hat_v` for the AB claim — derived from lincheck's
    /// pre-sumcheck `z_vec` via [`pcs::ring_switch::s_hat_v_from_z_vec`].
    /// Skips `fold_1b_rows` for the AB claim at PCS-open time.
    ///
    /// `None` when `k_log < LOG_PACKING` (the kernel needs `z_vec.len() ==
    /// 2^LOG_PACKING * 2^tail.len()`, which requires `k_log >= LOG_PACKING`).
    /// Real R1CS instances have `k_log >= 16` so this branch only fires in
    /// tiny test setups.
    pub s_hat_v_ab: Option<Vec<F128>>,
    /// Precomputed `s_hat_v` for the C claim — produced by zerocheck round 1's
    /// two-bank fusion kernel (one extra `vld1q+veorq` per chunk-lane-b_med
    /// vs the original single-bank C-side). Skips `fold_1b_rows` for the C
    /// claim at PCS-open time.
    pub s_hat_v_c: Vec<F128>,
}

/// Run commit → bind → zerocheck → lincheck and build the base claims, stopping
/// just before the PCS open. See [`ProveCore`].
pub fn prove_fast_core<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    challenger: &mut Ch,
) -> ProveCore {
    prove_fast_core_with_codeword(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        None,
        challenger,
    )
}

/// [`prove_fast_core`] with an optional pre-faulted codeword buffer (see
/// [`pcs::prefault_codeword_during`]). When `Some`, the commit reuses it via
/// [`pcs::commit_into`] instead of allocating — the alloc was already done,
/// overlapped with witness generation. When `None`, behaves exactly like
/// [`prove_fast_core`] (commit allocates inline).
#[allow(clippy::too_many_arguments)]
pub fn prove_fast_core_with_codeword<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    prefaulted_codeword: Option<Vec<F128>>,
    challenger: &mut Ch,
) -> ProveCore {
    prove_fast_core_impl(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        prefaulted_codeword,
        None,
        challenger,
    )
}

/// zk variant of [`prove_fast_core`] — see [`prove_fast_ligerito_from_witness_zk`].
#[allow(clippy::too_many_arguments)]
pub fn prove_fast_core_zk<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    zk_rng: &mut dyn flock_core::zk::MaskSampler,
    challenger: &mut Ch,
) -> ProveCore {
    assert!(pcs_params.zk, "zk prove entry requires PcsParams.zk");
    prove_fast_core_impl(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        None,
        Some(zk_rng),
        challenger,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_fast_core_impl<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    prefaulted_codeword: Option<Vec<F128>>,
    zk_rng: Option<&mut dyn flock_core::zk::MaskSampler>,
    challenger: &mut Ch,
) -> ProveCore {
    let (commitment, prover_data) =
        commit_dispatch(&z_packed, pcs_params, prefaulted_codeword, zk_rng);
    bind_statement(challenger, r1cs, &commitment);

    let padding = r1cs.padding_spec();
    let (zc_proof, zc_claim, s_hat_v_c) = {
        // Zero-cost &[u8] views of the F128 buffers; c aliases z (C = I).
        let a_packed: &[u8] = unsafe {
            std::slice::from_raw_parts(
                a_packed_f128.as_ptr() as *const u8,
                a_packed_f128.len() * core::mem::size_of::<F128>(),
            )
        };
        let b_packed: &[u8] = unsafe {
            std::slice::from_raw_parts(
                b_packed_f128.as_ptr() as *const u8,
                b_packed_f128.len() * core::mem::size_of::<F128>(),
            )
        };
        let c_packed: &[u8] = unsafe {
            std::slice::from_raw_parts(
                z_packed.as_ptr() as *const u8,
                z_packed.len() * core::mem::size_of::<F128>(),
            )
        };
        zerocheck::prove_packed_padded_capture_s_hat_v_c(
            a_packed, b_packed, c_packed, r1cs.m, &padding, challenger,
        )
    };
    // Nothing downstream reads a/b (zerocheck consumed them in rounds 1–2);
    // recycle the two buffers (2 × 2^(m-3) bytes — 128 MB at m = 29) instead
    // of carrying them through lincheck and the PCS open.
    flock_core::scratch::give_f128(a_packed_f128);
    flock_core::scratch::give_f128(b_packed_f128);

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);

    // Capture lincheck's pre-sumcheck z_vec so the PCS open can derive the
    // AB-claim's `s_hat_v` from it (skips fold_1b_rows for AB).
    let (lc_proof, lc_claim, z_vec_pre) = lincheck::prove_padded_capture_z_vec(
        &z_packed_lincheck,
        r1cs.m,
        r1cs.k_log,
        r1cs.k_skip,
        r1cs.useful_bits,
        lincheck_circuit,
        &x_ab,
        challenger,
    );
    // The lincheck stripe copy of z is dead from here on; free it before the
    // PCS open (2^(m-3) bytes — 64 MB at m = 29).
    drop(z_packed_lincheck);

    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };

    // Strided fold of z_vec_pre against the AB-claim suffix's inner-rest tail
    // (everything past prefix0). Byte-identical to `fold_1b_rows` on the AB
    // suffix tensor — see `s_hat_v_from_z_vec`. Skip when k_log < LOG_PACKING
    // (only test setups; real R1CS has k_log >= 16).
    let s_hat_v_ab = if r1cs.k_log >= pcs::LOG_PACKING {
        Some(pcs::ring_switch::s_hat_v_from_z_vec(
            &z_vec_pre,
            &lc_claim.r_inner_rest[1..],
        ))
    } else {
        None
    };

    ProveCore {
        zc_proof,
        lc_proof,
        ab,
        c,
        commitment,
        prover_data,
        z_packed,
        s_hat_v_ab,
        s_hat_v_c,
    }
}

/// Per-phase wall-clock timings (seconds) of the Ligerito fast prover, for
/// benchmark cost breakdowns. See [`prove_fast_ligerito_timed`].
#[derive(Clone, Copy, Debug, Default)]
pub struct ProvePhaseTimings {
    /// Witness generation. Filled by the per-setup `prove_fast_timed` wrappers
    /// (not by [`prove_fast_ligerito_timed`], which takes the witness as input).
    pub witness_s: f64,
    pub commit_s: f64,
    pub zerocheck_s: f64,
    /// Lincheck prove + the small post-lincheck base-claim / `s_hat_v` setup.
    pub lincheck_s: f64,
    /// The real Ligerito recursive PCS open (`open_claims_…_ligerito`).
    pub open_s: f64,
}

/// [`prove_fast_ligerito_from_witness`] with per-phase timers. Inlines the same
/// calls in the same order as `prove_fast_core_with_codeword` + the Ligerito
/// open, wrapping each phase in an `Instant`, so the returned
/// [`ProvePhaseTimings`] decompose the *real* Ligerito prover --- including its
/// recursive opening. Kept in lockstep
/// with `prove_fast_ligerito_from_witness`; benchmark-only.
#[allow(clippy::too_many_arguments)]
pub fn prove_fast_ligerito_timed<Ch: Challenger>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    prefaulted_codeword: Option<Vec<F128>>,
    challenger: &mut Ch,
) -> (R1csProofLigerito, Commitment, R1csClaim, ProvePhaseTimings) {
    use std::time::Instant;
    let mut t = ProvePhaseTimings::default();

    let log_n = r1cs.m - pcs::LOG_PACKING;
    let lig_config =
        pcs::ligerito::prover_config_for(log_n, pcs_params.log_batch_size, pcs_params.profile)
            .expect("Ligerito default config; bump m for tiny instances");

    // --- PCS commit ---
    let t0 = Instant::now();
    let (commitment, prover_data) = match prefaulted_codeword {
        Some(buf) => pcs::commit_into(&z_packed, pcs_params, buf),
        None => pcs::commit(&z_packed, pcs_params),
    };
    t.commit_s = t0.elapsed().as_secs_f64();
    bind_statement(challenger, r1cs, &commitment);

    let padding = r1cs.padding_spec();

    // --- zerocheck ---
    let t0 = Instant::now();
    let (zc_proof, zc_claim, s_hat_v_c) = {
        let a_packed: &[u8] = unsafe {
            std::slice::from_raw_parts(
                a_packed_f128.as_ptr() as *const u8,
                a_packed_f128.len() * core::mem::size_of::<F128>(),
            )
        };
        let b_packed: &[u8] = unsafe {
            std::slice::from_raw_parts(
                b_packed_f128.as_ptr() as *const u8,
                b_packed_f128.len() * core::mem::size_of::<F128>(),
            )
        };
        let c_packed: &[u8] = unsafe {
            std::slice::from_raw_parts(
                z_packed.as_ptr() as *const u8,
                z_packed.len() * core::mem::size_of::<F128>(),
            )
        };
        zerocheck::prove_packed_padded_capture_s_hat_v_c(
            a_packed, b_packed, c_packed, r1cs.m, &padding, challenger,
        )
    };
    t.zerocheck_s = t0.elapsed().as_secs_f64();
    flock_core::scratch::give_f128(a_packed_f128);
    flock_core::scratch::give_f128(b_packed_f128);

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);

    // --- lincheck + base-claim / s_hat_v setup ---
    let t0 = Instant::now();
    let (lc_proof, lc_claim, z_vec_pre) = lincheck::prove_padded_capture_z_vec(
        &z_packed_lincheck,
        r1cs.m,
        r1cs.k_log,
        r1cs.k_skip,
        r1cs.useful_bits,
        lincheck_circuit,
        &x_ab,
        challenger,
    );
    drop(z_packed_lincheck);
    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };
    let s_hat_v_ab = if r1cs.k_log >= pcs::LOG_PACKING {
        Some(pcs::ring_switch::s_hat_v_from_z_vec(
            &z_vec_pre,
            &lc_claim.r_inner_rest[1..],
        ))
    } else {
        None
    };
    t.lincheck_s = t0.elapsed().as_secs_f64();

    // --- Ligerito recursive PCS open ---
    let pre_ab: Option<&[F128]> = s_hat_v_ab.as_deref();
    let pre_c: Option<&[F128]> = Some(s_hat_v_c.as_slice());
    let t0 = Instant::now();
    let pcs_open = open_claims_with_precomputed_ligerito(
        z_packed,
        &prover_data,
        &commitment,
        &[ab.clone(), c.clone()],
        &[pre_ab, pre_c],
        &padding,
        &lig_config,
        challenger,
    );
    t.open_s = t0.elapsed().as_secs_f64();

    let proof = R1csProofLigerito {
        zerocheck: zc_proof,
        lincheck: lc_proof,
        pcs_open,
    };
    let claim = R1csClaim { ab, c };
    (proof, commitment, claim, t)
}

// ===========================================================================
// End-to-end reference prover/verifier for the A1′ amendment (Z10).
//
// Wires the degree-2 mask channel (Z1: `zerocheck::prove_packed_padded_zk`)
// and the hiding P,Q openings (Z2) into the full R1CS pipeline. This is a
// REFERENCE path — correctness/certification-oriented, self-contained, and it
// does NOT touch the shipped `prove_fast_zk` hot path. `P,Q` are opened
// hidingly at the zerocheck point so the joint-coverage leakage is
// `L = {P(ρ),Q(ρ)}`; the witness is committed and opened via the existing
// hiding PCS. The whole thing verifies through `verify_r1cs_zk_a1`.
// ===========================================================================

/// The A1′ end-to-end proof: the masked zerocheck, lincheck, the witness PCS
/// opening (for the `ab`,`c` claims, which the verifier recomputes itself),
/// and the two hiding `P,Q` openings at ρ.
///
/// Deliberately carries **no** claim values: the verifier derives the `ab`/`c`
/// claims from the transcript, so shipping copies in the proof would be
/// unchecked malleable bytes. Every field of this struct is classified in
/// [`crate::transcript_schema`]; changing the shape here requires updating the
/// flattener there (a compile error enforces it) and bumping the schema.
#[cfg(feature = "zk")]
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct R1csProofZkA1 {
    pub zerocheck: zerocheck::ZkZerocheckProof,
    pub lincheck: lincheck::LincheckProof,
    pub pcs_open: pcs::BatchOpeningProofLigerito,
    pub open_p: pcs::BatchOpeningProofLigerito,
    pub open_q: pcs::BatchOpeningProofLigerito,
    pub comm_p: Commitment,
    pub comm_q: Commitment,
}

/// Fill a length-`2^m` boolean cube from a mask sampler (one bit per entry),
/// returned in F128-packed form (as the commit + zerocheck both consume).
#[cfg(feature = "zk")]
fn sample_mask_bits(rng: &mut dyn flock_core::zk::MaskSampler, m: usize) -> Vec<F128> {
    let n = 1usize << m;
    let mut words = vec![0u64; n.div_ceil(64)];
    rng.fill_u64s(&mut words);
    let bits: Vec<bool> = (0..n).map(|i| (words[i / 64] >> (i % 64)) & 1 == 1).collect();
    pcs::pack_witness(&bits, m)
}

/// End-to-end A1′ prover. `zk_rng` is forked into independent streams for the
/// witness mask, the two mask polynomials, and their commitments.
///
/// Uses the production Ligerito config ladder for the statement's shape and
/// asserts the statement carries a zk randomizer layout (`r1cs.zk`): without
/// randomizer rows the affine transcript classes are unmasked and the proof
/// is NOT hiding. Audit fixtures with hand-rolled randomizer rows use
/// [`prove_r1cs_zk_a1_with_config`], which leaves layout responsibility to
/// the caller.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn prove_r1cs_zk_a1<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    zk_rng: &mut flock_core::zk::ZkRng,
    challenger: &mut Ch,
) -> (R1csProofZkA1, Commitment) {
    assert!(
        r1cs.zk.is_some(),
        "A1′ prove requires a zk randomizer layout (r1cs.zk); a statement \
         without randomizer rows yields a non-hiding transcript"
    );
    let log_n = pcs_params.log_msg_len();
    let lig_config =
        pcs::ligerito::prover_config_for(log_n, pcs_params.log_batch_size, pcs_params.profile)
            .expect("Ligerito config");
    prove_r1cs_zk_a1_with_config(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        &lig_config,
        zk_rng,
        challenger,
    )
}

/// The five independent mask streams the A1′ prover consumes. Production
/// builds these by domain-separated forks of one per-proof DRBG (see
/// [`A1MaskSources::from_rng`]); the leakage certificates substitute
/// playback samplers to unit-probe one channel at a time, which is how the
/// mask→transcript maps are extracted from the **real** prover rather than
/// from a re-implementation.
#[cfg(feature = "zk")]
pub struct A1MaskSources<'a> {
    /// Low-half mask μ and blinder g of the witness commitment.
    pub witness_commit: &'a mut dyn flock_core::zk::MaskSampler,
    /// Bits of the mask polynomial `P`.
    pub p: &'a mut dyn flock_core::zk::MaskSampler,
    /// Bits of the mask polynomial `Q`.
    pub q: &'a mut dyn flock_core::zk::MaskSampler,
    /// μ and g of the `P` commitment.
    pub commit_p: &'a mut dyn flock_core::zk::MaskSampler,
    /// μ and g of the `Q` commitment.
    pub commit_q: &'a mut dyn flock_core::zk::MaskSampler,
}

/// Owning form of [`A1MaskSources`] for the DRBG case (the forks must
/// outlive the borrow).
#[cfg(feature = "zk")]
pub struct A1MaskForks {
    pub witness_commit: flock_core::zk::ZkRng,
    pub p: flock_core::zk::ZkRng,
    pub q: flock_core::zk::ZkRng,
    pub commit_p: flock_core::zk::ZkRng,
    pub commit_q: flock_core::zk::ZkRng,
}

#[cfg(feature = "zk")]
impl A1MaskForks {
    /// Derive the five streams from one per-proof DRBG. The labels are part
    /// of the protocol: they make the channels independent, which is a
    /// hypothesis of the composition argument.
    pub fn from_rng(zk_rng: &mut flock_core::zk::ZkRng) -> Self {
        Self {
            witness_commit: zk_rng.fork(b"a1-witness-mask"),
            p: zk_rng.fork(b"a1-P"),
            q: zk_rng.fork(b"a1-Q"),
            commit_p: zk_rng.fork(b"a1-commit-P"),
            commit_q: zk_rng.fork(b"a1-commit-Q"),
        }
    }
    pub fn sources(&mut self) -> A1MaskSources<'_> {
        A1MaskSources {
            witness_commit: &mut self.witness_commit,
            p: &mut self.p,
            q: &mut self.q,
            commit_p: &mut self.commit_p,
            commit_q: &mut self.commit_q,
        }
    }
}

/// [`prove_r1cs_zk_a1`] with an explicit Ligerito prover config, for audit
/// fixtures at shapes outside the production config ladder (e.g. the m=15
/// certificate fixture). Does NOT check `r1cs.zk` — the caller owns the
/// randomizer-layout correctness of the statement.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn prove_r1cs_zk_a1_with_config<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_config: &pcs::ligerito::ProverConfig,
    zk_rng: &mut flock_core::zk::ZkRng,
    challenger: &mut Ch,
) -> (R1csProofZkA1, Commitment) {
    let mut forks = A1MaskForks::from_rng(zk_rng);
    let (proof, comm, _) = prove_r1cs_zk_a1_with_masks(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        lig_config,
        forks.sources(),
        None,
        challenger,
    );
    (proof, comm)
}

/// The A1′ prover with every mask channel supplied explicitly. This is the
/// map the leakage certificates probe.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn prove_r1cs_zk_a1_with_masks<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_config: &pcs::ligerito::ProverConfig,
    masks: A1MaskSources<'_>,
    coverage_probe_seed: Option<u64>,
    challenger: &mut Ch,
) -> (R1csProofZkA1, Commitment, Option<crate::zk_rank_check::RankCheckReport>) {
    assert!(pcs_params.zk, "A1′ prove requires PcsParams.zk");
    let m = r1cs.m;
    let padding = r1cs.padding_spec();
    let cast = |v: &[F128]| -> &[u8] {
        unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
    };

    let A1MaskSources { witness_commit, p, q, commit_p, commit_q } = masks;

    let p_f128 = sample_mask_bits(p, m);
    let q_f128 = sample_mask_bits(q, m);

    let (commitment, prover_data) = pcs::commit::commit_zk(&z_packed, pcs_params, witness_commit);
    let (comm_p, pd_p) = pcs::commit::commit_zk(&p_f128, pcs_params, commit_p);
    let (comm_q, pd_q) = pcs::commit::commit_zk(&q_f128, pcs_params, commit_q);

    bind_statement(challenger, r1cs, &commitment);
    challenger.observe_bytes(&comm_p.root);
    challenger.observe_bytes(&comm_q.root);

    // Per-proof mask-coverage self-check (ε_rank): the challenger is now at
    // exactly the position `prove_packed_padded_zk` starts from, so a clone
    // sees the same challenge schedule the proof will use. Pure observer —
    // it never touches `challenger` itself.
    let coverage = coverage_probe_seed.map(|seed| {
        crate::zk_rank_check::check_mask_coverage(cast(&q_f128), m, seed, &*challenger)
    });
    let coverage = match coverage {
        None => None,
        Some(Ok(report)) => Some(report),
        Some(Err(failed)) => Some(failed.report),
    };

    let (zk_zc, zc_claim) = zerocheck::prove_packed_padded_zk(
        cast(&a_packed_f128),
        cast(&b_packed_f128),
        cast(&z_packed),
        cast(&p_f128),
        cast(&q_f128),
        m,
        &padding,
        challenger,
    );
    flock_core::scratch::give_f128(a_packed_f128);
    flock_core::scratch::give_f128(b_packed_f128);

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);
    let (lc_proof, lc_claim, _z_vec_pre) = lincheck::prove_padded_capture_z_vec(
        &z_packed_lincheck,
        m,
        r1cs.k_log,
        r1cs.k_skip,
        r1cs.useful_bits,
        lincheck_circuit,
        &x_ab,
        challenger,
    );
    drop(z_packed_lincheck);

    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };

    // P,Q openings at ρ = (z, mlv_challenges), forked (domain-tagged) from the
    // post-lincheck transcript so they and the witness opening are independent.
    let x_point = zc_claim.mlv_challenges.clone();
    let mut ch_p = challenger.clone();
    ch_p.observe_label(b"flock-a1-open-P");
    let open_p = pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v(
        p_f128, &pd_p, &comm_p, &[x_point.as_slice()], &[], &[], &padding, lig_config, &mut ch_p,
    );
    let mut ch_q = challenger.clone();
    ch_q.observe_label(b"flock-a1-open-Q");
    let open_q = pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v(
        q_f128, &pd_q, &comm_q, &[x_point.as_slice()], &[], &[], &padding, lig_config, &mut ch_q,
    );

    let pcs_open = open_claims_with_precomputed_ligerito(
        z_packed,
        &prover_data,
        &commitment,
        &[ab, c],
        &[None, None],
        &padding,
        lig_config,
        challenger,
    );

    (
        R1csProofZkA1 { zerocheck: zk_zc, lincheck: lc_proof, pcs_open, open_p, open_q, comm_p, comm_q },
        commitment,
        coverage,
    )
}

/// End-to-end A1′ verifier. Mirrors `prove_r1cs_zk_a1`.
#[cfg(feature = "zk")]
pub fn verify_r1cs_zk_a1<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &R1csProofZkA1,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    challenger: &mut Ch,
) -> Result<(), flock_core::verifier::VerifyError> {
    let log_n = pcs_params.log_msg_len();
    let lig_v =
        pcs::ligerito::verifier_config_for(log_n, pcs_params.log_batch_size, pcs_params.profile)
            .expect("Ligerito verifier config");
    verify_r1cs_zk_a1_with_config(r1cs, pcs_params, proof, commitment, lincheck_circuit, &lig_v, challenger)
}

/// [`verify_r1cs_zk_a1`] with an explicit Ligerito verifier config, for audit
/// fixtures at shapes outside the production config ladder.
#[cfg(feature = "zk")]
pub fn verify_r1cs_zk_a1_with_config<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &R1csProofZkA1,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_v: &pcs::ligerito::VerifierConfig,
    challenger: &mut Ch,
) -> Result<(), flock_core::verifier::VerifyError> {
    use flock_core::verifier::VerifyError;
    let m = r1cs.m;

    // The P,Q commitments' params are attacker-supplied proof data; the
    // opening circuits key shapes and the zk branch off them, so they must
    // equal the verifier-owned params exactly (the witness path gets the
    // same check inside `verify_claims_ligerito`).
    if proof.comm_p.params != *pcs_params || proof.comm_q.params != *pcs_params {
        return Err(VerifyError::PcsAb(pcs::VerifyError::Ligerito));
    }

    bind_statement(challenger, r1cs, commitment);
    challenger.observe_bytes(&proof.comm_p.root);
    challenger.observe_bytes(&proof.comm_q.root);

    let zc_claim =
        zerocheck::verify_zk(m, &proof.zerocheck, challenger).map_err(VerifyError::Zerocheck)?;

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);
    let lc_claim = lincheck::verify(
        m,
        r1cs.k_log,
        r1cs.k_skip,
        lincheck_circuit,
        &x_ab,
        zc_claim.a_eval,
        zc_claim.b_eval,
        &proof.lincheck,
        challenger,
    )
    .map_err(VerifyError::Lincheck)?;

    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };

    let x_point = zc_claim.mlv_challenges.clone();
    let mut ch_p = challenger.clone();
    ch_p.observe_label(b"flock-a1-open-P");
    if pcs::verify_opening_batch_ligerito_mixed(
        &proof.comm_p,
        &[proof.zerocheck.final_p_eval],
        &[zc_claim.z],
        &[x_point.as_slice()],
        &[],
        &proof.open_p,
        lig_v,
        &mut ch_p,
    )
    .is_err()
    {
        return Err(VerifyError::PcsAb(pcs::VerifyError::Ligerito));
    }
    let mut ch_q = challenger.clone();
    ch_q.observe_label(b"flock-a1-open-Q");
    if pcs::verify_opening_batch_ligerito_mixed(
        &proof.comm_q,
        &[proof.zerocheck.final_q_eval],
        &[zc_claim.z],
        &[x_point.as_slice()],
        &[],
        &proof.open_q,
        lig_v,
        &mut ch_q,
    )
    .is_err()
    {
        return Err(VerifyError::PcsAb(pcs::VerifyError::Ligerito));
    }

    flock_core::verifier::verify_claims_ligerito_with_config(
        commitment,
        &[ab, c],
        &proof.pcs_open,
        pcs_params,
        lig_v,
        challenger,
    )
    .map_err(VerifyError::PcsAb)?;
    Ok(())
}

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
    let ro = flock_core::ro::RoContext::plain();
    open_claims_with_precomputed_ligerito_ro(
        z_packed,
        prover_data,
        commitment,
        claims,
        precomputed_s_hat_v,
        padding,
        lig_config,
        &ro,
        flock_core::ro::RoChannel::Witness,
        challenger,
    )
}

/// Batched claim opening with an explicit point-oracle context and channel.
#[allow(clippy::too_many_arguments)]
pub(crate) fn open_claims_with_precomputed_ligerito_ro<Ch: Challenger>(
    z_packed: Vec<F128>,
    prover_data: &pcs::ProverData,
    commitment: &Commitment,
    claims: &[ZClaim],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &zerocheck::PaddingSpec,
    lig_config: &pcs::ligerito::ProverConfig,
    ro: &flock_core::ro::RoContext,
    channel: flock_core::ro::RoChannel,
    challenger: &mut Ch,
) -> pcs::BatchOpeningProofLigerito {
    open_claims_with_precomputed_ligerito_pd_ro(
        z_packed,
        prover_data,
        commitment,
        claims,
        precomputed_s_hat_v,
        &[],
        padding,
        lig_config,
        ro,
        channel,
        challenger,
    )
}

/// Packed-direct batched opening with an explicit point-oracle context.
#[allow(clippy::too_many_arguments)]
pub(crate) fn open_claims_with_precomputed_ligerito_pd_ro<Ch: Challenger>(
    z_packed: Vec<F128>,
    prover_data: &pcs::ProverData,
    commitment: &Commitment,
    claims: &[ZClaim],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[pcs::PackedDirectClaim],
    padding: &zerocheck::PaddingSpec,
    lig_config: &pcs::ligerito::ProverConfig,
    ro: &flock_core::ro::RoContext,
    channel: flock_core::ro::RoChannel,
    challenger: &mut Ch,
) -> pcs::BatchOpeningProofLigerito {
    let x_fulls: Vec<Vec<F128>> = claims
        .iter()
        .map(|c| quirky_x_outer_full(&c.point))
        .collect();
    let x_refs: Vec<&[F128]> = x_fulls.iter().map(|v| v.as_slice()).collect();
    pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v_ro(
        z_packed,
        prover_data,
        commitment,
        &x_refs,
        precomputed_s_hat_v,
        packed_direct,
        padding,
        lig_config,
        ro,
        channel,
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
            let rng =
                zk_rng.expect("zk PcsParams require a mask sampler — use a *_zk prove entry point");
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
    bind_statement(challenger, r1cs, &commitment, &[0u8; 32]);

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
    bind_statement(challenger, r1cs, &commitment, &[0u8; 32]);

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
    bind_statement(challenger, r1cs, &commitment, &[0u8; 32]);

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
// Wires the field-valued P*Q-star mask channel (Z1:
// `zerocheck::prove_packed_padded_zk`) and the hiding P opening (Z2) into the
// full R1CS pipeline. This is a
// REFERENCE path — correctness/certification-oriented, self-contained, and it
// does NOT touch the shipped `prove_fast_zk` hot path. `P` is opened through
// an arbitrary public linear claim at the zerocheck point, while Q-star is
// fixed and public. The joint-coverage leakage is `L = {P(ρ)}`; the witness is
// committed and opened via the existing
// hiding PCS. The whole thing verifies through `verify_r1cs_zk_a1`.
// ===========================================================================

/// The A1′+A2+A3 end-to-end proof: the masked zerocheck, the masked lincheck,
/// the witness PCS opening (for the `ab`,`c` claims, which the verifier
/// recomputes itself), and the four hiding mask openings — `P` at rho, `S` at
/// the lincheck's output point, and A3's `S_c`,`S_h` at the c-claim point.
///
/// Deliberately carries **no** claim values: the verifier derives the `ab`/`c`
/// claims from the transcript, so shipping copies in the proof would be
/// unchecked malleable bytes. `sigma_lc`/`s_eval` are the exception and are
/// not claims about the witness — both are witness-free values of the A2 mask
/// channel, and both are bound (σ_lc by Fiat–Shamir ordering, s_eval by `S`'s
/// commitment).
///
/// Every field of this struct is classified in [`crate::transcript_schema`];
/// changing the shape here requires updating the flattener there (a compile
/// error enforces it) and bumping the schema.
#[cfg(feature = "zk")]
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct R1csProofZkA1 {
    /// Public per-proof nonce. It provides fresh RO/Merkle domains and is
    /// absorbed by `bind_statement` before any challenge.
    pub proof_nonce: [u8; 32],
    pub zerocheck: zerocheck::ZkZerocheckProof,
    pub lincheck: lincheck::LincheckProof,
    pub pcs_open: pcs::BatchOpeningProofLigerito,
    pub open_p: pcs::BatchOpeningProofLigerito,
    pub open_s: pcs::BatchOpeningProofLigerito,
    pub open_s_c: pcs::BatchOpeningProofLigerito,
    pub open_s_h: pcs::BatchOpeningProofLigerito,
    pub comm_p: Commitment,
    pub comm_s: Commitment,
    pub comm_s_c: Commitment,
    pub comm_s_h: Commitment,
    /// A2: `Σ_i comb[i]·S_vec[i]`, absorbed before `γ_lc` is drawn.
    pub sigma_lc: F128,
    /// A2: `Ŝ(ρ_lc)`, checked against `comm_s` at the lincheck output point.
    pub s_eval: F128,
    /// A3: `M_c(z) = Ŝ_c(z, r_rest)`, checked against `comm_s_c`.
    pub mc_at_z: F128,
    /// A3: `h(z) = Ŝ_h(z, r_rest)`, checked against `comm_s_h`.
    pub h_at_z: F128,
}

/// Fill a length-`2^m` boolean cube from a mask sampler (one bit per entry),
/// returned in F128-packed form (as the commit + zerocheck both consume).
#[cfg(feature = "zk")]
fn sample_mask_bits(rng: &mut dyn flock_core::zk::MaskSampler, m: usize) -> Vec<F128> {
    let n = 1usize << m;
    let mut words = vec![0u64; n.div_ceil(64)];
    rng.fill_u64s(&mut words);
    let bits: Vec<bool> = (0..n)
        .map(|i| (words[i / 64] >> (i % 64)) & 1 == 1)
        .collect();
    pcs::pack_witness(&bits, m)
}

#[cfg(feature = "zk")]
fn sample_mask_field_small(rng: &mut dyn flock_core::zk::MaskSampler, m: usize) -> Vec<F128> {
    let d = zerocheck::SmallMaskSpec::default().d(m);
    let mut words = vec![0u64; 2 * d];
    rng.fill_u64s(&mut words);
    words
        .chunks_exact(2)
        .map(|pair| F128::new(pair[0], pair[1]))
        .collect()
}

/// End-to-end A1′ prover. `zk_rng` is forked into independent streams for the
/// witness mask, the four mask polynomials, and their commitments.
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

/// The nine independent mask streams the A1′ prover consumes: field-valued
/// `P`, bit-cube channels `S`, `S_c`, and `S_h`, the witness commitment's
/// mu/g stream, and one mu/g stream per mask commitment. Production
/// builds these by domain-separated forks of one per-proof DRBG (see
/// [`A1MaskSources::from_rng`]); the leakage certificates substitute
/// playback samplers to unit-probe one channel at a time, which is how the
/// mask→transcript maps are extracted from the **real** prover rather than
/// from a re-implementation.
#[cfg(feature = "zk")]
pub struct A1MaskSources<'a> {
    /// Low-half mask μ and blinder g of the witness commitment.
    pub witness_commit: &'a mut dyn flock_core::zk::MaskSampler,
    /// Field coordinates of the mask polynomial `P`.
    pub p: &'a mut dyn flock_core::zk::MaskSampler,
    /// μ and g of the `P` commitment.
    pub commit_p: &'a mut dyn flock_core::zk::MaskSampler,
    /// Bits of the lincheck mask polynomial `S` (amendment A2).
    pub s: &'a mut dyn flock_core::zk::MaskSampler,
    /// μ and g of the `S` commitment.
    pub commit_s: &'a mut dyn flock_core::zk::MaskSampler,
    /// Bits of the round-1 C-side mask cube `S_c` (amendment A3).
    pub s_c: &'a mut dyn flock_core::zk::MaskSampler,
    /// Bits of the round-1 off-diagonal generator cube `S_h` (amendment A3).
    pub s_h: &'a mut dyn flock_core::zk::MaskSampler,
    /// μ and g of the `S_c` commitment.
    pub commit_s_c: &'a mut dyn flock_core::zk::MaskSampler,
    /// μ and g of the `S_h` commitment.
    pub commit_s_h: &'a mut dyn flock_core::zk::MaskSampler,
}

/// Owning form of [`A1MaskSources`] for the DRBG case (the forks must
/// outlive the borrow).
#[cfg(feature = "zk")]
pub struct A1MaskForks {
    pub witness_commit: flock_core::zk::ZkRng,
    pub p: flock_core::zk::ZkRng,
    pub commit_p: flock_core::zk::ZkRng,
    pub s: flock_core::zk::ZkRng,
    pub commit_s: flock_core::zk::ZkRng,
    pub s_c: flock_core::zk::ZkRng,
    pub s_h: flock_core::zk::ZkRng,
    pub commit_s_c: flock_core::zk::ZkRng,
    pub commit_s_h: flock_core::zk::ZkRng,
    pub proof_nonce: [u8; 32],
}

#[cfg(feature = "zk")]
impl A1MaskForks {
    /// Derive the nine mask streams plus the nonce from one per-proof DRBG.
    /// The labels are part
    /// of the protocol: they make the channels independent, which is a
    /// hypothesis of the composition argument.
    pub fn from_rng(zk_rng: &mut flock_core::zk::ZkRng) -> Self {
        let witness_commit = zk_rng.fork(b"a1-witness-mask");
        let p = zk_rng.fork(b"a1-P");
        let commit_p = zk_rng.fork(b"a1-commit-P");
        let s = zk_rng.fork(b"a2-S");
        let commit_s = zk_rng.fork(b"a2-commit-S");
        let s_c = zk_rng.fork(b"a3-Sc");
        let s_h = zk_rng.fork(b"a3-Sh");
        let commit_s_c = zk_rng.fork(b"a3-commit-Sc");
        let commit_s_h = zk_rng.fork(b"a3-commit-Sh");
        let mut nonce_rng = zk_rng.fork(b"a1-proof-nonce");
        let mut proof_nonce = [0u8; 32];
        for (chunk, word) in proof_nonce
            .chunks_exact_mut(8)
            .zip((0..4).map(|_| nonce_rng.next_u64()))
        {
            chunk.copy_from_slice(&word.to_le_bytes());
        }
        Self {
            witness_commit,
            p,
            commit_p,
            s,
            commit_s,
            s_c,
            s_h,
            commit_s_c,
            commit_s_h,
            proof_nonce,
        }
    }
    pub fn sources(&mut self) -> A1MaskSources<'_> {
        A1MaskSources {
            witness_commit: &mut self.witness_commit,
            p: &mut self.p,
            commit_p: &mut self.commit_p,
            s: &mut self.s,
            commit_s: &mut self.commit_s,
            s_c: &mut self.s_c,
            s_h: &mut self.s_h,
            commit_s_c: &mut self.commit_s_c,
            commit_s_h: &mut self.commit_s_h,
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
    let proof_nonce = forks.proof_nonce;
    let (proof, comm, _) = prove_r1cs_zk_a1_with_masks_nonce(
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
        proof_nonce,
        challenger,
    );
    (proof, comm)
}

/// Where the A1′ prover's zerocheck sub-proof comes from.
///
/// This exists so a **simulator** can supply zerocheck messages of its own
/// while every other part of the proof — the five hiding commitments, the
/// masked lincheck, the batched opening — runs the production code
/// unmodified. The alternative, a second orchestration maintained alongside
/// this one, would drift; and a simulator that runs different code from the
/// prover demonstrates nothing about the prover.
///
/// Production never constructs one: the prove entry points pass `None`.
#[cfg(feature = "zk")]
pub trait ZerocheckSource<Ch: Challenger> {
    /// Emit a zerocheck sub-proof, absorbing exactly what the honest prover
    /// would absorb, and return it with the claim the verifier will
    /// reconstruct and the A3 round-1 mask transcript.
    fn emit(
        &mut self,
        m: usize,
        inputs: ZerocheckSourceInputs<'_>,
        challenger: &mut Ch,
        honest: &mut dyn FnMut(
            &mut Ch,
        ) -> (
            zerocheck::ZkZerocheckProof,
            zerocheck::ZerocheckClaim,
            zerocheck::Round1MaskTranscript,
        ),
    ) -> (
        zerocheck::ZkZerocheckProof,
        zerocheck::ZerocheckClaim,
        zerocheck::Round1MaskTranscript,
    );
}

/// Borrowed zerocheck inputs exposed to a simulator source. Production uses
/// the honest closure; the one-pass ROM simulator evaluates these same inputs
/// at its pre-sampled challenge tuple through flock-core's shipped kernels.
#[cfg(feature = "zk")]
#[derive(Clone, Copy)]
pub struct ZerocheckSourceInputs<'a> {
    pub a_packed: &'a [u8],
    pub b_packed: &'a [u8],
    pub c_packed: &'a [u8],
    pub p_small: &'a [F128],
    pub s_c_packed: &'a [u8],
    pub s_h_packed: &'a [u8],
    pub padding: &'a zerocheck::PaddingSpec,
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
) -> (
    R1csProofZkA1,
    Commitment,
    Option<crate::zk_rank_check::RankCheckReport>,
) {
    prove_r1cs_zk_a1_with_masks_nonce(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        lig_config,
        masks,
        coverage_probe_seed,
        [0u8; 32],
        challenger,
    )
}

/// [`prove_r1cs_zk_a1_with_masks`] with an explicit public proof nonce.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn prove_r1cs_zk_a1_with_masks_nonce<Ch: Challenger + Clone>(
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
    proof_nonce: [u8; 32],
    challenger: &mut Ch,
) -> (
    R1csProofZkA1,
    Commitment,
    Option<crate::zk_rank_check::RankCheckReport>,
) {
    prove_r1cs_zk_a1_with_masks_pd_nonce(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        lig_config,
        masks,
        &mut |_: &mut Ch| Vec::new(),
        None,
        coverage_probe_seed,
        proof_nonce,
        challenger,
    )
}

/// [`prove_r1cs_zk_a1_with_masks`] with **public packed-direct claims**.
///
/// `packed_direct` is a callback rather than a slice because the claims'
/// challenges must be drawn from the live transcript, at a position both
/// prover and verifier agree on: after the zerocheck and lincheck, immediately
/// before the batched opening. The callback receives the challenger at exactly
/// that point and returns the claims it built.
///
/// This is the seam the fixed-digest statement uses: the callback samples the
/// digest-binding point and returns one claim whose value is a public function
/// of the statement (see `crate::digest_bind`). Because the value is public,
/// the verifier recomputes it rather than reading it from the proof, and the
/// hiding argument may condition on it legitimately.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn prove_r1cs_zk_a1_with_masks_pd<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_config: &pcs::ligerito::ProverConfig,
    masks: A1MaskSources<'_>,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<pcs::PackedDirectClaim>,
    zerocheck_source: Option<&mut dyn ZerocheckSource<Ch>>,
    coverage_probe_seed: Option<u64>,
    challenger: &mut Ch,
) -> (
    R1csProofZkA1,
    Commitment,
    Option<crate::zk_rank_check::RankCheckReport>,
) {
    prove_r1cs_zk_a1_with_masks_pd_nonce(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        lig_config,
        masks,
        packed_direct,
        zerocheck_source,
        coverage_probe_seed,
        [0u8; 32],
        challenger,
    )
}

/// [`prove_r1cs_zk_a1_with_masks_pd`] with an explicit public proof nonce.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn prove_r1cs_zk_a1_with_masks_pd_nonce<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_config: &pcs::ligerito::ProverConfig,
    masks: A1MaskSources<'_>,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<pcs::PackedDirectClaim>,
    zerocheck_source: Option<&mut dyn ZerocheckSource<Ch>>,
    coverage_probe_seed: Option<u64>,
    proof_nonce: [u8; 32],
    challenger: &mut Ch,
) -> (
    R1csProofZkA1,
    Commitment,
    Option<crate::zk_rank_check::RankCheckReport>,
) {
    let ro = flock_core::ro::RoContext::native(proof_nonce);
    prove_r1cs_zk_a1_with_masks_pd_nonce_ro(
        r1cs,
        pcs_params,
        z_packed,
        a_packed_f128,
        b_packed_f128,
        z_packed_lincheck,
        lincheck_circuit,
        lig_config,
        masks,
        packed_direct,
        zerocheck_source,
        coverage_probe_seed,
        proof_nonce,
        &ro,
        challenger,
    )
}

/// Explicit-nonce A1′ prover using a caller-supplied point-oracle backend.
/// The simulator and recording-oracle extractor use this entry point; the
/// production wrapper above supplies the native SHA-256 backend.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn prove_r1cs_zk_a1_with_masks_pd_nonce_ro<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    z_packed: Vec<F128>,
    a_packed_f128: Vec<F128>,
    b_packed_f128: Vec<F128>,
    z_packed_lincheck: Vec<u8>,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_config: &pcs::ligerito::ProverConfig,
    masks: A1MaskSources<'_>,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<pcs::PackedDirectClaim>,
    zerocheck_source: Option<&mut dyn ZerocheckSource<Ch>>,
    coverage_probe_seed: Option<u64>,
    proof_nonce: [u8; 32],
    ro: &flock_core::ro::RoContext,
    challenger: &mut Ch,
) -> (
    R1csProofZkA1,
    Commitment,
    Option<crate::zk_rank_check::RankCheckReport>,
) {
    assert!(pcs_params.zk, "A1′ prove requires PcsParams.zk");
    let m = r1cs.m;
    let padding = r1cs.padding_spec();
    let cast = |v: &[F128]| -> &[u8] {
        unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
    };

    let A1MaskSources {
        witness_commit,
        p,
        commit_p,
        s,
        commit_s,
        s_c,
        s_h,
        commit_s_c,
        commit_s_h,
    } = masks;

    let p_small = sample_mask_field_small(p, m);
    let mut p_f128 = vec![F128::ZERO; 1usize << pcs_params.witness_log_msg_len()];
    p_f128[..p_small.len()].copy_from_slice(&p_small);
    let mut s_f128 = sample_mask_bits(s, m);
    // A2's mask enters the lincheck through the same partial fold the witness
    // does, so it needs the lincheck packing of the very same cube that
    // `comm_s` commits to — and the same honest zero padding, since the fold
    // skips those rows while the committed `Ŝ` would not.
    flock_core::lincheck::zero_lincheck_padding_rows(&mut s_f128, r1cs.k_log, r1cs.useful_bits);
    let s_packed_lincheck =
        flock_core::lincheck::pack_z_lincheck_from_packed(&s_f128, m, r1cs.k_log);

    let (commitment, prover_data) = pcs::commit::commit_zk_with_ro(
        &z_packed,
        pcs_params,
        witness_commit,
        ro,
        flock_core::ro::RoChannel::Witness,
    );
    let (comm_p, pd_p) = pcs::commit::commit_zk_with_ro(
        &p_f128,
        pcs_params,
        commit_p,
        ro,
        flock_core::ro::RoChannel::MaskP,
    );
    let (comm_s, pd_s) = pcs::commit::commit_zk_with_ro(
        &s_f128,
        pcs_params,
        commit_s,
        ro,
        flock_core::ro::RoChannel::MaskS,
    );
    // A3: the round-1 mask pair. Both are full-support witness-free cubes;
    // the round-1 fold reads their whole support, so no padding surgery.
    let s_c_f128 = sample_mask_bits(s_c, m);
    let s_h_f128 = sample_mask_bits(s_h, m);
    let (comm_s_c, pd_s_c) = pcs::commit::commit_zk_with_ro(
        &s_c_f128,
        pcs_params,
        commit_s_c,
        ro,
        flock_core::ro::RoChannel::MaskSc,
    );
    let (comm_s_h, pd_s_h) = pcs::commit::commit_zk_with_ro(
        &s_h_f128,
        pcs_params,
        commit_s_h,
        ro,
        flock_core::ro::RoChannel::MaskSh,
    );

    bind_statement(challenger, r1cs, &commitment, &proof_nonce);
    challenger.observe_bytes(&comm_p.root);
    // Bound here, before every challenge of the run: the A2 batching argument
    // needs `S` fixed before `γ_lc`, and this is the earliest safe point.
    challenger.observe_bytes(&comm_s.root);
    challenger.observe_bytes(&comm_s_c.root);
    challenger.observe_bytes(&comm_s_h.root);

    // Per-proof mask-coverage self-check (ε_rank): the challenger is now at
    // exactly the position `prove_packed_padded_zk` starts from, so a clone
    // sees the same challenge schedule the proof will use. Pure observer —
    // it never touches `challenger` itself.
    let coverage =
        coverage_probe_seed.map(|seed| {
            match crate::zk_rank_check::check_mask_coverage_fv(
                zerocheck::SmallMaskSpec::default(),
                m,
                seed,
            ) {
                Ok(report) => report,
                Err(failed) => failed.report,
            }
        });

    // The zerocheck seam. Production passes `None` and the honest masked
    // zerocheck runs. A *simulator* passes a source that emits its own
    // messages here — and only here — so that everything else (the
    // commitments, the lincheck, the openings) stays on this exact code path
    // rather than a copy of it that could drift out of agreement with the
    // prover it is supposed to be indistinguishable from.
    let a_bytes = cast(&a_packed_f128);
    let b_bytes = cast(&b_packed_f128);
    let c_bytes = cast(&z_packed);
    let sc_bytes = cast(&s_c_f128);
    let sh_bytes = cast(&s_h_f128);
    let mut honest = |ch: &mut Ch| {
        let (p, c, mk) = zerocheck::prove_packed_padded_zk_masked(
            a_bytes,
            b_bytes,
            c_bytes,
            &p_small,
            m,
            &padding,
            Some(zerocheck::Round1Mask {
                s_c_packed: sc_bytes,
                s_h_packed: sh_bytes,
            }),
            ch,
        );
        (
            p,
            c,
            mk.expect("mask=Some must produce a round-1 mask transcript"),
        )
    };
    let (zk_zc, zc_claim, zc_mask) = match zerocheck_source {
        Some(src) => src.emit(
            m,
            ZerocheckSourceInputs {
                a_packed: a_bytes,
                b_packed: b_bytes,
                c_packed: c_bytes,
                p_small: &p_small,
                s_c_packed: sc_bytes,
                s_h_packed: sh_bytes,
                padding: &padding,
            },
            challenger,
            &mut honest,
        ),
        None => honest(challenger),
    };
    flock_core::scratch::give_f128(a_packed_f128);
    flock_core::scratch::give_f128(b_packed_f128);

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);
    let (lc_proof, lc_claim, _z_vec_pre, lc_mask) = lincheck::prove_padded_masked_capture_z_vec(
        &z_packed_lincheck,
        m,
        r1cs.k_log,
        r1cs.k_skip,
        r1cs.useful_bits,
        lincheck_circuit,
        &x_ab,
        lincheck::LincheckMask {
            s_packed: &s_packed_lincheck,
        },
        challenger,
    );
    drop(z_packed_lincheck);
    drop(s_packed_lincheck);

    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc_claim.r_inner_skip, &lc_claim.r_inner_rest, &x_ab.x_outer),
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(zc_claim.z, &zc_claim.r_rest),
        value: zc_claim.c_eval,
    };

    // Bind the diagonal-support functional P(rho) against the field-valued
    // mask commitment. It is a general linear claim, not an ordinary MLE
    // point claim.
    let p_basis =
        zerocheck::SmallMaskSpec::default().terminal_basis(&zc_claim.mlv_challenges, p_f128.len());
    let mut ch_p = challenger.clone();
    ch_p.observe_label(b"flock-a1-open-P");
    let open_p = pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v_linear_ro(
        p_f128,
        &pd_p,
        &comm_p,
        &[],
        &[],
        &[],
        &[pcs::PackedLinearClaim {
            basis: p_basis,
            value: zk_zc.final_p_eval,
        }],
        &padding,
        lig_config,
        ro,
        flock_core::ro::RoChannel::MaskP,
        &mut ch_p,
    );

    // A3: open both round-1 mask cubes at the c-claim point — the same point
    // and shape as the C-claim, because that is where the un-shift happens.
    let s_c_claim = ZClaim {
        point: c.point.clone(),
        value: zc_mask.mc_at_z,
    };
    let s_h_claim = ZClaim {
        point: c.point.clone(),
        value: zc_mask.h_at_z,
    };
    let mut ch_sc = challenger.clone();
    ch_sc.observe_label(b"flock-a3-open-Sc");
    let open_s_c = open_claims_with_precomputed_ligerito_ro(
        s_c_f128,
        &pd_s_c,
        &comm_s_c,
        &[s_c_claim],
        &[None],
        &padding,
        lig_config,
        ro,
        flock_core::ro::RoChannel::MaskSc,
        &mut ch_sc,
    );
    let mut ch_sh = challenger.clone();
    ch_sh.observe_label(b"flock-a3-open-Sh");
    let open_s_h = open_claims_with_precomputed_ligerito_ro(
        s_h_f128,
        &pd_s_h,
        &comm_s_h,
        &[s_h_claim],
        &[None],
        &padding,
        lig_config,
        ro,
        flock_core::ro::RoChannel::MaskSh,
        &mut ch_sh,
    );

    // A2: open S hidingly at the lincheck's output point — the same point and
    // the same quirky shape as the `ab` claim, because `s_eval` un-shifts
    // exactly that claim. Without this opening `s_eval` would be a free
    // scalar chosen after ρ, and the output claim would be unconstrained.
    let s_claim = ZClaim {
        point: ab.point.clone(),
        value: lc_mask.s_eval,
    };
    let mut ch_s = challenger.clone();
    ch_s.observe_label(b"flock-a2-open-S");
    let open_s = open_claims_with_precomputed_ligerito_ro(
        s_f128,
        &pd_s,
        &comm_s,
        &[s_claim],
        &[None],
        &padding,
        lig_config,
        ro,
        flock_core::ro::RoChannel::MaskS,
        &mut ch_s,
    );

    // Public packed-direct claims (e.g. the fixed-digest binding) are built
    // here: after every PIOP message is bound, immediately before the open.
    let pd = packed_direct(challenger);
    let pcs_open = open_claims_with_precomputed_ligerito_pd_ro(
        z_packed,
        &prover_data,
        &commitment,
        &[ab, c],
        &[None, None],
        &pd,
        &padding,
        lig_config,
        ro,
        flock_core::ro::RoChannel::Witness,
        challenger,
    );

    (
        R1csProofZkA1 {
            proof_nonce,
            zerocheck: zk_zc,
            lincheck: lc_proof,
            pcs_open,
            open_p,
            open_s,
            open_s_c,
            open_s_h,
            comm_p,
            comm_s,
            comm_s_c,
            comm_s_h,
            sigma_lc: lc_mask.sigma_lc,
            s_eval: lc_mask.s_eval,
            mc_at_z: zc_mask.mc_at_z,
            h_at_z: zc_mask.h_at_z,
        },
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
    verify_r1cs_zk_a1_pd(
        r1cs,
        pcs_params,
        proof,
        commitment,
        lincheck_circuit,
        &mut |_: &mut Ch| Vec::new(),
        challenger,
    )
}

/// [`verify_r1cs_zk_a1`] with public packed-direct claims. Mirror of
/// [`prove_r1cs_zk_a1_with_masks_pd`]: the callback runs at the same
/// transcript position and must rebuild the same claims — from public data
/// only, since the verifier has no witness. A claim whose value the verifier
/// recomputes cannot be forged by the prover; a claim it fails to reproduce
/// makes the opening's combined target disagree and the proof is rejected.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn verify_r1cs_zk_a1_pd<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &R1csProofZkA1,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<(Vec<F128>, F128)>,
    challenger: &mut Ch,
) -> Result<(), flock_core::verifier::VerifyError> {
    let log_n = pcs_params.log_msg_len();
    let lig_v =
        pcs::ligerito::verifier_config_for(log_n, pcs_params.log_batch_size, pcs_params.profile)
            .expect("Ligerito verifier config");
    verify_r1cs_zk_a1_with_config_pd(
        r1cs,
        pcs_params,
        proof,
        commitment,
        lincheck_circuit,
        &lig_v,
        challenger,
        packed_direct,
    )
}

/// Packed-direct A1′ verification through an explicit point-oracle backend.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn verify_r1cs_zk_a1_pd_ro<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &R1csProofZkA1,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    ro: &flock_core::ro::RoContext,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<(Vec<F128>, F128)>,
    challenger: &mut Ch,
) -> Result<(), flock_core::verifier::VerifyError> {
    let log_n = pcs_params.log_msg_len();
    let lig_v =
        pcs::ligerito::verifier_config_for(log_n, pcs_params.log_batch_size, pcs_params.profile)
            .expect("Ligerito verifier config");
    verify_r1cs_zk_a1_with_config_pd_ro(
        r1cs,
        pcs_params,
        proof,
        commitment,
        lincheck_circuit,
        &lig_v,
        ro,
        challenger,
        packed_direct,
    )
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
    verify_r1cs_zk_a1_with_config_pd(
        r1cs,
        pcs_params,
        proof,
        commitment,
        lincheck_circuit,
        lig_v,
        challenger,
        &mut |_: &mut Ch| Vec::new(),
    )
}

/// [`verify_r1cs_zk_a1_with_config`] with public packed-direct claims.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn verify_r1cs_zk_a1_with_config_pd<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &R1csProofZkA1,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_v: &pcs::ligerito::VerifierConfig,
    challenger: &mut Ch,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<(Vec<F128>, F128)>,
) -> Result<(), flock_core::verifier::VerifyError> {
    let ro = flock_core::ro::RoContext::native(proof.proof_nonce);
    verify_r1cs_zk_a1_with_config_pd_ro(
        r1cs,
        pcs_params,
        proof,
        commitment,
        lincheck_circuit,
        lig_v,
        &ro,
        challenger,
        packed_direct,
    )
}

/// A1′ verifier using a caller-supplied point-oracle backend.
#[cfg(feature = "zk")]
#[allow(clippy::too_many_arguments)]
pub fn verify_r1cs_zk_a1_with_config_pd_ro<Ch: Challenger + Clone>(
    r1cs: &BlockR1cs,
    pcs_params: &PcsParams,
    proof: &R1csProofZkA1,
    commitment: &Commitment,
    lincheck_circuit: &dyn lincheck::LincheckCircuit,
    lig_v: &pcs::ligerito::VerifierConfig,
    ro: &flock_core::ro::RoContext,
    challenger: &mut Ch,
    packed_direct: &mut dyn FnMut(&mut Ch) -> Vec<(Vec<F128>, F128)>,
) -> Result<(), flock_core::verifier::VerifyError> {
    use flock_core::verifier::VerifyError;
    let m = r1cs.m;

    // The mask commitments' params are attacker-supplied proof data; the
    // opening circuits key shapes and the zk branch off them, so they must
    // equal the verifier-owned params exactly (the witness path gets the
    // same check inside `verify_claims_ligerito`).
    if proof.comm_p.params != *pcs_params
        || proof.comm_s.params != *pcs_params
        || proof.comm_s_c.params != *pcs_params
        || proof.comm_s_h.params != *pcs_params
    {
        return Err(VerifyError::PcsAb(pcs::VerifyError::Ligerito));
    }

    bind_statement(challenger, r1cs, commitment, &proof.proof_nonce);
    challenger.observe_bytes(&proof.comm_p.root);
    challenger.observe_bytes(&proof.comm_s.root);
    challenger.observe_bytes(&proof.comm_s_c.root);
    challenger.observe_bytes(&proof.comm_s_h.root);

    // A3: `mc_at_z`/`h_at_z` are unchecked here — they only un-shift the
    // C-claim and the AB running claim. The openings below bind them.
    let zc_claim = zerocheck::verify_zk_masked(
        m,
        &proof.zerocheck,
        Some((proof.mc_at_z, proof.h_at_z)),
        challenger,
    )
    .map_err(VerifyError::Zerocheck)?;

    let x_ab = r1cs.x_ab_from_mlv(zc_claim.z, &zc_claim.mlv_challenges);
    // A2: `s_eval` is still unchecked at this point — it only un-shifts the
    // claim. The opening against `comm_s` below is what binds it.
    let lc_claim = lincheck::verify_masked(
        m,
        r1cs.k_log,
        r1cs.k_skip,
        lincheck_circuit,
        &x_ab,
        zc_claim.a_eval,
        zc_claim.b_eval,
        &proof.lincheck,
        Some((proof.sigma_lc, proof.s_eval)),
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

    let p_basis = zerocheck::SmallMaskSpec::default().terminal_basis(
        &zc_claim.mlv_challenges,
        1usize << pcs_params.witness_log_msg_len(),
    );
    let mut ch_p = challenger.clone();
    ch_p.observe_label(b"flock-a1-open-P");
    if pcs::verify_opening_batch_ligerito_mixed_linear_ro(
        &proof.comm_p,
        &[],
        &[],
        &[],
        &[],
        &[pcs::PackedLinearClaimRef {
            basis: &p_basis,
            value: proof.zerocheck.final_p_eval,
        }],
        &proof.open_p,
        lig_v,
        ro,
        flock_core::ro::RoChannel::MaskP,
        &mut ch_p,
    )
    .is_err()
    {
        return Err(VerifyError::PcsAb(pcs::VerifyError::Ligerito));
    }

    // A2: bind `s_eval`. The lincheck already used it to un-shift `ab.value`,
    // so a wrong `s_eval` yields a wrong `ab` claim — but that would only be
    // caught by the witness opening below if the two errors failed to cancel.
    // Checking S's own opening removes the freedom outright.
    // A3: bind the two round-1 mask evaluations at the c-claim point.
    for (label, comm, opening, value, channel) in [
        (
            &b"flock-a3-open-Sc"[..],
            &proof.comm_s_c,
            &proof.open_s_c,
            proof.mc_at_z,
            flock_core::ro::RoChannel::MaskSc,
        ),
        (
            &b"flock-a3-open-Sh"[..],
            &proof.comm_s_h,
            &proof.open_s_h,
            proof.h_at_z,
            flock_core::ro::RoChannel::MaskSh,
        ),
    ] {
        let claim = ZClaim {
            point: c.point.clone(),
            value,
        };
        let mut ch = challenger.clone();
        ch.observe_label(label);
        flock_core::verifier::verify_claims_ligerito_with_config_ro(
            comm,
            &[claim],
            opening,
            pcs_params,
            lig_v,
            ro,
            channel,
            &mut ch,
        )
        .map_err(VerifyError::PcsAb)?;
    }

    let s_claim = ZClaim {
        point: ab.point.clone(),
        value: proof.s_eval,
    };
    let mut ch_s = challenger.clone();
    ch_s.observe_label(b"flock-a2-open-S");
    flock_core::verifier::verify_claims_ligerito_with_config_ro(
        &proof.comm_s,
        &[s_claim],
        &proof.open_s,
        pcs_params,
        lig_v,
        ro,
        flock_core::ro::RoChannel::MaskS,
        &mut ch_s,
    )
    .map_err(VerifyError::PcsAb)?;

    let pd = packed_direct(challenger);
    let pd_refs: Vec<pcs::PackedDirectClaimRef<'_>> = pd
        .iter()
        .map(|(point, value)| pcs::PackedDirectClaimRef {
            point: point.as_slice(),
            value: *value,
        })
        .collect();
    flock_core::verifier::verify_claims_ligerito_with_config_pd_ro(
        commitment,
        &[ab, c],
        &pd_refs,
        &proof.pcs_open,
        pcs_params,
        lig_v,
        ro,
        flock_core::ro::RoChannel::Witness,
        challenger,
    )
    .map_err(VerifyError::PcsAb)?;
    Ok(())
}

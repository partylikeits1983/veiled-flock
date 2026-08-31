//! FLOCK's zerocheck and lincheck over the example contexts.
//!
//! The prove side runs the native `flock_core` provers through the masking
//! prover context. The verify side is a port of the shifted verifier circuit
//! in `flock-prover/src/succinct_veil.rs`: it reads the masked messages as
//! affine expressions, samples the same challenges, and emits the round
//! recurrences and the terminal product as VEIL constraints.

use flock_core::{
    field::F128,
    lincheck::{self, LincheckCircuit, QuirkyPoint},
    pcs::LOG_PACKING,
    r1cs::{BlockR1cs, WitnessLayout},
    zerocheck::{self, K_SKIP, N_INNER, PaddingSpec, multilinear},
};

use crate::ctx::{Expr, ReadingCtx, SendingCtx, linear_combination};
use crate::error::VeilError;

/// Zerocheck output: the claim points plus the three terminal evaluations as
/// affine expressions in the masks.
pub struct ZerocheckOutput {
    pub z: F128,
    pub mlv_challenges: Vec<F128>,
    pub r_rest: Vec<F128>,
    /// `a_hat(z, mlv_challenges)`.
    pub a_eval: Expr,
    /// `b_hat(z, mlv_challenges)`.
    pub b_eval: Expr,
    /// `c_hat(z, r_rest)`, reconstructed from the round-one C message.
    pub c_eval: Expr,
}

/// Lincheck output: the fresh inner point and the single `z` claim value.
pub struct LincheckOutput {
    pub r_inner_skip: F128,
    pub r_inner_rest: Vec<F128>,
    pub w: Expr,
}

/// Run the native FLOCK zerocheck prover through the masking context. The
/// inputs are LSB-first bit-packed bytes of `a`, `b`, `c` over `2^m` bits.
pub fn zerocheck_prove<C: SendingCtx>(
    ctx: &mut C,
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
) -> Result<zerocheck::ZerocheckClaim, VeilError> {
    let (_, claim, _) = zerocheck::prove_packed_padded_capture_s_hat_v_c(
        a_packed, b_packed, c_packed, m, padding, ctx,
    );
    Ok(claim)
}

/// Read the masked zerocheck transcript and emit its constraints.
pub fn zerocheck_verify<C: ReadingCtx>(
    m: usize,
    ctx: &mut C,
) -> Result<ZerocheckOutput, VeilError> {
    if m < K_SKIP + N_INNER {
        return Err(VeilError::ProofShape("zerocheck m below K_SKIP + N_INNER"));
    }
    let ell = 1usize << K_SKIP;
    let rounds = m - K_SKIP;

    ctx.absorb_label(b"flock-zerocheck");
    let r = ctx.sample_eq_point(m)?;

    let round1_ab = ctx.read_next(ell)?;
    let round1_c = ctx.read_next(ell)?;
    let z = ctx.sample();

    let c_weights = multilinear::lagrange_weights_lambda_naive(K_SKIP, z);
    let c_eval = linear_combination(&round1_c, &c_weights);

    let combined_weights = multilinear::interpolate_at_z_combined_weights(K_SKIP, z);
    let combined: Vec<Expr> = round1_ab
        .iter()
        .zip(&round1_c)
        .map(|(ab, c)| ab.add(c))
        .collect();
    let mut running = linear_combination(&combined, &combined_weights).add(&c_eval);

    let mut mlv_challenges = Vec::with_capacity(rounds);
    for i in 0..rounds {
        let msg_1 = ctx.read_one()?;
        let msg_inf = ctx.read_one()?;
        let rho = ctx.sample();
        mlv_challenges.push(rho);
        let [running_weight, one_weight, infinity_weight] =
            zerocheck::sumcheck_round_weights(r[K_SKIP + i], rho)
                .ok_or(VeilError::DegenerateChallenge)?;
        running = running
            .scale(running_weight)
            .add(&msg_1.scale(one_weight))
            .add(&msg_inf.scale(infinity_weight));
    }

    let a_eval = ctx.read_one()?;
    let b_eval = ctx.read_one()?;
    ctx.assert_mul(a_eval.clone(), b_eval.clone(), running);

    Ok(ZerocheckOutput {
        z,
        mlv_challenges,
        r_rest: r[K_SKIP..].to_vec(),
        a_eval,
        b_eval,
        c_eval,
    })
}

/// Reject a block shape that the FLOCK layers cannot address.
/// Call before `BlockR1cs` point helpers, which assert on shape.
pub fn check_block_shape(r1cs: &BlockR1cs) -> Result<(), VeilError> {
    let batch_major_needs_packing_bit =
        matches!(r1cs.layout, WitnessLayout::BatchMajor) && r1cs.k_log < LOG_PACKING;
    if r1cs.k_skip != K_SKIP
        || r1cs.k_log < r1cs.k_skip
        || r1cs.m < r1cs.k_log
        || r1cs.m < K_SKIP + N_INNER
        || batch_major_needs_packing_bit
    {
        return Err(VeilError::ProofShape("block shape"));
    }
    Ok(())
}

/// Run the native FLOCK lincheck prover through the masking context.
/// `z_lincheck` is the lincheck packing of the Boolean witness
/// (`flock_core::lincheck::pack_z_lincheck`).
pub fn lincheck_prove<C: SendingCtx>(
    ctx: &mut C,
    r1cs: &BlockR1cs,
    circuit: &dyn LincheckCircuit,
    z_lincheck: &[u8],
    x_ab: &QuirkyPoint,
) -> lincheck::LincheckClaim {
    let (_, claim, _) = lincheck::prove_padded_capture_z_vec(
        z_lincheck,
        r1cs.m,
        r1cs.k_log,
        r1cs.k_skip,
        r1cs.useful_bits,
        circuit,
        x_ab,
        ctx,
    );
    claim
}

/// Read the masked lincheck transcript and emit its constraints. `v_a` and
/// `v_b` are the zerocheck's terminal evaluations at `x_ab`.
pub fn lincheck_verify<C: ReadingCtx>(
    r1cs: &BlockR1cs,
    circuit: &dyn LincheckCircuit,
    x_ab: &QuirkyPoint,
    v_a: Expr,
    v_b: Expr,
    ctx: &mut C,
) -> Result<LincheckOutput, VeilError> {
    check_block_shape(r1cs)?;
    if circuit.n_cols() != r1cs.k() {
        return Err(VeilError::ProofShape("lincheck circuit width"));
    }
    if x_ab.x_inner_rest.len() != r1cs.k_log - r1cs.k_skip
        || x_ab.x_outer.len() != r1cs.m - r1cs.k_log
    {
        return Err(VeilError::ProofShape("lincheck point shape"));
    }
    ctx.absorb_label(b"flock-lincheck");
    let alpha = ctx.sample();
    let eq_inner = lincheck::build_quirky_eq_table(x_ab.z_skip, &x_ab.x_inner_rest, r1cs.k_skip);
    let mut comb_vec = circuit.fold_alpha_batched(alpha, &eq_inner);
    let mut running = v_a.scale(alpha).add(&v_b);
    if let Some(column) = circuit.const_pin_col() {
        let beta = ctx.sample();
        comb_vec[column] += beta;
        running = running.add(&Expr::constant(beta));
    }

    let rounds = r1cs.k_log - r1cs.k_skip;
    let mut challenges = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let e1 = ctx.read_one()?;
        let einf = ctx.read_one()?;
        let rho = ctx.sample();
        let e0 = running.add(&e1);
        let c1 = e0.add(&e1).add(&einf);
        running = einf.scale(rho * rho).add(&c1.scale(rho)).add(&e0);
        lincheck::sumcheck_bind_top_in_place_par_pub(&mut comb_vec, rho);
        challenges.push(rho);
    }
    let z_partial = ctx.read_next(1usize << r1cs.k_skip)?;
    ctx.assert_zero(running.add(&linear_combination(&z_partial, &comb_vec)));

    let r_inner_skip = ctx.sample();
    let lambda = lincheck::build_quirky_eq_table(r_inner_skip, &[], r1cs.k_skip);
    let w = linear_combination(&z_partial, &lambda);
    challenges.reverse();
    Ok(LincheckOutput {
        r_inner_skip,
        r_inner_rest: challenges,
        w,
    })
}

/// The one squeeze order of a quirky point for `2^m` bits split as `k_log`
/// inner and `m - k_log` outer bits: `z_skip`, then the inner-rest
/// coordinates, then the outer coordinates, one scalar squeeze each.
fn quirky_point_from(
    mut sample: impl FnMut() -> F128,
    m: usize,
    k_log: usize,
) -> Result<QuirkyPoint, VeilError> {
    if k_log < K_SKIP || m < k_log {
        return Err(VeilError::ProofShape("quirky point shape"));
    }
    let z_skip = sample();
    let x_inner_rest = (0..k_log - K_SKIP).map(|_| sample()).collect();
    let x_outer = (0..m - k_log).map(|_| sample()).collect();
    Ok(QuirkyPoint {
        z_skip,
        x_inner_rest,
        x_outer,
    })
}

/// Sample a fresh quirky point on a reading context.
pub fn sample_quirky_point<C: ReadingCtx>(
    ctx: &mut C,
    m: usize,
    k_log: usize,
) -> Result<QuirkyPoint, VeilError> {
    quirky_point_from(|| ctx.sample(), m, k_log)
}

/// Sample the same quirky point on the prover, through its challenger.
pub fn sample_quirky_point_sending<C: SendingCtx>(
    ctx: &mut C,
    m: usize,
    k_log: usize,
) -> Result<QuirkyPoint, VeilError> {
    quirky_point_from(|| ctx.sample_f128(), m, k_log)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ctx::MaskCounter;
    use flock_core::r1cs::SparseBinaryMatrix;

    fn empty_matrix(k: usize) -> SparseBinaryMatrix {
        SparseBinaryMatrix {
            num_rows: k,
            num_cols: k,
            rows: vec![Vec::new(); k],
        }
    }

    fn empty_block_r1cs(m: usize, k_log: usize, layout: WitnessLayout) -> BlockR1cs {
        let k = 1usize << k_log;
        BlockR1cs {
            m,
            k_log,
            k_skip: K_SKIP,
            useful_bits: k,
            a_0: empty_matrix(k),
            b_0: empty_matrix(k),
            c_0: empty_matrix(k),
            layout,
            const_pin: None,
            zk: None,
            digest_cache: std::sync::OnceLock::new(),
            csc_cache: std::sync::OnceLock::new(),
        }
    }

    #[test]
    fn quirky_point_shape_is_guarded() {
        let mut counter = MaskCounter::new(None);
        assert_eq!(
            sample_quirky_point(&mut counter, 22, 5).unwrap_err(),
            VeilError::ProofShape("quirky point shape")
        );
        assert_eq!(
            sample_quirky_point(&mut counter, 5, 6).unwrap_err(),
            VeilError::ProofShape("quirky point shape")
        );
        let point = sample_quirky_point(&mut counter, 22, 6).unwrap();
        assert!(point.x_inner_rest.is_empty());
        assert_eq!(point.x_outer.len(), 16);
    }

    #[test]
    fn block_shape_rejects_unaddressable_batch_major_layout() {
        let r1cs = empty_block_r1cs(K_SKIP + N_INNER, K_SKIP, WitnessLayout::BatchMajor);
        assert_eq!(
            check_block_shape(&r1cs).unwrap_err(),
            VeilError::ProofShape("block shape")
        );

        let addressable =
            empty_block_r1cs(K_SKIP + N_INNER, LOG_PACKING, WitnessLayout::BatchMajor);
        assert!(check_block_shape(&addressable).is_ok());
    }
}

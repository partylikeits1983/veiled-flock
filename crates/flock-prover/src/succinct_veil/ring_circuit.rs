use super::*;
use std::sync::LazyLock;

pub(super) const AUXILIARY_PER_CLAIM: usize = 127;

fn basis(i: usize) -> F128 {
    if i < 64 {
        F128::new(1 << i, 0)
    } else {
        F128::new(0, 1 << (i - 64))
    }
}

fn trace(mut x: F128) -> F128 {
    let mut value = x;
    for _ in 1..128 {
        x *= x;
        value += x;
    }
    value
}

static DUAL_BASIS: LazyLock<Vec<F128>> = LazyLock::new(|| {
    let mut rows: Vec<(u128, u128)> = (0..128)
        .map(|i| {
            let mut row = 0u128;
            for j in 0..128 {
                let t = trace(basis(i) * basis(j));
                assert!(t == F128::ZERO || t == F128::ONE);
                row |= (t.lo as u128) << j;
            }
            (row, 1u128 << i)
        })
        .collect();
    for i in 0..128 {
        let pivot = (i..128)
            .find(|&j| rows[j].0 >> i & 1 != 0)
            .expect("trace pairing nondegenerate");
        rows.swap(i, pivot);
        let (a, b) = rows[i];
        for (j, row) in rows.iter_mut().enumerate() {
            if j != i && row.0 >> i & 1 != 0 {
                row.0 ^= a;
                row.1 ^= b;
            }
        }
    }
    rows.into_iter()
        .map(|(_, row)| F128::new(row as u64, (row >> 64) as u64))
        .collect()
});

static ROOT_BASIS: LazyLock<Vec<Vec<F128>>> = LazyLock::new(|| {
    let mut powers = vec![(0..128).map(basis).collect::<Vec<_>>()];
    for k in 1..128 {
        powers.push(powers[k - 1].iter().map(|v| *v * *v).collect());
    }
    (0..128).map(|k| powers[(128 - k) % 128].clone()).collect()
});

fn coefficients(weights: &[F128]) -> Vec<F128> {
    let mut dual = DUAL_BASIS.clone();
    (0..128)
        .map(|k| {
            let mut a = pcs::ring_switch::inner_product(weights, &dual);
            for _ in 0..((128 - k) % 128) {
                a *= a;
            }
            for d in &mut dual {
                *d *= *d;
            }
            a
        })
        .collect()
}

pub(super) struct AuxiliaryWires<'a> {
    pub masks: Option<&'a [F128]>,
    pub offset: usize,
    pub values: &'a mut Vec<F128>,
    pub cursor: usize,
}

impl AuxiliaryWires<'_> {
    fn square(
        &mut self,
        builder: &mut CircuitBuilder,
        input: &LinearCombination,
    ) -> Result<LinearCombination, SuccinctVeilError> {
        let index = self.offset + self.cursor;
        let masked = if let Some(masks) = self.masks {
            let value = input.evaluate(masks)?;
            let masked = value * value + masks[index];
            self.values.push(masked);
            masked
        } else {
            *self
                .values
                .get(self.cursor)
                .ok_or(SuccinctVeilError::InvalidShape("ring auxiliary values"))?
        };
        self.cursor += 1;
        let output = LinearCombination::constant(masked).add(&builder.input(index));
        builder.assert_mul(input, input, &output);
        Ok(output)
    }
}

// Express the bit transpose through a linearized polynomial. Mask each
// intermediate square so every committed circuit input is a fresh mask.
pub(super) fn transpose_claim(
    builder: &mut CircuitBuilder,
    input: &[LinearCombination],
    weights: &[F128],
    auxiliary: &mut AuxiliaryWires<'_>,
) -> Result<LinearCombination, SuccinctVeilError> {
    let coefficients = coefficients(weights);
    let linear = |k: usize| {
        let mut result = LinearCombination::zero();
        for (input, root) in input.iter().zip(&ROOT_BASIS[k]) {
            let c = *root * coefficients[k];
            result.constant += input.constant * c;
            result
                .terms
                .extend(input.terms.iter().map(|(i, v)| (*i, *v * c)));
        }
        result
    };
    let mut result = linear(127);
    for k in (0..127).rev() {
        result = auxiliary.square(builder, &result)?.add(&linear(k));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn masked_transpose_claim_matches_bits_and_rejects_tampering() {
        let mut rng = ZkRng::from_seed([44; 32]);
        let mut values = vec![F128::ZERO; 128];
        let mut weights = values.clone();
        let mut masks = vec![F128::ZERO; 128 + AUXILIARY_PER_CLAIM];
        rng.fill_f128(&mut values);
        rng.fill_f128(&mut weights);
        rng.fill_f128(&mut masks);
        let input: Vec<_> = values
            .iter()
            .zip(&masks)
            .enumerate()
            .map(|(i, (v, m))| {
                LinearCombination::constant(*v + *m).add(&LinearCombination::variable(i))
            })
            .collect();
        let expected = pcs::ring_switch::inner_product(
            &pcs::ring_switch::tensor_algebra_transpose(&values),
            &weights,
        );
        let mut outputs = Vec::new();
        let build = |private, outputs: &mut Vec<F128>| {
            let mut builder = CircuitBuilder::new(masks.len());
            let mut wires = AuxiliaryWires {
                masks: private,
                offset: 128,
                values: outputs,
                cursor: 0,
            };
            let claim = transpose_claim(&mut builder, &input, &weights, &mut wires).unwrap();
            assert_eq!(wires.cursor, AUXILIARY_PER_CLAIM);
            builder.assert_zero(&claim.add(&LinearCombination::constant(expected)));
            builder.finish()
        };
        let circuit = build(Some(masks.as_slice()), &mut outputs);
        assert!(circuit.is_satisfied(&masks).unwrap());
        assert_eq!(circuit, build(None, &mut outputs));
        let mut delta_v = vec![F128::ZERO; 128];
        let t = F128::new(0x1234, 0x5678);
        delta_v[0] = weights[1] * t;
        delta_v[1] = weights[0] * t;
        let delta_u = pcs::ring_switch::tensor_algebra_transpose(&delta_v);
        let mut translated_masks = masks.clone();
        for (m, d) in translated_masks[..128].iter_mut().zip(delta_u) {
            *m += d;
        }
        translated_masks[128..].fill(F128::ZERO);
        let mut unmasked_auxiliary = Vec::new();
        let interim_masks = translated_masks.clone();
        let _ = build(Some(&interim_masks), &mut unmasked_auxiliary);
        for ((m, old), new) in translated_masks[128..]
            .iter_mut()
            .zip(&outputs)
            .zip(&unmasked_auxiliary)
        {
            *m = *old + *new;
        }
        let mut translated_outputs = Vec::new();
        let translated = build(Some(&translated_masks), &mut translated_outputs);
        assert_eq!(outputs, translated_outputs);
        assert_eq!(circuit, translated);
        assert!(translated.is_satisfied(&translated_masks).unwrap());

        let ro = RoContext::native([44; 32]);
        let mut prover_ch = flock_core::challenger::FsChallenger::new(b"ring-circuit");
        let proof =
            veil_f128::prove_constraints(&circuit, &masks, &mut rng, &mut prover_ch, &ro).unwrap();
        let mut verifier_ch = flock_core::challenger::FsChallenger::new(b"ring-circuit");
        veil_f128::verify_constraints(&circuit, &proof, &mut verifier_ch, &ro, &ro).unwrap();
        for i in [0, 63, 126] {
            let mut bad = outputs.clone();
            bad[i] += F128::ONE;
            assert!(!build(None, &mut bad).is_satisfied(&masks).unwrap());
        }
        assert!(
            certify_constraint_soundness(&circuit, ConstraintParameters::succinct_flock_secure())
                .is_ok()
        );
    }
}

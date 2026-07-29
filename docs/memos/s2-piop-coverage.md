# S2 symbolic coverage: field-valued zerocheck mask

Protocol: `flock-zk-fv-v3`

This memo states exactly what the current S2 artifact proves. It does not turn
the older finite-seed rank probes into a theorem, and it does not claim that a
numeric rank check proves zero knowledge by itself.

## Linear spaces

Fix the public zerocheck schedule `c = (r_rest, rho)` and write:

- `R_c` for the `2n` round-message functionals of `p_small`;
- `L_c` for the two revealed leakage functionals `mask_init` and `P(rho)`;
- `A_c = [R_c; L_c]` for the stacked field-linear map.

The sumcheck recurrence makes both rows of `L_c` dependent on the round block.
Consequently the old target `rank(A_c) = 2n + 2` is impossible. The correct
conditioned-image criterion is:

```
rank(A_c) = 2n
rank(L_c) = 2
dim R_c(ker L_c) = 2n - 2.
```

The last equality follows from the first two and is also recomputed directly
by `flock_core::linalg::conditioned_image`.

## Polynomial certificate

`symbolic::kernels::mask_functional_matrix_fv_sym` is the straight-line
polynomial specialization of the shipped mask functional map. A differential
test checks it entry-for-entry against `mask_functional_matrix_fv` over
F2^128. The symbolic engine has no challenge-dependent inversion operation.

For each deployed shape, the artifact selects one `2n x 2n` minor of `A_c`.
Its determinant is not expanded. Instead the artifact records:

1. one exact challenge tuple where the determinant evaluates nonzero;
2. a component-wise determinant degree bound obtained by summing the maximum
   entry degree in each selected row;
3. the selected original rows and mask columns, so the calculation can be
   independently repeated.

The production `m = 22` determinant has total degree at most 720. Therefore
Mathlib's Schwartz-Zippel theorem bounds its zero set by
`720 / 2^128 < 2^-118.5`. The smaller `m = 13` and `m = 15` profiles have
degree bounds 126 and 216.

The checked data is in `docs/artifacts/s2_mask_coverage.json`; the replayer is
`crates/flock-core/tests/symbolic_mask_coverage.rs`. The generic Lean bridge is
`Flockzk.SchwartzZippelBound.schwartz_zippel_degree_budget`.

## Scope

This establishes the all-challenge bad-set bound for the corrected
field-valued zerocheck mask block. The witness, lincheck, and PCS replacement
layers require their own functional enumeration and are composed only after
their artifacts pass. The final ZK label is gated on that composition and on
the production certification run.

# Formal proof that the zk-Flock masking design is zero-knowledge

A Lean 4 + Mathlib development of the **masking theorems** behind Flock's
`zk` mode. `Flockzk/Masking.lean`: if the prover's transcript is an affine
function of uniform secret masks, and every witness-dependent direction
(conditioned on the public inputs) lies inside the mask image, then the
transcript distribution is witness-independent and exactly simulatable
without the witness.

`Flockzk/MaskingSurjective.lean` (the amended protocol A1′):
`transcript_witness_indep_of_surjective` — a mask map that is **surjective**
onto the value space needs no coset condition: the transcript is
witness-independent for every witness pair. This applies to the zerocheck
round-pair block under the degree-2 `γ·P·Q` channel **only in its
conditional form**: the load-bearing hypothesis is coverage on the kernel of
the leaked `P`-functionals (`P(ρ)`, `σ_z`, opening-internal values), a Rust
measurement (★′ in `docs/zk-proof.md` §5), not a Lean fact.
`mem_range_coprod` / `coprod_covers` — the ranges of two *independent
additive* mask channels compose (sumset). **Correction:** an earlier revision
used `coprod_covers` to compose the existing-mask channel with the `P·Q`
channel and concluded the entire amended transcript reduces to the single-map
theorem. That instantiation is invalid — the existing-mask channel is
*bilinear* (not additive) on the round-pair coordinates
(`zk_affinity_probe.rs` certifies the nonzero cross-species defect), so
`coprod_covers`'s hypothesis fails on exactly the class it was needed for.
The valid composition is triangular/conditional; the corresponding lemma
(`MaskingTriangular.lean`) is the replacement — see `docs/zk-proof.md` §4.

`Flockzk/MaskingMixture.lean` (historical stepping stone): the conditional
form for the zerocheck round pairs when they are left bilinear across the two
randomizer species — for a family of affine maps indexed by `(witness, u_B)`
with constant image and coset-covered offsets, the joint distribution over
uniform `(u_A, u_B)` is witness-independent. **Its `h_coset` hypothesis is
disproved on the full transcript** (`final_b_breaks_full_mixture_hcoset`:
`final_b_eval` has an identically-zero `u_A`-derivative but varies with
`u_B`), so this theorem does not apply as-is; it is retained only as a
stepping stone toward the triangular argument.

## The two-layer argument

The zero-knowledge claim for the implementation splits into a proved
theorem and machine-checked hypotheses:

1. **This directory (proved, machine-checked by Lean):**
   - `Masking.lean` — for `transcript(u, w) = A u + f w` with
     `A : U →+ V` (over F₂, F₂-linear = additive) and `u` uniform on the
     finite mask space `U`: `transcript_witness_indep` (if
     `pub w = pub w'` implies `f w − f w' ∈ Image A`, the transcript
     distributions of `w` and `w'` are **identical**), `simulator_exact`
     (sampling `A u + r` from any public coset representative `r`
     reproduces the honest distribution exactly),
     `fiber_card_const` / `fiber_card_off_coset` (uniform on its coset,
     `|ker A|` masks per attainable value), and `pmf_*` forms.
   - `MaskingMixture.lean` — for a *family* `A w b : U →+ V` (the
     transcript is affine in `u_A` only after conditioning on `u_B`; the
     map may depend on both the witness and `u_B`):
     `mixture_witness_indep` and `pmf_mixture_*` — if every slice has
     the **same image** `V₀` and all offsets of equal-public-input
     witnesses lie in one coset of `V₀`, the joint distribution over
     uniform `(u_A, u_B)` is witness-independent, and running the honest
     prover on any public reference witness is an exact simulator.

   No `sorry`; the proofs depend only on Lean's standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`).

2. **The Rust rank audits** (re-runnable locally, and run in CI:
   `.github/workflows/test.yml` compiles and tests the `zk` feature per PR,
   and `.github/workflows/zk-certificates.yml` runs the offline certificate
   suite on a schedule) verify hypotheses on the real prover at fixed
   challenges:
   - *PCS layer* (`crates/flock-core/src/pcs/zk_audit.rs`): unit-probe
     differencing extracts the mask map, and Gaussian elimination checks
     that witness-difference directions, restricted to the kernel of the
     public claim functionals, lie inside the extracted mask image.
     Affinity itself is structural at this layer — every revealed value
     is F₂₁₂₈-linear in the committed data and the opening basis carries
     no mask randomness — the probes do not independently certify it.
   - *PIOP layer, affine classes*
     (`crates/flock-prover/tests/zk_piop_audit.rs`): k-wise rank
     certificate over mixed-species probes — a valid uniformity inference
     for the classes that are jointly affine in the masks.
   - *PIOP layer, zerocheck round pairs*
     (`crates/flock-prover/tests/zk_affinity_probe.rs`): measures that
     the joint-affinity defect is confined to the round pairs and absent
     at fixed `u_B`. **Caveat:** its second test was built to check the
     mixture theorem's hypotheses on 6-value subsets, and passed only
     because those subsets never sampled `final_b_eval` — the coordinate
     on which the hypothesis is disproved
     (`final_b_breaks_full_mixture_hcoset`). Its within-slice image
     measurements survive as evidence for the triangular argument's
     inner-stage hypotheses; the cross-`u_B` coset claim does not.

   Negative controls (withholding the blinder `g`, withholding the A-type
   randomizer group) make the audits fail, demonstrating the checks are
   not vacuous.

Together: formally verified theorems whose hypotheses are empirically
certified on the implementation. The remaining informal gap is the usual
model-vs-binary correspondence: the audits sample specific instances,
challenge tuples, and value subsets. What Lean does **not** cover: the
computational hiding of unopened Merkle siblings (SHA-256 preimage
resistance) and the Fiat–Shamir lift to NIZK — see
`docs/zk-leakage.md` §3.

## Instantiation for zk-Flock

- `U` = the mask space: randomizer witness bits × the PCS mask block × the
  blinder `g` (all uniform, drawn from the prover's DRBG);
- `V` = F₂^(128 · #revealed values): every field element the prover
  reveals — zerocheck round-1 vectors, all round pairs, final evals,
  `z_partial`, `s_hat_v`, opened codeword rows, PCS sumcheck messages,
  `yr`, `y_g`;
- `A` = the transcript's linear dependence on the masks at fixed
  challenges — a single map for the affine classes (`Masking.lean`), the
  family of fixed-`u_B` slices `A w u_B` for the zerocheck round pairs
  (`MaskingMixture.lean`);
- `f w` = the witness/statement-dependent offset;
- `pub` = the public claim values (the PCS opening genuinely determines
  them from the transcript — conditioning on them is part of the HVZK
  definition, not a weakening).

## Building

```sh
cd lean
lake exe cache get   # fetch prebuilt Mathlib (first time only)
lake build
```

Pinned to the Mathlib release in `lakefile.toml` / `lean-toolchain`.

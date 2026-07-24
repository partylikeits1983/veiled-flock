# Formal proof that the zk-Flock masking design is zero-knowledge

A Lean 4 + Mathlib development proving the **masking theorem** behind
Flock's `zk` mode (`Flockzk/Masking.lean`): if the prover's transcript is
an affine function of uniform secret masks, and every witness-dependent
direction (conditioned on the public inputs) lies inside the mask image,
then the transcript distribution is witness-independent and exactly
simulatable without the witness.

## The two-layer argument

The zero-knowledge claim for the implementation splits into a proved
theorem and machine-checked hypotheses:

1. **This directory (proved, machine-checked by Lean):**
   for `transcript(u, w) = A u + f w` with `A : U →+ V` (over F₂,
   F₂-linear = additive) and `u` uniform on the finite mask space `U`:
   - `transcript_witness_indep` — if `pub w = pub w'` implies
     `f w − f w' ∈ Image A`, the transcript distributions of `w` and `w'`
     are **identical** (exact fiber-count equality for every value);
   - `simulator_exact` — sampling `A u + r` from any public coset
     representative `r` reproduces the honest distribution exactly:
     honest-verifier zero-knowledge at fixed challenges;
   - `fiber_card_const` / `fiber_card_off_coset` — the transcript is
     uniform on its coset (`|ker A|` masks per attainable value, none
     elsewhere);
   - `pmf_*` — the same statements in Mathlib's `PMF` (probability
     distribution) form.

   No `sorry`; the proofs depend only on Lean's standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`).

2. **The Rust rank audits (checked per instance, in CI):** the audits in
   `crates/flock-core/src/pcs/zk_audit.rs` and
   `crates/flock-prover/tests/zk_piop_audit.rs` verify exactly the two
   hypotheses on the real prover at fixed challenges:
   - *affinity* — unit/combination-probe differencing recovers a
     consistent linear map, which is exact only if the transcript map is
     affine in the masks (this is how the probe matrices are built);
   - *coverage* — witness-difference directions, restricted to the kernel
     of the public claim functionals, lie inside the extracted mask image
     (`Image B ⊆ Image A`, Gaussian elimination over F₂/F₂₁₂₈).

   Negative controls (withholding the blinder `g`, withholding the A-type
   randomizer group) make the audits fail, demonstrating the checks are
   not vacuous.

Together: a formally verified theorem whose hypotheses are empirically
certified on the implementation. The remaining informal gap is the usual
model-vs-binary correspondence (the audits sample specific instances and
challenge tuples; the affine structure itself is
challenge-value-independent by construction). What Lean does **not**
cover: the computational hiding of unopened Merkle siblings (SHA-256
preimage resistance) and the Fiat–Shamir lift to NIZK — see
`docs/zk-leakage.md` §3.

## Instantiation for zk-Flock

- `U` = the mask space: randomizer witness bits × the PCS mask block × the
  blinder `g` (all uniform, drawn from the prover's DRBG);
- `V` = F₂^(128 · #revealed values): every field element the prover
  reveals — zerocheck round-1 vectors, all round pairs, final evals,
  `z_partial`, `s_hat_v`, opened codeword rows, PCS sumcheck messages,
  `yr`, `y_g`;
- `A` = the transcript's linear dependence on the masks at fixed
  challenges (extracted by the audits);
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

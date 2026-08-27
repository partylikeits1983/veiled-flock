import VeiledFlock.ProductionLayerSpec

/-!
# Production VEIL constraint-compiler semantics

This file instantiates the abstract `ProductionLayerSpec.Spec` with the exact
algebraic compiler used by `veil-f128`:

* one original multiplication row;
* dummy rows `(r,s,rs)` and `(r+1,t,(r+1)t)`;
* Hadamard weights `(1, alpha, alpha^2)`; and
* one batched affine-linear claim whose target depends only on the public
  statement and the three published Hadamard claims.

The two proof obligations previously stored directly in `Spec` are derived
here.  The Hadamard claim identity follows by interpolation and computation;
the linear kernel follows because every compiled assignment evaluates to the
same public target.
-/

namespace VeiledFlock.ProductionConstraintCompiler

set_option maxHeartbeats 100000

open Function
open Polynomial
open VeiledFlock.AdditiveReedSolomon
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionLayerSpec
open VeiledFlock.ProductionMultiplicationPadding
open VeiledFlock.ProductionProductMask
open VeiledFlock.ProductionVeilCore
open VeiledFlock.ProductionVeilLayer

/-- The production Hadamard dot vector `powers(alpha, 3)`. -/
noncomputable def multiplicationFunctional (alpha : GhashField) :
    (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField where
  toFun values :=
    values ⟨0, by decide⟩ + alpha * values ⟨1, by decide⟩ +
      alpha ^ 2 * values ⟨2, by decide⟩
  map_add' left right := by
    simp only [Pi.add_apply]
    ring
  map_smul' scalar values := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- Literal three multiplication rows after `padded_circuit`: the original
shifted-verifier multiplication followed by the two VEIL dummy products. -/
noncomputable def rowA (secret : GhashField × GhashField × GhashField)
    (dummy : DummyCoins) : Fin paddedMultiplications → GhashField := ![
  secret.1, dummy.1, dummy.1 + 1]

noncomputable def rowB (secret : GhashField × GhashField × GhashField)
    (dummy : DummyCoins) : Fin paddedMultiplications → GhashField := ![
  secret.2.1, dummy.2.1, dummy.2.2]

noncomputable def rowC (secret : GhashField × GhashField × GhashField)
    (dummy : DummyCoins) : Fin paddedMultiplications → GhashField := ![
  secret.2.2, dummy.1 * dummy.2.1, (dummy.1 + 1) * dummy.2.2]

theorem rows_valid (secret : GhashField × GhashField × GhashField)
    (hsecret : secret.1 * secret.2.1 = secret.2.2)
    (dummy : DummyCoins) :
    ∀ index, rowA secret dummy index * rowB secret dummy index =
      rowC secret dummy index := by
  intro index
  fin_cases index
  · exact hsecret
  · rfl
  · rfl

/-- Kernel-checked identity corresponding to Rust's
`claimed_dot_products = [dot(a), dot(b), dot(c)]`. -/
theorem triple_claims_of_rows (alpha : GhashField)
    (secret : GhashField × GhashField × GhashField)
    (dummy : DummyCoins) (triple : ValidTriple)
    (ha : ∀ index, triple.a.1.eval (multiplicationPoint index) =
      rowA secret dummy index)
    (hb : ∀ index, triple.b.1.eval (multiplicationPoint index) =
      rowB secret dummy index)
    (hc : ∀ index, triple.c.1.eval (multiplicationPoint index) =
      rowC secret dummy index) :
    tripleClaims (multiplicationFunctional alpha) triple =
      visibleClaims alpha (fun _ : Unit => secret) () dummy := by
  rcases secret with ⟨a, b, c⟩
  rcases dummy with ⟨r, s, t⟩
  simp only [tripleClaims, visibleClaims]
  apply Prod.ext
  · change
      triple.a.1.eval (multiplicationPoint ⟨0, by decide⟩) +
          alpha * triple.a.1.eval (multiplicationPoint ⟨1, by decide⟩) +
        alpha ^ 2 * triple.a.1.eval
          (multiplicationPoint ⟨2, by decide⟩) = _
    rw [ha, ha, ha]
    simp [productionDummyView, rowA, paddedMultiplications]
    ring
  · apply Prod.ext
    · change
        triple.b.1.eval (multiplicationPoint ⟨0, by decide⟩) +
            alpha * triple.b.1.eval (multiplicationPoint ⟨1, by decide⟩) +
          alpha ^ 2 * triple.b.1.eval
            (multiplicationPoint ⟨2, by decide⟩) = _
      rw [hb, hb, hb]
      simp [productionDummyView, rowB, paddedMultiplications]
      ring
    · change
        triple.c.1.eval (multiplicationPoint ⟨0, by decide⟩) +
            alpha * triple.c.1.eval (multiplicationPoint ⟨1, by decide⟩) +
          alpha ^ 2 * triple.c.1.eval
            (multiplicationPoint ⟨2, by decide⟩) = _
      rw [hc, hc, hc]
      simp [productionDummyView, rowC, paddedMultiplications]
      ring

/-- Exact semantic interface exported by the production shifted circuit.
`linear_accepted` is the ordinary circuit-satisfaction fact: after appending
the six dummy values, the combined linear claim equals the verifier's target.
Rust's `combine_linear_constraints` target contains both public constants and
the three published Hadamard claims, so both dependencies are explicit here.
The dummy-coin equivalence preserves the latter exactly.  Separate modules
prove this fact for the honest and ROM-simulated shifted executions. -/
structure Semantics (shape : BatchShape) (W Public : Type*)
    (statement : W → Public) (multiplicationAlpha : GhashField) where
  multiplicationSecret : W → GhashField × GhashField × GhashField
  triple : W → DummyCoins → ValidTriple
  triple_a_rows : ∀ witness dummy index,
    (triple witness dummy).a.1.eval (multiplicationPoint index) =
      rowA (multiplicationSecret witness) dummy index
  triple_b_rows : ∀ witness dummy index,
    (triple witness dummy).b.1.eval (multiplicationPoint index) =
      rowB (multiplicationSecret witness) dummy index
  triple_c_rows : ∀ witness dummy index,
    (triple witness dummy).c.1.eval (multiplicationPoint index) =
      rowC (multiplicationSecret witness) dummy index
  linearFunctional :
    (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField] GhashField
  linearMessage : W → DummyCoins → Fin 1 →
    Fin (linearLogicalLength shape) → GhashField
  publicLinearTarget :
    Public → (GhashField × GhashField × GhashField) → GhashField
  linear_accepted : ∀ witness dummy column,
    linearFunctional (linearMessage witness dummy column) =
      publicLinearTarget (statement witness)
        (visibleClaims multiplicationAlpha multiplicationSecret witness dummy)
  gammaFunctional :
    (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField

/-- Construct the full production VEIL layer spec.  No caller-provided
Hadamard or linear-kernel lemma remains. -/
noncomputable def toLayerSpec {shape : BatchShape} {W Public : Type*}
    {statement : W → Public} (multiplicationAlpha : GhashField)
    (semantics : Semantics shape W Public statement multiplicationAlpha)
    (linearPositions : Fin veilQueryCount → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : Fin veilQueryCount → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearRho hadamardRho productCoefficient : GhashField)
    (hmultiplicationAlpha : multiplicationAlpha ≠ 0)
    (hmultiplicationPlus : 1 + multiplicationAlpha ≠ 0)
    (hlinearRho : linearRho ≠ 0)
    (hhadamardRho : hadamardRho ≠ 0)
    (hproductCoefficient : productCoefficient ≠ 0) :
    Spec shape W Public where
  statement := statement
  linearPositions := linearPositions
  linearPositions_injective := hlinearPositions
  hadamardPositions := hadamardPositions
  hadamardPositions_injective := hhadamardPositions
  multiplicationAlpha := multiplicationAlpha
  linearRho := linearRho
  hadamardRho := hadamardRho
  productCoefficient := productCoefficient
  multiplicationAlpha_ne_zero := hmultiplicationAlpha
  multiplicationAlpha_plus_ne_zero := hmultiplicationPlus
  linearRho_ne_zero := hlinearRho
  hadamardRho_ne_zero := hhadamardRho
  productCoefficient_ne_zero := hproductCoefficient
  multiplicationSecret := semantics.multiplicationSecret
  linearFunctional := semantics.linearFunctional
  linearMessage := semantics.linearMessage
  hadamardFunctional := multiplicationFunctional multiplicationAlpha
  triple := semantics.triple
  gammaFunctional := semantics.gammaFunctional
  triple_claims witness dummy := by
    exact triple_claims_of_rows multiplicationAlpha
      (semantics.multiplicationSecret witness) dummy
      (semantics.triple witness dummy)
      (semantics.triple_a_rows witness dummy)
      (semantics.triple_b_rows witness dummy)
      (semantics.triple_c_rows witness dummy)
  linear_public left right hpublic dummy := by
    dsimp only
    let rightDummy := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus
      semantics.multiplicationSecret left right dummy
    have hclaims := visibleClaims_claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus
      semantics.multiplicationSecret left right dummy
    intro column
    rw [map_sub, semantics.linear_accepted, semantics.linear_accepted,
      hpublic, hclaims, sub_self]

@[simp]
theorem toLayerSpec_statement {shape : BatchShape} {W Public : Type*}
    {statement : W → Public} (multiplicationAlpha : GhashField)
    (semantics : Semantics shape W Public statement multiplicationAlpha)
    (linearPositions : Fin veilQueryCount → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : Fin veilQueryCount → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearRho hadamardRho productCoefficient : GhashField)
    (hmultiplicationAlpha : multiplicationAlpha ≠ 0)
    (hmultiplicationPlus : 1 + multiplicationAlpha ≠ 0)
    (hlinearRho : linearRho ≠ 0)
    (hhadamardRho : hadamardRho ≠ 0)
    (hproductCoefficient : productCoefficient ≠ 0) :
    (toLayerSpec multiplicationAlpha semantics linearPositions hlinearPositions
      hadamardPositions hhadamardPositions linearRho hadamardRho
      productCoefficient hmultiplicationAlpha hmultiplicationPlus hlinearRho
      hhadamardRho hproductCoefficient).statement = statement := rfl

end VeiledFlock.ProductionConstraintCompiler

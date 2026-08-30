import VeiledFlock.Production.Algebra.CorrelatedLayerSpec
import VeiledFlock.Production.Algebra.LinearBatch

/-!
# Corrected production constraint compiler

This derives the complete correlated VEIL specification from satisfaction of
the literal 263 affine rows.  The one multiplication validity fact is the
shifted zerocheck gate; the remaining rows are batched exactly in Rust order.
-/

namespace VeiledFlock.ProductionCorrelatedConstraintCompiler

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionCorrelatedLayerSpec
open VeiledFlock.ProductionLinearBatch
open VeiledFlock.ProductionMultiplicationPadding

structure Execution (shape : BatchShape) (W Public : Type*)
    (statement : W → Public) (multiplicationAlpha : GhashField) where
  multiplicationSecret : W →
    GhashField × GhashField × GhashField
  multiplicationValid : ∀ witness,
    (multiplicationSecret witness).1 *
        (multiplicationSecret witness).2.1 =
      (multiplicationSecret witness).2.2
  linearRows : Fin combinedLinearConstraints →
    (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField] GhashField
  rowConstants : Public → (GhashField × GhashField × GhashField) →
    Fin combinedLinearConstraints → GhashField
  linearMessage : W → (GhashField × GhashField × GhashField) →
    Fin (linearLogicalLength shape) → GhashField
  rows_satisfied : ∀ witness dummy row,
    linearRows row (linearMessage witness dummy) +
      rowConstants (statement witness)
        (visibleClaims multiplicationAlpha multiplicationSecret witness dummy)
        row = 0
  constraintRlc : GhashField
  gammaFunctional :
    (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField

noncomputable def toSpec {shape : BatchShape} {W Public : Type*}
    {statement : W → Public} (multiplicationAlpha : GhashField)
    (execution : Execution shape W Public statement multiplicationAlpha)
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
  multiplicationSecret := execution.multiplicationSecret
  multiplicationValid := execution.multiplicationValid
  linearFunctional :=
    combinedFunctional execution.linearRows execution.constraintRlc
  linearMessage := fun witness dummy _ =>
    execution.linearMessage witness dummy
  gammaFunctional := execution.gammaFunctional
  linear_public left right hpublic dummy := by
    dsimp only
    let rightDummy := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus execution.multiplicationSecret
      left right dummy
    have hclaims := visibleClaims_claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus execution.multiplicationSecret
      left right dummy
    intro column
    rw [map_sub]
    have hleft := combinedFunctional_eq_target execution.linearRows
      (execution.rowConstants (statement left)
        (visibleClaims multiplicationAlpha execution.multiplicationSecret
          left dummy)) execution.constraintRlc
      (execution.linearMessage left dummy)
      (execution.rows_satisfied left dummy)
    have hright := combinedFunctional_eq_target execution.linearRows
      (execution.rowConstants (statement right)
        (visibleClaims multiplicationAlpha execution.multiplicationSecret
          right rightDummy)) execution.constraintRlc
      (execution.linearMessage right rightDummy)
      (execution.rows_satisfied right rightDummy)
    rw [hleft, hright, ← hpublic, ← hclaims, sub_self]

@[simp]
theorem toSpec_statement {shape : BatchShape} {W Public : Type*}
    {statement : W → Public} (multiplicationAlpha : GhashField)
    (execution : Execution shape W Public statement multiplicationAlpha)
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
    (toSpec multiplicationAlpha execution linearPositions hlinearPositions
      hadamardPositions hhadamardPositions linearRho hadamardRho
      productCoefficient hmultiplicationAlpha hmultiplicationPlus hlinearRho
      hhadamardRho hproductCoefficient).statement = statement := rfl

end VeiledFlock.ProductionCorrelatedConstraintCompiler

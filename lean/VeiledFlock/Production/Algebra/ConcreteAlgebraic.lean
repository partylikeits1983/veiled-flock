import VeiledFlock.Production.Algebra.ConcreteOuter
import VeiledFlock.Production.Algebra.CorrelatedConstraintCompiler
import VeiledFlock.Production.Algebra.ShiftedRows

/-!
# Fully instantiated production algebraic composition

This module joins the exact outer `[mask || witness]` code domain with the
exact three-row VEIL constraint compiler.  The resulting theorem has no
abstract padding equivalence, packed-direct kernel, Hadamard-claim identity,
or linear-kernel premise.  Its context consists only of values emitted by the
Fiat--Shamir/rejection samplers and the accepted shifted-circuit semantics.
-/

namespace VeiledFlock.ProductionConcreteAlgebraic

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionCorrelatedConstraintCompiler
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionShiftedRows

variable {K Direct PublicCoord W Rest : Type*}
variable {rounds : ℕ}
variable [Fintype PublicCoord]

abbrev Public (_shape : BatchShape) := PublicCoord → GhashField

/-- One accepted, nondegenerate production VEIL compiler context selected by
the already-visible transcript and auxiliary tape. -/
structure LayerContext (shape : BatchShape) (W Public : Type*)
    (statement : W → Public) where
  multiplicationAlpha : GhashField
  execution : ProductionShiftedRows.Execution shape W
  linearPositions : Fin veilQueryCount → Fin linearCodeLength
  linearPositions_injective : Injective linearPositions
  hadamardPositions : Fin veilQueryCount → Fin hadamardCodeLength
  hadamardPositions_injective : Injective hadamardPositions
  linearRho : GhashField
  hadamardRho : GhashField
  productCoefficient : GhashField
  multiplicationAlpha_ne_zero : multiplicationAlpha ≠ 0
  multiplicationAlpha_plus_ne_zero : 1 + multiplicationAlpha ≠ 0
  linearRho_ne_zero : linearRho ≠ 0
  hadamardRho_ne_zero : hadamardRho ≠ 0
  productCoefficient_ne_zero : productCoefficient ≠ 0

noncomputable def layerSpec {shape : BatchShape} {W Public : Type*}
    {statement : W → Public}
    (context : LayerContext shape W Public statement) :
    VeiledFlock.ProductionCorrelatedLayerSpec.Spec shape W Public :=
  toSpec context.multiplicationAlpha
    (ProductionShiftedCompiler.toExecution shape context.multiplicationAlpha
      (ProductionShiftedRows.toShiftedExecution shape context.execution)
      statement)
    context.linearPositions context.linearPositions_injective
    context.hadamardPositions context.hadamardPositions_injective
    context.linearRho context.hadamardRho
    context.productCoefficient context.multiplicationAlpha_ne_zero
    context.multiplicationAlpha_plus_ne_zero context.linearRho_ne_zero
    context.hadamardRho_ne_zero context.productCoefficient_ne_zero

@[simp]
theorem layerSpec_statement {shape : BatchShape} {W Public : Type*}
    {statement : W → Public}
    (context : LayerContext shape W Public statement) :
    (layerSpec context).statement = statement := rfl

/-- Exact complete algebraic witness independence for every registered shape.
All FLOCK masks, the outer message mask, the full PCS blinder, raw L0 message
and blinder rows, public-direct blinder evaluations, both VEIL commitments,
dummy multiplication rows, and the product-code mask are transported by one
bijection on the honest coin space. -/
theorem witness_independent
    [Fintype K] [Fintype (K → GhashField)]
    [Fintype Rest] [Nonempty Rest]
    (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Injective (positions rest))
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := BaseScalarIndex shape) (Pad := ActivePadding shape) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord →
      ResidualDataIndex shape × LaneIndex)
    (weights : Prefix (K := K) (rounds := rounds) → Rest → Direct →
      PublicCoord → GhashField)
    (context : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Direct)
        (Opened := OpenedRows shape) → Rest →
      LayerContext shape W (Public shape)
        (publicStatement shape publicPositions baseMessage))
    {left right : W}
    (hpublic : publicStatement shape publicPositions baseMessage left =
      publicStatement shape publicPositions baseMessage right) :
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
        (K := K) (I := BaseScalarIndex shape)
        (Pad := ActivePadding shape) (Rest := Rest)
        (rounds := rounds) shape)).map
      (VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret challenge
        (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
        (fun rest => baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions weights)
        (fun history outer rest => layerSpec (context history outer rest))
        left) =
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
        (K := K) (I := BaseScalarIndex shape)
        (Pad := ActivePadding shape) (Rest := Rest)
        (rounds := rounds) shape)).map
      (VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret challenge
        (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
        (fun rest => baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions weights)
        (fun history outer rest => layerSpec (context history outer rest))
        right) := by
  apply VeiledFlock.ProductionConcreteOuter.witness_independent
    shape positions hpositions secret challenge hchallenge baseMessage
    publicPositions weights
    (fun history outer rest => layerSpec (context history outer rest))
    (fun _ _ _ => layerSpec_statement _) hpublic

end VeiledFlock.ProductionConcreteAlgebraic

import VeiledFlock.Production.Algebra.PaddedAlgebraicE2E
import VeiledFlock.Algebra.PublicProjection

/-!
# Concrete outer-domain specialization

This module removes the abstract padding/opening hypotheses from the corrected
FLOCK--outer-PCS--VEIL composition theorem.  For every registered batch shape,
the hidden message is the literal split pre-NTT `[mask || witness]` word, the
opening is the complete Secure-profile L0 row set, and the padding-to-opening
map is the proved production additive-Reed--Solomon equivalence.

It also discharges the packed-direct kernel condition for arbitrary linear
functionals supported on public data coordinates.  Active and residual low
mask coordinates therefore cannot affect a packed-direct public claim.
-/

namespace VeiledFlock.ProductionConcreteOuter

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCorrelatedLayerSpec
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.PublicProjection

variable {K Direct PublicCoord W Public Rest : Type*}
variable {rounds : ℕ}
variable [Fintype PublicCoord]

/-- Embed a public coordinate in the residual-data summand of the literal
split base message.  In production these are witness/digest coordinates, never
active low-mask coordinates. -/
def publicDataPosition (shape : BatchShape)
    (positions : PublicCoord → ResidualDataIndex shape × LaneIndex) :
    PublicCoord → BaseScalarIndex shape :=
  fun index => (Sum.inl (positions index).1, (positions index).2)

/-- The public statement exposed by the packed-direct adapter: exactly the
values at its public-support coordinates. -/
def publicStatement (shape : BatchShape)
    (positions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (baseMessage : W → BaseWord shape) : W → PublicCoord → GhashField :=
  fun witness => projection (publicDataPosition shape positions)
    (baseMessage witness)

/-- The production family of public packed-direct functionals.  Fiat--Shamir
may choose different public weights for each direct claim, history, and rest
fiber, but support remains confined to the public data coordinates. -/
noncomputable def publicDirectFunctional (shape : BatchShape)
    (positions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : Prefix (K := K) (rounds := rounds) → Rest → Direct →
      PublicCoord → GhashField) :
    Prefix (K := K) (rounds := rounds) → Rest → Direct →
      BaseWord shape →ₗ[GhashField] GhashField :=
  fun history rest direct =>
    weightedFunctional (publicDataPosition shape positions)
      (weights history rest direct)

@[simp]
theorem projection_fullMessage (shape : BatchShape)
    (positions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (baseMessage : W → BaseWord shape) (witness : W)
    (rest : Rest) (padding : ActivePadding shape) :
    projection (publicDataPosition shape positions)
        (VeiledFlock.ProductionOuterPaddedPcs.fullMessage
          (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
          rest witness padding) =
      projection (publicDataPosition shape positions) (baseMessage witness) := by
  funext index
  simp [projection, publicDataPosition,
    VeiledFlock.ProductionOuterPaddedPcs.fullMessage]

/-- Equal public statements imply the exact kernel condition needed to keep
all public-direct evaluations of the translated PCS blinder unchanged. -/
theorem publicDirect_kernel (shape : BatchShape)
    (positions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (baseMessage : W → BaseWord shape)
    (weights : Prefix (K := K) (rounds := rounds) → Rest → Direct →
      PublicCoord → GhashField)
    (history : Prefix (K := K) (rounds := rounds)) (rest : Rest)
    (direct : Direct) (left right : W)
    (leftPadding rightPadding : ActivePadding shape)
    (hpublic : publicStatement shape positions baseMessage left =
      publicStatement shape positions baseMessage right) :
    publicDirectFunctional shape positions weights history rest direct
        (VeiledFlock.ProductionOuterPaddedPcs.fullMessage
            (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
            rest right rightPadding -
      VeiledFlock.ProductionOuterPaddedPcs.fullMessage
            (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
            rest left leftPadding) = 0 := by
  apply weightedFunctional_sub_eq_zero
  rw [projection_fullMessage, projection_fullMessage]
  exact hpublic

/-- Concrete padding/opening compatibility.  This is the load-bearing bridge
from the generic coin bijection to the literal production NTT and L0 rows. -/
theorem opening_paddingEmbed (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Injective (positions rest))
    (rest : Rest) (padding : ActivePadding shape) :
    baseOpening shape (positions rest) (basePaddingEmbed shape padding) =
      outerPaddingQueryEquiv shape (positions rest) (hpositions rest)
        padding :=
  baseOpening_paddingEmbed shape (positions rest) (hpositions rest) padding

/-- Corrected complete algebraic witness-independence theorem with all outer
code-domain types and the packed-direct kernel instantiated concretely.  The
remaining `Spec` argument describes the shifted VEIL verifier circuit and is
constructed in the subsequent production-circuit module. -/
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
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Direct)
        (Opened := OpenedRows shape) →
      Rest → Spec shape W (PublicCoord → GhashField))
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement =
        publicStatement shape publicPositions baseMessage)
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
        layerSpec left) =
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
        (K := K) (I := BaseScalarIndex shape)
        (Pad := ActivePadding shape) (Rest := Rest)
        (rounds := rounds) shape)).map
      (VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret challenge
        (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
        (fun rest => baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions weights)
        layerSpec right) := by
  apply VeiledFlock.ProductionPaddedAlgebraicE2E.witness_independent
    shape secret challenge hchallenge (fun _ => baseMessage)
    (fun _ => basePaddingEmbed shape)
    (fun rest => baseOpening shape (positions rest))
    (fun rest => outerPaddingQueryEquiv shape (positions rest)
      (hpositions rest))
    (opening_paddingEmbed shape positions hpositions)
    (publicDirectFunctional shape publicPositions weights)
    (publicStatement shape publicPositions baseMessage)
    (publicDirect_kernel shape publicPositions baseMessage weights)
    layerSpec hspecStatement hpublic

end VeiledFlock.ProductionConcreteOuter

import VeiledFlock.Production.Algebra.ConcreteAlgebraic
import VeiledFlock.Production.Core.QuerySchedule
import VeiledFlock.Oracle.ProtectedAdaptiveStateMachine

/-!
# Production public simulator preserving prior adversary queries

This is the strengthened end-to-end exact hybrid.  The algebraic translation
is the corrected production outer-PCS/FLOCK/correlated-VEIL bijection.  The
oracle translation includes every earlier adversary query in both point
families, so its answers are fixed pointwise on the no-prequery good event.
-/

namespace VeiledFlock.ProductionProtectedSimulator

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionQuerySchedule

variable {K Direct PublicCoord W Rest Prior FullView Outcome : Type*}
variable {rounds : ℕ}
variable [Fintype K] [DecidableEq K] [Fintype (K → GhashField)]
variable [Fintype PublicCoord]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Finite Prior]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Exact public-only simulator preserving the complete earlier classical
adversary oracle view.  Freshness is expressed as disjointness of its unique
prior-query set from both realized protocol traces. -/
theorem publicSimulator_withPrior_exact
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
    (representative : Public shape → W)
    (hrepresentative : ∀ publicInput,
      publicStatement shape publicPositions baseMessage
        (representative publicInput) = publicInput)
    (witness : W) (sites maxPointLength : ℕ)
    (realLogical simulatedLogical :
      VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := BaseScalarIndex shape)
          (Pad := ActivePadding shape) (Rest := Rest)
          (rounds := rounds) shape →
        Schedule (Point := ProductionQuery) (Outcome := Outcome))
    (hrealBound : ∀ coins oracleRounds history,
      (encodeProductionQuery
        (realLogical coins oracleRounds history)).length ≤ maxPointLength)
    (hsimulatedBound : ∀ coins oracleRounds history,
      (encodeProductionQuery
        (simulatedLogical coins oracleRounds history)).length ≤
          maxPointLength)
    (hrealLogical : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (realLogical coins) answers))
    (hsimulatedLogical : ∀ coins
      (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (simulatedLogical coins) answers))
    (priorPoints : Prior → BoundedBytes maxPointLength)
    (hprior : Injective priorPoints)
    (hrealFresh : ∀ coins (answers : History (Outcome := Outcome) sites)
      prior site,
      priorPoints prior ≠
        tracePoint (boundedSchedule maxPointLength (realLogical coins)
          (hrealBound coins)) answers site)
    (hsimulatedFresh : ∀ coins
      (answers : History (Outcome := Outcome) sites) prior site,
      priorPoints prior ≠
        tracePoint (boundedSchedule maxPointLength (simulatedLogical coins)
          (hsimulatedBound coins)) answers site)
    (continueWith :
      VeiledFlock.ProductionPaddedAlgebraicE2E.View
          (K := K) (I := BaseScalarIndex shape) (P := Direct)
          (Opened := OpenedRows shape) (Rest := Rest)
          (rounds := rounds) shape →
        (Prior → Outcome) →
        History (Outcome := Outcome) sites → FullView) :
    let statement := publicStatement shape publicPositions baseMessage
    let simulatedWitness := representative (statement witness)
    let layer := fun history outer rest =>
      ProductionConcreteAlgebraic.layerSpec (context history outer rest)
    let realState := VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret
      challenge (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
      (fun rest => baseOpening shape (positions rest))
      (publicDirectFunctional shape publicPositions weights)
      layer witness
    let simulatedState :=
      VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret challenge
        (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
        (fun rest => baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions weights)
        layer simulatedWitness
    let realSchedule := fun coins => boundedSchedule maxPointLength
      (realLogical coins) (hrealBound coins)
    let simulatedSchedule := fun coins => boundedSchedule maxPointLength
      (simulatedLogical coins) (hsimulatedBound coins)
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := BaseScalarIndex shape)
          (Pad := ActivePadding shape) (Rest := Rest)
          (rounds := rounds) shape ×
        VeiledFlock.ProtectedAdaptiveOracle.RandomOracle
          (Point := BoundedBytes maxPointLength)
          (Outcome := Outcome))).map
      (VeiledFlock.ProtectedAdaptiveStateMachine.machine realState
        (fun _ => priorPoints) realSchedule continueWith) =
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := BaseScalarIndex shape)
          (Pad := ActivePadding shape) (Rest := Rest)
          (rounds := rounds) shape ×
        VeiledFlock.ProtectedAdaptiveOracle.RandomOracle
          (Point := BoundedBytes maxPointLength)
          (Outcome := Outcome))).map
      (VeiledFlock.ProtectedAdaptiveStateMachine.machine simulatedState
        (fun _ => priorPoints) simulatedSchedule continueWith) := by
  classical
  dsimp only
  let simulatedWitness := representative
    (publicStatement shape publicPositions baseMessage witness)
  let layer := fun history outer rest =>
    ProductionConcreteAlgebraic.layerSpec (context history outer rest)
  let stateEquiv :=
    VeiledFlock.ProductionPaddedAlgebraicE2E.coinEquiv shape secret challenge
      hchallenge (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
      (fun rest => baseOpening shape (positions rest))
      (fun rest => outerPaddingQueryEquiv shape (positions rest)
        (hpositions rest))
      (opening_paddingEmbed shape positions hpositions)
      (publicDirectFunctional shape publicPositions weights)
      layer witness simulatedWitness
  apply VeiledFlock.ProtectedAdaptiveStateMachine.simulator_exact
    (stateEquiv := stateEquiv)
  · intro coins
    exact VeiledFlock.ProductionPaddedAlgebraicE2E.view_coinEquiv shape
      secret challenge hchallenge (fun _ => baseMessage)
      (fun _ => basePaddingEmbed shape)
      (fun rest => baseOpening shape (positions rest))
      (fun rest => outerPaddingQueryEquiv shape (positions rest)
        (hpositions rest))
      (opening_paddingEmbed shape positions hpositions)
      (publicDirectFunctional shape publicPositions weights)
      (publicStatement shape publicPositions baseMessage)
      (publicDirect_kernel shape publicPositions baseMessage weights)
      layer (fun _ _ _ => ProductionConcreteAlgebraic.layerSpec_statement _)
      witness simulatedWitness
      (by
        exact (hrepresentative
          (publicStatement shape publicPositions baseMessage witness)).symm)
      coins
  · intro _ _
    rfl
  · intro coins answers
    exact VeiledFlock.ProtectedAdaptiveOracle.points_injective priorPoints
      (boundedSchedule maxPointLength (realLogical coins) (hrealBound coins))
      answers hprior
      (tracePoints_boundedSchedule_injective (realLogical coins)
        (hrealBound coins) answers (hrealLogical coins answers))
      (hrealFresh coins answers)
  · intro coins answers
    exact VeiledFlock.ProtectedAdaptiveOracle.points_injective priorPoints
      (boundedSchedule maxPointLength
        (simulatedLogical (stateEquiv coins))
        (hsimulatedBound (stateEquiv coins)))
      answers hprior
      (tracePoints_boundedSchedule_injective
        (simulatedLogical (stateEquiv coins))
        (hsimulatedBound (stateEquiv coins)) answers
        (hsimulatedLogical (stateEquiv coins) answers))
      (hsimulatedFresh (stateEquiv coins) answers)

end VeiledFlock.ProductionProtectedSimulator

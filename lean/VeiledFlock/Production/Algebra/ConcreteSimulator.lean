import VeiledFlock.Production.Algebra.ConcreteAlgebraic
import VeiledFlock.Production.Algebra.PaddedAlgebraicTrace

/-!
# Public simulator for the corrected production protocol

This is the public-input corollary of the corrected algebraic and adaptive
oracle-trace theorems.  The simulator runs the same finite state machine using
an arbitrary canonical representative of the public statement.  It therefore
has no access to the honest witness.  Its hidden-query oracle table is
retargeted by the proved adaptive trace equivalence.
-/

namespace VeiledFlock.ProductionConcreteSimulator

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

variable {K Direct PublicCoord W Rest FullView Outcome : Type*}
variable {rounds : ℕ}
variable [Fintype K] [DecidableEq K] [Fintype (K → GhashField)]
variable [Fintype PublicCoord]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Exact public simulator through the complete injective, byte-framed
production oracle trace.  `representative` depends only on the public R1CS
statement. -/
theorem publicSimulator_exact
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
    (continueWith :
      VeiledFlock.ProductionPaddedAlgebraicE2E.View
          (K := K) (I := BaseScalarIndex shape) (P := Direct)
          (Opened := OpenedRows shape) (Rest := Rest)
          (rounds := rounds) shape →
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
        Oracle (Point := BoundedBytes maxPointLength)
          (Outcome := Outcome))).map
      (VeiledFlock.AdaptiveTraceStateMachine.machine realState realSchedule
        continueWith) =
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := BaseScalarIndex shape)
          (Pad := ActivePadding shape) (Rest := Rest)
          (rounds := rounds) shape ×
        Oracle (Point := BoundedBytes maxPointLength)
          (Outcome := Outcome))).map
      (VeiledFlock.AdaptiveTraceStateMachine.machine simulatedState
        simulatedSchedule continueWith) := by
  dsimp only
  apply VeiledFlock.ProductionPaddedAlgebraicTrace.encoded_simulator_exact
    shape secret challenge hchallenge
    (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
    (fun rest => baseOpening shape (positions rest))
    (fun rest => outerPaddingQueryEquiv shape (positions rest)
      (hpositions rest))
    (opening_paddingEmbed shape positions hpositions)
    (publicDirectFunctional shape publicPositions weights)
    (publicStatement shape publicPositions baseMessage)
    (publicDirect_kernel shape publicPositions baseMessage weights)
    (fun history outer rest =>
      ProductionConcreteAlgebraic.layerSpec (context history outer rest))
    (fun _ _ _ => ProductionConcreteAlgebraic.layerSpec_statement _)
    witness
    (representative
      (publicStatement shape publicPositions baseMessage witness))
    (by
      exact (hrepresentative
        (publicStatement shape publicPositions baseMessage witness)).symm)
    sites maxPointLength realLogical simulatedLogical hrealBound
    hsimulatedBound hrealLogical hsimulatedLogical continueWith

end VeiledFlock.ProductionConcreteSimulator

import VeiledFlock.Oracle.InterleavedFiatShamir
import VeiledFlock.Production.Algebra.ConcreteAlgebraic
import VeiledFlock.Production.Core.QuerySchedule

/-!
# Production algebraic simulator interleaved with Fiat--Shamir

This is the production public-input instantiation of the joint theorem.  The
FLOCK challenge function is indexed by the exact random-oracle answer vector,
and that same vector selects the algebraic masking bijection.  Consequently
the algebraic transcript and the adaptively programmed oracle trace are no
longer separate, unconstrained views.
-/

namespace VeiledFlock.ProductionInterleavedSimulator

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

omit [DecidableEq Outcome] in
omit [Fintype K] [DecidableEq K] [DecidableEq Rest] in
/-- Exact public-only simulator with the production algebraic coin
translation selected by the oracle answers that the execution actually sees.
The protected family represents the complete earlier classical adversary
oracle view. -/
theorem publicSimulator_interleaved_exact
    (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Injective (positions rest))
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := BaseScalarIndex shape) (Pad := ActivePadding shape) (W := W)))
    (sites : ℕ)
    (challenge : History (Outcome := Outcome) sites →
      Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ answers history rest,
      challenge answers history rest ≠ 0)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord →
      ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := Outcome) sites →
      Prefix (K := K) (rounds := rounds) → Rest → Direct →
      PublicCoord → GhashField)
    (context : History (Outcome := Outcome) sites →
      Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Direct)
        (Opened := OpenedRows shape) → Rest →
      LayerContext shape W (Public shape)
        (publicStatement shape publicPositions baseMessage))
    (representative : Public shape → W)
    (hrepresentative : ∀ publicInput,
      publicStatement shape publicPositions baseMessage
        (representative publicInput) = publicInput)
    (witness : W) (maxPointLength : ℕ)
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
    let layer := fun answers history outer rest =>
      ProductionConcreteAlgebraic.layerSpec
        (context answers history outer rest)
    let realState := fun coins answers =>
      VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret
        (challenge answers) (fun _ => baseMessage)
        (fun _ => basePaddingEmbed shape)
        (fun rest => baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions (weights answers))
        (layer answers) witness coins
    let simulatedState := fun coins answers =>
      VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret
        (challenge answers) (fun _ => baseMessage)
        (fun _ => basePaddingEmbed shape)
        (fun rest => baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions (weights answers))
        (layer answers) simulatedWitness coins
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
      (VeiledFlock.InterleavedFiatShamir.machine realState priorPoints
        realSchedule continueWith) =
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := BaseScalarIndex shape)
          (Pad := ActivePadding shape) (Rest := Rest)
          (rounds := rounds) shape ×
        VeiledFlock.ProtectedAdaptiveOracle.RandomOracle
          (Point := BoundedBytes maxPointLength)
          (Outcome := Outcome))).map
      (VeiledFlock.InterleavedFiatShamir.machine simulatedState priorPoints
        simulatedSchedule continueWith) := by
  classical
  dsimp only
  let simulatedWitness := representative
    (publicStatement shape publicPositions baseMessage witness)
  let layer := fun answers history outer rest =>
    ProductionConcreteAlgebraic.layerSpec
      (context answers history outer rest)
  let answerEquiv := fun answers =>
    VeiledFlock.ProductionPaddedAlgebraicE2E.coinEquiv shape secret
      (challenge answers) (hchallenge answers)
      (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
      (fun rest => baseOpening shape (positions rest))
      (fun rest => outerPaddingQueryEquiv shape (positions rest)
        (hpositions rest))
      (opening_paddingEmbed shape positions hpositions)
      (publicDirectFunctional shape publicPositions (weights answers))
      (layer answers) witness simulatedWitness
  apply VeiledFlock.InterleavedFiatShamir.simulator_exact
    (answerEquiv := answerEquiv)
  · intro coins answers
    exact VeiledFlock.ProductionPaddedAlgebraicE2E.view_coinEquiv shape
      secret (challenge answers) (hchallenge answers)
      (fun _ => baseMessage) (fun _ => basePaddingEmbed shape)
      (fun rest => baseOpening shape (positions rest))
      (fun rest => outerPaddingQueryEquiv shape (positions rest)
        (hpositions rest))
      (opening_paddingEmbed shape positions hpositions)
      (publicDirectFunctional shape publicPositions (weights answers))
      (publicStatement shape publicPositions baseMessage)
      (publicDirect_kernel shape publicPositions baseMessage (weights answers))
      (layer answers)
      (fun _ _ _ => ProductionConcreteAlgebraic.layerSpec_statement _)
      witness simulatedWitness
      (by
        exact (hrepresentative
          (publicStatement shape publicPositions baseMessage witness)).symm)
      coins
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
        (simulatedLogical (answerEquiv answers coins))
        (hsimulatedBound (answerEquiv answers coins)))
      answers hprior
      (tracePoints_boundedSchedule_injective
        (simulatedLogical (answerEquiv answers coins))
        (hsimulatedBound (answerEquiv answers coins)) answers
        (hsimulatedLogical (answerEquiv answers coins) answers))
      (hsimulatedFresh (answerEquiv answers coins) answers)

end VeiledFlock.ProductionInterleavedSimulator

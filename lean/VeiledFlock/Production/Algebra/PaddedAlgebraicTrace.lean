import VeiledFlock.Oracle.AdaptiveTraceStateMachine
import VeiledFlock.Production.Algebra.PaddedAlgebraicE2E
import VeiledFlock.Production.Core.QuerySchedule

/-!
# Corrected algebraic state through the production oracle trace

The joint outer-message/PCS/FLOCK/VEIL coin bijection is composed here with
an arbitrary finite causal random-oracle trace.  Honest and simulated hidden
query points may differ.  Trace injectivity permits an exact oracle-table
retargeting which preserves every oracle answer and the complete corrected
algebraic view.
-/

namespace VeiledFlock.ProductionPaddedAlgebraicTrace

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.AdaptiveTraceStateMachine
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.ProductionCorrelatedLayerSpec
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionQuerySchedule

variable {K I P Pad Opened W Public Rest FullView Point Outcome : Type*}
variable {rounds : ℕ}
variable [AddCommGroup Pad] [Module GhashField Pad]
variable [AddCommGroup Opened] [Module GhashField Opened]
variable [Fintype K] [DecidableEq K] [Fintype (K → GhashField)]
variable [Fintype I] [DecidableEq I] [Fintype (I → GhashField)]
variable [Fintype Pad] [DecidableEq Pad]
variable [Fintype Opened] [DecidableEq Opened]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

omit [DecidableEq Outcome] in
omit [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] [DecidableEq Pad] [Fintype Opened] [DecidableEq Opened] [DecidableEq Rest] in
theorem simulator_exact
    (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest publicIndex left right leftPadding rightPadding,
      statement left = statement right →
        functionals history rest publicIndex
          (VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest right rightPadding -
            VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest left leftPadding) = 0)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := I) (P := P) (Opened := Opened) →
      Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    (left right : W) (hpublic : statement left = statement right)
    (sites : ℕ)
    (realSchedule simulatedSchedule :
      VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := I) (Pad := Pad) (Rest := Rest)
          (rounds := rounds) shape →
        Schedule (Point := Point) (Outcome := Outcome))
    (hreal : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (realSchedule coins) answers))
    (hsimulated : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (simulatedSchedule coins) answers))
    (continueWith :
      VeiledFlock.ProductionPaddedAlgebraicE2E.View
          (K := K) (I := I) (P := P) (Opened := Opened) (Rest := Rest)
          (rounds := rounds) shape →
        History (Outcome := Outcome) sites → FullView) :
    let leftState := VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret
      challenge baseMessage paddingEmbed opening functionals layerSpec left
    let rightState := VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret
      challenge baseMessage paddingEmbed opening functionals layerSpec right
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := I) (Pad := Pad) (Rest := Rest)
          (rounds := rounds) shape ×
        Oracle (Point := Point) (Outcome := Outcome))).map
      (machine leftState realSchedule continueWith) =
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := I) (Pad := Pad) (Rest := Rest)
          (rounds := rounds) shape ×
        Oracle (Point := Point) (Outcome := Outcome))).map
      (machine rightState simulatedSchedule continueWith) := by
  classical
  dsimp only
  apply AdaptiveTraceStateMachine.simulator_exact
    (coinEquiv := VeiledFlock.ProductionPaddedAlgebraicE2E.coinEquiv shape
      secret challenge hchallenge baseMessage paddingEmbed opening
      paddingOpening hpadding functionals layerSpec left right)
    (hleft := hreal) (hright := hsimulated)
  intro coins
  exact VeiledFlock.ProductionPaddedAlgebraicE2E.view_coinEquiv shape secret
    challenge hchallenge baseMessage paddingEmbed opening paddingOpening
    hpadding functionals statement hpublicKernel layerSpec hspecStatement
    left right hpublic coins

omit [DecidableEq Outcome] in
omit [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] [DecidableEq Pad] [Fintype Opened] [DecidableEq Opened] [DecidableEq Rest] in
/-- Byte-level specialization using the injective production query framing. -/
theorem encoded_simulator_exact
    (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest publicIndex left right leftPadding rightPadding,
      statement left = statement right →
        functionals history rest publicIndex
          (VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest right rightPadding -
            VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest left leftPadding) = 0)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := I) (P := P) (Opened := Opened) →
      Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    (left right : W) (hpublic : statement left = statement right)
    (sites maxPointLength : ℕ)
    (realLogical simulatedLogical :
      VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := I) (Pad := Pad) (Rest := Rest)
          (rounds := rounds) shape →
        Schedule (Point := ProductionQuery) (Outcome := Outcome))
    (hrealBound : ∀ coins oracleRounds history,
      (encodeProductionQuery
        (realLogical coins oracleRounds history)).length ≤ maxPointLength)
    (hsimulatedBound : ∀ coins oracleRounds history,
      (encodeProductionQuery
        (simulatedLogical coins oracleRounds history)).length ≤ maxPointLength)
    (hrealLogical : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (realLogical coins) answers))
    (hsimulatedLogical : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (simulatedLogical coins) answers))
    (continueWith :
      VeiledFlock.ProductionPaddedAlgebraicE2E.View
          (K := K) (I := I) (P := P) (Opened := Opened) (Rest := Rest)
          (rounds := rounds) shape →
        History (Outcome := Outcome) sites → FullView) :
    let leftState := VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret
      challenge baseMessage paddingEmbed opening functionals layerSpec left
    let rightState := VeiledFlock.ProductionPaddedAlgebraicE2E.view shape secret
      challenge baseMessage paddingEmbed opening functionals layerSpec right
    let realSchedule := fun coins => boundedSchedule maxPointLength
      (realLogical coins) (hrealBound coins)
    let simulatedSchedule := fun coins => boundedSchedule maxPointLength
      (simulatedLogical coins) (hsimulatedBound coins)
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := I) (Pad := Pad) (Rest := Rest)
          (rounds := rounds) shape ×
        Oracle (Point := BoundedBytes maxPointLength) (Outcome := Outcome))).map
      (machine leftState realSchedule continueWith) =
    (PMF.uniformOfFintype
      (VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
          (K := K) (I := I) (Pad := Pad) (Rest := Rest)
          (rounds := rounds) shape ×
        Oracle (Point := BoundedBytes maxPointLength) (Outcome := Outcome))).map
      (machine rightState simulatedSchedule continueWith) := by
  classical
  dsimp only
  apply simulator_exact shape secret challenge hchallenge baseMessage
    paddingEmbed opening paddingOpening hpadding functionals statement
    hpublicKernel layerSpec hspecStatement left right hpublic sites
  · intro coins answers
    exact tracePoints_boundedSchedule_injective (realLogical coins)
      (hrealBound coins) answers (hrealLogical coins answers)
  · intro coins answers
    exact tracePoints_boundedSchedule_injective (simulatedLogical coins)
      (hsimulatedBound coins) answers (hsimulatedLogical coins answers)

end VeiledFlock.ProductionPaddedAlgebraicTrace

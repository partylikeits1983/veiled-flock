import VeiledFlock.AdaptiveTraceStateMachine
import VeiledFlock.ProductionAlgebraicE2E
import VeiledFlock.ProductionQuerySchedule

/-!
# Complete algebraic state through the production oracle trace

The complete outer-PCS/FLOCK/VEIL coin translation is composed here with an
arbitrary finite causal random-oracle trace. Honest and simulated hidden query
points may differ. Injectivity of each logical trace permits an exact oracle
retargeting which preserves every answer and the complete algebraic state.
-/

namespace VeiledFlock.ProductionAlgebraicTrace

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.AdaptiveTraceStateMachine
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.ProductionAlgebraicE2E
open VeiledFlock.ProductionLayerSpec
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionQuerySchedule

variable {K I P W Public Rest FullView Point Outcome : Type*}
variable {rounds : ℕ}
variable [Fintype K] [DecidableEq K] [Fintype (K → GhashField)]
variable [Fintype I] [DecidableEq I] [Fintype (I → GhashField)]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

theorem simulator_exact
    (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest publicIndex left right,
      statement left = statement right →
        functionals history rest publicIndex
          (message rest right - message rest left) = 0)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      OuterView (I := I) (P := P) → Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    (left right : W) (hpublic : statement left = statement right)
    (sites : ℕ)
    (realSchedule simulatedSchedule :
      Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape →
        Schedule (Point := Point) (Outcome := Outcome))
    (hreal : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (realSchedule coins) answers))
    (hsimulated : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (simulatedSchedule coins) answers))
    (continueWith :
      View (K := K) (I := I) (P := P) (Rest := Rest)
          (rounds := rounds) shape →
        History (Outcome := Outcome) sites → FullView) :
    let leftState := view shape secret challenge message functionals
      layerSpec left
    let rightState := view shape secret challenge message functionals
      layerSpec right
    (PMF.uniformOfFintype
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape ×
        Oracle (Point := Point) (Outcome := Outcome))).map
          (machine leftState realSchedule continueWith) =
      (PMF.uniformOfFintype
        (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape ×
          Oracle (Point := Point) (Outcome := Outcome))).map
            (machine rightState simulatedSchedule continueWith) := by
  classical
  dsimp only
  apply AdaptiveTraceStateMachine.simulator_exact
    (coinEquiv := ProductionAlgebraicE2E.coinEquiv shape secret challenge
      hchallenge message functionals layerSpec left right)
    (hleft := hreal) (hright := hsimulated)
  intro coins
  exact ProductionAlgebraicE2E.view_coinEquiv shape secret challenge
    hchallenge message functionals statement hpublicKernel layerSpec
    hspecStatement left right hpublic coins

/-- Byte-level specialization using the exact production query encoder. The
only schedule premise left to implementation refinement is injectivity of the
typed logical query sequence; framing cannot introduce a collision. -/
theorem encoded_simulator_exact
    (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest publicIndex left right,
      statement left = statement right →
        functionals history rest publicIndex
          (message rest right - message rest left) = 0)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      OuterView (I := I) (P := P) → Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    (left right : W) (hpublic : statement left = statement right)
    (sites maxPointLength : ℕ)
    (realLogical simulatedLogical :
      Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape →
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
      View (K := K) (I := I) (P := P) (Rest := Rest)
          (rounds := rounds) shape →
        History (Outcome := Outcome) sites → FullView) :
    let leftState := view shape secret challenge message functionals
      layerSpec left
    let rightState := view shape secret challenge message functionals
      layerSpec right
    let realSchedule := fun coins => boundedSchedule maxPointLength
      (realLogical coins) (hrealBound coins)
    let simulatedSchedule := fun coins => boundedSchedule maxPointLength
      (simulatedLogical coins) (hsimulatedBound coins)
    (PMF.uniformOfFintype
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape ×
        Oracle (Point := BoundedBytes maxPointLength)
          (Outcome := Outcome))).map
          (machine leftState realSchedule continueWith) =
      (PMF.uniformOfFintype
        (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape ×
          Oracle (Point := BoundedBytes maxPointLength)
            (Outcome := Outcome))).map
            (machine rightState simulatedSchedule continueWith) := by
  classical
  dsimp only
  apply simulator_exact shape secret challenge hchallenge message functionals
    statement hpublicKernel layerSpec hspecStatement left right hpublic sites
  · intro coins answers
    exact tracePoints_boundedSchedule_injective (realLogical coins)
      (hrealBound coins) answers (hrealLogical coins answers)
  · intro coins answers
    exact tracePoints_boundedSchedule_injective (simulatedLogical coins)
      (hsimulatedBound coins) answers (hsimulatedLogical coins answers)

end VeiledFlock.ProductionAlgebraicTrace

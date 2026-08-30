import VeiledFlock.Production.Core.AdaptiveTrace
import VeiledFlock.Production.Core.QuerySchedule

/-!
# End-to-end simulator over exact production query bytes

This specializes the production algebraic/oracle theorem to the literal Rust
query encoder.  Consequently the random-oracle premise is stated only at the
logical-query level; collisions introduced by byte serialization are ruled
out by `ProductionFraming.encodeProductionQuery_injective`.
-/

namespace VeiledFlock.ProductionEncodedTrace

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.AlgebraicProtocol
open VeiledFlock.Framing
open VeiledFlock.InteractiveAlgebraic
open VeiledFlock.ProductionAlgebraic
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionProm
open VeiledFlock.ProductionQuerySchedule

variable {F K Data Padding J W Public Rest FullView Outcome : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype K] [DecidableEq K] [Fintype (K → F)]
variable [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J] [DecidableEq J]
variable [Fintype (Padding → F)] [Fintype (J → F)]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
variable {rounds : ℕ}

theorem productionEncodedTraceSimulator_exact
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (hc : ∀ history rest, c history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Injective (queries history rest))
    (hdisjoint : ∀ history rest data query,
      base history rest (Sum.inl data) ≠ queries history rest query)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (veilSecret : History (F := F) (I := K) rounds → Rest →
      W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest left right,
      statement left = statement right →
        functional history rest
          (message history rest right - message history rest left) = 0)
    (representative : Public → W)
    (hrepresentative : ∀ publicInput,
      statement (representative publicInput) = publicInput)
    (witness : W) (sites maxPointLength : ℕ)
    (realLogical simulatedLogical :
      ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
          (Rest := Rest) rounds →
        Schedule (Point := ProductionQuery) (Outcome := Outcome))
    (hrealBound : ∀ coins oracleRounds history,
      (encodeProductionQuery
        (realLogical coins oracleRounds history)).length ≤ maxPointLength)
    (hsimulatedBound : ∀ coins oracleRounds history,
      (encodeProductionQuery
        (simulatedLogical coins oracleRounds history)).length ≤ maxPointLength)
    (hrealLogical : ∀ coins (answers :
      AdaptiveOracleProgramming.History (Outcome := Outcome) sites),
      Injective (tracePoints (realLogical coins) answers))
    (hsimulatedLogical : ∀ coins (answers :
      AdaptiveOracleProgramming.History (Outcome := Outcome) sites),
      Injective (tracePoints (simulatedLogical coins) answers))
    (continueWith :
      AlgebraicState (F := F) (K := K) (Padding := Padding) (J := J)
          (Rest := Rest) rounds →
        AdaptiveOracleProgramming.History (Outcome := Outcome) sites →
          FullView) :
    let realState := productionState secret alpha c base hbase queries
      functional veilSecret querySecret message witness
    let simulatedWitness := representative (statement witness)
    let simulatedState := productionState secret alpha c base hbase queries
      functional veilSecret querySecret message simulatedWitness
    let realSchedule := fun coins => boundedSchedule maxPointLength
      (realLogical coins) (hrealBound coins)
    let simulatedSchedule := fun coins => boundedSchedule maxPointLength
      (simulatedLogical coins) (hsimulatedBound coins)
    (PMF.uniformOfFintype
      (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ×
        Oracle (Point := BoundedBytes maxPointLength)
          (Outcome := Outcome))).map
          (VeiledFlock.AdaptiveTraceStateMachine.machine realState realSchedule
            continueWith) =
      (PMF.uniformOfFintype
        (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
          (Rest := Rest) rounds ×
          Oracle (Point := BoundedBytes maxPointLength)
            (Outcome := Outcome))).map
            (VeiledFlock.AdaptiveTraceStateMachine.machine simulatedState
              simulatedSchedule continueWith) := by
  dsimp only
  apply ProductionAdaptiveTrace.productionAdaptiveTraceSimulator_exact
    secret alpha c halpha hplus hc base hbase queries hqueries hdisjoint
    functional veilSecret querySecret message statement hpublicKernel
    representative hrepresentative witness sites
  · intro coins answers
    exact tracePoints_boundedSchedule_injective (realLogical coins)
      (hrealBound coins) answers (hrealLogical coins answers)
  · intro coins answers
    exact tracePoints_boundedSchedule_injective (simulatedLogical coins)
      (hsimulatedBound coins) answers (hsimulatedLogical coins answers)

end VeiledFlock.ProductionEncodedTrace

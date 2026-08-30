import VeiledFlock.Oracle.AdaptiveTraceStateMachine
import VeiledFlock.Production.Core.Prom

/-!
# Production VEIL--FLOCK through all causal random-oracle work

This is the exact (no-bad-event) core of the end-to-end proof.  It composes
the one production FLOCK mask tape, VEIL multiplication padding, queried-code
padding, the PCS blinder, and an arbitrary finite causal trace containing the
salted Merkle and Fiat--Shamir oracle calls.  Honest and simulated hidden query
points may differ; their oracle tables are retargeted so the complete answer
transcript and visible algebraic state agree pointwise.
-/

namespace VeiledFlock.ProductionAdaptiveTrace

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.AdaptiveTraceStateMachine
open VeiledFlock.AlgebraicProtocol
open VeiledFlock.InteractiveAlgebraic
open VeiledFlock.ProductionAlgebraic
open VeiledFlock.ProductionProm

variable {F K Data Padding J W Public Rest FullView Point Outcome : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype K] [DecidableEq K] [Fintype (K → F)]
variable [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J] [DecidableEq J]
variable [Fintype (Padding → F)] [Fintype (J → F)]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
variable {rounds : ℕ}

/-- Exact public-input simulator for the full injective causal oracle trace.
The schedule arguments are where the concrete implementation enumerates
salted leaves, internal nodes, grinding, Fiat--Shamir squeezes, and all other
random-oracle calls.  The later conditional theorem charges precisely the
tapes where these families collide with external queries or each other. -/
theorem productionAdaptiveTraceSimulator_exact
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
    (witness : W) (sites : ℕ)
    (realSchedule simulatedSchedule :
      ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
        (Rest := Rest) rounds →
          Schedule (Point := Point) (Outcome := Outcome))
    (hreal : ∀ coins (answers :
        AdaptiveOracleProgramming.History (Outcome := Outcome) sites),
      Injective (tracePoints (realSchedule coins) answers))
    (hsimulated : ∀ coins (answers :
        AdaptiveOracleProgramming.History (Outcome := Outcome) sites),
      Injective (tracePoints (simulatedSchedule coins) answers))
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
    (PMF.uniformOfFintype
      (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ×
        Oracle (Point := Point) (Outcome := Outcome))).map
          (AdaptiveTraceStateMachine.machine realState realSchedule
            continueWith) =
      (PMF.uniformOfFintype
        (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
          (Rest := Rest) rounds ×
          Oracle (Point := Point) (Outcome := Outcome))).map
            (AdaptiveTraceStateMachine.machine simulatedState
              simulatedSchedule continueWith) := by
  classical
  dsimp only
  let simulatedWitness := representative (statement witness)
  let coinEquiv := jointWitnessCoinEquiv secret alpha c halpha hplus base hbase
    queries hqueries hdisjoint emptyFlockSecret veilSecret querySecret message
    witness simulatedWitness
  apply AdaptiveTraceStateMachine.simulator_exact
    (coinEquiv := coinEquiv)
    (hleft := hreal) (hright := hsimulated)
  intro coins
  apply productionState_transport secret alpha c halpha hplus hc base hbase
    queries hqueries hdisjoint functional veilSecret querySecret message
    statement hpublicKernel
  exact (hrepresentative (statement witness)).symm

end VeiledFlock.ProductionAdaptiveTrace

import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Production.Algebra.Algebraic
import VeiledFlock.Concrete.ProtocolStateMachine

/-!
# Production algebraic tape plus adaptive Fiat--Shamir programming

This module composes the production-faithful single FLOCK mask tape with the
exact adaptive programmable-random-oracle equivalence.  Unlike the older
`VeilFlockProm` theorem, there is no second, fictitious fixed FLOCK mask
channel: `Fin 0` occupies that legacy slot and the causal tape is the sole
source of the 754--760 transcript masks.
-/

namespace VeiledFlock.ProductionProm

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.AlgebraicProtocol
open VeiledFlock.InteractiveAlgebraic
open VeiledFlock.ProductionAlgebraic

variable {F K Data Padding J W Public Rest FullView Point Outcome : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype K] [Fintype (K → F)]
variable [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J]
variable [Fintype (Padding → F)] [Fintype (J → F)]
variable [Fintype Rest] [Nonempty Rest]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
variable {rounds : ℕ}

/-- State exposed after the exact algebraic reparameterization and before the
Fiat--Shamir continuation. -/
abbrev AlgebraicState (rounds : ℕ) :=
  Rest × History (F := F) (I := K) rounds ×
    ProductionAlgebraicView (F := F) (Padding := Padding) (J := J)

/-- Production algebraic execution packaged as state for the oracle machine. -/
noncomputable def productionState
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (veilSecret : History (F := F) (I := K) rounds → Rest →
      W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (witness : W)
    (coins : ProductionCoins (F := F) (K := K) (Padding := Padding)
      (J := J) (Rest := Rest) rounds) :
    AlgebraicState (F := F) (K := K) (Padding := Padding) (J := J)
      (Rest := Rest) rounds :=
  realJointView secret alpha c base hbase queries functional emptyFlockSecret
    veilSecret querySecret message
    (fun rest history view => (rest, history, view)) witness coins

/-- Pointwise production algebraic transport, packaged for composition with
the random-oracle state machine. -/
theorem productionState_transport
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
    {left right : W} (hpublic : statement left = statement right)
    (coins : ProductionCoins (F := F) (K := K) (Padding := Padding)
      (J := J) (Rest := Rest) rounds) :
    productionState secret alpha c base hbase queries functional veilSecret
        querySecret message left coins =
      productionState secret alpha c base hbase queries functional veilSecret
        querySecret message right
        (jointWitnessCoinEquiv secret alpha c halpha hplus base hbase queries
          hqueries hdisjoint emptyFlockSecret veilSecret querySecret message
          left right coins) := by
  exact realJointView_transport secret alpha c halpha hplus hc base hbase
    queries hqueries hdisjoint functional emptyFlockSecret veilSecret
    querySecret message statement hpublicKernel
    (fun rest history view => (rest, history, view)) hpublic coins

/-- Exact production algebraic+pROM simulator theorem.  The public simulator
uses a representative of the public statement; the representative need not
satisfy the private nonlinear relation because the accepting zerocheck
transcript is constructed separately by `ConcreteZerocheck`. -/
theorem productionPromSimulator_exact
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
    (schedule : AlgebraicState (F := F) (K := K) (Padding := Padding)
      (J := J) (Rest := Rest) rounds →
        Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ algebraic answers,
      Injective (tracePoints (schedule algebraic) answers))
    (continueWith : AlgebraicState (F := F) (K := K) (Padding := Padding)
      (J := J) (Rest := Rest) rounds →
        Oracle (Point := Point) (Outcome := Outcome) →
        AdaptiveOracleProgramming.History (Outcome := Outcome) sites →
          FullView) :
    let realAlgebraic := productionState secret alpha c base hbase queries
      functional veilSecret querySecret message witness
    let simulatedAlgebraic := productionState secret alpha c base hbase queries
      functional veilSecret querySecret message
        (representative (statement witness))
    (PMF.uniformOfFintype
      (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ×
        Oracle (Point := Point) (Outcome := Outcome))).map
          (ProtocolStateMachine.realMachine sites realAlgebraic schedule
            continueWith) =
      (PMF.uniformOfFintype
        (ProtocolStateMachine.SimulatorCoins (Point := Point)
          (Outcome := Outcome) sites simulatedAlgebraic schedule)).map
            (ProtocolStateMachine.simulatedMachine sites simulatedAlgebraic
              schedule hinjective continueWith) := by
  dsimp only
  let simulatedWitness := representative (statement witness)
  let coinEquiv := jointWitnessCoinEquiv secret alpha c halpha hplus base hbase
    queries hqueries hdisjoint emptyFlockSecret veilSecret querySecret message
    witness simulatedWitness
  apply ProtocolStateMachine.combinedSimulator_exact
    (algebraicCoinEquiv := coinEquiv)
    (hinjective := hinjective)
  intro coins
  apply productionState_transport secret alpha c halpha hplus hc base hbase
    queries hqueries hdisjoint functional veilSecret querySecret message
    statement hpublicKernel
  exact (hrepresentative (statement witness)).symm

section ConcreteScalarSchedule

open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.TranscriptSchedule

/-- Byte-concrete specialization using the production 32-byte oracle block,
16-byte scalar prefix, and 54-byte append-only round growth. -/
theorem productionScalarPromSimulator_exact
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
    (witness : W) (sites maxStartLength : ℕ)
    (start : AlgebraicState (F := F) (K := K) (Padding := Padding)
      (J := J) (Rest := Rest) rounds → List Byte)
    (hstart : ∀ algebraic, (start algebraic).length ≤ maxStartLength)
    (encode : F → Fin 16 → Byte)
    (first second : AlgebraicState (F := F) (K := K) (Padding := Padding)
      (J := J) (Rest := Rest) rounds → ∀ oracleRounds,
        AdaptiveOracleProgramming.History (Outcome := OracleBlock)
          (oracleRounds + 1) → F)
    (continueWith : AlgebraicState (F := F) (K := K) (Padding := Padding)
      (J := J) (Rest := Rest) rounds →
        Oracle
          (Point := BoundedBytes
            (maxPointLengthFromBound sites maxStartLength 54))
          (Outcome := OracleBlock) →
        AdaptiveOracleProgramming.History (Outcome := OracleBlock) sites →
          FullView) :
    let realAlgebraic := productionState secret alpha c base hbase queries
      functional veilSecret querySecret message witness
    let simulatedAlgebraic := productionState secret alpha c base hbase queries
      functional veilSecret querySecret message
        (representative (statement witness))
    let schedule := scalarSchedule sites maxStartLength start hstart encode
      first second
    (PMF.uniformOfFintype
      (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ×
        Oracle
          (Point := BoundedBytes
            (maxPointLengthFromBound sites maxStartLength 54))
          (Outcome := OracleBlock))).map
          (ProtocolStateMachine.realMachine sites realAlgebraic schedule
            continueWith) =
      (PMF.uniformOfFintype
        (ProtocolStateMachine.SimulatorCoins
          (Point := BoundedBytes
            (maxPointLengthFromBound sites maxStartLength 54))
          (Outcome := OracleBlock) sites simulatedAlgebraic schedule)).map
            (ProtocolStateMachine.simulatedMachine sites simulatedAlgebraic
              schedule
              (scalarSchedule_injective sites maxStartLength start hstart
                encode first second)
              continueWith) := by
  dsimp only
  exact productionPromSimulator_exact secret alpha c halpha hplus hc base
    hbase queries hqueries hdisjoint functional veilSecret querySecret message
    statement hpublicKernel representative hrepresentative witness sites
    (scalarSchedule sites maxStartLength start hstart encode first second)
    (scalarSchedule_injective sites maxStartLength start hstart encode first
      second)
    continueWith

end ConcreteScalarSchedule

end VeiledFlock.ProductionProm

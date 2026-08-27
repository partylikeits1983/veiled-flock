import VeiledFlock.AlgebraicProtocol
import VeiledFlock.ConcreteOracle
import VeiledFlock.ProtocolStateMachine

/-!
# VEIL--FLOCK algebraic simulator in the programmable random-oracle model

This is the first theorem that composes the actual four-part algebraic
VEIL--FLOCK simulator with the concrete 32-byte, append-only Fiat--Shamir
programming schedule.  An arbitrary finite auxiliary tape is carried through
unchanged; it represents public coins and honest oracle answers obtained before
the first programmed zerocheck point.  Therefore the initial programmed point
may depend on the complete prior public interaction, not just on algebraic
messages.
-/

namespace VeiledFlock.VeilFlockProm

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.AlgebraicProtocol
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.TranscriptSchedule

variable {F I Data Padding J W Aux FullView : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype I] [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J]
variable [Fintype (I → F)] [Fintype (Padding → F)] [Fintype (J → F)]
variable [Fintype Aux] [Nonempty Aux]

abbrev AlgCoins :=
  Coins (F := F) (I := I) (Padding := Padding) (J := J) × Aux

abbrev AlgView :=
  View (F := F) (I := I) (Padding := Padding) (J := J) × Aux

/-- Exact classical-pROM simulation of the joint FLOCK masks, VEIL
multiplication padding, RS query padding, PCS blinder, and every scalar
challenge programmed by the zerocheck simulator.  The deterministic
continuation may expose the complete oracle table and all remaining protocol
state, so equality covers any witness-independent post-processing. -/
theorem scalarPromSimulator_exact
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (witness : W)
    (sites maxStartLength : ℕ)
    (start : AlgView (F := F) (I := I) (Padding := Padding) (J := J)
      (Aux := Aux) → List Byte)
    (hstart : ∀ algebraic, (start algebraic).length ≤ maxStartLength)
    (encode : F → Fin 16 → Byte)
    (first second :
      AlgView (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) →
        ∀ rounds, History (Outcome := OracleBlock) (rounds + 1) → F)
    (continueWith :
      AlgView (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) →
      Oracle
        (Point := BoundedBytes
          (maxPointLengthFromBound sites maxStartLength 54))
        (Outcome := OracleBlock) →
      History (Outcome := OracleBlock) sites → FullView) :
    let realAlgebraic :
        AlgCoins (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) →
          AlgView (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) :=
      fun coins =>
        (realView alpha c base hbase queries functional flockSecret veilSecret
          querySecret message witness coins.1, coins.2)
    let simulatedAlgebraic :
        AlgCoins (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) →
          AlgView (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) :=
      fun coins =>
        (simulatedView c functional (functional (message witness)) coins.1,
          coins.2)
    let algebraicCoinEquiv :
        AlgCoins (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) ≃
          AlgCoins (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) :=
      Equiv.prodCongr
        (simulatorCoinEquiv alpha c halpha hplus hc base hbase queries hqueries
          hdisjoint (flockSecret witness) (veilSecret witness)
          (querySecret witness) (message witness))
        (Equiv.refl Aux)
    let schedule := scalarSchedule sites maxStartLength start hstart encode first second
    (PMF.uniformOfFintype
      (AlgCoins (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) ×
        Oracle
          (Point := BoundedBytes
            (maxPointLengthFromBound sites maxStartLength 54))
          (Outcome := OracleBlock))).map
        (ProtocolStateMachine.realMachine sites realAlgebraic schedule continueWith) =
      (PMF.uniformOfFintype
        (ProtocolStateMachine.SimulatorCoins
          (Point := BoundedBytes
            (maxPointLengthFromBound sites maxStartLength 54))
          (Outcome := OracleBlock) sites simulatedAlgebraic schedule)).map
        (ProtocolStateMachine.simulatedMachine sites simulatedAlgebraic schedule
          (scalarSchedule_injective sites maxStartLength start hstart encode first second)
          continueWith) := by
  dsimp only
  apply ProtocolStateMachine.combinedSimulator_exact
    (realAlgebraic := fun coins =>
      (realView alpha c base hbase queries functional flockSecret veilSecret
        querySecret message witness coins.1, coins.2))
    (simulatedAlgebraic := fun coins =>
      (simulatedView c functional (functional (message witness)) coins.1,
        coins.2))
    (algebraicCoinEquiv := Equiv.prodCongr
      (simulatorCoinEquiv alpha c halpha hplus hc base hbase queries hqueries
        hdisjoint (flockSecret witness) (veilSecret witness)
        (querySecret witness) (message witness))
      (Equiv.refl Aux))
    (schedule := scalarSchedule sites maxStartLength start hstart encode first second)
    (hinjective := scalarSchedule_injective sites maxStartLength start hstart encode first second)
  intro coins
  apply Prod.ext
  · exact realView_simulator_transport alpha c halpha hplus hc base hbase queries
      hqueries hdisjoint functional flockSecret veilSecret querySecret message
      witness coins.1
  · rfl

end VeiledFlock.VeilFlockProm

import VeiledFlock.Oracle.CoupledOperationalSimulator
import VeiledFlock.Oracle.DependentScalarPrefixSimulator

/-!
# Coupled honest execution to scalar-prefix operational simulator

This is the executable form of the causal Fiat--Shamir coupling.  It composes
the unchanged-oracle algebraic translation with the exact distributional
equivalence between whole-block programming and Rust's low-128-bit scalar
programmer.
-/

namespace VeiledFlock.CoupledScalarOperationalSimulator

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle

variable {AlgCoins State Point View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]

/-- Exact distributional identity between honest execution with a uniform
complete oracle and the adaptive scalar-prefix programmer.  The complete
reconstructed oracle is passed to `continueWith`, so the identity covers any
bounded adaptive continuation after the proof. -/
theorem trace_simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := OracleBlock) sites → State)
    (answerEquiv :
      History (Outcome := OracleBlock) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (htrace : ∀ coins answers site,
      tracePoint (rightSchedule (answerEquiv answers coins)) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hrightInjective : ∀ coins
      (answers : History (Outcome := OracleBlock) sites),
      Function.Injective (tracePoints (rightSchedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := OracleBlock) →
      History (Outcome := OracleBlock) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × Oracle (Point := Point) (Outcome := OracleBlock))).map
        (VeiledFlock.CoupledFiatShamir.machine leftState leftSchedule
          continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.DependentScalarPrefixSimulator.ScalarSimulatorCoins
          (Point := Point) sites rightSchedule)).map
        (VeiledFlock.DependentScalarPrefixSimulator.programmedMachine sites
          rightState rightSchedule hrightInjective continueWith) := by
  calc
    _ = (PMF.uniformOfFintype
        (VeiledFlock.DependentProtocolSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock) sites rightSchedule)).map
        (VeiledFlock.DependentProtocolSimulator.programmedMachine sites
          rightState rightSchedule hrightInjective continueWith) :=
      VeiledFlock.CoupledOperationalSimulator.trace_simulator_exact
        leftState rightState answerEquiv hstate leftSchedule rightSchedule
        htrace hrightInjective continueWith
    _ = _ :=
      (VeiledFlock.DependentScalarPrefixSimulator.simulator_exact sites
        rightState rightSchedule hrightInjective continueWith).symm

end VeiledFlock.CoupledScalarOperationalSimulator

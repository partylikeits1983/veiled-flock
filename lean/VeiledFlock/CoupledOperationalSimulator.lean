import VeiledFlock.CoupledFiatShamir
import VeiledFlock.DependentProtocolSimulator

/-!
# Coupled honest execution to operational programmable simulator

This composes the two exact transformations:

1. translate algebraic coins using the Fiat--Shamir answers while leaving the
   full random oracle unchanged;
2. split that unchanged oracle into desired adaptive answers and its untouched
   complement, which is the straightline programmable simulator's coin space.
-/

namespace VeiledFlock.CoupledOperationalSimulator

open VeiledFlock.AdaptiveOracleProgramming

variable {AlgCoins State Point Outcome View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Exact distributional identity between an honest Fiat--Shamir execution
and the answer-dependent adaptive programmable-oracle simulator.  The only
remaining statistical step in an external ZK game is the failure probability
for attempting to program a point already exposed before the proof. -/
theorem simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hschedule : ∀ coins answers,
      rightSchedule (answerEquiv answers coins) = leftSchedule coins)
    (hrightInjective : ∀ coins
      (answers : History (Outcome := Outcome) sites),
      Function.Injective (tracePoints (rightSchedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
        (VeiledFlock.CoupledFiatShamir.machine leftState leftSchedule
          continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.DependentProtocolSimulator.SimulatorCoins
          (Point := Point) (Outcome := Outcome) sites rightSchedule)).map
        (VeiledFlock.DependentProtocolSimulator.programmedMachine sites
          rightState rightSchedule hrightInjective continueWith) := by
  calc
    _ = (PMF.uniformOfFintype
        (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
          (VeiledFlock.CoupledFiatShamir.machine rightState rightSchedule
            continueWith) :=
      VeiledFlock.CoupledFiatShamir.simulator_exact leftState rightState
        answerEquiv hstate leftSchedule rightSchedule hschedule continueWith
    _ = (PMF.uniformOfFintype
        (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
          (VeiledFlock.DependentProtocolSimulator.oracleMachine sites
            rightState rightSchedule continueWith) := rfl
    _ = _ :=
      VeiledFlock.DependentProtocolSimulator.programmed_exact sites rightState
        rightSchedule hrightInjective continueWith

/-- Production-strength form of `simulator_exact`: the honest and simulated
schedules need only agree at each causal trace point along the proposed full
answer vector.  This permits an earlier simulated mask to depend on challenges
that are sampled later, while the joint coin equivalence still leaves the
complete random-oracle table pointwise unchanged. -/
theorem trace_simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint (rightSchedule (answerEquiv answers coins)) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hrightInjective : ∀ coins
      (answers : History (Outcome := Outcome) sites),
      Function.Injective (tracePoints (rightSchedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
        (VeiledFlock.CoupledFiatShamir.machine leftState leftSchedule
          continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.DependentProtocolSimulator.SimulatorCoins
          (Point := Point) (Outcome := Outcome) sites rightSchedule)).map
        (VeiledFlock.DependentProtocolSimulator.programmedMachine sites
          rightState rightSchedule hrightInjective continueWith) := by
  calc
    _ = (PMF.uniformOfFintype
        (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
          (VeiledFlock.CoupledFiatShamir.machine rightState rightSchedule
            continueWith) :=
      VeiledFlock.CoupledFiatShamir.trace_simulator_exact leftState rightState
        answerEquiv hstate leftSchedule rightSchedule htrace continueWith
    _ = (PMF.uniformOfFintype
        (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
          (VeiledFlock.DependentProtocolSimulator.oracleMachine sites
            rightState rightSchedule continueWith) := rfl
    _ = _ :=
      VeiledFlock.DependentProtocolSimulator.programmed_exact sites rightState
        rightSchedule hrightInjective continueWith

end VeiledFlock.CoupledOperationalSimulator

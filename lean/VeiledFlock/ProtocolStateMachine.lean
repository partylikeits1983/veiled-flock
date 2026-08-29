import VeiledFlock.AdaptiveOracleProgramming
import VeiledFlock.AlgebraicProtocol
import VeiledFlock.Probability

/-!
# Algebraic protocol plus adaptive programmable-oracle state machine

This module composes the two exact simulator reparameterizations used by the
VEIL--FLOCK proof.  The first changes the honest FLOCK/VEIL masking coins into
the public-input-only algebraic simulator coins.  The second changes a random
oracle into independently selected adaptive challenges plus the untouched
table off the programmed trace.

The oracle schedule is allowed to depend on the entire algebraic transcript.
Consequently this theorem covers the load-bearing Fiat--Shamir dependency: the
programmed point at round `i` may depend on every simulated message and all
earlier programmed answers.
-/

namespace VeiledFlock.ProtocolStateMachine

open Function
open VeiledFlock.AdaptiveOracleProgramming

variable {AlgCoins AlgView Point Outcome FullView : Type*}
variable [Fintype AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Simulator coins after both reparameterizations.  The oracle coin fiber may
depend on the simulated algebraic transcript. -/
abbrev SimulatorCoins (sites : ℕ)
    (simulatedAlgebraic : AlgCoins → AlgView)
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome)) :=
  Σ coins : AlgCoins,
    AdaptiveOracleProgramming.SimulatorCoins
      (sites := sites) (schedule (simulatedAlgebraic coins))

noncomputable instance protocolSimulatorCoinsNonempty (sites : ℕ)
    (simulatedAlgebraic : AlgCoins → AlgView)
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome)) :
    Nonempty (SimulatorCoins (Point := Point) (Outcome := Outcome) sites
      simulatedAlgebraic schedule) := by
  let coins : AlgCoins := Classical.choice inferInstance
  exact ⟨⟨coins, Classical.choice inferInstance⟩⟩

/-- Product/sigma equivalence composing an algebraic coin bijection with exact
adaptive oracle programming. -/
noncomputable def combinedCoinEquiv (sites : ℕ)
    (simulatedAlgebraic : AlgCoins → AlgView)
    (algebraicCoinEquiv : AlgCoins ≃ AlgCoins)
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ algebraic
      (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (schedule algebraic) answers)) :
    (AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) ≃
      SimulatorCoins (Point := Point) (Outcome := Outcome) sites
        simulatedAlgebraic schedule :=
  (Equiv.sigmaEquivProd AlgCoins
      (Oracle (Point := Point) (Outcome := Outcome))).symm |>.trans
    (Equiv.sigmaCongr
      (β₁ := fun _ : AlgCoins =>
        Oracle (Point := Point) (Outcome := Outcome))
      (β₂ := fun coins : AlgCoins =>
        AdaptiveOracleProgramming.SimulatorCoins (sites := sites)
          (schedule (simulatedAlgebraic coins)))
      algebraicCoinEquiv fun coins =>
        splitAdaptive (sites := sites)
          (schedule (simulatedAlgebraic (algebraicCoinEquiv coins)))
          (hinjective (simulatedAlgebraic (algebraicCoinEquiv coins))))

@[simp]
theorem combinedCoinEquiv_apply (sites : ℕ)
    (simulatedAlgebraic : AlgCoins → AlgView)
    (algebraicCoinEquiv : AlgCoins ≃ AlgCoins)
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ algebraic
      (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (schedule algebraic) answers))
    (coins : AlgCoins) (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    combinedCoinEquiv sites simulatedAlgebraic algebraicCoinEquiv schedule
        hinjective (coins, oracle) =
      ⟨algebraicCoinEquiv coins,
        splitAdaptive (sites := sites)
          (schedule (simulatedAlgebraic (algebraicCoinEquiv coins)))
          (hinjective (simulatedAlgebraic (algebraicCoinEquiv coins))) oracle⟩ :=
  rfl

noncomputable def realMachine (sites : ℕ)
    (realAlgebraic : AlgCoins → AlgView)
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : AlgView →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → FullView)
    (coins : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) : FullView :=
  continueWith (realAlgebraic coins.1) coins.2
    (run (schedule (realAlgebraic coins.1)) coins.2 sites)

noncomputable def simulatedMachine (sites : ℕ)
    (simulatedAlgebraic : AlgCoins → AlgView)
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ algebraic
      (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (schedule algebraic) answers))
    (continueWith : AlgView →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → FullView)
    (coins : SimulatorCoins (Point := Point) (Outcome := Outcome) sites
      simulatedAlgebraic schedule) : FullView :=
  continueWith (simulatedAlgebraic coins.1)
    (simulatedOracle (schedule (simulatedAlgebraic coins.1))
      (hinjective (simulatedAlgebraic coins.1)) coins.2)
    coins.2.1

/-- Pointwise equality after the combined algebraic/oracle coin equivalence. -/
theorem realMachine_transport (sites : ℕ)
    (realAlgebraic simulatedAlgebraic : AlgCoins → AlgView)
    (algebraicCoinEquiv : AlgCoins ≃ AlgCoins)
    (halgebraic : ∀ coins,
      realAlgebraic coins = simulatedAlgebraic (algebraicCoinEquiv coins))
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ algebraic
      (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (schedule algebraic) answers))
    (continueWith : AlgView →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → FullView)
    (coins : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    realMachine sites realAlgebraic schedule continueWith coins =
      simulatedMachine sites simulatedAlgebraic schedule hinjective continueWith
        (combinedCoinEquiv sites simulatedAlgebraic algebraicCoinEquiv schedule
          hinjective coins) := by
  rcases coins with ⟨algebraicCoins, oracle⟩
  simp only [realMachine, simulatedMachine]
  rw [combinedCoinEquiv_apply]
  change
    continueWith (realAlgebraic algebraicCoins) oracle
        (run (schedule (realAlgebraic algebraicCoins)) oracle sites) =
      continueWith
        (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins))
        (simulatedOracle
          (schedule (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
          (hinjective
            (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
          ((splitAdaptive (sites := sites)
            (schedule (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
            (hinjective
              (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))) oracle))
        ((splitAdaptive (sites := sites)
          (schedule (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
          (hinjective
            (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))) oracle).1
  rw [halgebraic]
  have horacle :=
    (splitAdaptive (sites := sites)
      (schedule (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
      (hinjective
        (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))).symm_apply_apply
        oracle
  change
    simulatedOracle
        (schedule (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
        (hinjective (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
        ((splitAdaptive
          (schedule (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))
          (hinjective
            (simulatedAlgebraic (algebraicCoinEquiv algebraicCoins)))) oracle) =
      oracle at horacle
  rw [horacle]
  rfl

/-- Exact distributional ZK for the combined algebraic and adaptive-pROM
state machine. -/
theorem combinedSimulator_exact (sites : ℕ)
    (realAlgebraic simulatedAlgebraic : AlgCoins → AlgView)
    (algebraicCoinEquiv : AlgCoins ≃ AlgCoins)
    (halgebraic : ∀ coins,
      realAlgebraic coins = simulatedAlgebraic (algebraicCoinEquiv coins))
    (schedule : AlgView → Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ algebraic
      (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (schedule algebraic) answers))
    (continueWith : AlgView →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → FullView) :
    (PMF.uniformOfFintype
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
        (realMachine sites realAlgebraic schedule continueWith) =
      (PMF.uniformOfFintype
        (SimulatorCoins (Point := Point) (Outcome := Outcome) sites
          simulatedAlgebraic schedule)).map
          (simulatedMachine sites simulatedAlgebraic schedule hinjective
            continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (combinedCoinEquiv sites simulatedAlgebraic algebraicCoinEquiv schedule
      hinjective)
  exact realMachine_transport sites realAlgebraic simulatedAlgebraic
    algebraicCoinEquiv halgebraic schedule hinjective continueWith

end VeiledFlock.ProtocolStateMachine

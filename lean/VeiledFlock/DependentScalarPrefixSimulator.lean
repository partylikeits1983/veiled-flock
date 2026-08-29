import VeiledFlock.AdaptiveScalarPrefixProgramming
import VeiledFlock.DependentProtocolSimulator

/-!
# Answer-dependent scalar-prefix operational simulator

This lifts scalar-prefix programming through the production simulator's
answer-dependent algebraic schedule.  It is the exact distributional bridge
from the whole-block mathematical programmer to Rust's
`program_next_scalar`: chosen field scalars are uniform, old low halves are
discarded, and old high halves remain in the reconstructed oracle.
-/

namespace VeiledFlock.DependentScalarPrefixSimulator

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle

variable {AlgCoins State Point View : Type*}
variable [Fintype AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]

abbrev ScalarSimulatorCoins (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock)) :=
  Σ coins : AlgCoins,
    VeiledFlock.AdaptiveScalarPrefixProgramming.ScalarSimulatorCoins
      (Point := Point) sites (schedule coins)

noncomputable instance scalarSimulatorCoinsNonempty (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    Nonempty (ScalarSimulatorCoins (Point := Point) sites schedule) := by
  classical
  let coins : AlgCoins := Classical.choice inferInstance
  exact ⟨⟨coins, Classical.choice
    (VeiledFlock.AdaptiveScalarPrefixProgramming.scalarSimulatorCoinsNonempty
      sites (schedule coins))⟩⟩

noncomputable instance scalarSimulatorCoinsFintype (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    Fintype (ScalarSimulatorCoins (Point := Point) sites schedule) := by
  classical
  unfold ScalarSimulatorCoins
  infer_instance

/-- Global coin equivalence, retaining one common discarded-prefix vector
outside the answer-dependent algebraic sigma. -/
noncomputable def coinEquiv (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    ScalarSimulatorCoins (Point := Point) sites schedule ≃
      (VeiledFlock.DependentProtocolSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock) sites schedule ×
        VeiledFlock.ScalarPrefixProgramming.DiscardedPrefixes sites) :=
  (Equiv.sigmaCongrRight fun coins ↦
      VeiledFlock.AdaptiveScalarPrefixProgramming.coinEquiv sites
        (schedule coins)).trans
    (Equiv.sigmaProdDistrib
      (fun coins ↦ AdaptiveOracleProgramming.SimulatorCoins
        (sites := sites) (schedule coins))
      (VeiledFlock.ScalarPrefixProgramming.DiscardedPrefixes sites)).symm

/-- Executable low-half programmer, expressed through the proved coin
equivalence so that the reconstructed complete oracle is exactly the one used
by the whole-block operational simulator. -/
noncomputable def programmedMachine (sites : ℕ)
    (state : AlgCoins → History (Outcome := OracleBlock) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (hinjective : ∀ coins (answers : History (Outcome := OracleBlock) sites),
      Function.Injective (tracePoints (schedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := OracleBlock) →
      History (Outcome := OracleBlock) sites → View)
    (input : ScalarSimulatorCoins (Point := Point) sites schedule) : View :=
  VeiledFlock.DependentProtocolSimulator.programmedMachine sites state schedule
    hinjective continueWith (coinEquiv sites schedule input).1

/-- Exact equality between whole-block programming and the scalar-prefix
operation performed by the Rust simulator. -/
theorem simulator_exact (sites : ℕ)
    (state : AlgCoins → History (Outcome := OracleBlock) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (hinjective : ∀ coins (answers : History (Outcome := OracleBlock) sites),
      Function.Injective (tracePoints (schedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := OracleBlock) →
      History (Outcome := OracleBlock) sites → View) :
    (PMF.uniformOfFintype
      (ScalarSimulatorCoins (Point := Point) sites schedule)).map
        (programmedMachine sites state schedule hinjective continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.DependentProtocolSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock) sites schedule)).map
        (VeiledFlock.DependentProtocolSimulator.programmedMachine sites state
          schedule hinjective continueWith) := by
  let view := VeiledFlock.DependentProtocolSimulator.programmedMachine sites
    state schedule hinjective continueWith
  change
    (PMF.uniformOfFintype
      (ScalarSimulatorCoins (Point := Point) sites schedule)).map
        (fun input ↦ view (coinEquiv sites schedule input).1) =
      (PMF.uniformOfFintype
        (VeiledFlock.DependentProtocolSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock) sites schedule)).map view
  calc
    _ = (PMF.uniformOfFintype
          (VeiledFlock.DependentProtocolSimulator.SimulatorCoins
              (Point := Point) (Outcome := OracleBlock) sites schedule ×
            VeiledFlock.ScalarPrefixProgramming.DiscardedPrefixes sites)).map
          (fun input ↦ view input.1) := by
        apply VeiledFlock.Probability.uniform_map_eq_of_equiv
          (coinEquiv sites schedule)
        intro input
        rfl
    _ = _ := VeiledFlock.Probability.uniform_map_ignore_right view

end VeiledFlock.DependentScalarPrefixSimulator

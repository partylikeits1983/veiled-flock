import VeiledFlock.Oracle.LookaheadOperationalSimulator
import VeiledFlock.Oracle.ScalarPrefixProgramming

/-!
# Look-ahead scalar-prefix simulator

This refines the look-ahead programmable-oracle theorem to the operation used
by Rust: sample every target `F128`, preserve an independent pre-programming
oracle block, overwrite only bytes 0--15, and retain bytes 16--31.  The old
low halves are proved to be unused independent coins.
-/

namespace VeiledFlock.LookaheadScalarPrefixSimulator

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.OracleProgramming
open VeiledFlock.ScalarPrefixProgramming

variable {AlgCoins State Point View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]

abbrev FullFiber (sites : ℕ)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (coins : AlgCoins) :=
  Σ answers : BlockAnswers sites,
    Unprogrammed (tracePoints (rightSchedule coins answers) answers) →
      OracleBlock

/-- Rust-shaped look-ahead coins: selected scalar targets, old blocks at the
reached sites, and the oracle complement selected by the resulting blocks. -/
abbrev ScalarSimulatorCoins (sites : ℕ)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :=
  Σ coins : AlgCoins,
    Σ raw : ScalarAnswers sites × BlockAnswers sites,
      Unprogrammed
        (tracePoints
          (rightSchedule coins (answerCoinEquiv sites raw).1)
          (answerCoinEquiv sites raw).1) → OracleBlock

noncomputable instance scalarSimulatorCoinsNonempty (sites : ℕ)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    Nonempty (ScalarSimulatorCoins (Point := Point) sites rightSchedule) := by
  classical
  let coins : AlgCoins := Classical.choice inferInstance
  let scalar : VeiledFlock.Field128Ghash.GhashField :=
    Classical.choice inferInstance
  let block : OracleBlock := Classical.choice inferInstance
  exact ⟨⟨coins, ⟨(fun _ ↦ scalar, fun _ ↦ block), fun _ ↦ block⟩⟩⟩

noncomputable instance scalarSimulatorCoinsFintype (sites : ℕ)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    Fintype (ScalarSimulatorCoins (Point := Point) sites rightSchedule) := by
  classical
  unfold ScalarSimulatorCoins
  infer_instance

private noncomputable def fiberEquiv (sites : ℕ)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (coins : AlgCoins) :
    (Σ raw : ScalarAnswers sites × BlockAnswers sites,
      Unprogrammed
        (tracePoints
          (rightSchedule coins (answerCoinEquiv sites raw).1)
          (answerCoinEquiv sites raw).1) → OracleBlock) ≃
      (FullFiber (Point := Point) sites rightSchedule coins ×
        DiscardedPrefixes sites) := by
  let sourceFamily := fun raw : ScalarAnswers sites × BlockAnswers sites ↦
    Unprogrammed
      (tracePoints
        (rightSchedule coins (answerCoinEquiv sites raw).1)
        (answerCoinEquiv sites raw).1) → OracleBlock
  let targetFamily :=
    fun output : BlockAnswers sites × DiscardedPrefixes sites ↦
      Unprogrammed
        (tracePoints (rightSchedule coins output.1) output.1) → OracleBlock
  let first : (Σ raw, sourceFamily raw) ≃
      (Σ output, targetFamily output) :=
    Equiv.sigmaCongr (answerCoinEquiv sites)
      (fun raw ↦ Equiv.refl (sourceFamily raw))
  let second : (Σ output, targetFamily output) ≃
      (FullFiber (Point := Point) sites rightSchedule coins ×
        DiscardedPrefixes sites) := by
    dsimp only [targetFamily, FullFiber]
    exact
      (Equiv.sigmaCongr
        (Equiv.sigmaEquivProd (BlockAnswers sites)
          (DiscardedPrefixes sites)).symm
        (fun _ ↦ Equiv.refl _)).trans
      ((Equiv.sigmaAssoc (fun answers (_ : DiscardedPrefixes sites) ↦
          Unprogrammed
            (tracePoints (rightSchedule coins answers) answers) →
              OracleBlock)).trans
        ((Equiv.sigmaCongrRight fun answers ↦
            (Equiv.sigmaEquivProd (DiscardedPrefixes sites)
                (Unprogrammed
                  (tracePoints (rightSchedule coins answers) answers) →
                    OracleBlock)).trans
              (Equiv.prodComm _ _)).trans
          (Equiv.sigmaProdDistrib
            (fun answers ↦
              Unprogrammed
                (tracePoints (rightSchedule coins answers) answers) →
                  OracleBlock)
            (DiscardedPrefixes sites)).symm))
  exact first.trans second

/-- Global exact reparameterization to the ordinary full-block look-ahead
coin space plus the discarded old low halves. -/
noncomputable def coinEquiv (sites : ℕ)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    ScalarSimulatorCoins (Point := Point) sites rightSchedule ≃
      (VeiledFlock.LookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock) sites rightSchedule ×
        DiscardedPrefixes sites) :=
  (Equiv.sigmaCongrRight fun coins ↦
      fiberEquiv sites rightSchedule coins).trans
    (Equiv.sigmaProdDistrib
      (fun coins ↦ FullFiber (Point := Point) sites rightSchedule coins)
      (DiscardedPrefixes sites)).symm

/-- Execute the full-block look-ahead machine after the proved scalar-prefix
coin conversion. -/
noncomputable def programmedMachine (sites : ℕ)
    (state : AlgCoins → BlockAnswers sites → State)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (hright : ∀ coins answers,
      Function.Injective
        (tracePoints (rightSchedule coins answers) answers))
    (continueWith : State →
      AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := OracleBlock) →
      BlockAnswers sites → View)
    (input : ScalarSimulatorCoins (Point := Point) sites rightSchedule) : View :=
  VeiledFlock.LookaheadOperationalSimulator.programmedMachine sites state
    rightSchedule hright continueWith (coinEquiv sites rightSchedule input).1

omit [DecidableEq AlgCoins] in
/-- The implementation-shaped low-half programmer and the ordinary
full-block look-ahead programmer induce exactly equal distributions. -/
theorem simulator_exact (sites : ℕ)
    (state : AlgCoins → BlockAnswers sites → State)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (hright : ∀ coins answers,
      Function.Injective
        (tracePoints (rightSchedule coins answers) answers))
    (continueWith : State →
      AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := OracleBlock) →
      BlockAnswers sites → View) :
    (PMF.uniformOfFintype
      (ScalarSimulatorCoins (Point := Point) sites rightSchedule)).map
        (programmedMachine sites state rightSchedule hright continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.LookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock)
          sites rightSchedule)).map
        (VeiledFlock.LookaheadOperationalSimulator.programmedMachine sites
          state rightSchedule hright continueWith) := by
  let view := VeiledFlock.LookaheadOperationalSimulator.programmedMachine sites
    state rightSchedule hright continueWith
  change
    (PMF.uniformOfFintype
      (ScalarSimulatorCoins (Point := Point) sites rightSchedule)).map
        (fun input ↦ view (coinEquiv sites rightSchedule input).1) =
      (PMF.uniformOfFintype
        (VeiledFlock.LookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock)
          sites rightSchedule)).map view
  calc
    _ = (PMF.uniformOfFintype
        (VeiledFlock.LookaheadOperationalSimulator.SimulatorCoins
            (Point := Point) (Outcome := OracleBlock)
            sites rightSchedule × DiscardedPrefixes sites)).map
          (fun input ↦ view input.1) := by
      apply VeiledFlock.Probability.uniform_map_eq_of_equiv
        (coinEquiv sites rightSchedule)
      intro input
      rfl
    _ = _ := VeiledFlock.Probability.uniform_map_ignore_right view

/-- Honest execution is exactly distributed as the Rust-shaped look-ahead
scalar-prefix simulator. -/
theorem honest_simulator_exact {sites : ℕ}
    (leftState rightState : AlgCoins → BlockAnswers sites → State)
    (answerEquiv : BlockAnswers sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (htrace : ∀ coins answers site,
      tracePoint
          (rightSchedule (answerEquiv answers coins) answers) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hright : ∀ coins answers,
      Function.Injective
        (tracePoints (rightSchedule coins answers) answers))
    (continueWith : State →
      AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := OracleBlock) →
      BlockAnswers sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := OracleBlock))).map
        (VeiledFlock.LookaheadOperationalSimulator.honestMachine
          leftState leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (ScalarSimulatorCoins (Point := Point) sites rightSchedule)).map
        (programmedMachine sites rightState rightSchedule hright
          continueWith) := by
  calc
    _ = (PMF.uniformOfFintype
        (VeiledFlock.LookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock)
          sites rightSchedule)).map
        (VeiledFlock.LookaheadOperationalSimulator.programmedMachine sites
          rightState rightSchedule hright continueWith) :=
      VeiledFlock.LookaheadOperationalSimulator.simulator_exact leftState
        rightState answerEquiv hstate leftSchedule rightSchedule htrace hright
        continueWith
    _ = _ :=
      (simulator_exact sites rightState rightSchedule hright
        continueWith).symm

end VeiledFlock.LookaheadScalarPrefixSimulator

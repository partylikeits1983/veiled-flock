import VeiledFlock.Oracle.ProtectedLookaheadOperationalSimulator
import VeiledFlock.Oracle.ScalarPrefixProgramming

/-!
# Prior-query-preserving scalar-prefix look-ahead simulator

This is the exact Rust 128-bit-prefix refinement of the protected operational
look-ahead theorem.  The simulator samples a target `F128`, retains a complete
independent old 256-bit block, replaces only bytes 0--15, and keeps both the
old low half and every protected adversary answer as explicit finite coins.
-/

namespace VeiledFlock.ProtectedLookaheadScalarPrefixSimulator

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ProtectedAdaptiveOracle
open VeiledFlock.ScalarPrefixProgramming

variable {AlgCoins State Prior Point View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]

abbrev FullFiber (sites : ℕ) (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (coins : AlgCoins) :=
  Σ answers : BlockAnswers sites,
    (Prior → OracleBlock) ×
      (Outside
        (points fixedPoints (rightSchedule coins answers) answers) →
          OracleBlock)

/-- Rust-shaped coins with protected answers and the joint oracle
complement. -/
abbrev ScalarSimulatorCoins (sites : ℕ) (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :=
  Σ coins : AlgCoins,
    Σ raw : ScalarAnswers sites × BlockAnswers sites,
      (Prior → OracleBlock) ×
        (Outside
          (points fixedPoints
            (rightSchedule coins (answerCoinEquiv sites raw).1)
            (answerCoinEquiv sites raw).1) → OracleBlock)

noncomputable instance scalarSimulatorCoinsNonempty (sites : ℕ)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    Nonempty (ScalarSimulatorCoins (Point := Point)
      sites fixedPoints rightSchedule) := by
  classical
  let coins : AlgCoins := Classical.choice inferInstance
  let scalar : VeiledFlock.Field128Ghash.GhashField :=
    Classical.choice inferInstance
  let block : OracleBlock := Classical.choice inferInstance
  exact ⟨⟨coins, ⟨(fun _ ↦ scalar, fun _ ↦ block),
    fun _ ↦ block, fun _ ↦ block⟩⟩⟩

noncomputable instance scalarSimulatorCoinsFintype (sites : ℕ)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    Fintype (ScalarSimulatorCoins (Point := Point)
      sites fixedPoints rightSchedule) := by
  classical
  letI := Fintype.ofFinite Prior
  unfold ScalarSimulatorCoins
  infer_instance

private noncomputable def fiberEquiv (sites : ℕ)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (coins : AlgCoins) :
    (Σ raw : ScalarAnswers sites × BlockAnswers sites,
      (Prior → OracleBlock) ×
        (Outside
          (points fixedPoints
            (rightSchedule coins (answerCoinEquiv sites raw).1)
            (answerCoinEquiv sites raw).1) → OracleBlock)) ≃
      (FullFiber (Point := Point) sites fixedPoints rightSchedule coins ×
        DiscardedPrefixes sites) := by
  let sourceFamily := fun raw : ScalarAnswers sites × BlockAnswers sites ↦
    (Prior → OracleBlock) ×
      (Outside
        (points fixedPoints
          (rightSchedule coins (answerCoinEquiv sites raw).1)
          (answerCoinEquiv sites raw).1) → OracleBlock)
  let targetFamily :=
    fun output : BlockAnswers sites × DiscardedPrefixes sites ↦
      (Prior → OracleBlock) ×
        (Outside
          (points fixedPoints (rightSchedule coins output.1) output.1) →
            OracleBlock)
  let first : (Σ raw, sourceFamily raw) ≃
      (Σ output, targetFamily output) :=
    Equiv.sigmaCongr (answerCoinEquiv sites)
      (fun raw ↦ Equiv.refl (sourceFamily raw))
  let second : (Σ output, targetFamily output) ≃
      (FullFiber (Point := Point) sites fixedPoints rightSchedule coins ×
        DiscardedPrefixes sites) := by
    dsimp only [targetFamily, FullFiber]
    exact
      (Equiv.sigmaCongr
        (Equiv.sigmaEquivProd (BlockAnswers sites)
          (DiscardedPrefixes sites)).symm
        (fun _ ↦ Equiv.refl _)).trans
      ((Equiv.sigmaAssoc
          (fun answers (_ : DiscardedPrefixes sites) ↦
            (Prior → OracleBlock) ×
              (Outside
                (points fixedPoints (rightSchedule coins answers) answers) →
                  OracleBlock))).trans
        ((Equiv.sigmaCongrRight fun answers ↦
            (Equiv.sigmaEquivProd (DiscardedPrefixes sites)
                ((Prior → OracleBlock) ×
                  (Outside
                    (points fixedPoints (rightSchedule coins answers) answers) →
                      OracleBlock))).trans
              (Equiv.prodComm _ _)).trans
          (Equiv.sigmaProdDistrib
            (fun answers ↦
              (Prior → OracleBlock) ×
                (Outside
                  (points fixedPoints (rightSchedule coins answers) answers) →
                    OracleBlock))
            (DiscardedPrefixes sites)).symm))
  exact first.trans second

/-- Global conversion to the protected full-block simulator coin space plus
the unused old low halves. -/
noncomputable def coinEquiv (sites : ℕ) (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock)) :
    ScalarSimulatorCoins (Point := Point) sites fixedPoints rightSchedule ≃
      (VeiledFlock.ProtectedLookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock)
          sites fixedPoints rightSchedule × DiscardedPrefixes sites) :=
  (Equiv.sigmaCongrRight fun coins ↦
      fiberEquiv sites fixedPoints rightSchedule coins).trans
    (Equiv.sigmaProdDistrib
      (fun coins ↦
        FullFiber (Point := Point) sites fixedPoints rightSchedule coins)
      (DiscardedPrefixes sites)).symm

noncomputable def programmedMachine (sites : ℕ)
    (state : AlgCoins → BlockAnswers sites → State)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (hright : ∀ coins answers,
      Function.Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (continueWith : State → (Prior → OracleBlock) →
      RandomOracle (Point := Point) (Outcome := OracleBlock) →
      BlockAnswers sites → View)
    (input : ScalarSimulatorCoins (Point := Point)
      sites fixedPoints rightSchedule) : View :=
  VeiledFlock.ProtectedLookaheadOperationalSimulator.programmedMachine sites
    state fixedPoints rightSchedule hright continueWith
    (coinEquiv sites fixedPoints rightSchedule input).1

omit [DecidableEq AlgCoins] in
theorem simulator_exact (sites : ℕ)
    (state : AlgCoins → BlockAnswers sites → State)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → BlockAnswers sites →
      Schedule (Point := Point) (Outcome := OracleBlock))
    (hright : ∀ coins answers,
      Function.Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (continueWith : State → (Prior → OracleBlock) →
      RandomOracle (Point := Point) (Outcome := OracleBlock) →
      BlockAnswers sites → View) :
    (PMF.uniformOfFintype
      (ScalarSimulatorCoins (Point := Point)
        sites fixedPoints rightSchedule)).map
        (programmedMachine sites state fixedPoints rightSchedule hright
          continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock)
          sites fixedPoints rightSchedule)).map
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.programmedMachine
          sites state fixedPoints rightSchedule hright continueWith) := by
  let view :=
    VeiledFlock.ProtectedLookaheadOperationalSimulator.programmedMachine sites
      state fixedPoints rightSchedule hright continueWith
  change
    (PMF.uniformOfFintype
      (ScalarSimulatorCoins (Point := Point)
        sites fixedPoints rightSchedule)).map
        (fun input ↦ (view (coinEquiv sites fixedPoints rightSchedule input).1)) =
      (PMF.uniformOfFintype
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock)
          sites fixedPoints rightSchedule)).map view
  calc
    _ = (PMF.uniformOfFintype
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.SimulatorCoins
            (Point := Point) (Outcome := OracleBlock)
            sites fixedPoints rightSchedule × DiscardedPrefixes sites)).map
          (fun input ↦ view input.1) := by
      apply VeiledFlock.Probability.uniform_map_eq_of_equiv
        (coinEquiv sites fixedPoints rightSchedule)
      intro input
      rfl
    _ = _ := VeiledFlock.Probability.uniform_map_ignore_right view

omit [DecidableEq AlgCoins] in
/-- Honest execution is exactly distributed as the protected Rust-shaped
scalar-prefix simulator. -/
theorem honest_simulator_exact {sites : ℕ}
    (leftState rightState : AlgCoins → BlockAnswers sites → State)
    (answerEquiv : BlockAnswers sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (fixedPoints : Prior → Point)
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
        (points fixedPoints (rightSchedule coins answers) answers))
    (continueWith : State → (Prior → OracleBlock) →
      RandomOracle (Point := Point) (Outcome := OracleBlock) →
      BlockAnswers sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × RandomOracle
        (Point := Point) (Outcome := OracleBlock))).map
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.honestMachine
          leftState fixedPoints leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (ScalarSimulatorCoins (Point := Point)
          sites fixedPoints rightSchedule)).map
        (programmedMachine sites rightState fixedPoints rightSchedule hright
          continueWith) := by
  calc
    _ = (PMF.uniformOfFintype
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.SimulatorCoins
          (Point := Point) (Outcome := OracleBlock)
          sites fixedPoints rightSchedule)).map
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.programmedMachine
          sites rightState fixedPoints rightSchedule hright continueWith) :=
      VeiledFlock.ProtectedLookaheadOperationalSimulator.simulator_exact
        leftState rightState answerEquiv hstate fixedPoints leftSchedule
        rightSchedule htrace hright continueWith
    _ = _ :=
      (simulator_exact sites rightState fixedPoints rightSchedule hright
        continueWith).symm

end VeiledFlock.ProtectedLookaheadScalarPrefixSimulator

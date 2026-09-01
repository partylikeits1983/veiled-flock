import VeiledFlock.Oracle.AdaptiveOracleProgramming
import VeiledFlock.Core.Probability

/-!
# Operational simulator with a look-ahead target vector

The production simulator samples every Fiat--Shamir value it intends to
program before emitting the proof.  Therefore an early simulated message may
depend on a value programmed at a later site.  The honest prover remains
causal, but the simulator schedule is parameterized by its complete target
answer vector.

This module proves the exact finite-random-oracle reparameterization for that
setting.  The output coin space consists of translated algebraic coins, the
full target vector, and the untouched oracle table away from the resulting
adaptive trace.
-/

namespace VeiledFlock.LookaheadOperationalSimulator

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.OracleProgramming

variable {AlgCoins State Point Outcome View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Simulator-owned target answers and the complete oracle complement for a
schedule that may inspect that target vector. -/
abbrev SimulatorCoins (sites : ℕ)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome)) :=
  Σ coins : AlgCoins,
    Σ answers : History (Outcome := Outcome) sites,
      Unprogrammed (tracePoints (rightSchedule coins answers) answers) →
        Outcome

noncomputable instance simulatorCoinsNonempty (sites : ℕ)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome)) :
    Nonempty (SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites rightSchedule) := by
  classical
  let coins : AlgCoins := Classical.choice inferInstance
  let answer : Outcome := Classical.choice inferInstance
  exact ⟨⟨coins, fun _ ↦ answer, fun _ ↦ answer⟩⟩

noncomputable instance simulatorCoinsFintype (sites : ℕ)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome)) :
    Fintype (SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites rightSchedule) := by
  classical
  unfold SimulatorCoins
  infer_instance

/-- Reconstruct the complete oracle by installing the look-ahead target
answers at the trace they themselves select. -/
noncomputable def programmedOracle (sites : ℕ)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins answers,
      Injective (tracePoints (rightSchedule coins answers) answers))
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites rightSchedule) :
    AdaptiveOracleProgramming.Oracle
      (Point := Point) (Outcome := Outcome) :=
  (splitOracle
    (tracePoints (rightSchedule input.1 input.2.1) input.2.1)
    (hright input.1 input.2.1)).symm (input.2.1, input.2.2)

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
omit [Fintype Point] in
@[simp]
theorem programmedOracle_at (sites : ℕ)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins answers,
      Injective (tracePoints (rightSchedule coins answers) answers))
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites rightSchedule) (site : Fin sites) :
    programmedOracle sites rightSchedule hright input
        (tracePoint (rightSchedule input.1 input.2.1) input.2.1 site) =
      input.2.1 site := by
  let points := tracePoints (rightSchedule input.1 input.2.1) input.2.1
  let oracle := programmedOracle sites rightSchedule hright input
  have h := splitOracle_programmed points (hright input.1 input.2.1)
    oracle site
  have hsplit :
      splitOracle points (hright input.1 input.2.1) oracle =
        (input.2.1, input.2.2) := by
    exact (splitOracle points
      (hright input.1 input.2.1)).apply_symm_apply _
  rw [hsplit] at h
  exact h.symm

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
omit [Fintype Point] in
/-- The honest causal schedule realizes the proposed target vector in the
reconstructed oracle whenever its reached points match the look-ahead trace
along that vector. -/
theorem run_left_programmedOracle {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint
          (rightSchedule (answerEquiv answers coins) answers) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hright : ∀ coins answers,
      Injective (tracePoints (rightSchedule coins answers) answers))
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites rightSchedule) :
    let recovered := (answerEquiv input.2.1).symm input.1
    run (leftSchedule recovered)
      (programmedOracle sites rightSchedule hright input) sites = input.2.1 := by
  let answers := input.2.1
  let translated := input.1
  let recovered := (answerEquiv answers).symm translated
  let oracle := programmedOracle sites rightSchedule hright input
  have htranslated : answerEquiv answers recovered = translated := by
    simp [recovered]
  have hround : ∀ count (hle : count ≤ sites),
      run (leftSchedule recovered) oracle count =
        fun site ↦ answers (Fin.castLE hle site) := by
    intro count
    induction count with
    | zero =>
        intro _
        funext site
        exact Fin.elim0 site
    | succ count ih =>
        intro hle
        funext site
        refine Fin.lastCases ?_ (fun prior ↦ ?_) site
        · rw [run_succ_last]
          have hprevious : run (leftSchedule recovered) oracle count =
              priorAnswers answers ⟨count, Nat.lt_of_succ_le hle⟩ := by
            rw [ih (Nat.le_trans (Nat.le_succ count) hle)]
            funext prior
            rfl
          rw [hprevious]
          let fullSite : Fin sites := ⟨count, Nat.lt_of_succ_le hle⟩
          have hpoint := htrace recovered answers fullSite
          rw [htranslated] at hpoint
          change oracle (tracePoint (leftSchedule recovered) answers fullSite) =
            answers fullSite
          rw [← hpoint]
          exact programmedOracle_at sites rightSchedule hright input fullSite
        · rw [run_succ_castSucc,
            ih (Nat.le_trans (Nat.le_succ count) hle)]
          rfl
  simpa only [Fin.castLE_refl] using hround sites (le_refl sites)

/-- Exact joint reparameterization from honest algebraic coins and a complete
uniform oracle to look-ahead simulator coins. -/
noncomputable def coinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint
          (rightSchedule (answerEquiv answers coins) answers) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hright : ∀ coins answers,
      Injective (tracePoints (rightSchedule coins answers) answers)) :
    (AlgCoins × AdaptiveOracleProgramming.Oracle
      (Point := Point) (Outcome := Outcome)) ≃
      SimulatorCoins (Point := Point) (Outcome := Outcome)
        sites rightSchedule where
  toFun input :=
    let answers := run (leftSchedule input.1) input.2 sites
    let translated := answerEquiv answers input.1
    let points := tracePoints (rightSchedule translated answers) answers
    ⟨translated, answers,
      (splitOracle points (hright translated answers) input.2).2⟩
  invFun output :=
    ((answerEquiv output.2.1).symm output.1,
      programmedOracle sites rightSchedule hright output)
  left_inv input := by
    rcases input with ⟨coins, oracle⟩
    let answers := run (leftSchedule coins) oracle sites
    let translated := answerEquiv answers coins
    let points := tracePoints (rightSchedule translated answers) answers
    have hprogrammed : ∀ site,
        oracle (points site) = answers site := by
      intro site
      have hpoint := htrace coins answers site
      change tracePoint (rightSchedule translated answers) answers site =
        tracePoint (leftSchedule coins) answers site at hpoint
      change oracle
        (tracePoint (rightSchedule translated answers) answers site) =
          answers site
      rw [hpoint]
      exact oracle_tracePoint_run (leftSchedule coins) oracle site
    have hsplit :
        (answers,
          (splitOracle points (hright translated answers) oracle).2) =
        splitOracle points (hright translated answers) oracle := by
      apply Prod.ext
      · funext site
        rw [splitOracle_programmed]
        exact (hprogrammed site).symm
      · rfl
    change
      ((answerEquiv answers).symm translated,
        (splitOracle points (hright translated answers)).symm
          (answers,
            (splitOracle points (hright translated answers) oracle).2)) =
        (coins, oracle)
    apply Prod.ext
    · simp [translated]
    · rw [hsplit]
      exact (splitOracle points
        (hright translated answers)).symm_apply_apply oracle
  right_inv output := by
    rcases output with ⟨translated, answers, outside⟩
    let input : SimulatorCoins (Point := Point) (Outcome := Outcome)
        sites rightSchedule := ⟨translated, answers, outside⟩
    let recovered := (answerEquiv answers).symm translated
    let oracle := programmedOracle sites rightSchedule hright input
    have hrun : run (leftSchedule recovered) oracle sites = answers := by
      exact run_left_programmedOracle answerEquiv leftSchedule rightSchedule
        htrace hright input
    have htranslated : answerEquiv answers recovered = translated := by
      simp [recovered]
    change
      (let realized := run (leftSchedule recovered) oracle sites
       let mapped := answerEquiv realized recovered
       (⟨mapped, ⟨realized,
          (splitOracle
            (tracePoints (rightSchedule mapped realized) realized)
            (hright mapped realized) oracle).2⟩⟩ :
          SimulatorCoins (Point := Point) (Outcome := Outcome)
            sites rightSchedule)) = input
    rw [hrun]
    dsimp only
    rw [htranslated]
    change
      (⟨translated, ⟨answers,
        (splitOracle
          (tracePoints (rightSchedule translated answers) answers)
          (hright translated answers) oracle).2⟩⟩ :
        SimulatorCoins (Point := Point) (Outcome := Outcome)
          sites rightSchedule) =
      ⟨translated, ⟨answers, outside⟩⟩
    apply congrArg (fun remaining ↦
      (⟨translated, remaining⟩ :
        SimulatorCoins (Point := Point) (Outcome := Outcome)
          sites rightSchedule))
    apply congrArg (fun remaining ↦
      (⟨answers, remaining⟩ :
        Σ proposed : History (Outcome := Outcome) sites,
          Unprogrammed
            (tracePoints (rightSchedule translated proposed) proposed) →
              Outcome))
    exact congrArg Prod.snd
      ((splitOracle
        (tracePoints (rightSchedule translated answers) answers)
        (hright translated answers)).apply_symm_apply (answers, outside))

def honestMachine {sites : ℕ}
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State →
      AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × AdaptiveOracleProgramming.Oracle
      (Point := Point) (Outcome := Outcome)) : View :=
  let answers := run (schedule input.1) input.2 sites
  continueWith (state input.1 answers) input.2 answers

noncomputable def programmedMachine (sites : ℕ)
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins answers,
      Injective (tracePoints (rightSchedule coins answers) answers))
    (continueWith : State →
      AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites rightSchedule) : View :=
  continueWith (state input.1 input.2.1)
    (programmedOracle sites rightSchedule hright input) input.2.1

omit [DecidableEq AlgCoins] [DecidableEq Outcome] in
/-- Honest execution and the straightline look-ahead programmable simulator
have exactly equal full-view distributions. -/
theorem simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint
          (rightSchedule (answerEquiv answers coins) answers) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hright : ∀ coins answers,
      Injective (tracePoints (rightSchedule coins answers) answers))
    (continueWith : State →
      AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × AdaptiveOracleProgramming.Oracle
        (Point := Point) (Outcome := Outcome))).map
        (honestMachine leftState leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (SimulatorCoins (Point := Point) (Outcome := Outcome)
          sites rightSchedule)).map
        (programmedMachine sites rightState rightSchedule hright
          continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv answerEquiv leftSchedule rightSchedule htrace hright)
  intro input
  let answers := run (leftSchedule input.1) input.2 sites
  let translated := answerEquiv answers input.1
  let mapped := coinEquiv answerEquiv leftSchedule rightSchedule htrace
    hright input
  have horacle : programmedOracle sites rightSchedule hright mapped =
      input.2 := by
    exact congrArg Prod.snd
      ((coinEquiv answerEquiv leftSchedule rightSchedule htrace hright).symm_apply_apply
        input)
  change
    continueWith (leftState input.1 answers) input.2 answers =
      continueWith (rightState translated answers)
        (programmedOracle sites rightSchedule hright mapped) answers
  rw [horacle, hstate input.1 answers]

end VeiledFlock.LookaheadOperationalSimulator

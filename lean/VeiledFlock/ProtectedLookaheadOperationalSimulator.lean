import VeiledFlock.LookaheadOperationalSimulator
import VeiledFlock.ProtectedAdaptiveOracle

/-!
# Prior-query-preserving operational look-ahead simulator

The production simulator chooses its complete target Fiat--Shamir answer
vector before it emits the first masked message.  The ordinary look-ahead
theorem reconstructs a uniform oracle around that vector, but a multi-theorem
ZK game must additionally retain every oracle answer already exposed to the
adversary.  This module splits the oracle at the disjoint union of those
protected points and the adaptive programmed trace.
-/

namespace VeiledFlock.ProtectedLookaheadOperationalSimulator

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ProtectedAdaptiveOracle

variable {AlgCoins State Prior Point Outcome View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Simulator-owned algebraic coins and target answers, the exact answers at
all prior adversary points, and the untouched complement of the joint point
family. -/
abbrev SimulatorCoins (sites : ℕ) (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome)) :=
  Σ coins : AlgCoins,
    Σ answers : History (Outcome := Outcome) sites,
      (Prior → Outcome) ×
        (Outside
          (points fixedPoints (rightSchedule coins answers) answers) → Outcome)

noncomputable instance simulatorCoinsNonempty (sites : ℕ)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome)) :
    Nonempty (SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites fixedPoints rightSchedule) := by
  classical
  let coins : AlgCoins := Classical.choice inferInstance
  let answer : Outcome := Classical.choice inferInstance
  exact ⟨⟨coins, fun _ ↦ answer, fun _ ↦ answer, fun _ ↦ answer⟩⟩

noncomputable instance simulatorCoinsFintype (sites : ℕ)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome)) :
    Fintype (SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites fixedPoints rightSchedule) := by
  classical
  letI := Fintype.ofFinite Prior
  unfold SimulatorCoins
  infer_instance

/-- Reconstruct the complete oracle, installing both the preserved prior
answers and the simulator's target answers. -/
noncomputable def programmedOracle (sites : ℕ) (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins answers,
      Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites fixedPoints rightSchedule) :
    RandomOracle (Point := Point) (Outcome := Outcome) :=
  let family := points fixedPoints
    (rightSchedule input.1 input.2.1) input.2.1
  (splitTable family (hright input.1 input.2.1)).symm
    (Sum.elim input.2.2.1 input.2.1, input.2.2.2)

@[simp]
theorem programmedOracle_fixed (sites : ℕ) (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins answers,
      Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites fixedPoints rightSchedule) (prior : Prior) :
    programmedOracle sites fixedPoints rightSchedule hright input
        (fixedPoints prior) = input.2.2.1 prior := by
  let family := points fixedPoints
    (rightSchedule input.1 input.2.1) input.2.1
  change
    ((splitTable family (hright input.1 input.2.1)).symm
      (Sum.elim input.2.2.1 input.2.1, input.2.2.2))
        (family (Sum.inl prior)) = input.2.2.1 prior
  have h := splitTable_programmed family (hright input.1 input.2.1)
    ((splitTable family (hright input.1 input.2.1)).symm
      (Sum.elim input.2.2.1 input.2.1, input.2.2.2)) (Sum.inl prior)
  rw [(splitTable family (hright input.1 input.2.1)).apply_symm_apply] at h
  exact h.symm

@[simp]
theorem programmedOracle_trace (sites : ℕ) (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins answers,
      Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites fixedPoints rightSchedule) (site : Fin sites) :
    programmedOracle sites fixedPoints rightSchedule hright input
        (tracePoint (rightSchedule input.1 input.2.1) input.2.1 site) =
      input.2.1 site := by
  let family := points fixedPoints
    (rightSchedule input.1 input.2.1) input.2.1
  change
    ((splitTable family (hright input.1 input.2.1)).symm
      (Sum.elim input.2.2.1 input.2.1, input.2.2.2))
        (family (Sum.inr site)) = input.2.1 site
  have h := splitTable_programmed family (hright input.1 input.2.1)
    ((splitTable family (hright input.1 input.2.1)).symm
      (Sum.elim input.2.2.1 input.2.1, input.2.2.2)) (Sum.inr site)
  rw [(splitTable family (hright input.1 input.2.1)).apply_symm_apply] at h
  exact h.symm

theorem run_left_programmedOracle {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint
          (rightSchedule (answerEquiv answers coins) answers) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hright : ∀ coins answers,
      Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites fixedPoints rightSchedule) :
    let recovered := (answerEquiv input.2.1).symm input.1
    run (leftSchedule recovered)
      (programmedOracle sites fixedPoints rightSchedule hright input) sites =
        input.2.1 := by
  let answers := input.2.1
  let translated := input.1
  let recovered := (answerEquiv answers).symm translated
  let oracle := programmedOracle sites fixedPoints rightSchedule hright input
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
          exact programmedOracle_trace sites fixedPoints rightSchedule hright
            input fullSite
        · rw [run_succ_castSucc,
            ih (Nat.le_trans (Nat.le_succ count) hle)]
          rfl
  simpa only [Fin.castLE_refl] using hround sites (le_refl sites)

/-- Exact joint reparameterization retaining every protected oracle answer. -/
noncomputable def coinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint
          (rightSchedule (answerEquiv answers coins) answers) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hright : ∀ coins answers,
      Injective
        (points fixedPoints (rightSchedule coins answers) answers)) :
    (AlgCoins × RandomOracle (Point := Point) (Outcome := Outcome)) ≃
      SimulatorCoins (Point := Point) (Outcome := Outcome)
        sites fixedPoints rightSchedule where
  toFun input :=
    let answers := run (leftSchedule input.1) input.2 sites
    let translated := answerEquiv answers input.1
    let family := points fixedPoints
      (rightSchedule translated answers) answers
    let split := splitTable family (hright translated answers) input.2
    ⟨translated, answers, (fun prior ↦ split.1 (Sum.inl prior)), split.2⟩
  invFun output :=
    ((answerEquiv output.2.1).symm output.1,
      programmedOracle sites fixedPoints rightSchedule hright output)
  left_inv input := by
    rcases input with ⟨coins, oracle⟩
    let answers := run (leftSchedule coins) oracle sites
    let translated := answerEquiv answers coins
    let family := points fixedPoints (rightSchedule translated answers) answers
    let split := splitTable family (hright translated answers) oracle
    have hselected :
        Sum.elim (fun prior ↦ split.1 (Sum.inl prior)) answers = split.1 := by
      funext site
      cases site with
      | inl prior => rfl
      | inr protocol =>
          change answers protocol = split.1 (Sum.inr protocol)
          rw [splitTable_programmed]
          have hpoint := htrace coins answers protocol
          change
            tracePoint (rightSchedule translated answers) answers protocol =
              tracePoint (leftSchedule coins) answers protocol at hpoint
          change answers protocol =
            oracle
              (tracePoint (rightSchedule translated answers) answers protocol)
          rw [hpoint]
          exact (oracle_tracePoint_run (leftSchedule coins) oracle protocol).symm
    change
      ((answerEquiv answers).symm translated,
        (splitTable family (hright translated answers)).symm
          (Sum.elim (fun prior ↦ split.1 (Sum.inl prior)) answers,
            split.2)) = (coins, oracle)
    apply Prod.ext
    · simp [translated]
    · rw [hselected]
      exact (splitTable family
        (hright translated answers)).symm_apply_apply oracle
  right_inv output := by
    rcases output with ⟨translated, answers, priorAnswers, outside⟩
    let input : SimulatorCoins (Point := Point) (Outcome := Outcome)
        sites fixedPoints rightSchedule :=
      ⟨translated, answers, priorAnswers, outside⟩
    let recovered := (answerEquiv answers).symm translated
    let oracle := programmedOracle sites fixedPoints rightSchedule hright input
    have hrun : run (leftSchedule recovered) oracle sites = answers :=
      run_left_programmedOracle answerEquiv fixedPoints leftSchedule
        rightSchedule htrace hright input
    have htranslated : answerEquiv answers recovered = translated := by
      simp [recovered]
    change
      (let realized := run (leftSchedule recovered) oracle sites
       let mapped := answerEquiv realized recovered
       let family := points fixedPoints (rightSchedule mapped realized) realized
       let split := splitTable family (hright mapped realized) oracle
       (⟨mapped, realized, (fun prior ↦ split.1 (Sum.inl prior)), split.2⟩ :
        SimulatorCoins (Point := Point) (Outcome := Outcome)
          sites fixedPoints rightSchedule)) = input
    rw [hrun]
    dsimp only
    rw [htranslated]
    let family := points fixedPoints
      (rightSchedule translated answers) answers
    have hsplit :
        splitTable family (hright translated answers) oracle =
          (Sum.elim priorAnswers answers, outside) := by
      exact (splitTable family (hright translated answers)).apply_symm_apply _
    have hprotected : ∀ prior,
        (splitTable family (hright translated answers) oracle).1
            (Sum.inl prior) = priorAnswers prior := by
      intro prior
      rw [hsplit]
      rfl
    have houtside :
        (splitTable family (hright translated answers) oracle).2 = outside := by
      exact congrArg Prod.snd hsplit
    have hpair :
        ((fun prior ↦
            (splitTable family (hright translated answers) oracle).1
              (Sum.inl prior)),
          (splitTable family (hright translated answers) oracle).2) =
            (priorAnswers, outside) := by
      apply Prod.ext
      · funext prior
        exact hprotected prior
      · exact houtside
    exact congrArg
      (fun pair ↦
        (⟨translated, answers, pair⟩ :
          SimulatorCoins (Point := Point) (Outcome := Outcome)
            sites fixedPoints rightSchedule)) hpair

def honestMachine {sites : ℕ}
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (fixedPoints : Prior → Point)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State → (Prior → Outcome) →
      RandomOracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × RandomOracle (Point := Point) (Outcome := Outcome)) :
    View :=
  let answers := run (schedule input.1) input.2 sites
  continueWith (state input.1 answers)
    (fun prior ↦ input.2 (fixedPoints prior)) input.2 answers

noncomputable def programmedMachine (sites : ℕ)
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins answers,
      Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (continueWith : State → (Prior → Outcome) →
      RandomOracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites fixedPoints rightSchedule) : View :=
  let oracle := programmedOracle sites fixedPoints rightSchedule hright input
  continueWith (state input.1 input.2.1) input.2.2.1 oracle input.2.1

/-- Honest execution and the straightline look-ahead simulator have exactly
equal full-view distributions while retaining the prior adversary view. -/
theorem simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (fixedPoints : Prior → Point)
    (leftSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (rightSchedule : AlgCoins → History (Outcome := Outcome) sites →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint
          (rightSchedule (answerEquiv answers coins) answers) answers site =
        tracePoint (leftSchedule coins) answers site)
    (hright : ∀ coins answers,
      Injective
        (points fixedPoints (rightSchedule coins answers) answers))
    (continueWith : State → (Prior → Outcome) →
      RandomOracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × RandomOracle (Point := Point) (Outcome := Outcome))).map
        (honestMachine leftState fixedPoints leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (SimulatorCoins (Point := Point) (Outcome := Outcome)
          sites fixedPoints rightSchedule)).map
        (programmedMachine sites rightState fixedPoints rightSchedule hright
          continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule htrace
      hright)
  intro input
  let answers := run (leftSchedule input.1) input.2 sites
  let translated := answerEquiv answers input.1
  let mapped := coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule
    htrace hright input
  have horacle :
      programmedOracle sites fixedPoints rightSchedule hright mapped =
        input.2 := by
    exact congrArg Prod.snd
      ((coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule htrace
        hright).symm_apply_apply input)
  have hprotected : ∀ prior,
      mapped.2.2.1 prior = input.2 (fixedPoints prior) := by
    intro prior
    change
      (splitTable
        (points fixedPoints (rightSchedule translated answers) answers)
        (hright translated answers) input.2).1 (Sum.inl prior) = _
    exact splitTable_programmed
      (points fixedPoints (rightSchedule translated answers) answers)
      (hright translated answers) input.2 (Sum.inl prior)
  change
    continueWith (leftState input.1 answers)
        (fun prior ↦ input.2 (fixedPoints prior)) input.2 answers =
      continueWith (rightState translated answers) mapped.2.2.1
        (programmedOracle sites fixedPoints rightSchedule hright mapped)
        answers
  rw [horacle, hstate input.1 answers]
  apply congrArg (fun priorAnswers ↦
    continueWith (rightState translated answers) priorAnswers input.2 answers)
  funext prior
  exact (hprotected prior).symm

end VeiledFlock.ProtectedLookaheadOperationalSimulator

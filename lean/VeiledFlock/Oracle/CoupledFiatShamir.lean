import VeiledFlock.Oracle.AdaptiveOracleProgramming
import VeiledFlock.Core.Probability

/-!
# Answer-indexed algebraic simulation with an unchanged random oracle

The strongest Fiat--Shamir coupling does not retarget oracle points at all.
For the correct masking bijection, the honest and simulated serialized proof
prefixes are identical.  Therefore their causal schedules are identical after
translation.  The algebraic translation is selected by the answer vector
actually obtained from the unchanged oracle.

This formulation exposes the entire oracle to arbitrary post-processing, so
it covers adaptive adversary queries made after the proof rather than only a
predeclared query list.
-/

namespace VeiledFlock.CoupledFiatShamir

open VeiledFlock.AdaptiveOracleProgramming

variable {AlgCoins State Point Outcome View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Joint coin equivalence selected by honest Fiat--Shamir answers.  The
random-oracle table is literally unchanged. -/
def coinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hschedule : ∀ coins answers,
      rightSchedule (answerEquiv answers coins) = leftSchedule coins) :
    (AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) ≃
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) where
  toFun input :=
    let answers := run (leftSchedule input.1) input.2 sites
    (answerEquiv answers input.1, input.2)
  invFun output :=
    let answers := run (rightSchedule output.1) output.2 sites
    ((answerEquiv answers).symm output.1, output.2)
  left_inv input := by
    rcases input with ⟨coins, oracle⟩
    let answers := run (leftSchedule coins) oracle sites
    have hs := hschedule coins answers
    change
      ((answerEquiv
          (run (rightSchedule (answerEquiv answers coins)) oracle sites)).symm
          (answerEquiv answers coins), oracle) = (coins, oracle)
    rw [hs]
    change
      ((answerEquiv answers).symm (answerEquiv answers coins), oracle) =
        (coins, oracle)
    simp
  right_inv output := by
    rcases output with ⟨translated, oracle⟩
    let answers := run (rightSchedule translated) oracle sites
    let coins := (answerEquiv answers).symm translated
    have hs := hschedule coins answers
    have htranslated : answerEquiv answers coins = translated := by
      simp [coins]
    rw [htranslated] at hs
    change
      (answerEquiv (run (leftSchedule coins) oracle sites) coins, oracle) =
        (translated, oracle)
    rw [← hs]
    change (answerEquiv answers coins, oracle) = (translated, oracle)
    rw [htranslated]

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
@[simp]
theorem coinEquiv_oracle {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hschedule : ∀ coins answers,
      rightSchedule (answerEquiv answers coins) = leftSchedule coins)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).2 =
      input.2 := rfl

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem coinEquiv_state {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hschedule : ∀ coins answers,
      rightSchedule (answerEquiv answers coins) = leftSchedule coins)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).1 =
      answerEquiv (run (leftSchedule input.1) input.2 sites) input.1 := rfl

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem coinEquiv_answers {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hschedule : ∀ coins answers,
      rightSchedule (answerEquiv answers coins) = leftSchedule coins)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    run (rightSchedule
        (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).1)
      (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).2
      sites =
      run (leftSchedule input.1) input.2 sites := by
  rw [coinEquiv_state, coinEquiv_oracle,
    hschedule input.1 (run (leftSchedule input.1) input.2 sites)]

/-- A complete execution view.  `continueWith` receives the unchanged full
oracle, so it may run any bounded adaptive distinguisher after seeing the
proof. -/
def machine {sites : ℕ}
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) : View :=
  let answers := run (schedule input.1) input.2 sites
  continueWith (state input.1 answers) input.2 answers

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- Pointwise equality of the algebraic proof, every Fiat--Shamir answer, and
the complete oracle table. -/
theorem machine_transport {sites : ℕ}
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
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    machine leftState leftSchedule continueWith input =
      machine rightState rightSchedule continueWith
        (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input) := by
  let answers := run (leftSchedule input.1) input.2 sites
  have hanswers := coinEquiv_answers answerEquiv leftSchedule rightSchedule
    hschedule input
  change
    continueWith (leftState input.1 answers) input.2 answers =
      continueWith
        (rightState
          (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).1
          (run (rightSchedule
            (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).1)
            (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).2
            sites))
        (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).2
        (run (rightSchedule
          (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).1)
          (coinEquiv answerEquiv leftSchedule rightSchedule hschedule input).2
          sites)
  rw [hanswers, coinEquiv_oracle, coinEquiv_state,
    ← hstate input.1 answers]

omit [DecidableEq AlgCoins] [DecidableEq Outcome] in
/-- Exact zero-cost Fiat--Shamir hybrid with a fully preserved oracle. -/
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
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
        (machine leftState leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
          (machine rightState rightSchedule continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv answerEquiv leftSchedule rightSchedule hschedule)
  exact machine_transport leftState rightState answerEquiv hstate leftSchedule
    rightSchedule hschedule continueWith

/-! ## Causal trace correspondence

For the production simulator, translating an early mask may use challenges
sampled later by the simulator.  Consequently the two schedules need only
agree along the complete proposed answer trace, not on prefixes inconsistent
with that proposal.  The following stronger-purpose formulation proves that
this causal correspondence is sufficient for a joint coin equivalence.
-/

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- If every translated causal point agrees along the honest proposed answer
vector, running the translated schedule on the same oracle realizes exactly
that vector. -/
theorem run_translated_eq {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint (rightSchedule (answerEquiv answers coins)) answers site =
        tracePoint (leftSchedule coins) answers site)
    (coins : AlgCoins) (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    let answers := run (leftSchedule coins) oracle sites
    run (rightSchedule (answerEquiv answers coins)) oracle sites = answers := by
  let answers := run (leftSchedule coins) oracle sites
  let translated := answerEquiv answers coins
  have hround : ∀ count (hle : count ≤ sites),
      run (rightSchedule translated) oracle count =
        fun site ↦ answers (Fin.castLE hle site) := by
    intro count
    induction count with
    | zero =>
        intro hle
        funext site
        exact Fin.elim0 site
    | succ count ih =>
        intro hle
        funext site
        refine Fin.lastCases ?_ (fun prior ↦ ?_) site
        · rw [run_succ_last]
          have hprevious : run (rightSchedule translated) oracle count =
              priorAnswers answers ⟨count, Nat.lt_of_succ_le hle⟩ := by
            rw [ih (Nat.le_trans (Nat.le_succ count) hle)]
            funext prior
            rfl
          rw [hprevious]
          change oracle
              (tracePoint (rightSchedule translated) answers
                ⟨count, Nat.lt_of_succ_le hle⟩) = _
          rw [show Fin.castLE hle (Fin.last count) =
              ⟨count, Nat.lt_of_succ_le hle⟩ by
            apply Fin.ext
            rfl]
          rw [show translated = answerEquiv answers coins by rfl,
            htrace coins answers]
          exact oracle_tracePoint_run (leftSchedule coins) oracle _
        · rw [run_succ_castSucc,
            ih (Nat.le_trans (Nat.le_succ count) hle)]
          rfl
  simpa only [Fin.castLE_refl] using hround sites (le_refl sites)

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- The inverse translated schedule realizes its own proposed answer vector
as well. -/
theorem run_recovered_eq {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint (rightSchedule (answerEquiv answers coins)) answers site =
        tracePoint (leftSchedule coins) answers site)
    (translated : AlgCoins)
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    let answers := run (rightSchedule translated) oracle sites
    run (leftSchedule ((answerEquiv answers).symm translated)) oracle sites =
      answers := by
  let answers := run (rightSchedule translated) oracle sites
  let reverseEquiv := fun answers ↦ (answerEquiv answers).symm
  have hreverse : ∀ coins proposed site,
      tracePoint
          (leftSchedule (reverseEquiv proposed coins)) proposed site =
        tracePoint (rightSchedule coins) proposed site := by
    intro coins proposed site
    have h := htrace ((answerEquiv proposed).symm coins) proposed site
    simpa only [reverseEquiv, Equiv.apply_symm_apply] using h.symm
  exact run_translated_eq reverseEquiv rightSchedule leftSchedule hreverse
    translated oracle

/-- Answer-indexed coin equivalence under causal trace correspondence. -/
def traceCoinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint (rightSchedule (answerEquiv answers coins)) answers site =
        tracePoint (leftSchedule coins) answers site) :
    (AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) ≃
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) where
  toFun input :=
    let answers := run (leftSchedule input.1) input.2 sites
    (answerEquiv answers input.1, input.2)
  invFun output :=
    let answers := run (rightSchedule output.1) output.2 sites
    ((answerEquiv answers).symm output.1, output.2)
  left_inv input := by
    rcases input with ⟨coins, oracle⟩
    let answers := run (leftSchedule coins) oracle sites
    have hrun := run_translated_eq answerEquiv leftSchedule rightSchedule
      htrace coins oracle
    change run (rightSchedule (answerEquiv answers coins)) oracle sites =
      answers at hrun
    change
      ((answerEquiv
          (run (rightSchedule (answerEquiv answers coins)) oracle sites)).symm
          (answerEquiv answers coins), oracle) = (coins, oracle)
    rw [hrun]
    simp
  right_inv output := by
    rcases output with ⟨translated, oracle⟩
    let answers := run (rightSchedule translated) oracle sites
    have hrun := run_recovered_eq answerEquiv leftSchedule rightSchedule
      htrace translated oracle
    change
      run (leftSchedule ((answerEquiv answers).symm translated)) oracle sites =
        answers at hrun
    change
      (answerEquiv
          (run (leftSchedule ((answerEquiv answers).symm translated)) oracle
            sites)
          ((answerEquiv answers).symm translated), oracle) =
        (translated, oracle)
    rw [hrun]
    simp

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
@[simp]
theorem traceCoinEquiv_oracle {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint (rightSchedule (answerEquiv answers coins)) answers site =
        tracePoint (leftSchedule coins) answers site)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace input).2 =
      input.2 := rfl

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem traceCoinEquiv_answers {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (htrace : ∀ coins answers site,
      tracePoint (rightSchedule (answerEquiv answers coins)) answers site =
        tracePoint (leftSchedule coins) answers site)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    run (rightSchedule
        (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace input).1)
      (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace input).2
      sites = run (leftSchedule input.1) input.2 sites := by
  exact run_translated_eq answerEquiv leftSchedule rightSchedule htrace
    input.1 input.2

omit [DecidableEq AlgCoins] [DecidableEq Outcome] in
/-- Exact simulator theorem from causal trace correspondence, preserving the
entire random oracle pointwise. -/
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
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
        (machine leftState leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
          (machine rightState rightSchedule continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace)
  intro input
  let answers := run (leftSchedule input.1) input.2 sites
  have hanswers := traceCoinEquiv_answers answerEquiv leftSchedule
    rightSchedule htrace input
  change
    continueWith (leftState input.1 answers) input.2 answers =
      continueWith
        (rightState
          (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace
            input).1
          (run (rightSchedule
            (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace
              input).1)
            (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace
              input).2 sites))
        (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace input).2
        (run (rightSchedule
          (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace input).1)
          (traceCoinEquiv answerEquiv leftSchedule rightSchedule htrace input).2
          sites)
  rw [hanswers, traceCoinEquiv_oracle]
  change
    continueWith (leftState input.1 answers) input.2 answers =
      continueWith
        (rightState (answerEquiv answers input.1) answers) input.2 answers
  rw [hstate]

end VeiledFlock.CoupledFiatShamir

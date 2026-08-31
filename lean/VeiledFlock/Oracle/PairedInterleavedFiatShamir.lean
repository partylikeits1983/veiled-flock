import VeiledFlock.Oracle.DependentProtectedAdaptiveOracle
import VeiledFlock.Core.Probability

/-!
# Paired interleaved algebraic and oracle transport

The production zero-knowledge hybrid changes two adaptive objects at once:
the algebraic masking coins are translated after the Fiat--Shamir answers are
known, while honest salted-Merkle inputs are replaced by simulator inputs that
may depend on those same coins and answers.  This module gives one exact
finite-oracle bijection for that joint move.
-/

namespace VeiledFlock.PairedInterleavedFiatShamir

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.DependentProtectedAdaptiveOracle

variable {AlgCoins State Prior Point Outcome View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- For fixed algebraic coins and a candidate answer vector, retarget both the
dependent protected family and the adaptive protocol trace. -/
noncomputable def oracleEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers))
    (coins : AlgCoins) (answers : History (Outcome := Outcome) sites) :
    (Point → Outcome) ≃ (Point → Outcome) :=
  retarget (leftFixed coins) (rightFixed (answerEquiv answers coins))
    (leftSchedule coins) (rightSchedule (answerEquiv answers coins))
    (hleft coins) (hright (answerEquiv answers coins))

omit [DecidableEq Point] in
omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- The answer-dependent retargeting preserves the complete adaptive answer
vector for every input oracle. -/
theorem oracleEquiv_answers {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers))
    (coins : AlgCoins) (answers : History (Outcome := Outcome) sites)
    (oracle : Point → Outcome) :
    run (rightSchedule (answerEquiv answers coins))
        (oracleEquiv answerEquiv leftFixed rightFixed leftSchedule
          rightSchedule hleft hright coins answers oracle) sites =
      run (leftSchedule coins) oracle sites := by
  exact retarget_answers (leftFixed coins)
    (rightFixed (answerEquiv answers coins))
    (leftSchedule coins) (rightSchedule (answerEquiv answers coins))
    (hleft coins) (hright (answerEquiv answers coins)) oracle

omit [DecidableEq Point] in
omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- Corresponding protected inputs receive the same oracle answers. -/
theorem oracleEquiv_protected {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers))
    (coins : AlgCoins) (answers : History (Outcome := Outcome) sites)
    (oracle : Point → Outcome) (prior : Prior) :
    let realized := run (leftSchedule coins) oracle sites
    oracleEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright coins answers oracle
        (rightFixed (answerEquiv answers coins) realized prior) =
      oracle (leftFixed coins realized prior) := by
  exact retarget_protected (leftFixed coins)
    (rightFixed (answerEquiv answers coins))
    (leftSchedule coins) (rightSchedule (answerEquiv answers coins))
    (hleft coins) (hright (answerEquiv answers coins)) oracle prior

/-- Read the honest answer vector, translate the algebraic tape with it, then
retarget the dependent protected family and adaptive trace. -/
noncomputable def coinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers)) :
    (AlgCoins × (Point → Outcome)) ≃ (AlgCoins × (Point → Outcome)) where
  toFun input :=
    let answers := run (leftSchedule input.1) input.2 sites
    (answerEquiv answers input.1,
      oracleEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright input.1 answers input.2)
  invFun output :=
    let answers := run (rightSchedule output.1) output.2 sites
    let coins := (answerEquiv answers).symm output.1
    (coins,
      (oracleEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright coins answers).symm output.2)
  left_inv input := by
    rcases input with ⟨coins, oracle⟩
    let answers := run (leftSchedule coins) oracle sites
    let translated := answerEquiv answers coins
    let transported := oracleEquiv answerEquiv leftFixed rightFixed leftSchedule
      rightSchedule hleft hright coins answers oracle
    have hrun : run (rightSchedule translated) transported sites = answers := by
      exact oracleEquiv_answers answerEquiv leftFixed rightFixed leftSchedule
        rightSchedule hleft hright coins answers oracle
    change
      (let recoveredAnswers := run (rightSchedule translated) transported sites
       let recoveredCoins := (answerEquiv recoveredAnswers).symm translated
       (recoveredCoins,
         (oracleEquiv answerEquiv leftFixed rightFixed leftSchedule
           rightSchedule hleft hright recoveredCoins
           recoveredAnswers).symm transported)) = (coins, oracle)
    rw [hrun]
    dsimp only
    have hrecovered : (answerEquiv answers).symm translated = coins := by
      simp [translated]
    rw [hrecovered]
    change
      (coins,
        (oracleEquiv answerEquiv leftFixed rightFixed leftSchedule
          rightSchedule hleft hright coins answers).symm transported) =
        (coins, oracle)
    rw [show transported =
        oracleEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
          hleft hright coins answers oracle by rfl]
    simp
  right_inv output := by
    rcases output with ⟨translated, oracle⟩
    let answers := run (rightSchedule translated) oracle sites
    let coins := (answerEquiv answers).symm translated
    let transportedBack :=
      (oracleEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright coins answers).symm oracle
    have hrecovered : answerEquiv answers coins = translated := by
      simp [coins]
    have hrun : run (leftSchedule coins) transportedBack sites = answers := by
      have hforward := oracleEquiv_answers answerEquiv leftFixed rightFixed
        leftSchedule rightSchedule hleft hright coins answers transportedBack
      have htransport :
          oracleEquiv answerEquiv leftFixed rightFixed leftSchedule
              rightSchedule hleft hright coins answers transportedBack =
            oracle := by
        simp [transportedBack]
      rw [htransport] at hforward
      rw [hrecovered] at hforward
      exact hforward.symm
    change
      (let recoveredAnswers := run (leftSchedule coins) transportedBack sites
       (answerEquiv recoveredAnswers coins,
         oracleEquiv answerEquiv leftFixed rightFixed leftSchedule
           rightSchedule hleft hright coins recoveredAnswers
           transportedBack)) = (translated, oracle)
    rw [hrun]
    dsimp only
    rw [hrecovered]
    rw [show transportedBack =
        (oracleEquiv answerEquiv leftFixed rightFixed leftSchedule
          rightSchedule hleft hright coins answers).symm oracle by rfl]
    simp

omit [DecidableEq Point] in
omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem coinEquiv_answers {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers))
    (input : AlgCoins × (Point → Outcome)) :
    run (rightSchedule
        (coinEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
          hleft hright input).1)
      (coinEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright input).2 sites =
      run (leftSchedule input.1) input.2 sites := by
  change
    run (rightSchedule
        (answerEquiv (run (leftSchedule input.1) input.2 sites) input.1))
      (oracleEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright input.1 (run (leftSchedule input.1) input.2 sites)
        input.2) sites = _
  exact oracleEquiv_answers answerEquiv leftFixed rightFixed leftSchedule
    rightSchedule hleft hright input.1
    (run (leftSchedule input.1) input.2 sites) input.2

omit [DecidableEq Point] in
omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem coinEquiv_protected {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers))
    (input : AlgCoins × (Point → Outcome)) (prior : Prior) :
    let answers := run (leftSchedule input.1) input.2 sites
    (coinEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright input).2
        (rightFixed (answerEquiv answers input.1) answers prior) =
      input.2 (leftFixed input.1 answers prior) := by
  dsimp only
  exact oracleEquiv_protected answerEquiv leftFixed rightFixed leftSchedule
    rightSchedule hleft hright input.1
    (run (leftSchedule input.1) input.2 sites) input.2 prior

noncomputable def machine {sites : ℕ}
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (fixedPoints : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × (Point → Outcome)) : View :=
  let answers := run (schedule input.1) input.2 sites
  continueWith (state input.1 answers)
    (fun prior => input.2 (fixedPoints input.1 answers prior)) answers

omit [DecidableEq Point] in
omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- Exact pointwise transport of the visible algebraic state, every paired
protected answer, and the full adaptive oracle trace. -/
theorem machine_transport {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × (Point → Outcome)) :
    machine leftState leftFixed leftSchedule continueWith input =
      machine rightState rightFixed rightSchedule continueWith
        (coinEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
          hleft hright input) := by
  let answers := run (leftSchedule input.1) input.2 sites
  have hanswers := coinEquiv_answers answerEquiv leftFixed rightFixed
    leftSchedule rightSchedule hleft hright input
  have hprotected := coinEquiv_protected answerEquiv leftFixed rightFixed
    leftSchedule rightSchedule hleft hright input
  change
    continueWith (leftState input.1 answers)
        (fun prior => input.2 (leftFixed input.1 answers prior)) answers =
      continueWith
        (rightState
          (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
            rightSchedule hleft hright input).1
          (run (rightSchedule
            (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
              rightSchedule hleft hright input).1)
            (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
              rightSchedule hleft hright input).2 sites))
        (fun prior =>
          (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
            rightSchedule hleft hright input).2
            (rightFixed
              (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
                rightSchedule hleft hright input).1
              (run (rightSchedule
                (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
                  rightSchedule hleft hright input).1)
                (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
                  rightSchedule hleft hright input).2 sites) prior))
        (run (rightSchedule
          (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
            rightSchedule hleft hright input).1)
          (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
            rightSchedule hleft hright input).2 sites)
  rw [hanswers]
  have hcoins :
      (coinEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
        hleft hright input).1 = answerEquiv answers input.1 := rfl
  rw [hcoins, ← hstate input.1 answers]
  apply congrArg (fun protectedAnswers =>
    continueWith (leftState input.1 answers) protectedAnswers answers)
  funext prior
  exact (hprotected prior).symm

omit [DecidableEq AlgCoins] [DecidableEq Outcome] in
/-- Uniform real and simulator views are exactly equal on the good event. -/
theorem simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins answers,
      Injective (points (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective (points (rightFixed coins) (rightSchedule coins) answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype (AlgCoins × (Point → Outcome))).map
        (machine leftState leftFixed leftSchedule continueWith) =
      (PMF.uniformOfFintype (AlgCoins × (Point → Outcome))).map
        (machine rightState rightFixed rightSchedule continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv answerEquiv leftFixed rightFixed leftSchedule rightSchedule
      hleft hright)
  exact machine_transport leftState rightState answerEquiv hstate leftFixed
    rightFixed leftSchedule rightSchedule hleft hright continueWith

end VeiledFlock.PairedInterleavedFiatShamir

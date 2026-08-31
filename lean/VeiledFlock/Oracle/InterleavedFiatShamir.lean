import VeiledFlock.Oracle.ProtectedAdaptiveOracle

/-!
# Interleaved algebraic simulation and Fiat--Shamir programming

The algebraic simulator chooses its masking translation as a function of the
Fiat--Shamir answer vector.  Conversely, the transcript points programmed by
the random-oracle simulator depend on the translated algebraic coins and on
the earlier answers.  This module proves the required joint reparameterization
instead of treating those two correlated objects as independent views.

The theorem is exact on the good event: every protected adversary answer and
every adaptive protocol answer is preserved pointwise.  Statistical distance
enters only when the freshness and rejection-sampling good events are removed.
-/

namespace VeiledFlock.InterleavedFiatShamir

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ProtectedAdaptiveOracle

variable {AlgCoins State Prior Point Outcome View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Finite Prior] [Fintype Point] [DecidableEq Point] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- Pairwise distinctness of the right-hand schedule, phrased at a fixed
translated algebraic coin.  The inverse image may depend on the candidate
answer vector; this is why the premise is indexed by both objects. -/
theorem right_injective_at {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (translated : AlgCoins) (answers : History (Outcome := Outcome) sites) :
    Injective (points fixedPoints (rightSchedule translated) answers) := by
  simpa using hright ((answerEquiv answers).symm translated) answers

/-- For fixed algebraic coins and their realized answer vector, retarget the
complete oracle table from the honest schedule to the translated schedule.
Protected adversary points are coordinates of both oracle splittings. -/
noncomputable def oracleEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (coins : AlgCoins) (answers : History (Outcome := Outcome) sites) :
    RandomOracle (Point := Point) (Outcome := Outcome) ≃
      RandomOracle (Point := Point) (Outcome := Outcome) :=
  retarget fixedPoints (leftSchedule coins)
    (rightSchedule (answerEquiv answers coins)) (hleft coins)
    (right_injective_at answerEquiv fixedPoints rightSchedule hright
      (answerEquiv answers coins))

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem oracleEquiv_answers {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (coins : AlgCoins) (answers : History (Outcome := Outcome) sites)
    (oracle : RandomOracle (Point := Point) (Outcome := Outcome)) :
    run (rightSchedule (answerEquiv answers coins))
        (oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
          hright coins answers oracle) sites =
      run (leftSchedule coins) oracle sites := by
  exact retarget_answers fixedPoints (leftSchedule coins)
    (rightSchedule (answerEquiv answers coins)) (hleft coins)
    (right_injective_at answerEquiv fixedPoints rightSchedule hright
      (answerEquiv answers coins)) oracle

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem oracleEquiv_protected {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (coins : AlgCoins) (answers : History (Outcome := Outcome) sites)
    (oracle : RandomOracle (Point := Point) (Outcome := Outcome))
    (prior : Prior) :
    oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
        hright coins answers oracle (fixedPoints prior) =
      oracle (fixedPoints prior) := by
  exact retarget_protected fixedPoints (leftSchedule coins)
    (rightSchedule (answerEquiv answers coins)) (hleft coins)
    (right_injective_at answerEquiv fixedPoints rightSchedule hright
      (answerEquiv answers coins)) oracle prior

/-- The joint coin equivalence.  It first reads the answer vector actually
seen in the honest execution, uses that vector to translate the algebraic
coins, and retargets the oracle to the resulting simulated schedule.  Its
inverse reads the preserved vector from the simulated execution. -/
noncomputable def coinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers)) :
    (AlgCoins × RandomOracle (Point := Point) (Outcome := Outcome)) ≃
      (AlgCoins × RandomOracle (Point := Point) (Outcome := Outcome)) where
  toFun input :=
    let answers := run (leftSchedule input.1) input.2 sites
    (answerEquiv answers input.1,
      oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
        hright input.1 answers input.2)
  invFun output :=
    let answers := run (rightSchedule output.1) output.2 sites
    let coins := (answerEquiv answers).symm output.1
    (coins,
      (oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
        hright coins answers).symm output.2)
  left_inv input := by
    rcases input with ⟨coins, oracle⟩
    let answers := run (leftSchedule coins) oracle sites
    let translated := answerEquiv answers coins
    let transported := oracleEquiv answerEquiv fixedPoints leftSchedule
      rightSchedule hleft hright coins answers oracle
    have hrun : run (rightSchedule translated) transported sites = answers := by
      exact oracleEquiv_answers answerEquiv fixedPoints leftSchedule
        rightSchedule hleft hright coins answers oracle
    change
      (let recoveredAnswers := run (rightSchedule translated) transported sites
       let recoveredCoins := (answerEquiv recoveredAnswers).symm translated
       (recoveredCoins,
         (oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
           hright recoveredCoins recoveredAnswers).symm transported)) =
        (coins, oracle)
    rw [hrun]
    dsimp only
    have hrecovered : (answerEquiv answers).symm translated = coins := by
      simp [translated]
    rw [hrecovered]
    change
      (coins,
        (oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
          hright coins answers).symm transported) = (coins, oracle)
    rw [show transported =
        oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
          hright coins answers oracle by rfl]
    simp
  right_inv output := by
    rcases output with ⟨translated, oracle⟩
    let answers := run (rightSchedule translated) oracle sites
    let coins := (answerEquiv answers).symm translated
    let transportedBack :=
      (oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
        hright coins answers).symm oracle
    have hrecovered : answerEquiv answers coins = translated := by
      simp [coins]
    have hrun : run (leftSchedule coins) transportedBack sites = answers := by
      have hforward := oracleEquiv_answers answerEquiv fixedPoints leftSchedule
        rightSchedule hleft hright coins answers transportedBack
      have htransport :
          oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
              hright coins answers transportedBack = oracle := by
        simp [transportedBack]
      rw [htransport] at hforward
      rw [hrecovered] at hforward
      exact hforward.symm
    change
      (let recoveredAnswers := run (leftSchedule coins) transportedBack sites
       (answerEquiv recoveredAnswers coins,
         oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
           hright coins recoveredAnswers transportedBack)) =
        (translated, oracle)
    rw [hrun]
    dsimp only
    rw [hrecovered]
    change
      (translated,
        oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
          hright coins answers transportedBack) = (translated, oracle)
    rw [show transportedBack =
        (oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
          hright coins answers).symm oracle by rfl]
    simp

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem coinEquiv_answers {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (input : AlgCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) :
    run (rightSchedule
        (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
          hright input).1)
      (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
        hright input).2 sites =
      run (leftSchedule input.1) input.2 sites := by
  change
    run (rightSchedule
        (answerEquiv (run (leftSchedule input.1) input.2 sites) input.1))
      (oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
        hright input.1 (run (leftSchedule input.1) input.2 sites) input.2)
      sites = _
  exact oracleEquiv_answers answerEquiv fixedPoints leftSchedule rightSchedule
    hleft hright input.1 (run (leftSchedule input.1) input.2 sites) input.2

omit [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
theorem coinEquiv_protected {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (input : AlgCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) (prior : Prior) :
    (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft hright
        input).2 (fixedPoints prior) =
      input.2 (fixedPoints prior) := by
  change oracleEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
      hright input.1 (run (leftSchedule input.1) input.2 sites) input.2
      (fixedPoints prior) = _
  exact oracleEquiv_protected answerEquiv fixedPoints leftSchedule
    rightSchedule hleft hright input.1
    (run (leftSchedule input.1) input.2 sites) input.2 prior

noncomputable def machine {sites : ℕ}
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (fixedPoints : Prior → Point)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) : View :=
  let answers := run (schedule input.1) input.2 sites
  continueWith (state input.1 answers)
    (fun prior => input.2 (fixedPoints prior)) answers

/-- Exact interleaved simulator theorem.  The visible algebraic state, the
complete protected oracle prefix, and the complete Fiat--Shamir answer vector
are pointwise identical after the joint coin bijection. -/
theorem machine_transport {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) :
    machine leftState fixedPoints leftSchedule continueWith input =
      machine rightState fixedPoints rightSchedule continueWith
        (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
          hright input) := by
  let answers := run (leftSchedule input.1) input.2 sites
  have hanswers := coinEquiv_answers answerEquiv fixedPoints leftSchedule
    rightSchedule hleft hright input
  have hprotected := coinEquiv_protected answerEquiv fixedPoints leftSchedule
    rightSchedule hleft hright input
  change
    continueWith (leftState input.1 answers)
        (fun prior => input.2 (fixedPoints prior)) answers =
      continueWith
        (rightState
          (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
            hright input).1
          (run (rightSchedule
            (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
              hright input).1)
            (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
              hright input).2 sites))
        (fun prior =>
          (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
            hright input).2 (fixedPoints prior))
        (run (rightSchedule
          (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
            hright input).1)
          (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
            hright input).2 sites)
  rw [hanswers]
  have hcoins :
      (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft
        hright input).1 = answerEquiv answers input.1 := rfl
  rw [hcoins, ← hstate input.1 answers]
  apply congrArg (fun protectedAnswers =>
    continueWith (leftState input.1 answers) protectedAnswers answers)
  funext prior
  exact (hprotected prior).symm

theorem simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (fixedPoints : Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points fixedPoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points fixedPoints (rightSchedule (answerEquiv answers coins))
          answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × RandomOracle (Point := Point) (Outcome := Outcome))).map
        (machine leftState fixedPoints leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (AlgCoins × RandomOracle (Point := Point) (Outcome := Outcome))).map
          (machine rightState fixedPoints rightSchedule continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv answerEquiv fixedPoints leftSchedule rightSchedule hleft hright)
  exact machine_transport leftState rightState answerEquiv hstate fixedPoints
    leftSchedule rightSchedule hleft hright continueWith

end VeiledFlock.InterleavedFiatShamir

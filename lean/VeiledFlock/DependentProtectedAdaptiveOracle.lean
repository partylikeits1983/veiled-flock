import VeiledFlock.ProtectedAdaptiveOracle

/-!
# Answer-dependent protected adaptive-oracle splitting

Merkle inputs in VEIL--FLOCK are not a fixed family: the Hadamard tree is
constructed from earlier Fiat--Shamir answers.  This module generalizes the
protected adaptive-oracle split so the protected family may depend on the
complete realized answer vector.  The split remains an exact finite
equivalence because that vector is recovered by running the causal schedule.
-/

namespace VeiledFlock.DependentProtectedAdaptiveOracle

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ProtectedAdaptiveOracle

variable {Prior Point Outcome : Type*}
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]

abbrev RandomOracle := Point → Outcome

/-- Answer-dependent protected points followed by the adaptive trace. -/
def points {sites : ℕ}
    (fixedPoints : History (Outcome := Outcome) sites → Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (answers : History (Outcome := Outcome) sites) : Prior ⊕ Fin sites → Point
  | .inl prior => fixedPoints answers prior
  | .inr site => tracePoint next answers site

/-- Independent coordinates of a finite oracle at the dependent protected
family, the adaptive trace, and their complement. -/
abbrev Coins {sites : ℕ}
    (fixedPoints : History (Outcome := Outcome) sites → Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome)) :=
  Σ answers : History (Outcome := Outcome) sites,
    (Prior → Outcome) ×
      (Outside (points fixedPoints next answers) → Outcome)

noncomputable def simulatedOracle {sites : ℕ}
    (fixedPoints : History (Outcome := Outcome) sites → Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) :
    RandomOracle (Point := Point) (Outcome := Outcome) :=
  (splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
    (Sum.elim coins.2.1 coins.1, coins.2.2)

@[simp]
theorem simulatedOracle_protected {sites : ℕ}
    (fixedPoints : History (Outcome := Outcome) sites → Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) (prior : Prior) :
    simulatedOracle fixedPoints next hinjective coins
        (fixedPoints coins.1 prior) = coins.2.1 prior := by
  change
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2))
        (points fixedPoints next coins.1 (.inl prior)) = coins.2.1 prior
  have h := splitTable_programmed (points fixedPoints next coins.1)
    (hinjective coins.1)
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2)) (.inl prior)
  rw [(splitTable (points fixedPoints next coins.1)
    (hinjective coins.1)).apply_symm_apply] at h
  exact h.symm

@[simp]
theorem simulatedOracle_trace {sites : ℕ}
    (fixedPoints : History (Outcome := Outcome) sites → Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) (site : Fin sites) :
    simulatedOracle fixedPoints next hinjective coins
        (tracePoint next coins.1 site) = coins.1 site := by
  change
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2))
        (points fixedPoints next coins.1 (.inr site)) = coins.1 site
  have h := splitTable_programmed (points fixedPoints next coins.1)
    (hinjective coins.1)
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2)) (.inr site)
  rw [(splitTable (points fixedPoints next coins.1)
    (hinjective coins.1)).apply_symm_apply] at h
  exact h.symm

theorem run_simulatedOracle {sites : ℕ}
    (fixedPoints : History (Outcome := Outcome) sites → Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) :
    run next (simulatedOracle fixedPoints next hinjective coins) sites =
      coins.1 := by
  let oracle := simulatedOracle fixedPoints next hinjective coins
  have hround : ∀ rounds (hle : rounds ≤ sites),
      run next oracle rounds =
        fun site => coins.1 (Fin.castLE hle site) := by
    intro rounds
    induction rounds with
    | zero =>
        intro _
        funext site
        exact Fin.elim0 site
    | succ rounds inductionHypothesis =>
        intro hle
        funext site
        refine Fin.lastCases ?_ (fun prior => ?_) site
        · rw [run_succ_last]
          have hprevious : run next oracle rounds =
              priorAnswers coins.1 ⟨rounds, Nat.lt_of_succ_le hle⟩ := by
            rw [inductionHypothesis
              (Nat.le_trans (Nat.le_succ rounds) hle)]
            funext prior
            rfl
          rw [hprevious]
          change oracle
              (tracePoint next coins.1
                ⟨rounds, Nat.lt_of_succ_le hle⟩) = _
          rw [show Fin.castLE hle (Fin.last rounds) =
              ⟨rounds, Nat.lt_of_succ_le hle⟩ by
            apply Fin.ext
            rfl]
          exact simulatedOracle_trace fixedPoints next hinjective coins _
        · rw [run_succ_castSucc,
            inductionHypothesis (Nat.le_trans (Nat.le_succ rounds) hle)]
          rfl
  simpa only [Fin.castLE_refl] using hround sites (le_refl sites)

/-- Exact split of a finite oracle when protected points may be selected by
the realized answer vector. -/
noncomputable def split {sites : ℕ}
    (fixedPoints : History (Outcome := Outcome) sites → Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers)) :
    RandomOracle (Point := Point) (Outcome := Outcome) ≃
      Coins (sites := sites) fixedPoints next where
  toFun oracle :=
    let answers := run next oracle sites
    ⟨answers,
      (fun prior => oracle (fixedPoints answers prior)),
      (splitTable (points fixedPoints next answers) (hinjective answers)
        oracle).2⟩
  invFun := simulatedOracle fixedPoints next hinjective
  left_inv oracle := by
    let answers := run next oracle sites
    apply (splitTable (points fixedPoints next answers)
      (hinjective answers)).injective
    dsimp only [simulatedOracle]
    rw [(splitTable (points fixedPoints next answers)
      (hinjective answers)).apply_symm_apply]
    apply Prod.ext
    · funext site
      cases site with
      | inl prior =>
          rw [splitTable_programmed]
          rfl
      | inr protocolSite =>
          rw [splitTable_programmed]
          exact (oracle_tracePoint_run next oracle protocolSite).symm
    · rfl
  right_inv coins := by
    rcases coins with ⟨answers, protectedAnswers, outside⟩
    let input : Coins (sites := sites) fixedPoints next :=
      ⟨answers, protectedAnswers, outside⟩
    let oracle := simulatedOracle fixedPoints next hinjective input
    have hrun : run next oracle sites = answers :=
      run_simulatedOracle fixedPoints next hinjective input
    change
      (let realized := run next oracle sites
       (⟨realized,
          (fun prior => oracle (fixedPoints realized prior)),
          (splitTable (points fixedPoints next realized) (hinjective realized)
            oracle).2⟩ : Coins (sites := sites) fixedPoints next)) = input
    rw [hrun]
    dsimp only
    have hprotected :
        (fun prior => oracle (fixedPoints answers prior)) =
          protectedAnswers := by
      funext prior
      exact simulatedOracle_protected fixedPoints next hinjective input prior
    have houtside :
        (splitTable (points fixedPoints next answers) (hinjective answers)
          oracle).2 = outside := by
      change
        (splitTable (points fixedPoints next answers) (hinjective answers)
          ((splitTable (points fixedPoints next answers)
            (hinjective answers)).symm
              (Sum.elim protectedAnswers answers, outside))).2 = outside
      exact congrArg Prod.snd
        ((splitTable (points fixedPoints next answers)
          (hinjective answers)).apply_symm_apply
            (Sum.elim protectedAnswers answers, outside))
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Prod.ext hprotected houtside)

/-- Retarget answer-dependent protected points and the adaptive trace while
retaining the same answer coordinates. -/
noncomputable def retargetCoins {sites : ℕ}
    (leftFixed rightFixed :
      History (Outcome := Outcome) sites → Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points leftFixed left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points rightFixed right answers)) :
    Coins (sites := sites) leftFixed left ≃
      Coins (sites := sites) rightFixed right :=
  Equiv.sigmaCongrRight fun answers =>
    Equiv.prodCongr (Equiv.refl (Prior → Outcome))
      (Equiv.arrowCongr
        (VeiledFlock.OracleProgramming.unprogrammedRename
          (points leftFixed left answers) (points rightFixed right answers)
          (hleft answers) (hright answers))
        (Equiv.refl Outcome))

noncomputable def retarget {sites : ℕ}
    (leftFixed rightFixed :
      History (Outcome := Outcome) sites → Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points leftFixed left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points rightFixed right answers)) :
    RandomOracle (Point := Point) (Outcome := Outcome) ≃
      RandomOracle (Point := Point) (Outcome := Outcome) :=
  (split leftFixed left hleft).trans
    ((retargetCoins leftFixed rightFixed left right hleft hright).trans
      (split rightFixed right hright).symm)

theorem retarget_answers {sites : ℕ}
    (leftFixed rightFixed :
      History (Outcome := Outcome) sites → Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points leftFixed left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points rightFixed right answers))
    (oracle : RandomOracle (Point := Point) (Outcome := Outcome)) :
    run right (retarget leftFixed rightFixed left right hleft hright oracle)
        sites =
      run left oracle sites := by
  exact run_simulatedOracle rightFixed right hright
    (retargetCoins leftFixed rightFixed left right hleft hright
      (split leftFixed left hleft oracle))

theorem retarget_protected {sites : ℕ}
    (leftFixed rightFixed :
      History (Outcome := Outcome) sites → Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points leftFixed left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points rightFixed right answers))
    (oracle : RandomOracle (Point := Point) (Outcome := Outcome))
    (prior : Prior) :
    let answers := run left oracle sites
    retarget leftFixed rightFixed left right hleft hright oracle
        (rightFixed answers prior) =
      oracle (leftFixed answers prior) := by
  dsimp only
  let moved := retargetCoins leftFixed rightFixed left right hleft hright
    (split leftFixed left hleft oracle)
  have hmovedAnswers : moved.1 = run left oracle sites := rfl
  have h := simulatedOracle_protected rightFixed right hright moved prior
  calc
    retarget leftFixed rightFixed left right hleft hright oracle
          (rightFixed (run left oracle sites) prior) =
        simulatedOracle rightFixed right hright moved
          (rightFixed (run left oracle sites) prior) := rfl
    _ = simulatedOracle rightFixed right hright moved
          (rightFixed moved.1 prior) := by rw [hmovedAnswers]
    _ = moved.2.1 prior := h
    _ = oracle (leftFixed (run left oracle sites) prior) := rfl

end VeiledFlock.DependentProtectedAdaptiveOracle

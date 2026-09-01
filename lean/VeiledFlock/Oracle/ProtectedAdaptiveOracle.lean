import VeiledFlock.Oracle.AdaptiveOracleProgramming
import VeiledFlock.Oracle.MerkleHiding

/-!
# Adaptive oracle retargeting with fixedPoints adversary queries

The ordinary adaptive retargeting theorem preserves the protocol's answer
trace but is free to permute the unused oracle table.  A zero-knowledge game
must additionally preserve every oracle answer already seen by the adversary.
This module includes a finite injective family of fixedPoints points in the
oracle split.  On the good event that those points are disjoint from both
protocol traces, retargeting preserves their answers pointwise as well as the
complete adaptive protocol trace.
-/

namespace VeiledFlock.ProtectedAdaptiveOracle

open Function
open VeiledFlock.AdaptiveOracleProgramming

variable {Prior Point Outcome : Type*}
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]

abbrev RandomOracle := Point → Outcome

abbrev Outside {Index : Type*} (pointFamily : Index → Point) :=
  {point : Point // point ∉ Set.range pointFamily}

/-- Generic-index form of the finite oracle split. -/
noncomputable def splitTable {Index : Type*} [Finite Index]
    (pointFamily : Index → Point) (hinjective : Injective pointFamily) :
    RandomOracle (Point := Point) (Outcome := Outcome) ≃
      (Index → Outcome) × (Outside pointFamily → Outcome) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd
      (fun point => point ∈ Set.range pointFamily)
      (fun _ => Outcome)).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft (fun _ : Set.range pointFamily => Outcome)
        (Equiv.ofInjective pointFamily hinjective)).symm
      (Equiv.refl _))

omit [Fintype Point] [DecidableEq Point] in
theorem splitTable_programmed {Index : Type*} [Finite Index]
    (pointFamily : Index → Point) (hinjective : Injective pointFamily)
    (oracle : RandomOracle (Point := Point) (Outcome := Outcome))
    (site : Index) :
    (splitTable pointFamily hinjective oracle).1 site =
      oracle (pointFamily site) := by
  classical
  simp [splitTable]

/-- Protected points followed by one realized adaptive protocol trace. -/
def points {sites : ℕ} (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (answers : History (Outcome := Outcome) sites) : Prior ⊕ Fin sites → Point :=
  VeiledFlock.MerkleHiding.combinedPoints fixedPoints
    (tracePoints next answers)

omit [Finite Prior] in
omit [Fintype Point] [DecidableEq Point] in
theorem points_injective {sites : ℕ} (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (answers : History (Outcome := Outcome) sites)
    (hprotected : Injective fixedPoints)
    (htrace : Injective (tracePoints next answers))
    (hdisjoint : ∀ prior site,
      fixedPoints prior ≠ tracePoint next answers site) :
    Injective (points fixedPoints next answers) :=
  VeiledFlock.MerkleHiding.combinedPoints_injective
    fixedPoints (tracePoints next answers) hprotected htrace hdisjoint

/-- Independent coordinates for a random oracle while retaining the answers
at both the fixedPoints points and an adaptive trace. -/
abbrev Coins {sites : ℕ} (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome)) :=
  Σ answers : History (Outcome := Outcome) sites,
    (Prior → Outcome) ×
      (Outside (points fixedPoints next answers) → Outcome)

noncomputable def simulatedOracle {sites : ℕ}
    (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) :
    RandomOracle (Point := Point) (Outcome := Outcome) :=
  (splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
    (Sum.elim coins.2.1 coins.1, coins.2.2)

omit [Fintype Point] [DecidableEq Point] in
@[simp]
theorem simulatedOracle_protected {sites : ℕ}
    (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) (prior : Prior) :
    simulatedOracle fixedPoints next hinjective coins (fixedPoints prior) =
      coins.2.1 prior := by
  change
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2))
        (points fixedPoints next coins.1 (Sum.inl prior)) = coins.2.1 prior
  have h := splitTable_programmed (points fixedPoints next coins.1)
    (hinjective coins.1)
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2)) (Sum.inl prior)
  rw [(splitTable (points fixedPoints next coins.1)
    (hinjective coins.1)).apply_symm_apply] at h
  exact h.symm

omit [Fintype Point] [DecidableEq Point] in
@[simp]
theorem simulatedOracle_trace {sites : ℕ}
    (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) (site : Fin sites) :
    simulatedOracle fixedPoints next hinjective coins
        (tracePoint next coins.1 site) = coins.1 site := by
  change
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2))
        (points fixedPoints next coins.1 (Sum.inr site)) = coins.1 site
  have h := splitTable_programmed (points fixedPoints next coins.1)
    (hinjective coins.1)
    ((splitTable (points fixedPoints next coins.1) (hinjective coins.1)).symm
      (Sum.elim coins.2.1 coins.1, coins.2.2)) (Sum.inr site)
  rw [(splitTable (points fixedPoints next coins.1)
    (hinjective coins.1)).apply_symm_apply] at h
  exact h.symm

omit [Fintype Point] [DecidableEq Point] in
/-- The programmed adaptive schedule realizes its proposed answer vector. -/
theorem run_simulatedOracle {sites : ℕ}
    (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers))
    (coins : Coins (sites := sites) fixedPoints next) :
    run next (simulatedOracle fixedPoints next hinjective coins) sites =
      coins.1 := by
  let oracle := simulatedOracle fixedPoints next hinjective coins
  have hround : ∀ rounds (hle : rounds ≤ sites),
      run next oracle rounds = fun site => coins.1 (Fin.castLE hle site) := by
    intro rounds
    induction rounds with
    | zero =>
        intro _
        funext site
        exact Fin.elim0 site
    | succ rounds ih =>
        intro hle
        funext site
        refine Fin.lastCases ?_ (fun prior => ?_) site
        · rw [run_succ_last]
          have hprevious : run next oracle rounds =
              priorAnswers coins.1 ⟨rounds, Nat.lt_of_succ_le hle⟩ := by
            rw [ih (Nat.le_trans (Nat.le_succ rounds) hle)]
            funext prior
            rfl
          rw [hprevious]
          change oracle (tracePoint next coins.1
              ⟨rounds, Nat.lt_of_succ_le hle⟩) = _
          rw [show Fin.castLE hle (Fin.last rounds) =
              ⟨rounds, Nat.lt_of_succ_le hle⟩ by
            apply Fin.ext
            rfl]
          exact simulatedOracle_trace fixedPoints next hinjective coins _
        · rw [run_succ_castSucc, ih
              (Nat.le_trans (Nat.le_succ rounds) hle)]
          rfl
  simpa only [Fin.castLE_refl] using hround sites (le_refl sites)

/-- Exact split of a random oracle into fixedPoints answers, adaptive protocol
answers, and the untouched remainder. -/
noncomputable def split {sites : ℕ}
    (fixedPoints : Prior → Point)
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints next answers)) :
    RandomOracle (Point := Point) (Outcome := Outcome) ≃
      Coins (sites := sites) fixedPoints next where
  toFun oracle :=
    ⟨run next oracle sites,
      (fun prior => oracle (fixedPoints prior)),
      (splitTable (points fixedPoints next (run next oracle sites))
        (hinjective (run next oracle sites)) oracle).2⟩
  invFun := simulatedOracle fixedPoints next hinjective
  left_inv oracle := by
    apply (splitTable (points fixedPoints next (run next oracle sites))
      (hinjective (run next oracle sites))).injective
    dsimp only [simulatedOracle]
    rw [(splitTable (points fixedPoints next (run next oracle sites))
      (hinjective (run next oracle sites))).apply_symm_apply]
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
    let oracle := simulatedOracle fixedPoints next hinjective
      ⟨answers, protectedAnswers, outside⟩
    have hrun : run next oracle sites = answers :=
      run_simulatedOracle fixedPoints next hinjective
        ⟨answers, protectedAnswers, outside⟩
    change
      (⟨run next oracle sites,
        ((fun prior => oracle (fixedPoints prior)),
          (splitTable (points fixedPoints next (run next oracle sites))
            (hinjective (run next oracle sites)) oracle).2)⟩ :
          Coins (sites := sites) fixedPoints next) =
        ⟨answers, protectedAnswers, outside⟩
    calc
      _ = (⟨answers,
          ((fun prior => oracle (fixedPoints prior)),
            (splitTable (points fixedPoints next answers)
              (hinjective answers) oracle).2)⟩ :
            Coins (sites := sites) fixedPoints next) := by
        exact congrArg
          (fun proposed =>
            (⟨proposed,
              ((fun prior => oracle (fixedPoints prior)),
                (splitTable (points fixedPoints next proposed)
                  (hinjective proposed) oracle).2)⟩ :
              Coins (sites := sites) fixedPoints next)) hrun
      _ = ⟨answers, protectedAnswers, outside⟩ := by
        have hprotected :
            (fun prior => oracle (fixedPoints prior)) = protectedAnswers := by
          funext prior
          exact simulatedOracle_protected fixedPoints next hinjective
            ⟨answers, protectedAnswers, outside⟩ prior
        have houtside :
            (splitTable (points fixedPoints next answers)
              (hinjective answers) oracle).2 = outside := by
          change
            (splitTable (points fixedPoints next answers)
              (hinjective answers)
              ((splitTable (points fixedPoints next answers)
                (hinjective answers)).symm
                  (Sum.elim protectedAnswers answers, outside))).2 = outside
          exact congrArg Prod.snd
            ((splitTable (points fixedPoints next answers)
              (hinjective answers)).apply_symm_apply
                (Sum.elim protectedAnswers answers, outside))
        have hpair :
            ((fun prior => oracle (fixedPoints prior)),
                (splitTable (points fixedPoints next answers)
                  (hinjective answers) oracle).2) =
              (protectedAnswers, outside) :=
          Prod.ext hprotected houtside
        exact congrArg
          (fun payload =>
            (⟨answers, payload⟩ : Coins (sites := sites) fixedPoints next))
          hpair

/-- Retarget one adaptive trace to another while fixing every fixedPoints
answer coordinate. -/
noncomputable def retargetCoins {sites : ℕ}
    (fixedPoints : Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints right answers)) :
    Coins (sites := sites) fixedPoints left ≃
      Coins (sites := sites) fixedPoints right :=
  Equiv.sigmaCongrRight fun answers =>
    Equiv.prodCongr (Equiv.refl (Prior → Outcome))
      (Equiv.arrowCongr
        (VeiledFlock.OracleProgramming.unprogrammedRename
          (points fixedPoints left answers)
          (points fixedPoints right answers) (hleft answers) (hright answers))
        (Equiv.refl Outcome))

noncomputable def retarget {sites : ℕ}
    (fixedPoints : Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints right answers)) :
    RandomOracle (Point := Point) (Outcome := Outcome) ≃
      RandomOracle (Point := Point) (Outcome := Outcome) :=
  (split fixedPoints left hleft).trans
    ((retargetCoins fixedPoints left right hleft hright).trans
      (split fixedPoints right hright).symm)

omit [DecidableEq Point] in
theorem retarget_answers {sites : ℕ}
    (fixedPoints : Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints right answers))
    (oracle : RandomOracle (Point := Point) (Outcome := Outcome)) :
    run right (retarget fixedPoints left right hleft hright oracle) sites =
      run left oracle sites := by
  exact run_simulatedOracle fixedPoints right hright
    (retargetCoins fixedPoints left right hleft hright
      (split fixedPoints left hleft oracle))

omit [DecidableEq Point] in
theorem retarget_protected {sites : ℕ}
    (fixedPoints : Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints right answers))
    (oracle : RandomOracle (Point := Point) (Outcome := Outcome)) (prior : Prior) :
    retarget fixedPoints left right hleft hright oracle (fixedPoints prior) =
      oracle (fixedPoints prior) := by
  change simulatedOracle fixedPoints right hright
      (retargetCoins fixedPoints left right hleft hright
        (split fixedPoints left hleft oracle)) (fixedPoints prior) = _
  rw [simulatedOracle_protected]
  rfl

/-- Exact trace replacement on the no-prequery good event.  The output may
expose the complete vector of earlier adversary answers. -/
theorem replacement_exact [Fintype Outcome] [Nonempty Outcome]
    {sites : ℕ}
    (fixedPoints : Prior → Point)
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (points fixedPoints right answers))
    {View : Type*}
    (continueWith : (Prior → Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (RandomOracle (Point := Point) (Outcome := Outcome))).map
        (fun oracle => continueWith
          (fun prior => oracle (fixedPoints prior)) (run left oracle sites)) =
      (PMF.uniformOfFintype
        (RandomOracle (Point := Point) (Outcome := Outcome))).map
          (fun oracle => continueWith
            (fun prior => oracle (fixedPoints prior))
            (run right oracle sites)) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (retarget fixedPoints left right hleft hright)
  intro oracle
  have hfixed :
      (fun prior =>
          retarget fixedPoints left right hleft hright oracle
            (fixedPoints prior)) =
        (fun prior => oracle (fixedPoints prior)) := by
    funext prior
    exact retarget_protected fixedPoints left right hleft hright oracle prior
  have hanswers :=
    retarget_answers fixedPoints left right hleft hright oracle
  rw [hfixed, hanswers]

end VeiledFlock.ProtectedAdaptiveOracle

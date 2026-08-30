import Mathlib
import VeiledFlock.Core.Probability

/-!
# Exact finite random-oracle programming

At a fixed injective family of fresh points, a uniformly random oracle table
is exactly equivalent to a uniform vector of programmed answers together with
the unchanged table on every other point.  This is the simulator's central
reparameterization; freshness is handled separately by the prequery ledger
event.
-/

namespace VeiledFlock.OracleProgramming

open Function

variable {Point Outcome : Type*}
variable [Fintype Point] [DecidableEq Point]

abbrev Oracle := Point → Outcome

/-- Points outside an injective finite programming family. -/
abbrev Unprogrammed {sites : ℕ} (points : Fin sites → Point) :=
  {point : Point // point ∉ Set.range points}

/-- Split a complete oracle table into its answers at the programmed points
and its restriction to every unprogrammed point. -/
noncomputable def splitOracle {sites : ℕ}
    (points : Fin sites → Point) (hinjective : Injective points) :
    Oracle (Point := Point) (Outcome := Outcome) ≃
      (Fin sites → Outcome) × (Unprogrammed points → Outcome) :=
  (Equiv.piEquivPiSubtypeProd (fun point => point ∈ Set.range points)
      (fun _ => Outcome)).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft (fun _ : Set.range points => Outcome)
        (Equiv.ofInjective points hinjective)).symm
      (Equiv.refl _))

theorem splitOracle_programmed {sites : ℕ}
    (points : Fin sites → Point) (hinjective : Injective points)
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) (site : Fin sites) :
    (splitOracle points hinjective oracle).1 site = oracle (points site) := by
  simp [splitOracle]

theorem splitOracle_unprogrammed {sites : ℕ}
    (points : Fin sites → Point) (hinjective : Injective points)
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) (point : Unprogrammed points) :
    (splitOracle points hinjective oracle).2 point = oracle point.1 := by
  simp [splitOracle]

/-- Replace exactly the selected answers while retaining every other oracle
entry from `oracle`. -/
noncomputable def program {sites : ℕ}
    (points : Fin sites → Point) (hinjective : Injective points)
    (oracle : Oracle (Point := Point) (Outcome := Outcome))
    (answers : Fin sites → Outcome) :
      Oracle (Point := Point) (Outcome := Outcome) :=
  (splitOracle points hinjective).symm
    (answers, (splitOracle points hinjective oracle).2)

theorem program_at {sites : ℕ}
    (points : Fin sites → Point) (hinjective : Injective points)
    (oracle : Oracle (Point := Point) (Outcome := Outcome))
    (answers : Fin sites → Outcome) (site : Fin sites) :
    program points hinjective oracle answers (points site) = answers site := by
  rw [← splitOracle_programmed points hinjective
    (program points hinjective oracle answers) site]
  exact congrArg (fun pair => pair.1 site)
    ((splitOracle points hinjective).apply_symm_apply
      (answers, (splitOracle points hinjective oracle).2))

theorem program_off {sites : ℕ}
    (points : Fin sites → Point) (hinjective : Injective points)
    (oracle : Oracle (Point := Point) (Outcome := Outcome))
    (answers : Fin sites → Outcome) (point : Point)
    (hoff : point ∉ Set.range points) :
    program points hinjective oracle answers point = oracle point := by
  let outside : Unprogrammed points := ⟨point, hoff⟩
  change program points hinjective oracle answers outside.1 = oracle outside.1
  rw [← splitOracle_unprogrammed points hinjective
      (program points hinjective oracle answers) outside,
    ← splitOracle_unprogrammed points hinjective oracle outside]
  exact congrArg (fun pair => pair.2 outside)
    ((splitOracle points hinjective).apply_symm_apply
      (answers, (splitOracle points hinjective oracle).2))

/-- Programming with the answers already present in the table is the
identity. -/
theorem program_existing {sites : ℕ}
    (points : Fin sites → Point) (hinjective : Injective points)
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    program points hinjective oracle (fun site => oracle (points site)) =
      oracle := by
  apply (splitOracle points hinjective).injective
  apply Prod.ext
  · funext site
    rw [splitOracle_programmed]
    exact program_at points hinjective oracle _ site
  · exact congrArg Prod.snd
      ((splitOracle points hinjective).apply_symm_apply
        ((fun site => oracle (points site)),
          (splitOracle points hinjective oracle).2))

/-- The split is an exact simulator: sample programmed answers uniformly,
sample the off-set table uniformly, reconstruct the oracle, and expose the
answers.  This has exactly the honest random-table distribution. -/
theorem programmingSimulator_exact [Fintype Outcome] [Nonempty Outcome]
    {sites : ℕ} (points : Fin sites → Point)
    (hinjective : Injective points) {View : Type*}
    (view : Oracle (Point := Point) (Outcome := Outcome) →
      (Fin sites → Outcome) → View) :
    (PMF.uniformOfFintype
      (Oracle (Point := Point) (Outcome := Outcome))).map
        (fun oracle => view oracle (fun site => oracle (points site))) =
      (PMF.uniformOfFintype
        ((Fin sites → Outcome) × (Unprogrammed points → Outcome))).map
          (fun coins => view ((splitOracle points hinjective).symm coins)
            coins.1) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (splitOracle points hinjective)
  intro oracle
  rw [(splitOracle points hinjective).symm_apply_apply]
  apply congrArg (view oracle)
  funext site
  exact (splitOracle_programmed points hinjective oracle site).symm

/-! ## Retargeting a fresh family of oracle inputs -/

/-- Any bijection between two injectively indexed finite point families
extends to a permutation of the entire oracle domain. -/
noncomputable def pointRename {Index : Type*} [Finite Index]
    (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right) : Point ≃ Point := by
  classical
  let rangeEquiv : Set.range left ≃ Set.range right :=
    (Equiv.ofInjective left hleft).symm.trans (Equiv.ofInjective right hright)
  exact Equiv.extendSubtype rangeEquiv

@[simp]
theorem pointRename_apply {Index : Type*} [Finite Index]
    (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right) (site : Index) :
    pointRename left right hleft hright (left site) = right site := by
  classical
  rw [pointRename, Equiv.extendSubtype_apply_of_mem _ _ ⟨site, rfl⟩]
  simp

/-- The point permutation restricts to an equivalence between the complements
of the two renamed families.  This is the missing fiber map needed to retarget
an entire adaptive random-oracle trace, not just its selected answers. -/
noncomputable def unprogrammedRename {Index : Type*} [Finite Index]
    (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right) :
    {point : Point // point ∉ Set.range left} ≃
      {point : Point // point ∉ Set.range right} where
  toFun point := ⟨pointRename left right hleft hright point.1, by
    intro hrightRange
    obtain ⟨site, hsite⟩ := hrightRange
    have hmap := pointRename_apply left right hleft hright site
    have hpoint : left site = point.1 := by
      apply (pointRename left right hleft hright).injective
      exact hmap.trans hsite
    exact point.2 ⟨site, hpoint⟩⟩
  invFun point := ⟨(pointRename left right hleft hright).symm point.1, by
    intro hleftRange
    obtain ⟨site, hsite⟩ := hleftRange
    have hmap := pointRename_apply left right hleft hright site
    have hpoint : right site = point.1 := by
      rw [← hmap]
      simpa using congrArg (pointRename left right hleft hright) hsite
    exact point.2 ⟨site, hpoint⟩⟩
  left_inv point := by
    apply Subtype.ext
    exact (pointRename left right hleft hright).symm_apply_apply point.1
  right_inv point := by
    apply Subtype.ext
    exact (pointRename left right hleft hright).apply_symm_apply point.1

/-- Pull an oracle table through the point permutation that sends every old
hidden input to its replacement. -/
noncomputable def renameOracle {Index : Type*} [Finite Index]
    (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right) :
    Oracle (Point := Point) (Outcome := Outcome) ≃
      Oracle (Point := Point) (Outcome := Outcome) where
  toFun oracle point := oracle ((pointRename left right hleft hright).symm point)
  invFun oracle point := oracle (pointRename left right hleft hright point)
  left_inv oracle := by
    funext point
    simp
  right_inv oracle := by
    funext point
    simp

@[simp]
theorem renameOracle_at {Index : Type*} [Finite Index]
    (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) (site : Index) :
    renameOracle left right hleft hright oracle (right site) =
      oracle (left site) := by
  classical
  change oracle ((pointRename left right hleft hright).symm (right site)) = _
  have hmap := pointRename_apply left right hleft hright site
  have hinverse :
      (pointRename left right hleft hright).symm (right site) = left site := by
    rw [← hmap]
    exact Equiv.symm_apply_apply _ _
  exact congrArg oracle hinverse

/-- Exact fresh-input replacement: a uniform random function evaluated on
one injective family has exactly the same answer-vector distribution as on
any other injective family.  This is the algebraic core of salted-Merkle
hiding; the separate prequery event is what justifies treating the inputs as
fresh to an external adversary. -/
theorem freshFamilyReplacement_exact [Fintype Outcome] [Nonempty Outcome]
    {Index : Type*} [Finite Index] (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    {View : Type*} (continueWith : (Index → Outcome) → View) :
    (PMF.uniformOfFintype
      (Oracle (Point := Point) (Outcome := Outcome))).map
        (fun oracle => continueWith (fun site => oracle (left site))) =
      (PMF.uniformOfFintype
        (Oracle (Point := Point) (Outcome := Outcome))).map
          (fun oracle => continueWith (fun site => oracle (right site))) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (renameOracle left right hleft hright)
  intro oracle
  apply congrArg continueWith
  funext site
  exact (renameOracle_at left right hleft hright oracle site).symm

section FiberwiseReplacement

variable {Rest View : Type*}
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]

private def swapRestOracle :
    (Rest × Oracle (Point := Point) (Outcome := Outcome)) ≃
      (Oracle (Point := Point) (Outcome := Outcome) × Rest) where
  toFun coins := (coins.2, coins.1)
  invFun coins := (coins.2, coins.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Rename a finite query family separately in every fixed public-state
fiber. -/
noncomputable def fiberwiseRenameOracle {Index : Type*} [Finite Index]
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest)) :
    (Rest × Oracle (Point := Point) (Outcome := Outcome)) ≃
      (Rest × Oracle (Point := Point) (Outcome := Outcome)) :=
  VeiledFlock.Probability.fiberwiseEquiv swapRestOracle
    (fun rest => renameOracle (left rest) (right rest)
      (hleft rest) (hright rest))

theorem fiberwiseRenameOracle_rest {Index : Type*} [Finite Index]
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest))
    (coins : Rest × Oracle (Point := Point) (Outcome := Outcome)) :
    (fiberwiseRenameOracle left right hleft hright coins).1 = coins.1 := by
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapRestOracle
    (fun rest => renameOracle (left rest) (right rest)
      (hleft rest) (hright rest)) coins
  exact congrArg Prod.snd hsplit

theorem fiberwiseRenameOracle_at {Index : Type*} [Finite Index]
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest))
    (coins : Rest × Oracle (Point := Point) (Outcome := Outcome))
    (site : Index) :
    (fiberwiseRenameOracle left right hleft hright coins).2
        (right coins.1 site) = coins.2 (left coins.1 site) := by
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapRestOracle
    (fun rest => renameOracle (left rest) (right rest)
      (hleft rest) (hright rest)) coins
  have horacle : (fiberwiseRenameOracle left right hleft hright coins).2 =
      renameOracle (left coins.1) (right coins.1)
        (hleft coins.1) (hright coins.1) coins.2 :=
    congrArg Prod.fst hsplit
  rw [horacle]
  exact renameOracle_at (left coins.1) (right coins.1)
    (hleft coins.1) (hright coins.1) coins.2 site

/-- Exact replacement for point families depending on an arbitrary fixed
public-state fiber.  This form can carry salted-leaf assignments and a
canonicalized prior-query list together. -/
theorem fiberwiseFreshFamilyReplacement_exact {Index : Type*} [Finite Index]
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest))
    (continueWith : Rest → (Index → Outcome) → View) :
    (PMF.uniformOfFintype
      (Rest × Oracle (Point := Point) (Outcome := Outcome))).map
        (fun coins => continueWith coins.1
          (fun site => coins.2 (left coins.1 site))) =
      (PMF.uniformOfFintype
        (Rest × Oracle (Point := Point) (Outcome := Outcome))).map
          (fun coins => continueWith coins.1
            (fun site => coins.2 (right coins.1 site))) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (fiberwiseRenameOracle left right hleft hright)
  intro coins
  have hrest := fiberwiseRenameOracle_rest left right hleft hright coins
  rw [hrest]
  apply congrArg (continueWith coins.1)
  funext site
  exact (fiberwiseRenameOracle_at left right hleft hright coins site).symm

end FiberwiseReplacement

end VeiledFlock.OracleProgramming

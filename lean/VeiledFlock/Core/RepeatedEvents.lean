import Mathlib

/-!
# Repeated independent finite events

Several fail-closed protocol checks have the same shape: each proof (or each
site within a proof) receives an independent finite run, and the global event
occurs if any run belongs to a fixed bad set.  This module proves that the
multi-site probability is at most the number of sites times the one-site
probability.
-/

namespace VeiledFlock.RepeatedEvents

variable {Coin : Type*} [Fintype Coin] [DecidableEq Coin]

/-- Assignments whose selected coordinate belongs to `bad`. -/
noncomputable def coordinateBad {sites : ℕ} (site : Fin sites)
    (bad : Finset Coin) : Finset (Fin sites → Coin) :=
  Finset.univ.filter fun assignments => assignments site ∈ bad

@[simp]
theorem mem_coordinateBad_iff {sites : ℕ} (site : Fin sites)
    (bad : Finset Coin) (assignments : Fin sites → Coin) :
    assignments ∈ coordinateBad site bad ↔ assignments site ∈ bad := by
  simp [coordinateBad]

private def splitCoordinate {sites : ℕ} (site : Fin sites) :
    (Fin sites → Coin) ≃
      (({other : Fin sites // other ≠ site} → Coin) × Coin) where
  toFun assignments := (fun other => assignments other.1, assignments site)
  invFun := fun pair other =>
    if h : other = site then pair.2 else pair.1 ⟨other, h⟩
  left_inv assignments := by
    funext other
    by_cases h : other = site
    · subst other
      simp
    · simp [h]
  right_inv pair := by
    apply Prod.ext
    · funext other
      simp [other.property]
    · simp

private theorem card_otherCoordinates {sites : ℕ} (site : Fin sites) :
    Fintype.card {other : Fin sites // other ≠ site} = sites - 1 := by
  rw [Fintype.card_subtype_compl
    (p := fun other : Fin sites => other = site)]
  simp

theorem card_coordinateBad {sites : ℕ} (site : Fin sites)
    (bad : Finset Coin) :
    (coordinateBad site bad).card =
      bad.card * Fintype.card Coin ^ (sites - 1) := by
  classical
  calc
    (coordinateBad site bad).card =
        ((Finset.univ :
          Finset ({other : Fin sites // other ≠ site} → Coin)).product
            bad).card := by
      refine Finset.card_equiv (splitCoordinate site) fun assignments => ?_
      simp [coordinateBad, splitCoordinate]
    _ = bad.card * Fintype.card Coin ^ (sites - 1) := by
      simp [Fintype.card_fun, card_otherCoordinates site, Nat.mul_comm]

/-- Assignments on which at least one independent site is bad. -/
noncomputable def anyBad (sites : ℕ) (bad : Finset Coin) :
    Finset (Fin sites → Coin) :=
  Finset.univ.biUnion fun site => coordinateBad site bad

@[simp]
theorem mem_anyBad_iff (sites : ℕ) (bad : Finset Coin)
    (assignments : Fin sites → Coin) :
    assignments ∈ anyBad sites bad ↔
      ∃ site, assignments site ∈ bad := by
  simp [anyBad]

theorem card_anyBad_le (sites : ℕ) (bad : Finset Coin) :
    (anyBad sites bad).card ≤
      sites * bad.card * Fintype.card Coin ^ (sites - 1) := by
  classical
  calc
    (anyBad sites bad).card ≤
        ∑ site : Fin sites, (coordinateBad site bad).card := by
      simpa [anyBad] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin sites)))
          (t := fun site => coordinateBad site bad))
    _ = ∑ _site : Fin sites,
        bad.card * Fintype.card Coin ^ (sites - 1) := by
      apply Finset.sum_congr rfl
      intro site _
      exact card_coordinateBad site bad
    _ = sites * bad.card * Fintype.card Coin ^ (sites - 1) := by
      simp [mul_assoc]

/-- Probability union bound for any number of independent copies. -/
theorem anyBadProbability_le [Nonempty Coin]
    (sites : ℕ) (bad : Finset Coin) :
    ((anyBad sites bad).card : ℚ) /
        Fintype.card (Fin sites → Coin) ≤
      sites * ((bad.card : ℚ) / Fintype.card Coin) := by
  by_cases hsites : sites = 0
  · subst sites
    norm_num [anyBad]
  have hcoin : (0 : ℚ) < Fintype.card Coin := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coin)
  have hcount :
      ((anyBad sites bad).card : ℚ) ≤
        sites * bad.card * Fintype.card Coin ^ (sites - 1) := by
    exact_mod_cast card_anyBad_le sites bad
  have hcard : (Fintype.card (Fin sites → Coin) : ℚ) =
      Fintype.card Coin ^ sites := by
    norm_cast
    simp
  rw [hcard]
  have hpow : (0 : ℚ) < (Fintype.card Coin : ℚ) ^ sites :=
    pow_pos hcoin _
  rw [div_le_iff₀ hpow]
  have hpowSplit : (Fintype.card Coin : ℚ) ^ sites =
      Fintype.card Coin ^ (sites - 1) * Fintype.card Coin := by
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hsites
    simp [pow_succ]
  rw [hpowSplit]
  field_simp
  nlinarith [hcount]

end VeiledFlock.RepeatedEvents

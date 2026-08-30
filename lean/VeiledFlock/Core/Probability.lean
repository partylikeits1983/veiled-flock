import Flockzk.MaskingMixture
import Mathlib.Probability.Distributions.Uniform

/-!
# Finite uniform reparameterization

These lemmas turn the explicit coin bijections used throughout VEIL--FLOCK
into exact equality of probability mass functions.  They are deliberately
generic: the security proof must exhibit a bijection and a pointwise equality,
not merely assert that two views "look uniform".
-/

namespace VeiledFlock.Probability

open scoped ENNReal

/-- A bijection sends the uniform PMF on its domain to the uniform PMF on its
codomain. -/
theorem uniform_map_equiv {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (equiv : A ≃ B) :
    (PMF.uniformOfFintype A).map equiv = PMF.uniformOfFintype B := by
  classical
  ext value
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfiber : Finset.univ.filter (fun input : A => value = equiv input) =
      {equiv.symm value} := by
    ext input
    simp [eq_comm, Equiv.eq_symm_apply]
  rw [hfiber, Finset.card_singleton, Nat.cast_one, one_mul]
  congr 1
  exact_mod_cast Fintype.card_congr equiv

/-- Reparameterizing finite uniform coins through an explicit equivalence does
not change the output distribution. -/
theorem uniform_map_eq_of_equiv {A B View : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (equiv : A ≃ B) (left : A → View) (right : B → View)
    (hpoint : ∀ input, left input = right (equiv input)) :
    (PMF.uniformOfFintype A).map left =
      (PMF.uniformOfFintype B).map right := by
  calc
    (PMF.uniformOfFintype A).map left =
        (PMF.uniformOfFintype A).map (right ∘ equiv) := by
          congr 1
          funext input
          exact hpoint input
    _ = ((PMF.uniformOfFintype A).map equiv).map right :=
      (PMF.map_comp equiv _ right).symm
    _ = (PMF.uniformOfFintype B).map right := by
      rw [uniform_map_equiv equiv]

/-- An independent finite uniform component that is not observed may be
discarded without changing the output distribution. -/
theorem uniform_map_ignore_right {A B View : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (view : A → View) :
    (PMF.uniformOfFintype (A × B)).map (fun input ↦ view input.1) =
      (PMF.uniformOfFintype A).map view := by
  classical
  ext output
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  change (∑ input : A × B,
      if output = view input.1 then
        (Fintype.card (A × B) : ENNReal)⁻¹ else 0) =
    ∑ input : A,
      if output = view input then (Fintype.card A : ENNReal)⁻¹ else 0
  rw [Fintype.sum_prod_type]
  have hcardB : (Fintype.card B : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  apply Finset.sum_congr rfl
  intro input _
  by_cases houtput : output = view input
  · simp [houtput, Fintype.card_prod, ENNReal.mul_inv, hcardB,
      ENNReal.mul_inv_cancel hcardB (by simp), mul_left_comm]
  · simp [houtput]

section ComponentEvents

variable {Global Local Rest : Type*}
variable [Fintype Global] [DecidableEq Global]
variable [Fintype Local] [DecidableEq Local] [Fintype Rest]

/-- Reparameterize one independent component by a bijection that may depend
on all remaining coins.  This is still a bijection of the complete tape. -/
def fiberwiseEquiv (split : Global ≃ Local × Rest)
    (reparameterize : Rest → Local ≃ Local) : Global ≃ Global :=
  split |>.trans
    ({
      toFun := fun pair => (reparameterize pair.2 pair.1, pair.2)
      invFun := fun pair => ((reparameterize pair.2).symm pair.1, pair.2)
      left_inv := fun pair => by simp
      right_inv := fun pair => by simp
    } : (Local × Rest) ≃ (Local × Rest)) |>.trans split.symm

@[simp]
theorem fiberwiseEquiv_split_apply (split : Global ≃ Local × Rest)
    (reparameterize : Rest → Local ≃ Local) (global : Global) :
    split (fiberwiseEquiv split reparameterize global) =
      (reparameterize (split global).2 (split global).1, (split global).2) := by
  simp [fiberwiseEquiv]

/-- Lift an event on one independent component of a global random tape.  The
explicit equivalence records the factorization instead of assuming that an
arbitrary projection preserves uniformity. -/
noncomputable def liftBad (split : Global ≃ Local × Rest)
    (bad : Finset Local) : Finset Global :=
  Finset.univ.filter fun global => (split global).1 ∈ bad

theorem mem_liftBad_iff (split : Global ≃ Local × Rest)
    (bad : Finset Local) (global : Global) :
    global ∈ liftBad split bad ↔ (split global).1 ∈ bad := by
  simp [liftBad]

/-- A lifted component event has exactly `|bad| * |Rest|` global tapes. -/
theorem card_liftBad (split : Global ≃ Local × Rest)
    (bad : Finset Local) :
    (liftBad split bad).card = bad.card * Fintype.card Rest := by
  classical
  calc
    (liftBad split bad).card =
        (bad.product (Finset.univ : Finset Rest)).card := by
      refine Finset.card_equiv split fun global => ?_
      simp [liftBad]
    _ = bad.card * Fintype.card Rest := by simp

/-- Normalizing by the complete tape cancels every independent component not
used by the event. -/
theorem liftBad_probability_eq [Nonempty Local] [Nonempty Rest]
    (split : Global ≃ Local × Rest) (bad : Finset Local) :
    ((liftBad split bad).card : ℚ) / Fintype.card Global =
      (bad.card : ℚ) / Fintype.card Local := by
  rw [card_liftBad]
  have hcard : Fintype.card Global =
      Fintype.card Local * Fintype.card Rest := by
    rw [Fintype.card_congr split, Fintype.card_prod]
  rw [hcard]
  norm_num only [Nat.cast_mul]
  have hrest : (Fintype.card Rest : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Rest ≠ 0)
  have hlocal : (Fintype.card Local : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Local ≠ 0)
  field_simp [hrest, hlocal]

/-- Lift a family of local bad sets whose choice may depend on every other
coin.  This is the finite conditioning pattern needed for adaptive
adversaries: after the rest of the tape is fixed, the distinguished fresh
component remains uniform. -/
noncomputable def liftFiberBad (split : Global ≃ Local × Rest)
    (badAt : Rest → Finset Local) : Finset Global :=
  Finset.univ.filter fun global =>
    (split global).1 ∈ badAt (split global).2

theorem mem_liftFiberBad_iff (split : Global ≃ Local × Rest)
    (badAt : Rest → Finset Local) (global : Global) :
    global ∈ liftFiberBad split badAt ↔
      (split global).1 ∈ badAt (split global).2 := by
  simp [liftFiberBad]

theorem card_liftFiberBad (split : Global ≃ Local × Rest)
    (badAt : Rest → Finset Local) :
    (liftFiberBad split badAt).card = ∑ rest, (badAt rest).card := by
  classical
  calc
    (liftFiberBad split badAt).card =
        (Finset.univ.filter fun pair : Local × Rest =>
          pair.1 ∈ badAt pair.2).card := by
      refine Finset.card_equiv split fun global => ?_
      simp [liftFiberBad]
    _ = ∑ rest, (badAt rest).card := by
      simpa
        using (FlockZk.card_filter_prod_eq_sum
          (g := fun item rest => decide (item ∈ badAt rest)) true)

/-- Conditional component lifting: a uniform local bound in every fixed
fiber is also a bound in the complete global tape. -/
theorem liftFiberBad_probability_le [Nonempty Local] [Nonempty Rest]
    (split : Global ≃ Local × Rest) (badAt : Rest → Finset Local)
    (bound : ℚ)
    (hbound : ∀ rest,
      ((badAt rest).card : ℚ) / Fintype.card Local ≤ bound) :
    ((liftFiberBad split badAt).card : ℚ) / Fintype.card Global ≤
      bound := by
  rw [card_liftFiberBad]
  have hcard : Fintype.card Global =
      Fintype.card Local * Fintype.card Rest := by
    rw [Fintype.card_congr split, Fintype.card_prod]
  rw [hcard]
  norm_num only [Nat.cast_sum, Nat.cast_mul]
  have hlocal : (0 : ℚ) < Fintype.card Local := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Local)
  have hrest : (0 : ℚ) < Fintype.card Rest := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Rest)
  calc
    (∑ rest, ((badAt rest).card : ℚ)) /
          ((Fintype.card Local : ℚ) * Fintype.card Rest) =
        (∑ rest, ((badAt rest).card : ℚ) /
          Fintype.card Local) / Fintype.card Rest := by
      rw [← Finset.sum_div, div_div]
    _ ≤ (∑ _rest : Rest, bound) / Fintype.card Rest := by
      gcongr
      exact hbound rest
    _ = bound := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

end ComponentEvents

end VeiledFlock.Probability

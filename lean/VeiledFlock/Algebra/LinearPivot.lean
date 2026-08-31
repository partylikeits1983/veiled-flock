import Mathlib
import VeiledFlock.Algebra.BinaryPolynomial

/-!
# Solving one sampled linear coefficient

The zerocheck simulator samples an entire message vector, selects a nonzero
interpolation coefficient, and overwrites that coordinate so the required
public terminal evaluation holds.  This is the generic finite-dimensional
identity behind both round-one solver branches.
-/

namespace VeiledFlock.LinearPivot

variable {F Index : Type*} [Field F] [CharP F 2]
variable [Fintype Index] [DecidableEq Index]

def weightedSum (weights values : Index → F) : F :=
  ∑ index, weights index * values index

def partialSum (weights values : Index → F) (pivot : Index) : F :=
  ∑ index ∈ (Finset.univ.erase pivot), weights index * values index

def solveValue (weights values : Index → F) (pivot : Index)
    (target : F) : F :=
  (target + partialSum weights values pivot) / weights pivot

def solveAt (weights values : Index → F) (pivot : Index)
    (target : F) : Index → F :=
  Function.update values pivot (solveValue weights values pivot target)

theorem weightedSum_solveAt (weights values : Index → F) (pivot : Index)
    (target : F) (hpivot : weights pivot ≠ 0) :
    weightedSum weights (solveAt weights values pivot target) = target := by
  rw [weightedSum, ← Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
  simp only [solveAt, Function.update_self, solveValue]
  have hoff :
      ∑ x ∈ Finset.univ.erase pivot,
          weights x * Function.update values pivot
            ((target + partialSum weights values pivot) / weights pivot) x =
        partialSum weights values pivot := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hindex)]
  rw [hoff]
  field_simp
  have hcancel := BinaryPolynomial.add_self_eq_zero_charTwo
    (partialSum weights values pivot)
  linear_combination hcancel

omit [CharP F 2] [Fintype Index] [DecidableEq Index] in
/-- A nonzero coefficient exists whenever the weights do not all vanish. -/
theorem exists_nonzero_weight (weights : Index → F)
    (hnonzero : weights ≠ 0) : ∃ pivot, weights pivot ≠ 0 := by
  by_contra h
  push Not at h
  apply hnonzero
  funext pivot
  exact h pivot

omit [CharP F 2] [DecidableEq Index] in
/-- In particular, any linear interpolation rule that evaluates the constant
polynomial correctly has a usable pivot. -/
theorem exists_nonzero_weight_of_sum_eq_one (weights : Index → F)
    (hsum : ∑ index, weights index = 1) :
    ∃ pivot, weights pivot ≠ 0 := by
  apply exists_nonzero_weight weights
  intro hzero
  have : (∑ index, weights index) = 0 := by simp [hzero]
  rw [hsum] at this
  exact one_ne_zero this

/-- Formula used by the all-identity fallback in the executable simulator:
solve a coordinate of the left vector while the right vector and an outside
constant remain fixed. -/
def solveLeftAt (weights left right : Index → F) (pivot : Index)
    (outside target : F) : Index → F :=
  let combined := fun index => left index + right index
  let solved := solveAt weights combined pivot (target + outside)
  Function.update left pivot (solved pivot + right pivot)

theorem weightedSum_solveLeftAt (weights left right : Index → F)
    (pivot : Index) (outside target : F) (hpivot : weights pivot ≠ 0) :
    weightedSum weights
        (fun index => solveLeftAt weights left right pivot outside target index +
          right index) + outside = target := by
  have hcombined :
      (fun index => solveLeftAt weights left right pivot outside target index +
        right index) =
        solveAt weights (fun index => left index + right index) pivot
          (target + outside) := by
    funext index
    by_cases hindex : index = pivot
    · subst index
      simp only [solveLeftAt, solveAt, Function.update_self]
      have hcancel := BinaryPolynomial.add_self_eq_zero_charTwo (right pivot)
      rw [add_assoc, hcancel, add_zero]
    · simp [solveLeftAt, solveAt, Function.update_of_ne hindex]
  rw [hcombined, weightedSum_solveAt weights _ pivot (target + outside) hpivot]
  have hcancel := BinaryPolynomial.add_self_eq_zero_charTwo outside
  linear_combination hcancel

end VeiledFlock.LinearPivot

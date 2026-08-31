import VeiledFlock.Core.Probability

/-!
# Bounded rejection sampling

The production prover samples from a finite uniform source until it sees the
first value outside an exceptional set, and aborts after a fixed cap.  This
module proves the missing distributional fact: every accepted value has the
same mass.  The abort outcome is retained explicitly, so no conditioning or
informal appeal to symmetry is hidden in the statement.
-/

namespace VeiledFlock.RejectionSampling

variable {A : Type*} [Fintype A] [DecidableEq A]

def firstGoodList (bad : Finset A) : List A → Option A
  | [] => none
  | value :: values =>
      if value ∈ bad then firstGoodList bad values else some value

def firstGood (bad : Finset A) {trials : ℕ}
    (run : Fin trials → A) : Option A :=
  firstGoodList bad (List.ofFn run)

omit [Fintype A] in
theorem firstGoodList_eq_some_not_mem (bad : Finset A)
    {values : List A} {value : A}
    (houtput : firstGoodList bad values = some value) : value ∉ bad := by
  induction values with
  | nil => simp [firstGoodList] at houtput
  | cons head tail ih =>
      by_cases hhead : head ∈ bad
      · simpa [firstGoodList, hhead] using ih (by
          simpa [firstGoodList, hhead] using houtput)
      · simp only [firstGoodList, hhead, if_false, Option.some.injEq] at houtput
        simpa [houtput] using hhead

omit [Fintype A] in
/-- Every successful bounded rejection-sampling output satisfies the stated
acceptance predicate. -/
theorem firstGood_eq_some_not_mem (bad : Finset A) {trials : ℕ}
    {run : Fin trials → A} {value : A}
    (houtput : firstGood bad run = some value) : value ∉ bad := by
  exact firstGoodList_eq_some_not_mem bad houtput

def mapRunEquiv {trials : ℕ} (equiv : A ≃ A) :
    (Fin trials → A) ≃ (Fin trials → A) :=
  Equiv.piCongrRight fun _ => equiv

omit [Fintype A] in
theorem firstGoodList_map (bad : Finset A) (equiv : A ≃ A)
    (hpreserve : ∀ value, value ∈ bad ↔ equiv value ∈ bad)
    (values : List A) :
    firstGoodList bad (values.map equiv) =
      (firstGoodList bad values).map equiv := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, firstGoodList]
      by_cases hvalue : value ∈ bad
      · rw [if_pos ((hpreserve value).mp hvalue), if_pos hvalue, ih]
      · have hmapped : equiv value ∉ bad :=
          (not_congr (hpreserve value)).mp hvalue
        rw [if_neg hmapped, if_neg hvalue]
        rfl

omit [Fintype A] in
theorem firstGood_mapRunEquiv (bad : Finset A) {trials : ℕ}
    (equiv : A ≃ A)
    (hpreserve : ∀ value, value ∈ bad ↔ equiv value ∈ bad)
    (run : Fin trials → A) :
    firstGood bad (mapRunEquiv equiv run) =
      (firstGood bad run).map equiv := by
  rw [firstGood, firstGood]
  have hmap : List.ofFn (mapRunEquiv equiv run) =
      (List.ofFn run).map equiv := by
    change List.ofFn (fun index => equiv (run index)) = _
    rw [List.map_ofFn]
    rfl
  rw [hmap, firstGoodList_map bad equiv hpreserve]

def outputRuns (bad : Finset A) (trials : ℕ) (value : A) :
    Finset (Fin trials → A) :=
  Finset.univ.filter fun run => firstGood bad run = some value

/-- Swapping two acceptable source values is a bijection between the runs
whose first accepted output is either value. -/
theorem card_outputRuns_eq (bad : Finset A) (trials : ℕ)
    {left right : A} (hleft : left ∉ bad) (hright : right ∉ bad) :
    (outputRuns bad trials left).card =
      (outputRuns bad trials right).card := by
  let swap : A ≃ A := Equiv.swap left right
  have hpreserve : ∀ value, value ∈ bad ↔ swap value ∈ bad := by
    intro value
    by_cases hvl : value = left
    · subst value
      simp [swap, hleft, hright]
    by_cases hvr : value = right
    · subst value
      simp [swap, hleft, hright]
    simp [swap, Equiv.swap_apply_of_ne_of_ne hvl hvr]
  refine Finset.card_equiv (mapRunEquiv (trials := trials) swap) fun run => ?_
  simp only [outputRuns, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [firstGood_mapRunEquiv bad swap hpreserve run]
  constructor <;> intro h
  · rw [h]
    simp [swap]
  · cases hrun : firstGood bad run with
    | none => simp [hrun] at h
    | some value =>
        simp only [hrun, Option.map_some, Option.some.injEq] at h
        have : value = left := by
          apply swap.injective
          simpa [swap] using h
        simp [this]

/-- Uniform bounded rejection sampling assigns identical probability mass to
all accepted values. -/
theorem accepted_fiber_mass_eq (bad : Finset A) (trials : ℕ)
    {left right : A} (hleft : left ∉ bad) (hright : right ∉ bad) :
    ((outputRuns bad trials left).card : ℚ) /
        Fintype.card (Fin trials → A) =
      ((outputRuns bad trials right).card : ℚ) /
        Fintype.card (Fin trials → A) := by
  rw [card_outputRuns_eq bad trials hleft hright]

end VeiledFlock.RejectionSampling

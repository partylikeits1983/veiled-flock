import VeiledFlock.Oracle.AdaptiveOracleProgramming

/-!
# Uniform finite-coordinate windows

The operational rejection and grinding scheduler reserves a public, fixed
range of answer coordinates for every bounded loop.  This file proves once
that projecting any such range from a uniform finite answer tape has exactly
the uniform law used by the existing local abort lemmas.
-/

namespace VeiledFlock.FixedWindowProbability

open Function
open VeiledFlock.AdaptiveOracleProgramming

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/-- Pull a finite event back through an exact reindexing equivalence. -/
def transportBad {A B : Type*} [DecidableEq A]
    (equiv : A ≃ B) (bad : Finset B) : Finset A :=
  bad.map equiv.symm.toEmbedding

@[simp]
theorem mem_transportBad_iff {A B : Type*} [DecidableEq A]
    (equiv : A ≃ B) (bad : Finset B) (value : A) :
    value ∈ transportBad equiv bad ↔ equiv value ∈ bad := by
  simp [transportBad, Equiv.eq_symm_apply]

@[simp]
theorem card_transportBad {A B : Type*} [DecidableEq A]
    (equiv : A ≃ B) (bad : Finset B) :
    (transportBad equiv bad).card = bad.card := by
  simp [transportBad]

/-- The consecutive `width` coordinates beginning at `start`. -/
def window {total : ℕ} (start width : ℕ)
    (hfit : start + width ≤ total) (values : Fin total → Outcome) :
    Fin width → Outcome :=
  fun index ↦ values ⟨start + index.val, by omega⟩

/-- A total causal schedule for the same fixed coordinate window.  Natural
rounds outside the audited width are irrelevant to `run` and use coordinate
zero solely to keep the schedule total. -/
def windowSchedule {total : ℕ} (start width : ℕ)
    (hfit : start + width ≤ total) (htotal : 0 < total) :
    Schedule (Point := Fin total) (Outcome := Outcome) :=
  fun rounds _history ↦
    if hround : rounds < width then
      ⟨start + rounds, by omega⟩
    else
      ⟨0, htotal⟩

@[simp]
theorem tracePoint_windowSchedule {total : ℕ} (start width : ℕ)
    (hfit : start + width ≤ total) (htotal : 0 < total)
    (answers : History (Outcome := Outcome) width) (site : Fin width) :
    tracePoint (windowSchedule (Outcome := Outcome) start width hfit htotal)
        answers site =
      ⟨start + site.val, by omega⟩ := by
  simp [tracePoint, windowSchedule, site.isLt]

theorem windowSchedule_tracePoints_injective {total : ℕ}
    (start width : ℕ) (hfit : start + width ≤ total)
    (htotal : 0 < total)
    (answers : History (Outcome := Outcome) width) :
    Injective
      (tracePoints (windowSchedule (Outcome := Outcome) start width hfit htotal)
        answers) := by
  intro left right heq
  rw [tracePoints, tracePoint_windowSchedule,
    tracePoint_windowSchedule] at heq
  apply Fin.ext
  have := congrArg Fin.val heq
  exact Nat.add_left_cancel this

@[simp]
theorem run_windowSchedule {total : ℕ} (start width : ℕ)
    (hfit : start + width ≤ total) (htotal : 0 < total)
    (values : Fin total → Outcome) :
    run (windowSchedule (Outcome := Outcome) start width hfit htotal)
        values width =
      window start width hfit values := by
  funext site
  rw [← oracle_tracePoint_run
    (windowSchedule (Outcome := Outcome) start width hfit htotal) values site,
    tracePoint_windowSchedule]
  rfl

/-- Complete answer tapes whose selected fixed window belongs to `bad`. -/
noncomputable def windowBad {total : ℕ} (start width : ℕ)
    (hfit : start + width ≤ total)
    (bad : Finset (Fin width → Outcome)) : Finset (Fin total → Outcome) :=
  Finset.univ.filter fun values ↦ window start width hfit values ∈ bad

@[simp]
theorem mem_windowBad_iff {total : ℕ} (start width : ℕ)
    (hfit : start + width ≤ total)
    (bad : Finset (Fin width → Outcome)) (values : Fin total → Outcome) :
    values ∈ windowBad start width hfit bad ↔
      window start width hfit values ∈ bad := by
  simp [windowBad]

/-- Exact normalized cardinality of a fixed bad window. -/
theorem windowBad_probability_eq [Nonempty Outcome] {total : ℕ}
    (start width : ℕ) (hfit : start + width ≤ total)
    (htotal : 0 < total)
    (bad : Finset (Fin width → Outcome)) :
    ((windowBad start width hfit bad).card : ℚ) /
        Fintype.card (Fin total → Outcome) =
      (bad.card : ℚ) / Fintype.card (Fin width → Outcome) := by
  let schedule := windowSchedule (Outcome := Outcome) start width hfit htotal
  have hbad : windowBad start width hfit bad =
      adaptiveBadOracles schedule bad := by
    ext values
    rw [mem_windowBad_iff, mem_adaptiveBadOracles_iff]
    rw [run_windowSchedule (Outcome := Outcome) start width hfit htotal]
  rw [hbad]
  exact adaptiveBadOracles_probability_eq schedule
    (windowSchedule_tracePoints_injective (Outcome := Outcome) start width
      hfit htotal) bad

end VeiledFlock.FixedWindowProbability

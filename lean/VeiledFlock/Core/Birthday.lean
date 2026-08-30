import Mathlib

/-!
# Finite birthday bounds

This file proves the exact union bound used for random-oracle answer
collisions and for repeated 256-bit public nonces.  It counts unordered pairs,
so the numerator is `n.choose 2`, not the looser `n*n` bound.
-/

namespace VeiledFlock.Birthday

open Function

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/-- Restricting an equal-at-`i,j` vector to every coordinate except `j` is a
bijection.  The missing value is recovered from coordinate `i`. -/
private def equalAtEquiv {rounds : ℕ} {i j : Fin rounds} (hne : i ≠ j) :
    {run : Fin rounds → Outcome // run i = run j} ≃
      ({site : Fin rounds // site ≠ j} → Outcome) where
  toFun := fun run site => run.1 site.1
  invFun := fun remainder =>
    ⟨fun site => if hsite : site = j then remainder ⟨i, hne⟩
      else remainder ⟨site, hsite⟩, by simp [hne]⟩
  left_inv := fun run => by
    apply Subtype.ext
    funext site
    by_cases hsite : site = j
    · subst site
      simp [run.property]
    · simp [hsite]
  right_inv := fun remainder => by
    funext site
    simp [site.property]

/-- Exactly `|Outcome|^(rounds-1)` vectors collide at two distinct fixed
coordinates. -/
private theorem card_equalAt {rounds : ℕ} {i j : Fin rounds}
    (hne : i ≠ j) :
    (Finset.univ.filter fun run : Fin rounds → Outcome =>
      run i = run j).card = Fintype.card Outcome ^ (rounds - 1) := by
  classical
  calc
    (Finset.univ.filter fun run : Fin rounds → Outcome =>
        run i = run j).card =
        Fintype.card {run : Fin rounds → Outcome // run i = run j} := by
          symm
          exact Fintype.card_subtype _
    _ = Fintype.card ({site : Fin rounds // site ≠ j} → Outcome) :=
      Fintype.card_congr (equalAtEquiv hne)
    _ = Fintype.card Outcome ^ (rounds - 1) := by
      rw [Fintype.card_fun]
      congr 1
      rw [Fintype.card_subtype_compl (p := fun site : Fin rounds => site = j)]
      simp

/-- Symmetric collision predicate attached to an unordered index pair. -/
def pairCollides {rounds : ℕ} (run : Fin rounds → Outcome) :
    Sym2 (Fin rounds) → Prop :=
  Sym2.lift ⟨fun i j => run i = run j, fun _ _ => propext eq_comm⟩

/-- Runs that collide at a particular unordered pair. -/
noncomputable def pairCollisionRuns {rounds : ℕ} (edge : Sym2 (Fin rounds)) :
    Finset (Fin rounds → Outcome) := by
  classical
  exact Finset.univ.filter fun run => pairCollides run edge

private theorem card_pairCollisionRuns {rounds : ℕ}
    (edge : Sym2 (Fin rounds))
    (hedge : edge ∈ (⊤ : SimpleGraph (Fin rounds)).edgeFinset) :
    (pairCollisionRuns (Outcome := Outcome) edge).card =
      Fintype.card Outcome ^ (rounds - 1) := by
  induction edge using Sym2.ind with
  | _ i j =>
      have hne : i ≠ j := by
        simpa using hedge
      simpa [pairCollisionRuns, pairCollides] using
        (card_equalAt (Outcome := Outcome) hne)

/-- Every vector with any repeated value, represented as the union over the
complete graph's unordered index pairs. -/
noncomputable def collisionRuns (rounds : ℕ) : Finset (Fin rounds → Outcome) :=
  (⊤ : SimpleGraph (Fin rounds)).edgeFinset.biUnion
    (pairCollisionRuns (Outcome := Outcome))

theorem mem_collisionRuns_iff {rounds : ℕ} (run : Fin rounds → Outcome) :
    run ∈ collisionRuns (Outcome := Outcome) rounds ↔ ¬Injective run := by
  classical
  simp only [collisionRuns, Finset.mem_biUnion, pairCollisionRuns,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, hedge, hcollision⟩ hinjective
    induction edge using Sym2.ind with
    | _ i j =>
        have hne : i ≠ j := by simpa using hedge
        exact hne (hinjective (by simpa [pairCollides] using hcollision))
  · intro hnotinjective
    rw [not_injective_iff] at hnotinjective
    obtain ⟨i, j, hcollision, hij⟩ := hnotinjective
    refine ⟨s(i, j), ?_, ?_⟩
    · simpa [SimpleGraph.mem_edgeFinset]
    · simpa [pairCollides] using hcollision

/-- Counting form of the birthday union bound. -/
theorem card_collisionRuns_le (rounds : ℕ) :
    (collisionRuns (Outcome := Outcome) rounds).card ≤
      rounds.choose 2 * Fintype.card Outcome ^ (rounds - 1) := by
  classical
  calc
    (collisionRuns (Outcome := Outcome) rounds).card ≤
        ∑ edge ∈ (⊤ : SimpleGraph (Fin rounds)).edgeFinset,
          (pairCollisionRuns (Outcome := Outcome) edge).card :=
      Finset.card_biUnion_le
    _ = ∑ _edge ∈ (⊤ : SimpleGraph (Fin rounds)).edgeFinset,
          Fintype.card Outcome ^ (rounds - 1) := by
      apply Finset.sum_congr rfl
      intro edge hedge
      exact card_pairCollisionRuns edge hedge
    _ = rounds.choose 2 * Fintype.card Outcome ^ (rounds - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp

/-- Probability form for uniform independent outcomes. -/
theorem collisionProbability_le [Nonempty Outcome] (rounds : ℕ) :
    ((collisionRuns (Outcome := Outcome) rounds).card : ℚ) /
        Fintype.card (Fin rounds → Outcome) ≤
      (rounds.choose 2 : ℚ) / Fintype.card Outcome := by
  by_cases hrounds : rounds = 0
  · subst rounds
    norm_num [collisionRuns]
  have houtcome : (0 : ℚ) < Fintype.card Outcome := by positivity
  have hcard : (Fintype.card (Fin rounds → Outcome) : ℚ) =
      Fintype.card Outcome ^ rounds := by
    norm_cast
    simp [Fintype.card_fun]
  rw [hcard]
  have hpow : (0 : ℚ) < (Fintype.card Outcome : ℚ) ^ rounds :=
    pow_pos houtcome _
  rw [div_le_iff₀ hpow]
  have hcountQ :
      ((collisionRuns (Outcome := Outcome) rounds).card : ℚ) ≤
        rounds.choose 2 * Fintype.card Outcome ^ (rounds - 1) := by
    exact_mod_cast card_collisionRuns_le (Outcome := Outcome) rounds
  have hpow_split : (Fintype.card Outcome : ℚ) ^ rounds =
      Fintype.card Outcome ^ (rounds - 1) * Fintype.card Outcome := by
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrounds
    simp [pow_succ]
  rw [hpow_split]
  field_simp
  nlinarith [hcountQ]

/-- Concrete 256-bit birthday bound. -/
theorem collisionProbability256_le (rounds : ℕ) :
    ((collisionRuns (Outcome := Fin (2 ^ 256)) rounds).card : ℚ) /
        Fintype.card (Fin rounds → Fin (2 ^ 256)) ≤
      (rounds.choose 2 : ℚ) / Fintype.card (Fin (2 ^ 256)) :=
  collisionProbability_le (Outcome := Fin (2 ^ 256)) rounds

theorem card_outcome256 : Fintype.card (Fin (2 ^ 256)) = 2 ^ 256 :=
  Fintype.card_fin _

end VeiledFlock.Birthday

import Flockzk.MaskingMixture

/-!
Mixture masking with a bad set — the formal home of the rank-failure
term `ε_rank`.

The outer mask `Q` (more generally, the second mask species `b : B`) is
sampled uniformly. The per-`Q` certificates — and the prover's per-proof
rank self-check (`a1_prime_masks_round_pairs` in
`crates/flock-prover/tests/zk_leakage_certificate.rs`: for each drawn `Q`
the map `P ↦ round-pairs(P·Q)` is checked to have full rank) — establish
that for every `b` **outside a bad set** the per-`b` transcript
distributions of two claim-equal witnesses are *identical*. On the bad
set (the rank-deficient `Q` draws) nothing is guaranteed.

This file proves the resulting mixture bound in pure counting form (no
measure theory): the joint distributions over uniform `(u, b)` differ, in
total variation numerator, by at most the bad-set mass. Writing
`ε_rank = |Bad| / |B|`, the normalized form says the statistical distance
between the two transcript distributions is at most `ε_rank` — this is
where the Schwartz–Zippel-style bound `ε_rank ≤ D / 2^128` from the
challenge-dependent-rank certificate plugs in.

Main results:

  * `mixture_witness_indep_bad_set` — integer counting form: the sum over
    all transcript values `y` of the absolute difference of joint fiber
    counts is at most `2 · |Bad| · |U|`;
  * `mixture_statistical_distance_bad_set` — normalized (`ℚ`) form: the
    `L¹` distance between the two joint transcript distributions is at
    most `2 · |Bad| / |B|`, i.e. statistical distance at most
    `|Bad| / |B| = ε_rank`.

Proof shape: split each joint count over `b`
(`card_filter_prod_eq_sum`); good `b` cancel exactly (`hgood`); the
triangle inequality bounds each bad `b`'s contribution by the sum of the
two slice counts; summing a slice count over all `y` exhausts `U`
(`Finset.card_eq_sum_card_fiberwise`), giving `|U| + |U|` per bad `b`.

Note the transcript `T` here is *arbitrary* — no affinity or group
structure is assumed. All the structure lives in the per-`b` hypothesis
`hgood`, which for the good `b` is discharged by the exact per-slice
theorems (`fiber_card_eq_of_range_eq`, or the triangular slice argument
of `Flockzk.MaskingTriangular`).
-/
namespace FlockZk

open Finset

variable {U B V W P : Type*} [Fintype U] [Fintype B] [Fintype V] [DecidableEq V]

/-- **Mixture masking with a bad set (counting form).** If for every
outer mask `b` outside `Bad` the per-`b` transcript fiber counts of two
claim-equal witnesses agree at every value (the per-`Q` certificates plus
the prover's rank self-check), then the joint counts over uniform
`(u, b)` differ — summed over all transcript values — by at most
`2 · |Bad| · |U|`: only bad slices contribute, and each contributes at
most its full mass `|U|` on each side. -/
theorem mixture_witness_indep_bad_set (T : W → U → B → V) (pub : W → P)
    (Bad : Finset B)
    (hgood : ∀ w w', pub w = pub w' → ∀ b ∉ Bad, ∀ y : V,
      (univ.filter fun u => T w u b = y).card
        = (univ.filter fun u => T w' u b = y).card)
    {w w' : W} (hpub : pub w = pub w') :
    ∑ y : V,
        |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℤ)
          - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℤ)|
      ≤ 2 * Bad.card * Fintype.card U := by
  -- Joint counts split over the outer mask.
  have hsplit : ∀ (v : W) (y : V),
      ((((univ : Finset (U × B)).filter fun ub => T v ub.1 ub.2 = y).card : ℤ))
        = ∑ b : B, ((univ.filter fun u => T v u b = y).card : ℤ) := by
    intro v y
    exact_mod_cast card_filter_prod_eq_sum (T v) y
  -- A slice count summed over all values exhausts the inner mask space.
  have hmass : ∀ (v : W) (b : B),
      ∑ y : V, ((univ.filter fun u => T v u b = y).card : ℤ) = Fintype.card U := by
    intro v b
    have h : ∑ y : V, (univ.filter fun u => T v u b = y).card = Fintype.card U :=
      (Finset.card_eq_sum_card_fiberwise
        (f := fun u => T v u b) (t := (univ : Finset V))
        (fun u _ => Finset.mem_univ _)).symm.trans Finset.card_univ
    exact_mod_cast h
  -- Pointwise: only bad slices contribute to the difference at each value.
  have hpoint : ∀ y : V,
      |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℤ)
          - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℤ)|
        ≤ ∑ b ∈ Bad, (((univ.filter fun u => T w u b = y).card : ℤ)
            + ((univ.filter fun u => T w' u b = y).card : ℤ)) := by
    intro y
    rw [hsplit w y, hsplit w' y, ← Finset.sum_sub_distrib,
      ← Finset.sum_subset (Finset.subset_univ Bad)
        (fun b _ hb => by rw [hgood w w' hpub b hb y, sub_self])]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    have h1 : (0 : ℤ) ≤ ((univ.filter fun u => T w u b = y).card : ℤ) := Nat.cast_nonneg _
    have h2 : (0 : ℤ) ≤ ((univ.filter fun u => T w' u b = y).card : ℤ) := Nat.cast_nonneg _
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  calc ∑ y : V,
        |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℤ)
          - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℤ)|
      ≤ ∑ y : V, ∑ b ∈ Bad, (((univ.filter fun u => T w u b = y).card : ℤ)
          + ((univ.filter fun u => T w' u b = y).card : ℤ)) :=
        Finset.sum_le_sum fun y _ => hpoint y
    _ = ∑ b ∈ Bad, ∑ y : V, (((univ.filter fun u => T w u b = y).card : ℤ)
          + ((univ.filter fun u => T w' u b = y).card : ℤ)) := Finset.sum_comm
    _ = ∑ _b ∈ Bad, (2 * (Fintype.card U : ℤ)) :=
        Finset.sum_congr rfl fun b _ => by
          rw [Finset.sum_add_distrib, hmass w b, hmass w' b]; ring
    _ = 2 * Bad.card * Fintype.card U := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Statistical distance form.** Normalizing by the total mask mass
`|U| · |B|`, the `L¹` distance between the two joint transcript
distributions is at most `2 · |Bad| / |B|` — i.e. the statistical
(total-variation) distance is at most `|Bad| / |B| = ε_rank`, the
probability of drawing a rank-deficient outer mask. -/
theorem mixture_statistical_distance_bad_set [Nonempty U] [Nonempty B]
    (T : W → U → B → V) (pub : W → P) (Bad : Finset B)
    (hgood : ∀ w w', pub w = pub w' → ∀ b ∉ Bad, ∀ y : V,
      (univ.filter fun u => T w u b = y).card
        = (univ.filter fun u => T w' u b = y).card)
    {w w' : W} (hpub : pub w = pub w') :
    ∑ y : V,
        |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℚ)
              / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ))
          - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℚ)
              / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ))|
      ≤ 2 * Bad.card / Fintype.card B := by
  have hZ := mixture_witness_indep_bad_set T pub Bad hgood hpub
  have hU : 0 < (Fintype.card U : ℚ) := by exact_mod_cast Fintype.card_pos
  have hB : 0 < (Fintype.card B : ℚ) := by exact_mod_cast Fintype.card_pos
  have hN : 0 < (Fintype.card U : ℚ) * (Fintype.card B : ℚ) := mul_pos hU hB
  calc ∑ y : V,
        |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℚ)
              / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ))
          - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℚ)
              / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ))|
      = ∑ y : V,
          |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℚ)
            - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℚ)|
            / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [div_sub_div_same, abs_div, abs_of_pos hN]
    _ = (∑ y : V,
          |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℚ)
            - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℚ)|)
            / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ)) := by
        rw [Finset.sum_div]
    _ ≤ (2 * Bad.card * Fintype.card U : ℚ)
            / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ)) := by
        gcongr
        exact_mod_cast hZ
    _ = 2 * Bad.card / Fintype.card B := by
        have hU0 : (Fintype.card U : ℚ) ≠ 0 := hU.ne'
        have hB0 : (Fintype.card B : ℚ) ≠ 0 := hB.ne'
        field_simp

end FlockZk

import Flockzk.Masking

/-!
The mixture masking theorem behind the *repaired* zk-Flock audit.

`Flockzk.Masking` treats a transcript that is affine in a single mask
species: `T(u, w) = A u + f w` for one additive map `A`. The audit found
that the real prover's zerocheck round messages are **not** of that
form: the linear part depends on a second mask species `u_B` (and,
through it, on the witness). The repaired argument *conditions* on
`u_B`: at each fixed `b : B` the round messages are affine in `u_A`,

    T((u, b), w) = A w b u + f w b,

with a *family* of additive maps `A w b : U →+ V` and offsets
`f w b : V`. Witness independence of the joint distribution over
uniform `(u_A, u_B)` then follows from the two audited hypotheses:

  * constant image — every slice map has the same image
    `(A w b).range = V₀`, across both the witness and `u_B`;
  * coset coverage — the offsets `f w b` of all witnesses with equal
    public inputs lie in a single coset of `V₀`.

Main results:

  * `fiber_card_eq_of_range_eq` — the single-slice comparison: two
    affine maps with the same image and offsets in the same coset of it
    have identical fiber counts (on the common coset both fibers have
    size `|ker|`, which is determined by the image via the first
    isomorphism theorem; off the coset both are empty);
  * `mixture_witness_indep` — summing the slices over `b : B`: for
    witnesses with equal public inputs, the joint transcript
    distributions under uniform `(u_A, u_B)` are **identical** (stated
    as exact fiber counts, i.e. pointwise equality of the two
    distributions);
  * `pmf_mixture_witness_indep` — the same statement in `PMF` form;
  * `pmf_mixture_simulator_exact` — the simulator reading: running the
    honest prover on any public reference witness for the statement
    reproduces the honest transcript distribution exactly.
-/
namespace FlockZk

open Finset

variable {U B V W P : Type*} [Fintype U] [Fintype B] [DecidableEq V]
variable [AddCommGroup U] [AddCommGroup V]

omit [AddCommGroup U] [AddCommGroup V] in
/-- Counting helper: a fiber over the product mask space `U × B` splits
as the sum, over the second species `b : B`, of the per-`b` fibers in
`U`. -/
theorem card_filter_prod_eq_sum (g : U → B → V) (y : V) :
    ((univ : Finset (U × B)).filter fun ub => g ub.1 ub.2 = y).card
      = ∑ b : B, (univ.filter fun u => g u b = y).card := by
  rw [← Fintype.card_subtype]
  have e : { ub : U × B // g ub.1 ub.2 = y } ≃ (b : B) × { u : U // g u b = y } :=
    ((Equiv.prodComm U B).subtypeEquiv
        (q := fun bu => g bu.2 bu.1 = y) fun ub => by simp).trans
      (Equiv.subtypeProdEquivSigmaSubtype fun b u => g u b = y)
  rw [Fintype.card_congr e, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun b _ => Fintype.card_subtype _

/-- The kernel size of an additive map out of a finite group is
determined by its image: `|U| = |Image A| · |ker A|` (first isomorphism
theorem), so equal images force equal kernel sizes. -/
theorem card_ker_eq_of_range_eq (A₁ A₂ : U →+ V) (hrange : A₁.range = A₂.range) :
    (univ.filter fun u => A₁ u = 0).card = (univ.filter fun u => A₂ u = 0).card := by
  have hfilter : ∀ A : U →+ V,
      (univ.filter fun u => A u = 0).card = Nat.card A.ker := by
    intro A
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => AddMonoidHom.mem_ker.symm)
  have key : ∀ A : U →+ V, Nat.card U = Nat.card A.range * Nat.card A.ker := by
    intro A
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup A.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange A).toEquiv]
  haveI : Nonempty U := ⟨0⟩
  have h₁ := key A₁
  have h₂ := key A₂
  rw [hrange] at h₁
  have hpos : 0 < Nat.card A₂.range := by
    rcases Nat.eq_zero_or_pos (Nat.card A₂.range) with h | h
    · exfalso
      rw [h, zero_mul] at h₂
      exact (Nat.card_pos (α := U)).ne' h₂
    · exact h
  rw [hfilter A₁, hfilter A₂]
  exact Nat.eq_of_mul_eq_mul_left hpos (h₁.symm.trans h₂)

/-- **Single-slice comparison.** Two affine maps `u ↦ Aᵢ u + tᵢ` with
the same image and offsets differing by an element of that image have
identical fiber counts: on the common coset both fibers have kernel
size (`fiber_card_const` plus `card_ker_eq_of_range_eq`), off it both
are empty (`fiber_card_off_coset`). -/
theorem fiber_card_eq_of_range_eq (A₁ A₂ : U →+ V) (hrange : A₁.range = A₂.range)
    {t₁ t₂ : V} (ht : t₁ - t₂ ∈ A₁.range) (y : V) :
    (univ.filter fun u => A₁ u + t₁ = y).card
      = (univ.filter fun u => A₂ u + t₂ = y).card := by
  by_cases hy : y - t₁ ∈ A₁.range
  · -- On the coset: both fibers are kernel-sized cosets.
    have hy₂ : y - t₂ ∈ A₂.range := by
      rw [← hrange]
      have h := add_mem hy ht
      rwa [sub_add_sub_cancel] at h
    rw [fiber_card_const A₁ t₁ y (Set.mem_range.mpr (AddMonoidHom.mem_range.mp hy)),
      fiber_card_const A₂ t₂ y (Set.mem_range.mpr (AddMonoidHom.mem_range.mp hy₂))]
    exact card_ker_eq_of_range_eq A₁ A₂ hrange
  · -- Off the coset: both fibers are empty.
    have hy₂ : y - t₂ ∉ A₂.range := by
      intro h
      apply hy
      rw [← hrange] at h
      have h' := sub_mem h ht
      rwa [sub_sub_sub_cancel_right] at h'
    rw [fiber_card_off_coset A₁ t₁ y
        (fun h => hy (AddMonoidHom.mem_range.mpr (Set.mem_range.mp h))),
      fiber_card_off_coset A₂ t₂ y
        (fun h => hy₂ (AddMonoidHom.mem_range.mpr (Set.mem_range.mp h)))]

/-- **The mixture masking theorem (joint witness independence).** For a
family of additive maps `A w b : U →+ V` (fixed-`u_B` affinity) with

  * constant image `(A w b).range = V₀` across the witness and `u_B`,
  * offsets of equal-public-input witnesses in one coset of `V₀`,

the joint transcript distribution under uniform `(u_A, u_B)` is
independent of the witness: for every value `y`, the number of joint
mask assignments producing `y` is the same for `w` and `w'`. -/
theorem mixture_witness_indep (A : W → B → (U →+ V)) (f : W → B → V)
    (V₀ : AddSubgroup V) (pub : W → P)
    (h_range : ∀ w b, (A w b).range = V₀)
    (h_coset : ∀ w w' b b', pub w = pub w' → f w b - f w' b' ∈ V₀)
    {w w' : W} (hpub : pub w = pub w') (y : V) :
    ((univ : Finset (U × B)).filter fun ub => A w ub.2 ub.1 + f w ub.2 = y).card
      = ((univ : Finset (U × B)).filter fun ub => A w' ub.2 ub.1 + f w' ub.2 = y).card :=
  calc ((univ : Finset (U × B)).filter fun ub => A w ub.2 ub.1 + f w ub.2 = y).card
      = ∑ b : B, (univ.filter fun u => A w b u + f w b = y).card :=
        card_filter_prod_eq_sum (fun u b => A w b u + f w b) y
    _ = ∑ b : B, (univ.filter fun u => A w' b u + f w' b = y).card :=
        Finset.sum_congr rfl fun b _ =>
          fiber_card_eq_of_range_eq (A w b) (A w' b)
            (by rw [h_range, h_range])
            (by rw [h_range]; exact h_coset w w' b b hpub) y
    _ = ((univ : Finset (U × B)).filter fun ub => A w' ub.2 ub.1 + f w' ub.2 = y).card :=
        (card_filter_prod_eq_sum (fun u b => A w' b u + f w' b) y).symm

section PMF

open scoped ENNReal

variable [Nonempty U] [Nonempty B]

/-- `mixture_witness_indep`, in `PMF` form: the joint transcript
**distributions** of two witnesses with equal public inputs, over
uniform `(u_A, u_B)`, are equal. -/
theorem pmf_mixture_witness_indep (A : W → B → (U →+ V)) (f : W → B → V)
    (V₀ : AddSubgroup V) (pub : W → P)
    (h_range : ∀ w b, (A w b).range = V₀)
    (h_coset : ∀ w w' b b', pub w = pub w' → f w b - f w' b' ∈ V₀)
    {w w' : W} (hpub : pub w = pub w') :
    (PMF.uniformOfFintype (U × B)).map (fun ub => A w ub.2 ub.1 + f w ub.2)
      = (PMF.uniformOfFintype (U × B)).map (fun ub => A w' ub.2 ub.1 + f w' ub.2) := by
  ext y
  rw [pmf_map_affine_apply, pmf_map_affine_apply,
    mixture_witness_indep A f V₀ pub h_range h_coset hpub y]

/-- **Simulation for the mixture prover.** A simulator that knows any
public reference witness `w₀` for the statement (`pub w = pub w₀`) and
runs the honest prover on it — sampling both mask species uniformly —
reproduces the honest transcript distribution **exactly**, without
access to `w`. Immediate from `pmf_mixture_witness_indep`. -/
theorem pmf_mixture_simulator_exact (A : W → B → (U →+ V)) (f : W → B → V)
    (V₀ : AddSubgroup V) (pub : W → P)
    (h_range : ∀ w b, (A w b).range = V₀)
    (h_coset : ∀ w w' b b', pub w = pub w' → f w b - f w' b' ∈ V₀)
    {w w₀ : W} (hpub : pub w = pub w₀) :
    (PMF.uniformOfFintype (U × B)).map (fun ub => A w ub.2 ub.1 + f w ub.2)
      = (PMF.uniformOfFintype (U × B)).map (fun ub => A w₀ ub.2 ub.1 + f w₀ ub.2) :=
  pmf_mixture_witness_indep A f V₀ pub h_range h_coset hpub

end PMF

end FlockZk

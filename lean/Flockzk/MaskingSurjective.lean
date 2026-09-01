import Flockzk.Masking

/-!
Surjective and composed masking for a degree-two product-mask channel.

The WS-0 certificate shows the transcript splits into two kinds of
coordinates at fixed challenges:

  * **affine classes** — everything except the zerocheck round pairs — are
    affine in the existing masks with a witness-independent linear part, and
    the mask image *covers* every witness-difference direction there;
  * **zerocheck round pairs** — these use a degree-2 committed mask channel
    `γ·P·Q` whose contribution is affine in `P` at
    fixed `Q` and (for a uniform `Q`) **surjective** onto the entire
    round-pair coordinate block, carrying no witness.

`Flockzk.Masking` already proves that an affine transcript `A u + f w` with
`f w − f w' ∈ Image A` (for equal public inputs) is witness-independent and
exactly simulatable. This file adds the two facts needed to discharge that
coverage hypothesis:

  * `transcript_witness_indep_of_surjective` / `pmf_*` — if the mask map is
    surjective onto the value space, no coset condition is needed: the
    transcript is witness-independent for **every** witness pair (the P·Q
    channel does this on the round-pair block);
  * `mem_range_coprod` — the range of two *independent* mask channels
    `g₁ ⊞ g₂` acting on the same value space is the sumset of their ranges,
    so "P·Q covers the round-pair block" + "existing masks cover the rest"
    compose into full coverage of the joint map, feeding
    `transcript_witness_indep` directly.

Together with `Masking.lean`, these reduce the composed transcript to the
single-map masking theorem.
-/
namespace FlockZk

-- `mem_range_coprod` / `coprod_covers` are stated over the shared section
-- variables but do not use the `U`-side additive/finiteness instances; the
-- coproduct composition is what matters, so silence the section-variable lint.
set_option linter.unusedSectionVars false

open Finset

variable {U U₁ U₂ V W P : Type*} [Fintype U] [DecidableEq V]
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup U₁] [AddCommGroup U₂]

/-- **Surjective mask ⇒ unconditional witness independence.** If the mask map
`A` is surjective, every witness-difference lies in its image automatically,
so the transcript distribution is the same for *every* pair of witnesses
(no equal-public-input condition needed). The `γ·P·Q` channel supplies this
surjectivity for the round-pair block. -/
theorem transcript_witness_indep_of_surjective (A : U →+ V) (f : W → V)
    (hA : Function.Surjective A) (w w' : W) (y : V) :
    (univ.filter fun u => A u + f w = y).card
      = (univ.filter fun u => A u + f w' = y).card :=
  card_fiber_shift A y (Set.mem_range.mpr (hA (f w - f w')))

section PMF
open scoped ENNReal
variable [Nonempty U]

/-- `transcript_witness_indep_of_surjective` in `PMF` form: with a surjective
mask, the transcript distributions of any two witnesses are equal. -/
theorem pmf_transcript_witness_indep_of_surjective (A : U →+ V) (f : W → V)
    (hA : Function.Surjective A) (w w' : W) :
    (PMF.uniformOfFintype U).map (fun u => A u + f w)
      = (PMF.uniformOfFintype U).map (fun u => A u + f w') := by
  ext y
  rw [pmf_map_affine_apply, pmf_map_affine_apply,
    transcript_witness_indep_of_surjective A f hA w w' y]

end PMF

/-- **Two independent mask channels compose.** For maps `g₁ : U₁ →+ V` and
`g₂ : U₂ →+ V` into the same value space, the coproduct
`g₁ ⊞ g₂ : U₁ × U₂ →+ V`, `(u₁,u₂) ↦ g₁ u₁ + g₂ u₂`, has as its range the
sumset of the two ranges. Hence a value that is `d₁ + d₂` with `dᵢ ∈ range gᵢ`
is in the range of the joint map. Taking `g₂` as the `P·Q` channel covering
the round-pair block and `g₁` as the affine mask channel makes every
witness-difference decompose as such a sum, so it lies in the joint image and
`transcript_witness_indep` applies. -/
theorem mem_range_coprod {g₁ : U₁ →+ V} {g₂ : U₂ →+ V} {d d₁ d₂ : V}
    (h₁ : d₁ ∈ Set.range g₁) (h₂ : d₂ ∈ Set.range g₂) (hd : d = d₁ + d₂) :
    d ∈ Set.range (g₁.coprod g₂) := by
  obtain ⟨a₁, ha₁⟩ := h₁
  obtain ⟨a₂, ha₂⟩ := h₂
  refine ⟨(a₁, a₂), ?_⟩
  rw [AddMonoidHom.coprod_apply, ha₁, ha₂, ← hd]

/-- Coverage for the joint (composed) mask map: if every witness-difference of
equal-public-input witnesses splits as `d₁ + d₂` with `dᵢ ∈ range gᵢ`, the
coproduct mask map covers all witness directions — the hypothesis of
`transcript_witness_indep`. -/
theorem coprod_covers {g₁ : U₁ →+ V} {g₂ : U₂ →+ V} (f : W → V) (pub : W → P)
    (hsplit : ∀ w w', pub w = pub w' →
      ∃ d₁ ∈ Set.range g₁, ∃ d₂ ∈ Set.range g₂, f w - f w' = d₁ + d₂) :
    ∀ w w', pub w = pub w' → f w - f w' ∈ Set.range (g₁.coprod g₂) := by
  intro w w' hpub
  obtain ⟨d₁, h₁, d₂, h₂, hd⟩ := hsplit w w' hpub
  exact mem_range_coprod h₁ h₂ hd

end FlockZk

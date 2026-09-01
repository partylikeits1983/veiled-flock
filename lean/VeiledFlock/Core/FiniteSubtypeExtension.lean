import Mathlib

/-! # Extending an injective map on a finite subtype to a permutation -/

namespace VeiledFlock.FiniteSubtypeExtension

open Function

/-- Any injection from a subset of a finite type back into that type extends
to a permutation.  The complement is matched by cardinality. -/
noncomputable def extend {Alpha : Type*} [Fintype Alpha]
    (property : Alpha → Prop) (map : {x // property x} → Alpha)
    (hinjective : Injective map) : Alpha ≃ Alpha := by
  classical
  let imageProperty : Alpha → Prop := fun y ↦ y ∈ Set.range map
  let imageEquiv : {x // property x} ≃ {y // imageProperty y} :=
    Equiv.ofInjective map hinjective
  have hcomplement :
      Fintype.card {x // ¬ property x} =
        Fintype.card {y // ¬ imageProperty y} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
      Fintype.card_congr imageEquiv]
  let complementEquiv : {x // ¬ property x} ≃
      {y // ¬ imageProperty y} := Fintype.equivOfCardEq hcomplement
  exact (Equiv.sumCompl property).symm |>.trans
    (imageEquiv.sumCongr complementEquiv) |>.trans
    (Equiv.sumCompl imageProperty)

@[simp]
theorem extend_apply_mem {Alpha : Type*} [Fintype Alpha]
    (property : Alpha → Prop) (map : {x // property x} → Alpha)
    (hinjective : Injective map) (x : Alpha) (hx : property x) :
    extend property map hinjective x = map ⟨x, hx⟩ := by
  classical
  simp [extend, hx]

end VeiledFlock.FiniteSubtypeExtension

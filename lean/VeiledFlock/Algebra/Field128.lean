import VeiledFlock.Algebra.Field128Ghash

/-!
# The concrete 128-bit GHASH quotient field

The security theorems instantiate directly over the proved irreducible GHASH
quotient `F₂[X]/(X^128 + X^7 + X^2 + X + 1)`, rather than merely over an
unspecified isomorphic field.  `Field128Serialization` separately identifies
its power-basis coefficients with Rust's two little-endian limbs.
-/

noncomputable section

namespace VeiledFlock.Field128

/-- The exact field represented by the production GHASH limbs. -/
abbrev F128 := Field128Ghash.GhashField

noncomputable instance : Fintype F128 := Fintype.ofFinite F128
noncomputable instance : DecidableEq F128 := Classical.decEq F128

theorem natCard_f128 : Nat.card F128 = 2 ^ 128 := by
  exact Field128Ghash.ghashField_natCard

theorem card_f128 : Fintype.card F128 = 2 ^ 128 := by
  rw [Fintype.card_eq_nat_card, natCard_f128]

theorem characteristic_two : CharP F128 2 := by infer_instance

/-- Challenges accepted by `sample_nonzero`. -/
abbrev Nonzero := {value : F128 // value ≠ 0}

/-- Multiplication-padding challenges accepted by
`sample_not_zero_or_one`. -/
abbrev NotZeroOrOne := {value : F128 // value ≠ 0 ∧ value ≠ 1}

theorem card_nonzero : Fintype.card Nonzero = 2 ^ 128 - 1 := by
  rw [Fintype.card_subtype_compl (p := fun value : F128 => value = 0)]
  simp [card_f128]

private def exceptionalEquiv :
    {value : F128 // value = 0 ∨ value = 1} ≃ Bool where
  toFun value := if value.1 = 0 then false else true
  invFun bit := if bit then ⟨1, Or.inr rfl⟩ else ⟨0, Or.inl rfl⟩
  left_inv value := by
    apply Subtype.ext
    rcases value.property with hzero | hone
    · simp [hzero]
    · simp [hone, zero_ne_one]
  right_inv bit := by
    cases bit <;> simp

theorem card_notZeroOrOne : Fintype.card NotZeroOrOne = 2 ^ 128 - 2 := by
  classical
  let goodEquiv : NotZeroOrOne ≃
      {value : F128 // ¬(value = 0 ∨ value = 1)} :=
    Equiv.subtypeEquivRight fun _ => by simp [not_or]
  have hbad : Fintype.card {value : F128 // value = 0 ∨ value = 1} = 2 := by
    rw [Fintype.card_congr exceptionalEquiv, Fintype.card_bool]
  rw [Fintype.card_congr goodEquiv, Fintype.card_subtype_compl,
    hbad, card_f128]

end VeiledFlock.Field128

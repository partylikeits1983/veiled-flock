import Mathlib
import VeiledFlock.Core.Probability

/-!
# VEIL multiplication padding

VEIL appends the two products `(r,s,r*s)` and
`(r+1,t,(r+1)*t)`.  At a geometric challenge `alpha`, these coins mask the
three multiplication-table claims.  The following explicit inverse proves
that the resulting three values are uniform whenever `alpha` is neither zero
nor minus one.  Over `GF(2^128)`, minus one is one, matching the Rust
`sample_not_zero_or_one` gate.
-/

namespace VeiledFlock.VeilMultiplicationPadding

variable {F : Type*} [Field F]

/-- The normalized three-value view contributed by VEIL's two dummy products. -/
def dummyView (alpha : F) : F × F × F → F × F × F
  | (r, s, t) =>
      (r + alpha * (r + 1), s + alpha * t,
        r * s + alpha * (r + 1) * t)

/-- Explicit recovery of the dummy-product coins from their three-value view. -/
def recoverCoins (alpha : F) : F × F × F → F × F × F
  | (a, b, c) =>
      let r := (a - alpha) / (1 + alpha)
      let t := (c - r * b) / alpha
      (r, b - alpha * t, t)

theorem recoverCoins_dummyView (alpha : F) (halpha : alpha ≠ 0)
    (hplus : 1 + alpha ≠ 0) :
    Function.LeftInverse (recoverCoins alpha) (dummyView alpha) := by
  rintro ⟨r, s, t⟩
  simp only [dummyView, recoverCoins]
  apply Prod.ext
  · field_simp
    ring
  · apply Prod.ext
    · field_simp
      ring
    · field_simp
      ring

theorem dummyView_recoverCoins (alpha : F) (halpha : alpha ≠ 0)
    (hplus : 1 + alpha ≠ 0) :
    Function.RightInverse (recoverCoins alpha) (dummyView alpha) := by
  rintro ⟨a, b, c⟩
  simp only [dummyView, recoverCoins]
  apply Prod.ext
  · field_simp
    ring
  · apply Prod.ext
    · field_simp
      ring
    · field_simp
      ring

/-- The two dummy products give a bijective reparameterization of all three
visible multiplication claims. -/
noncomputable def dummyViewEquiv (alpha : F) (halpha : alpha ≠ 0)
    (hplus : 1 + alpha ≠ 0) : (F × F × F) ≃ (F × F × F) where
  toFun := dummyView alpha
  invFun := recoverCoins alpha
  left_inv := recoverCoins_dummyView alpha halpha hplus
  right_inv := dummyView_recoverCoins alpha halpha hplus

@[simp]
theorem dummyViewEquiv_apply (alpha : F) (halpha : alpha ≠ 0)
    (hplus : 1 + alpha ≠ 0) (coins : F × F × F) :
    dummyViewEquiv alpha halpha hplus coins = dummyView alpha coins := rfl

/-- The dummy-product contribution is exactly uniform.  This is the
distributional form of the explicit inverse above. -/
theorem dummyView_uniform [Fintype F] [DecidableEq F]
    (alpha : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0) :
    (PMF.uniformOfFintype (F × F × F)).map (dummyView alpha) =
      PMF.uniformOfFintype (F × F × F) := by
  change (PMF.uniformOfFintype (F × F × F)).map
      (dummyViewEquiv alpha halpha hplus) =
    PMF.uniformOfFintype (F × F × F)
  exact VeiledFlock.Probability.uniform_map_equiv
    (dummyViewEquiv alpha halpha hplus)

end VeiledFlock.VeilMultiplicationPadding

import VeiledFlock.VeilMultiplicationPadding
import VeiledFlock.Probability

/-!
# Exact production multiplication-claim padding

The Hadamard dot vector is `(1, alpha, alpha^2)`.  Therefore the two VEIL
dummy products contribute `alpha` times the normalized `dummyView` used in the
generic proof.  This module proves the literal production formula is still a
bijection, rather than silently dropping that nonzero scale factor.
-/

namespace VeiledFlock.ProductionMultiplicationPadding

open VeiledFlock.VeilMultiplicationPadding

variable {F : Type*} [Field F]

def scaleTriple (scalar : F) : F × F × F → F × F × F
  | (first, second, third) =>
      (scalar * first, scalar * second, scalar * third)

def unscaleTriple (scalar : F) : F × F × F → F × F × F
  | (first, second, third) =>
      (scalar⁻¹ * first, scalar⁻¹ * second, scalar⁻¹ * third)

theorem unscaleTriple_scaleTriple (scalar : F) (hscalar : scalar ≠ 0) :
    Function.LeftInverse (unscaleTriple scalar) (scaleTriple scalar) := by
  rintro ⟨first, second, third⟩
  simp only [scaleTriple, unscaleTriple]
  field_simp

theorem scaleTriple_unscaleTriple (scalar : F) (hscalar : scalar ≠ 0) :
    Function.RightInverse (unscaleTriple scalar) (scaleTriple scalar) := by
  rintro ⟨first, second, third⟩
  simp only [scaleTriple, unscaleTriple]
  field_simp

def scaleTripleEquiv (scalar : F) (hscalar : scalar ≠ 0) :
    (F × F × F) ≃ (F × F × F) where
  toFun := scaleTriple scalar
  invFun := unscaleTriple scalar
  left_inv := unscaleTriple_scaleTriple scalar hscalar
  right_inv := scaleTriple_unscaleTriple scalar hscalar

/-- Literal contribution of rows `(r,s,rs)` and
`(r+1,t,(r+1)t)` under weights `alpha` and `alpha^2`. -/
def productionDummyView (alpha : F) : F × F × F → F × F × F
  | (r, s, t) =>
      (alpha * r + alpha ^ 2 * (r + 1),
        alpha * s + alpha ^ 2 * t,
        alpha * (r * s) + alpha ^ 2 * ((r + 1) * t))

theorem productionDummyView_eq_scale_dummyView (alpha : F)
    (coins : F × F × F) :
    productionDummyView alpha coins =
      scaleTriple alpha (dummyView alpha coins) := by
  rcases coins with ⟨r, s, t⟩
  simp only [productionDummyView, scaleTriple, dummyView, pow_two]
  congr <;> ring

noncomputable def productionDummyViewEquiv (alpha : F)
    (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0) :
    (F × F × F) ≃ (F × F × F) :=
  (dummyViewEquiv alpha halpha hplus).trans
    (scaleTripleEquiv alpha halpha)

@[simp]
theorem productionDummyViewEquiv_apply (alpha : F)
    (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (coins : F × F × F) :
    productionDummyViewEquiv alpha halpha hplus coins =
      productionDummyView alpha coins := by
  rw [productionDummyView_eq_scale_dummyView]
  rfl

theorem productionDummyView_uniform [Fintype F] [DecidableEq F]
    (alpha : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0) :
    (PMF.uniformOfFintype (F × F × F)).map
        (productionDummyView alpha) =
      PMF.uniformOfFintype (F × F × F) := by
  have hfun : productionDummyView alpha =
      productionDummyViewEquiv alpha halpha hplus := by
    funext coins
    exact (productionDummyViewEquiv_apply alpha halpha hplus coins).symm
  rw [hfun]
  exact VeiledFlock.Probability.uniform_map_equiv
    (productionDummyViewEquiv alpha halpha hplus)

section WitnessTranslation

variable {W : Type*}

def visibleClaims (alpha : F) (secret : W → F × F × F)
    (witness : W) (coins : F × F × F) : F × F × F :=
  productionDummyView alpha coins + secret witness

noncomputable def claimCoinEquiv (alpha : F) (halpha : alpha ≠ 0)
    (hplus : 1 + alpha ≠ 0) (secret : W → F × F × F)
    (left right : W) : (F × F × F) ≃ (F × F × F) :=
  ((productionDummyViewEquiv alpha halpha hplus).trans
    (Equiv.addRight (secret left - secret right))).trans
      (productionDummyViewEquiv alpha halpha hplus).symm

theorem productionDummyView_claimCoinEquiv (alpha : F)
    (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (secret : W → F × F × F) (left right : W)
    (coins : F × F × F) :
    productionDummyView alpha
        (claimCoinEquiv alpha halpha hplus secret left right coins) =
      productionDummyView alpha coins + (secret left - secret right) := by
  rw [← productionDummyViewEquiv_apply alpha halpha hplus
    (claimCoinEquiv alpha halpha hplus secret left right coins)]
  rw [← productionDummyViewEquiv_apply alpha halpha hplus coins]
  change productionDummyViewEquiv alpha halpha hplus
      ((productionDummyViewEquiv alpha halpha hplus).symm
        (productionDummyViewEquiv alpha halpha hplus coins +
          (secret left - secret right))) = _
  rw [Equiv.apply_symm_apply, productionDummyViewEquiv_apply]

theorem visibleClaims_claimCoinEquiv (alpha : F)
    (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (secret : W → F × F × F) (left right : W)
    (coins : F × F × F) :
    visibleClaims alpha secret left coins =
      visibleClaims alpha secret right
        (claimCoinEquiv alpha halpha hplus secret left right coins) := by
  rw [visibleClaims, visibleClaims,
    productionDummyView_claimCoinEquiv]
  abel

theorem visibleClaims_witness_independent [Fintype F] [DecidableEq F]
    (alpha : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (secret : W → F × F × F) (left right : W) :
    (PMF.uniformOfFintype (F × F × F)).map
        (visibleClaims alpha secret left) =
      (PMF.uniformOfFintype (F × F × F)).map
        (visibleClaims alpha secret right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (claimCoinEquiv alpha halpha hplus secret left right)
  exact visibleClaims_claimCoinEquiv alpha halpha hplus secret left right

end WitnessTranslation

end VeiledFlock.ProductionMultiplicationPadding

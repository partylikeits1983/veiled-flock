import VeiledFlock.JointPcs
import VeiledFlock.Probability

/-!
# Multi-column Horner masking

Both VEIL proximity proofs reveal a random linear combination of several
secret columns and one additive-mask column, together with a public linear
functional of each column.  The coefficient of the additive-mask column is
nonzero.  This module proves the exact joint reparameterization, including the
correlated functional of the mask column.
-/

namespace VeiledFlock.HornerMask

open VeiledFlock.JointPcs

variable {F Index Column W : Type*}
variable [Field F] [Fintype Column]

/-- Weighted sum of all non-mask columns.  Horner folding is this map with
powers of the sampled scalar as weights. -/
def combinedMessage (weights : Column → F)
    (message : W → Column → Index → F) (witness : W) : Index → F :=
  ∑ column, weights column • message witness column

/-- Complete RLC value and the exposed functional of the additive mask. -/
def view (weights : Column → F) (maskCoefficient : F)
    (functional : (Index → F) →ₗ[F] F)
    (message : W → Column → Index → F)
    (witness : W) (mask : Index → F) : (Index → F) × F :=
  realOpeningView maskCoefficient functional
    (combinedMessage weights message witness) mask

/-- Translate the additive-mask vector when changing witnesses. -/
def coinEquiv (weights : Column → F) (maskCoefficient : F)
    (message : W → Column → Index → F) (left right : W) :
    (Index → F) ≃ (Index → F) :=
  Equiv.addRight
    (-maskCoefficient⁻¹ •
      (combinedMessage weights message right -
        combinedMessage weights message left))

@[simp]
theorem coinEquiv_apply (weights : Column → F) (maskCoefficient : F)
    (message : W → Column → Index → F) (left right : W)
    (mask : Index → F) :
    coinEquiv weights maskCoefficient message left right mask =
      translateBlind maskCoefficient
        (combinedMessage weights message right -
          combinedMessage weights message left) mask := by
  funext index
  simp [coinEquiv, translateBlind, sub_eq_add_neg, neg_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- If every non-mask column's exposed linear claim is unchanged, so is the
claim of their weighted combination. -/
theorem functional_combined_difference_eq_zero
    (weights : Column → F) (functional : (Index → F) →ₗ[F] F)
    (message : W → Column → Index → F) (left right : W)
    (hpublic : ∀ column,
      functional (message right column - message left column) = 0) :
    functional
      (combinedMessage weights message right -
        combinedMessage weights message left) = 0 := by
  have hcombined :
      combinedMessage weights message right -
          combinedMessage weights message left =
        ∑ column, weights column •
          (message right column - message left column) := by
    simp only [combinedMessage, Finset.sum_sub_distrib, smul_sub]
  rw [hcombined, map_sum]
  simp [hpublic]

/-- Pointwise preservation of the RLC vector and exposed mask claim. -/
theorem view_coinEquiv
    (weights : Column → F) (maskCoefficient : F)
    (hmaskCoefficient : maskCoefficient ≠ 0)
    (functional : (Index → F) →ₗ[F] F)
    (message : W → Column → Index → F) (left right : W)
    (hpublic : ∀ column,
      functional (message right column - message left column) = 0)
    (mask : Index → F) :
    view weights maskCoefficient functional message left mask =
      view weights maskCoefficient functional message right
        (coinEquiv weights maskCoefficient message left right mask) := by
  let delta := combinedMessage weights message right -
    combinedMessage weights message left
  have hkernel : functional delta = 0 :=
    functional_combined_difference_eq_zero weights functional message
      left right hpublic
  rw [coinEquiv_apply]
  change realOpeningView maskCoefficient functional
      (combinedMessage weights message left) mask =
    realOpeningView maskCoefficient functional
      (combinedMessage weights message right)
      (translateBlind maskCoefficient delta mask)
  apply Prod.ext
  · change folded maskCoefficient (combinedMessage weights message left) mask =
      folded maskCoefficient (combinedMessage weights message right)
        (translateBlind maskCoefficient delta mask)
    have hsum : combinedMessage weights message left + delta =
        combinedMessage weights message right := by
      dsimp only [delta]
      abel
    rw [← hsum]
    exact (folded_translate maskCoefficient hmaskCoefficient
      (combinedMessage weights message left) mask delta).symm
  · change functional mask =
      functional (translateBlind maskCoefficient delta mask)
    exact (functional_translate maskCoefficient mask delta functional
      hkernel).symm

/-- Exact finite-distribution form used by both production VEIL RLCs. -/
theorem witness_independent
    [Fintype F] [DecidableEq F]
    [Fintype Index] [Fintype (Index → F)]
    (weights : Column → F) (maskCoefficient : F)
    (hmaskCoefficient : maskCoefficient ≠ 0)
    (functional : (Index → F) →ₗ[F] F)
    (message : W → Column → Index → F) (left right : W)
    (hpublic : ∀ column,
      functional (message right column - message left column) = 0) :
    (PMF.uniformOfFintype (Index → F)).map
        (view weights maskCoefficient functional message left) =
      (PMF.uniformOfFintype (Index → F)).map
        (view weights maskCoefficient functional message right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv weights maskCoefficient message left right)
  exact view_coinEquiv weights maskCoefficient hmaskCoefficient functional
    message left right hpublic

end VeiledFlock.HornerMask

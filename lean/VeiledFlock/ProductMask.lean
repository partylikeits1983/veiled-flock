import VeiledFlock.JointPcs
import VeiledFlock.Probability

/-!
# Hadamard product-code mask

VEIL commits a fifth, uniformly random square-code word.  A nonzero challenge
uses it to mask the product defect `A*B+C`, while the transcript also reveals
one linear functional (`gamma`) of the mask after reduction to the base
domain.  The same affine translation preserves both values whenever the
honest product defect vanishes on the coordinates read by that functional.
-/

namespace VeiledFlock.ProductMask

variable {F Square Base W : Type*}
variable [Field F]
variable [AddCommGroup Square] [Module F Square]
variable [AddCommGroup Base] [Module F Base]

def view (coefficient : F) (reduce : Square →ₗ[F] Base)
    (functional : Base →ₗ[F] F) (defect : W → Square)
    (witness : W) (mask : Square) : Square × F :=
    (defect witness + coefficient • mask,
    functional (reduce mask))

def translate (coefficient : F) (delta mask : Square) : Square :=
  mask - coefficient⁻¹ • delta

def coinEquiv (coefficient : F) (defect : W → Square)
    (left right : W) : Square ≃ Square :=
  Equiv.addRight (-coefficient⁻¹ • (defect right - defect left))

@[simp]
theorem coinEquiv_apply (coefficient : F) (defect : W → Square)
    (left right : W) (mask : Square) :
    coinEquiv coefficient defect left right mask =
      translate coefficient (defect right - defect left) mask := by
  simp [coinEquiv, translate, sub_eq_add_neg, neg_smul]
  abel

theorem masked_translate (coefficient : F) (hcoefficient : coefficient ≠ 0)
    (message mask delta : Square) :
    message + delta + coefficient • translate coefficient delta mask =
      message + coefficient • mask := by
  simp only [translate, smul_sub, smul_smul,
    mul_inv_cancel₀ hcoefficient, one_smul]
  abel

theorem functional_translate (coefficient : F) (mask delta : Square)
    (functional : Square →ₗ[F] F) (hkernel : functional delta = 0) :
    functional (translate coefficient delta mask) = functional mask := by
  simp [translate, map_sub, map_smul, hkernel]

theorem view_coinEquiv (coefficient : F) (hcoefficient : coefficient ≠ 0)
    (reduce : Square →ₗ[F] Base) (functional : Base →ₗ[F] F)
    (defect : W → Square) (left right : W)
    (hvalid : reduce (defect right - defect left) = 0)
    (mask : Square) :
    view coefficient reduce functional defect left mask =
      view coefficient reduce functional defect right
        (coinEquiv coefficient defect left right mask) := by
  let delta := defect right - defect left
  have hkernel : (functional.comp reduce) delta = 0 := by
    change functional (reduce delta) = 0
    rw [hvalid, map_zero]
  rw [coinEquiv_apply]
  apply Prod.ext
  · change defect left + coefficient • mask =
      defect right + coefficient • translate coefficient delta mask
    have hsum : defect left + delta = defect right := by
      dsimp only [delta]
      abel
    rw [← hsum]
    exact (masked_translate coefficient hcoefficient (defect left) mask
      delta).symm
  · change (functional.comp reduce) mask =
      (functional.comp reduce) (translate coefficient delta mask)
    exact (ProductMask.functional_translate coefficient mask delta
      (functional.comp reduce) hkernel).symm

theorem witness_independent
    [Fintype Square] [Nonempty Square]
    (coefficient : F) (hcoefficient : coefficient ≠ 0)
    (reduce : Square →ₗ[F] Base) (functional : Base →ₗ[F] F)
    (defect : W → Square) (left right : W)
    (hvalid : reduce (defect right - defect left) = 0) :
    (PMF.uniformOfFintype Square).map
        (view coefficient reduce functional defect left) =
      (PMF.uniformOfFintype Square).map
        (view coefficient reduce functional defect right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv coefficient defect left right)
  exact view_coinEquiv coefficient hcoefficient reduce functional defect
    left right hvalid

end VeiledFlock.ProductMask

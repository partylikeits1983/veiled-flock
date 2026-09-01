import Mathlib
import VeiledFlock.Algebra.BinaryPolynomial

/-!
# Public packed-direct claim

The only unblinded linear functional of the outer witness commitment is the
batched digest claim.  It reads public witness coordinates exclusively.  This
module proves the kernel condition used by the joint PCS hiding theorem:
two witness vectors with the same public projection have zero difference
under every weighted functional supported on that projection.
-/

namespace VeiledFlock.PublicProjection

variable {F J P W : Type*}
variable [Field F] [Fintype P]

def projection (positions : P → J) (message : J → F) : P → F :=
  fun publicIndex => message (positions publicIndex)

def weightedFunctional (positions : P → J) (weights : P → F) :
    (J → F) →ₗ[F] F where
  toFun message := ∑ publicIndex, weights publicIndex * message (positions publicIndex)
  map_add' left right := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar message := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring

theorem weightedFunctional_eq_of_projection_eq
    (positions : P → J) (weights : P → F) {left right : J → F}
    (hpublic : projection positions left = projection positions right) :
    weightedFunctional positions weights left =
      weightedFunctional positions weights right := by
  apply Finset.sum_congr rfl
  intro publicIndex _
  exact congrArg (fun value => weights publicIndex * value)
    (congrFun hpublic publicIndex)

theorem weightedFunctional_sub_eq_zero
    (positions : P → J) (weights : P → F) {left right : J → F}
    (hpublic : projection positions left = projection positions right) :
    weightedFunctional positions weights (right - left) = 0 := by
  rw [map_sub, weightedFunctional_eq_of_projection_eq positions weights hpublic,
    sub_self]

/-- Relation-level form: if the public statement determines the exact digest
projection, then the production packed-direct functional annihilates every
equal-statement witness difference. -/
theorem publicKernel
    (positions : P → J) (weights : P → F)
    (message : W → J → F) (statement : W → P → F)
    (hstatement : ∀ witness,
      statement witness = projection positions (message witness))
    {left right : W} (hpublic : statement left = statement right) :
    weightedFunctional positions weights (message right - message left) = 0 := by
  apply weightedFunctional_sub_eq_zero
  rw [← hstatement left, ← hstatement right, hpublic]

end VeiledFlock.PublicProjection

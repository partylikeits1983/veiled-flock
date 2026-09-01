import Flockzk.MaskingMixtureBadSet

/-!
Composition rule for Flock's two replacement layers. The algebraic masking
argument contributes the probability of the symbolic determinant bad set.
The commitment/hash boundary contributes a separately audited conditional
term. Their statistical-distance costs add.
-/
namespace FlockZk

open Finset

variable {U B V W P : Type*} [Fintype U] [Fintype B] [Fintype V]
  [DecidableEq V]

/-- The counting theorem in `MaskingMixtureBadSet`, expressed as total
variation rather than L1 distance. -/
theorem mixture_tv_bad_set [Nonempty U] [Nonempty B]
    (T : W -> U -> B -> V) (pub : W -> P) (Bad : Finset B)
    (hgood : ∀ w w', pub w = pub w' → ∀ b, b ∉ Bad → ∀ y : V,
      (univ.filter fun u => T w u b = y).card
        = (univ.filter fun u => T w' u b = y).card)
    {w w' : W} (hpub : pub w = pub w') :
    (1 / 2 : ℚ) *
        (∑ y : V,
          |(((univ : Finset (U × B)).filter fun ub => T w ub.1 ub.2 = y).card : ℚ)
                / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ))
            - (((univ : Finset (U × B)).filter fun ub => T w' ub.1 ub.2 = y).card : ℚ)
                / ((Fintype.card U : ℚ) * (Fintype.card B : ℚ))|)
      <= Bad.card / Fintype.card B := by
  have h := mixture_statistical_distance_bad_set T pub Bad hgood hpub
  calc
    _ <= (1 / 2 : ℚ) * (2 * Bad.card / Fintype.card B) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = Bad.card / Fintype.card B := by ring

/-- Conditional replacement composition: once the algebraic-prefix distance
is bounded by the bad-set mass, an independently bounded commitment/hash
boundary adds exactly one further term. -/
-- @audit:FlockZk.conditional_replacement_tv_bound
theorem conditional_replacement_tv_bound
    (tvAlgebraic tvFull badMass boundary : ℚ)
    (halgebraic : tvAlgebraic <= badMass)
    (hboundary : tvFull <= tvAlgebraic + boundary) :
    tvFull <= badMass + boundary := by
  linarith
-- @audit:end

end FlockZk

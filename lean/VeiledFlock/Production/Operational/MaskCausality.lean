import VeiledFlock.Oracle.OracleCausalOneTimePad
import VeiledFlock.Production.Algebra.MaskLayout

/-!
# Fiat--Shamir availability at every production mask cursor

The first 128 zerocheck values precede programmed `z`.  Recursive pair `i`
is emitted after `z` and the first `i` programmed rhos.  Every later masked
PIOP and ring value is emitted after all programmed zerocheck challenges.
This is the exact second causality schedule needed to compare an honest
prefix execution with a simulator that sampled its whole target vector up
front.
-/

namespace VeiledFlock.ProductionMaskCausality

open VeiledFlock.ConcreteParameters
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionMaskLayout

/-- Number of programmed scalar answers available before flat mask cursor
`round` is observed. -/
def available (shape : BatchShape) (round : ℕ) : ℕ :=
  if round < 2 * ell then
    0
  else
    min (programmedPoints shape) ((round - 2 * ell) / 2 + 1)

theorem available_le_sites (shape : BatchShape) (round : ℕ) :
    available shape round ≤ programmedPoints shape := by
  by_cases hround : round < 2 * ell
  · simp [available, hround]
  · simp [available, hround]

theorem available_monotone (shape : BatchShape) :
    Monotone (available shape) := by
  intro left right hle
  by_cases hright : right < 2 * ell
  · have hleft : left < 2 * ell := lt_of_le_of_lt hle hright
    simp [available, hleft, hright]
  · by_cases hleft : left < 2 * ell
    · simp [available, hleft, hright]
    · simp only [available, hleft, hright, ↓reduceIte]
      apply min_le_min_left
      have hsub : left - 2 * ell ≤ right - 2 * ell :=
        Nat.sub_le_sub_right hle (2 * ell)
      exact Nat.add_le_add_right (Nat.div_le_div_right hsub) 1

theorem prefixAvailable_round1 (shape : BatchShape) :
    prefixAvailable (available shape) (2 * ell) = 0 := by
  simp [prefixAvailable, available, ell, kSkip]

theorem prefixAvailable_initial (shape : BatchShape) (rounds : ℕ)
    (hrounds : rounds ≤ 2 * ell) :
    prefixAvailable (available shape) rounds = 0 := by
  cases rounds with
  | zero => simp [prefixAvailable]
  | succ rounds =>
      have hlt : rounds < 2 * ell := by omega
      simp [prefixAvailable, available, hlt]

theorem available_recursive (shape : BatchShape)
    (round : Fin (zerocheckRounds shape)) (entry : PairIndex) :
    available shape
        (zerocheckRoundIndex shape round entry).val = round.val + 1 := by
  have hround : round.val < zerocheckRounds shape := round.isLt
  have hsite : round.val + 1 ≤ programmedPoints shape := by
    cases shape <;>
      simp [zerocheckRounds, programmedPoints, m, kSkip] at hround ⊢ <;>
      omega
  fin_cases entry
  · simp [available, zerocheckRoundIndex_val, min_eq_right hsite]
  · change
      (if 2 * ell + 2 * round.val + 1 < 2 * ell then 0
        else min (programmedPoints shape)
          ((2 * ell + 2 * round.val + 1 - 2 * ell) / 2 + 1)) =
        round.val + 1
    rw [if_neg (by omega)]
    have hsub : 2 * ell + 2 * round.val + 1 - 2 * ell =
        2 * round.val + 1 := by omega
    rw [hsub]
    have hdiv : (2 * round.val + 1) / 2 = round.val := by omega
    rw [hdiv, min_eq_right hsite]

theorem prefixAvailable_recursive (shape : BatchShape)
    (round : Fin (zerocheckRounds shape)) (entry : PairIndex) :
    prefixAvailable (available shape)
        ((zerocheckRoundIndex shape round entry).val + 1) =
      round.val + 1 := by
  simp only [prefixAvailable]
  exact available_recursive shape round entry

theorem recursive_available_le_reached (shape : BatchShape)
    (round : Fin (zerocheckRounds shape)) (entry : PairIndex) :
    prefixAvailable (available shape)
        ((zerocheckRoundIndex shape round entry).val + 1) ≤
      round.val + 1 := by
  rw [prefixAvailable_recursive]

theorem initialMask_before_recursive (shape : BatchShape)
    (index : Fin (2 * ell)) :
    available shape index.val = 0 := by
  simp [available, index.isLt]

theorem all_masks_available_bound (shape : BatchShape) :
    prefixAvailable (available shape) (expectedMasks shape) ≤
      programmedPoints shape := by
  exact (prefixAvailable_le_current (available shape)
    (available_monotone shape) _).trans (available_le_sites shape _)

end VeiledFlock.ProductionMaskCausality

import VeiledFlock.Algebra.Field128
import VeiledFlock.Concrete.Grinding
import VeiledFlock.Core.RejectionSampling
import VeiledFlock.Core.RepeatedEvents

/-!
# Bounded exceptional-challenge sampling

The algebraic proof conditions on challenges being outside the exceptional
sets `{0}` and `{0,1}`.  This file gives exact abort tails for a fail-closed
bounded rejection sampler over the implementation's 128-bit field.
-/

namespace VeiledFlock.ChallengeSampling

open VeiledFlock.Field128
open VeiledFlock.Grinding

noncomputable def zeroFailure : Finset F128 := {0}
noncomputable def zeroOrOneFailure : Finset F128 := {0, 1}
noncomputable def oneFailure : Finset F128 := {1}

theorem card_zeroFailure : zeroFailure.card = 1 := by
  simp [zeroFailure]

theorem card_zeroOrOneFailure : zeroOrOneFailure.card = 2 := by
  simp [zeroOrOneFailure]

theorem card_oneFailure : oneFailure.card = 1 := by
  simp [oneFailure]

/-- Exact probability that every draw is zero. -/
theorem nonzeroAbortProbability_eq (trials : ℕ) :
    ((abortRuns zeroFailure trials).card : ℚ) /
        Fintype.card (Fin trials → F128) =
      ((1 : ℚ) / (2 : ℚ) ^ 128) ^ trials := by
  rw [abortProbability_eq, card_zeroFailure, card_f128]
  norm_num only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]

/-- Exact probability that every draw is zero or one. -/
theorem notZeroOrOneAbortProbability_eq (trials : ℕ) :
    ((abortRuns zeroOrOneFailure trials).card : ℚ) /
        Fintype.card (Fin trials → F128) =
      ((2 : ℚ) / (2 : ℚ) ^ 128) ^ trials := by
  rw [abortProbability_eq, card_zeroOrOneFailure, card_f128]
  norm_num only [Nat.cast_ofNat, Nat.cast_pow]

def rejectionTrials : ℕ := 4096

/-- Largest sampled equality-point suffix among the four registered shapes:
`25 - K_SKIP(6) - N_INNER(7) = 12`. -/
def maxEqualityPointOuterCoordinates : ℕ := 12

/-- One whole-vector equality-point attempt fails if at least one outer
coordinate equals the exceptional value one. -/
noncomputable def equalityPointVectorFailure :
    Finset (Fin maxEqualityPointOuterCoordinates → F128) :=
  RepeatedEvents.anyBad maxEqualityPointOuterCoordinates oneFailure

theorem equalityPointVectorFailure_probability_le :
    ((equalityPointVectorFailure.card : ℚ) /
        Fintype.card (Fin maxEqualityPointOuterCoordinates → F128)) ≤
      maxEqualityPointOuterCoordinates *
        ((1 : ℚ) / (2 : ℚ) ^ 128) := by
  convert
    (RepeatedEvents.anyBadProbability_le
      maxEqualityPointOuterCoordinates oneFailure) using 1 <;>
    norm_num [equalityPointVectorFailure, card_f128, card_oneFailure,
      maxEqualityPointOuterCoordinates]

/-- Conservative tail for exhausting all whole-vector equality-point
attempts. -/
def equalityPointAbortBound : ℚ :=
  ((maxEqualityPointOuterCoordinates : ℚ) / (2 : ℚ) ^ 128) ^
    rejectionTrials

theorem equalityPointAbortProbability_le :
    ((abortRuns equalityPointVectorFailure rejectionTrials).card : ℚ) /
        Fintype.card
          (Fin rejectionTrials →
            (Fin maxEqualityPointOuterCoordinates → F128)) ≤
      equalityPointAbortBound := by
  rw [abortProbability_eq]
  simpa [equalityPointAbortBound, div_eq_mul_inv] using
    (pow_le_pow_left₀ (by positivity)
      equalityPointVectorFailure_probability_le rejectionTrials)

/-- A successful whole-vector equality-point sample contains no exceptional
one coordinate. -/
theorem equalityPointAccepted_ne_one
    {run : Fin rejectionTrials →
      (Fin maxEqualityPointOuterCoordinates → F128)}
    {accepted : Fin maxEqualityPointOuterCoordinates → F128}
    (haccepted : RejectionSampling.firstGood equalityPointVectorFailure run =
      some accepted) :
    ∀ index, accepted index ≠ 1 := by
  have hgood := RejectionSampling.firstGood_eq_some_not_mem
    equalityPointVectorFailure haccepted
  intro index hone
  apply hgood
  apply (RepeatedEvents.mem_anyBad_iff
    maxEqualityPointOuterCoordinates oneFailure accepted).2
  exact ⟨index, by simpa [oneFailure, hone]⟩

/-- Every accepted equality-point vector has the same exact probability mass;
the only discrepancy from uniform sampling over valid vectors is the explicit
bounded-sampler abort event. -/
theorem equalityPointAcceptedMass_eq
    {left right : Fin maxEqualityPointOuterCoordinates → F128}
    (hleft : ∀ index, left index ≠ 1)
    (hright : ∀ index, right index ≠ 1) :
    ((RejectionSampling.outputRuns equalityPointVectorFailure rejectionTrials
        left).card : ℚ) /
        Fintype.card (Fin rejectionTrials →
          (Fin maxEqualityPointOuterCoordinates → F128)) =
      ((RejectionSampling.outputRuns equalityPointVectorFailure rejectionTrials
        right).card : ℚ) /
        Fintype.card (Fin rejectionTrials →
          (Fin maxEqualityPointOuterCoordinates → F128)) := by
  apply RejectionSampling.accepted_fiber_mass_eq
  · intro hbad
    obtain ⟨index, hindex⟩ :=
      (RepeatedEvents.mem_anyBad_iff
        maxEqualityPointOuterCoordinates oneFailure left).mp hbad
    exact hleft index (by simpa [oneFailure] using hindex)
  · intro hbad
    obtain ⟨index, hindex⟩ :=
      (RepeatedEvents.mem_anyBad_iff
        maxEqualityPointOuterCoordinates oneFailure right).mp hbad
    exact hright index (by simpa [oneFailure] using hindex)

def nonzeroAbortBound : ℚ :=
  ((1 : ℚ) / (2 : ℚ) ^ 128) ^ rejectionTrials

def notZeroOrOneAbortBound : ℚ :=
  ((2 : ℚ) / (2 : ℚ) ^ 128) ^ rejectionTrials

theorem nonzeroAbortBound_eq :
    ((abortRuns zeroFailure rejectionTrials).card : ℚ) /
        Fintype.card (Fin rejectionTrials → F128) =
      nonzeroAbortBound :=
  nonzeroAbortProbability_eq rejectionTrials

theorem notZeroOrOneAbortBound_eq :
    ((abortRuns zeroOrOneFailure rejectionTrials).card : ℚ) /
        Fintype.card (Fin rejectionTrials → F128) =
      notZeroOrOneAbortBound :=
  notZeroOrOneAbortProbability_eq rejectionTrials

/-- Every nonzero result returned by the production 4096-draw sampler has
the same exact probability mass.  Thus the successful result is uniform over
the nonzero field elements; the only discrepancy is the separately charged
all-zero abort event. -/
theorem nonzeroAcceptedMass_eq {left right : F128}
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    ((RejectionSampling.outputRuns zeroFailure rejectionTrials left).card : ℚ) /
        Fintype.card (Fin rejectionTrials → F128) =
      ((RejectionSampling.outputRuns zeroFailure rejectionTrials right).card : ℚ) /
        Fintype.card (Fin rejectionTrials → F128) := by
  apply RejectionSampling.accepted_fiber_mass_eq
  · simpa [zeroFailure]
  · simpa [zeroFailure]

/-- Every result outside `{0,1}` returned by the multiplication-challenge
sampler has the same exact probability mass. -/
theorem notZeroOrOneAcceptedMass_eq {left right : F128}
    (hleft : left ≠ 0 ∧ left ≠ 1)
    (hright : right ≠ 0 ∧ right ≠ 1) :
    ((RejectionSampling.outputRuns zeroOrOneFailure rejectionTrials left).card : ℚ) /
        Fintype.card (Fin rejectionTrials → F128) =
      ((RejectionSampling.outputRuns zeroOrOneFailure rejectionTrials right).card : ℚ) /
        Fintype.card (Fin rejectionTrials → F128) := by
  apply RejectionSampling.accepted_fiber_mass_eq
  · simpa [zeroOrOneFailure]
  · simpa [zeroOrOneFailure]

end VeiledFlock.ChallengeSampling

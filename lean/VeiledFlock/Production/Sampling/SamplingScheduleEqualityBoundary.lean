import VeiledFlock.Production.Sampling.SamplingScheduleEqualityGrowth

/-! # Live production equality-attempt boundaries

The first accepting equality attempt exists outside the explicit sampling
ledger's bad set.  Every earlier complete attempt rejects without aborting, so
the literal production control remains live, has not fixed an equality point,
and retains its public skip value at every boundary through that first attempt.
-/

namespace VeiledFlock.ProductionSamplingScheduleEqualityBoundary

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole

def equalityAttemptAccepts (shape : BatchShape)
    (answers : SamplingAnswerTape) (attempt : ℕ) : Prop :=
  ∃ hattempt : attempt < rejectionTrials,
    accepted (sliceFromBlocks (m shape - kSkip - 7)
      (List.ofFn (equalityAttemptAnswers answers ⟨attempt, hattempt⟩)))

theorem exists_equalityAttemptAccepts_of_not_globalBad
    (shape : BatchShape) (answers : SamplingAnswerTape)
    (hgood : answers ∉ globalBad shape) :
    ∃ attempt, equalityAttemptAccepts shape answers attempt := by
  rcases equality_accepted_of_not_globalBad shape answers hgood with
    ⟨attempt, hattempt⟩
  refine ⟨attempt.val, attempt.isLt, ?_⟩
  rw [equalityAttemptAnswers_eq_flat]
  exact hattempt

noncomputable def firstEqualityAccepted (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) : ℕ :=
  by
    classical
    exact Nat.find
      (exists_equalityAttemptAccepts_of_not_globalBad shape answers hgood)

theorem firstEqualityAccepted_spec (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    equalityAttemptAccepts shape answers
      (firstEqualityAccepted shape answers hgood) := by
  classical
  exact Nat.find_spec
    (exists_equalityAttemptAccepts_of_not_globalBad shape answers hgood)

theorem firstEqualityAccepted_lt (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    firstEqualityAccepted shape answers hgood < rejectionTrials := by
  exact (firstEqualityAccepted_spec shape answers hgood).choose

theorem before_firstEqualityAccepted_rejects (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (attempt : ℕ)
    (hbefore : attempt < firstEqualityAccepted shape answers hgood)
    (hattempt : attempt < rejectionTrials) :
    ¬ accepted (sliceFromBlocks (m shape - kSkip - 7)
      (List.ofFn (equalityAttemptAnswers answers ⟨attempt, hattempt⟩))) := by
  classical
  intro haccepts
  have hp : equalityAttemptAccepts shape answers attempt :=
    ⟨hattempt, haccepts⟩
  exact (Nat.find_min
    (exists_equalityAttemptAccepts_of_not_globalBad shape answers hgood)
    hbefore) hp

set_option maxRecDepth 10000 in
theorem rawControlUntil_equality_boundary_live_none
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (attempt : ℕ)
    (hbound : attempt ≤ firstEqualityAccepted shape answers hgood) :
    let result := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + attempt * 7)
        (equalityBoundary_fits attempt
          (hbound.trans (firstEqualityAccepted_lt shape answers hgood).le))
    result.status = .live ∧
      result.equalityPoint = none ∧ result.skip.isSome = true := by
  classical
  induction attempt with
  | zero =>
      have hskip := rawControlUntil_skip shape causalSecret completion witness
        coins prelude answers
      simpa only [Nat.zero_mul, Nat.add_zero, hskip] using
        And.intro (afterSkipControl_status shape prelude _)
          (And.intro (afterSkipControl_equality_none shape prelude _)
            (afterSkipControl_skip_isSome shape prelude _))
  | succ attempt ih =>
      have hattemptBefore :
          attempt < firstEqualityAccepted shape answers hgood := by omega
      have hattempt : attempt < rejectionTrials :=
        lt_of_lt_of_le hattemptBefore
          (firstEqualityAccepted_lt shape answers hgood).le
      have hbefore := ih (by omega)
      have hrejected := before_firstEqualityAccepted_rejects shape answers hgood
        attempt hattemptBefore hattempt
      have hlocal := equalityAttempt_live_none_of_rejected_before_cap shape
        attempt
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + attempt * 7)
            (equalityBoundary_fits attempt hattempt.le))
        (equalityAttemptAnswers answers ⟨attempt, hattempt⟩)
        hbefore.1 hbefore.2.1 hrejected (by
          have := firstEqualityAccepted_lt shape answers hgood
          omega)
      have hstep := rawControlUntil_equality_boundary_step shape causalSecret
        completion witness coins prelude answers attempt hattempt hlocal.1
      rw [hstep]
      refine ⟨hlocal.1, hlocal.2, ?_⟩
      rw [iterateEquality_skip]
      exact hbefore.2.2

end VeiledFlock.ProductionSamplingScheduleEqualityBoundary

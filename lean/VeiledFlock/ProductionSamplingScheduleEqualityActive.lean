import VeiledFlock.ProductionSamplingScheduleEqualityPrefix

/-! # Literal production controls at active equality queries -/

namespace VeiledFlock.ProductionSamplingScheduleEqualityActive

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingScheduleEqualityPrefix
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawControlUntil_active_equality_fields
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (attempt counter : ℕ)
    (hattempt : attempt ≤ firstEqualityAccepted shape answers hgood)
    (hcounter : counter < equalityBlockCount shape) :
    let boundary := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + attempt * 6)
        (equalityBoundary_fits attempt
          (hattempt.trans
            (firstEqualityAccepted_lt shape answers hgood).le))
    let active := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + attempt * 6 + counter) (by
        have hc := equalityBlockCount_le_six shape
        have hc6 : counter ≤ 6 := by
          norm_num [equalityAttemptBlocks] at hc ⊢
          omega
        have ha := firstEqualityAccepted_lt shape answers hgood
        have hnext := equalityBoundary_fits (attempt + 1) (by omega)
        omega)
    active.status = .live ∧ active.equalityPoint = none ∧
      active.transcript = boundary.transcript := by
  dsimp only
  have hattemptLt : attempt < rejectionTrials :=
    lt_of_le_of_lt hattempt
      (firstEqualityAccepted_lt shape answers hgood)
  have hcounterSix : counter ≤ 6 :=
    (Nat.le_of_lt hcounter).trans (equalityBlockCount_le_six shape)
  have hfit : equalityOffset + attempt * 6 + counter ≤
      productionSamplingSlots := by
    have := equalityBoundary_fits (attempt + 1) (by omega)
    omega
  let boundary := rawControlUntil shape causalSecret completion witness coins
    prelude answers (equalityOffset + attempt * 6)
      (equalityBoundary_fits attempt hattemptLt.le)
  let localAnswers :=
    window (equalityOffset + attempt * 6) counter hfit answers
  have hboundary := rawControlUntil_equality_boundary_live_none shape
    causalSecret completion witness coins prelude answers hgood attempt hattempt
  have hlocal := equalityPrefix_control_fields shape attempt boundary counter
    localAnswers hcounter hboundary.1 hboundary.2.1
  have hraw := rawEqualityAttempt_eq_of_final_live shape causalSecret completion
    witness coins attempt hattemptLt counter hcounterSix boundary localAnswers
    hlocal.1
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers (equalityOffset + attempt * 6) counter hfit
  rw [hadd, hraw]
  exact hlocal

set_option maxRecDepth 10000 in
theorem rawControlUntil_equality_boundary_transcript_strict_succ
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (attempt : ℕ)
    (hbound : attempt + 1 ≤ firstEqualityAccepted shape answers hgood) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        (equalityOffset + attempt * 6)
          (equalityBoundary_fits attempt (by
            have := firstEqualityAccepted_lt shape answers hgood
            omega))).transcript.length <
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (equalityOffset + (attempt + 1) * 6)
          (equalityBoundary_fits (attempt + 1) (by
            have := firstEqualityAccepted_lt shape answers hgood
            omega))).transcript.length := by
  have hattempt : attempt < rejectionTrials := by
    have := firstEqualityAccepted_lt shape answers hgood
    omega
  have hbefore := rawControlUntil_equality_boundary_live_none shape
    causalSecret completion witness coins prelude answers hgood attempt (by omega)
  have hrejected := before_firstEqualityAccepted_rejects shape answers hgood
    attempt (by omega) hattempt
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers (equalityOffset + attempt * 6)
      (equalityBoundary_fits attempt hattempt.le)
  have hlocal := equalityAttempt_live_none_of_rejected_before_cap shape attempt
    before (equalityAttemptAnswers answers ⟨attempt, hattempt⟩)
    hbefore.1 hbefore.2.1 hrejected (by
      have := firstEqualityAccepted_lt shape answers hgood
      omega)
  have hstrict := equalityAttempt_transcript_length_strict shape attempt before
    (equalityAttemptAnswers answers ⟨attempt, hattempt⟩)
    hbefore.1 hbefore.2.1 hbefore.2.2
  have hstep := rawControlUntil_equality_boundary_step shape causalSecret
    completion witness coins prelude answers attempt hattempt hlocal.1
  rw [hstep]
  exact hstrict

theorem rawControlUntil_equality_boundaries_transcript_strict
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : ℕ) (hlt : left < right)
    (hright : right ≤ firstEqualityAccepted shape answers hgood) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        (equalityOffset + left * 6)
          (equalityBoundary_fits left (by
            have := firstEqualityAccepted_lt shape answers hgood
            omega))).transcript.length <
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (equalityOffset + right * 6)
          (equalityBoundary_fits right (by
            have := firstEqualityAccepted_lt shape answers hgood
            omega))).transcript.length := by
  have hstep := rawControlUntil_equality_boundary_transcript_strict_succ shape
    causalSecret completion witness coins prelude answers hgood left (by omega)
  have hmono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers
    (equalityOffset + (left + 1) * 6) (equalityOffset + right * 6)
    (by omega) (equalityBoundary_fits right (by
      have := firstEqualityAccepted_lt shape answers hgood
      omega))
  exact hstep.trans_le hmono

end VeiledFlock.ProductionSamplingScheduleEqualityActive

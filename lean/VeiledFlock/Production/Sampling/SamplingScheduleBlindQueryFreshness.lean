import VeiledFlock.Production.Sampling.SamplingScheduleBlindSegmentLength

/-! # Fiat--Shamir freshness across the blind-grinding seed -/

namespace VeiledFlock.ProductionSamplingScheduleBlindQueryFreshness

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingLayoutBounds
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindSegment
open VeiledFlock.ProductionSamplingScheduleBlindSegmentLength
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole

set_option maxRecDepth 10000 in
theorem fiat_query_not_in_blind_grinding
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (point : List Byte)
    (hfiat : isFiatShamirPoint point)
    (hquery : rawQuery shape causalSecret completion witness coins round
      control = some point) :
    ¬ (blindGrindingOffset ≤ round ∧ round < blindChallengeOffset) := by
  rintro ⟨hlower, hupper⟩
  have hskipBound : equalitySkipBlocks ≤ blindGrindingOffset := by decide
  have hequalityBound : zerocheckOffset ≤ blindGrindingOffset := by decide
  have hzeroBound : blindStateOffset ≤ blindGrindingOffset := by decide
  have hskip : ¬ round < equalitySkipBlocks := by omega
  have hequality : ¬ round < zerocheckOffset := by omega
  have hzero : ¬ round < blindStateOffset := by omega
  have hblindState : ¬ round < blindGrindingOffset := by omega
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hdone : control.stageDone
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState, hupper,
      hdone] at hquery
  · cases hpow : control.powState with
    | none =>
        simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState, hupper,
          hdone, hpow] at hquery
    | some state =>
        simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState, hupper,
          hdone, hpow] at hquery
        subst point
        exact fiatShamir_ne_pow hfiat state _ rfl

set_option maxRecDepth 10000 in
theorem blind_state_fiat_query_length_strict
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (right : Fin productionSamplingSlots) (hlt : blindStateOffset < right.val)
    (leftPoint rightPoint : List Byte)
    (hleftFiat : isFiatShamirPoint leftPoint)
    (hrightFiat : isFiatShamirPoint rightPoint)
    (hleft : rawQuery shape causalSecret completion witness coins
      blindStateOffset
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  have hrightAfter : blindChallengeOffset ≤ right.val := by
    by_contra hnot
    have hlower : blindGrindingOffset ≤ right.val := by
      rw [blindGrindingOffset_eq_state_succ]
      omega
    exact fiat_query_not_in_blind_grinding shape causalSecret completion witness
      coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le)
      rightPoint hrightFiat hright ⟨hlower, by omega⟩
  have hequality := rawControlUntil_equality_live_some shape causalSecret
    completion witness coins prelude answers
    (equality_accepted_of_not_globalBad shape answers hgood)
  have hzero := rawControlUntil_zerocheck_live_some shape causalSecret
    completion witness coins prelude answers hequality
  have hbound :
      (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindStateOffset blindStateOffset_le_slots).transcript.length + 17 ≤
      (blindSegmentResult shape causalSecret completion witness coins
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindStateOffset blindStateOffset_le_slots)
        (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩)
        (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
          answers)).transcript.length :=
    blindSegmentResult_add_seventeen shape causalSecret completion witness coins
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindStateOffset blindStateOffset_le_slots)
      (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩)
      (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
        answers) hzero.1
      (exists_blindGrinding_answer_of_not_globalBad shape answers hgood)
  have hlength := rawControlUntil_blind_length_eq_segment shape causalSecret
    completion witness coins prelude answers hzero.1
  have hmono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers blindChallengeOffset right.val
    hrightAfter right.isLt.le
  have hleftLength := rawQuery_afterZerocheck_fiat_length_le shape causalSecret
    completion witness coins blindStateOffset
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      blindStateOffset blindStateOffset_le_slots)
    leftPoint (by rfl) hleftFiat hleft
  have hrightLength := rawQuery_afterZerocheck_fiat_length_ge shape causalSecret
    completion witness coins right
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      right right.isLt.le) rightPoint (by omega) hrightFiat hright
  omega

end VeiledFlock.ProductionSamplingScheduleBlindQueryFreshness

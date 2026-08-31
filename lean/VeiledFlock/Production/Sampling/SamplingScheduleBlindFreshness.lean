import VeiledFlock.Production.Sampling.SamplingSchedulePostFreshness

/-! # Freshness across the blind-grinding seed -/

namespace VeiledFlock.ProductionSamplingScheduleBlindFreshness

open VeiledFlock.AdaptiveOracleProgramming
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
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole

set_option maxRecDepth 10000 in
set_option maxHeartbeats 300000 in
theorem rawBlindGrinding_add_seventeen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (stateAnswer : OracleBlock)
    (answers : Fin maxBlindTrials → OracleBlock)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin maxBlindTrials,
      blindGrindingGood shape (answers trial)) :
    let withState := rawStep shape causalSecret completion witness coins
      blindStateOffset control stateAnswer
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      blindGrindingOffset maxBlindTrials withState answers
    control.transcript.length + 17 ≤ result.transcript.length := by
  dsimp only
  rw [rawStep_blindState shape causalSecret completion witness coins control
    stateAnswer hstatus]
  let withState : Control shape :=
    { control with
      powState := some stateAnswer
      stageDone := false
      stageBlocks := [] }
  have hstate : withState.status = .live := by simp [withState, hstatus]
  have hdone : withState.stageDone = false := by simp [withState]
  have htranscript : withState.transcript = control.transcript := by
    simp [withState]
  rw [iterateFrom_eq_blindGrinding shape causalSecret completion witness coins
    maxBlindTrials withState answers (by rfl) hstate]
  rw [← htranscript]
  exact iterateFrom_blindGrinding_done_add_seventeen blindGrindingOffset
    maxBlindTrials withState answers hdone
      (blindGrindingLoop_live_done_of_exists maxBlindTrials withState answers
        (by rfl) hstate hexists).2

/-
set_option maxRecDepth 10000 in
set_option maxHeartbeats 300000 in
theorem rawControlUntil_blind_add_seventeen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hbefore : (rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset (by decide)).status = .live)
    (hexists : ∃ trial : Fin maxBlindTrials,
      blindGrindingGood shape
        (window blindGrindingOffset maxBlindTrials (by decide) answers trial)) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindStateOffset (by decide)).transcript.length + 17 ≤
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset (by decide)).transcript.length := by
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset (by decide)
  let grindAnswers := window blindGrindingOffset maxBlindTrials (by decide) answers
  have hlocal := rawBlindGrinding_add_seventeen shape causalSecret completion
    witness coins before (answers ⟨blindStateOffset, by decide⟩) grindAnswers
    hbefore hexists
  have hstate :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset (by decide) =
        rawStep shape causalSecret completion witness coins blindStateOffset
          before (answers ⟨blindStateOffset, by decide⟩) := by
    have hs := rawControlUntil_succ shape causalSecret completion witness coins
      prelude answers ⟨blindStateOffset, by decide⟩
    simpa [blindGrindingOffset, blindStateWidth] using hs
  have hfinal := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers blindGrindingOffset maxBlindTrials (by decide)
  have hround : blindGrindingOffset + maxBlindTrials = blindChallengeOffset := rfl
  have hfinal' :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindChallengeOffset (by decide) =
        iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset maxBlindTrials
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindGrindingOffset (by decide)) grindAnswers := by
    simpa only [hround] using hfinal
  rw [hstate] at hfinal'
  change before.transcript.length + 17 ≤ _
  rw [hfinal']
  exact hlocal
-/

/-
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
        answers blindStateOffset (by decide)) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  have hrightAfter : blindChallengeOffset ≤ right.val := by
    by_contra hnot
    have hlower : blindGrindingOffset ≤ right.val := by
      have hnext : blindGrindingOffset = blindStateOffset + 1 := by decide
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
  have hblindGrowth := rawControlUntil_blind_add_seventeen shape causalSecret
    completion witness coins prelude answers hzero.1
    (exists_blindGrinding_answer_of_not_globalBad shape answers hgood)
  have hmono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers blindChallengeOffset right.val
    hrightAfter right.isLt.le
  have hleftLength := rawQuery_afterZerocheck_fiat_length_eq shape causalSecret
    completion witness coins blindStateOffset
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      blindStateOffset (by decide)) leftPoint (by rfl) hleftFiat hleft
  have hrightLength := rawQuery_afterZerocheck_fiat_length_eq shape causalSecret
    completion witness coins right
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      right right.isLt.le) rightPoint (by omega) hrightFiat hright
  omega
-/

end VeiledFlock.ProductionSamplingScheduleBlindFreshness

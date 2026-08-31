import VeiledFlock.Production.Sampling.SamplingScheduleQueryFreshness

/-!
# Strict separation after zerocheck

Every ordinary live Fiat--Shamir query consumes its answer immediately and
extends the transcript by 18 bytes.  Consequently its serialized query is
strictly shorter than every later Fiat--Shamir query.  PoW-state seed rounds
are isolated separately because their transcript extension occurs only after
the first successful grinding answer.
-/

namespace VeiledFlock.ProductionSamplingSchedulePostFreshness

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole

theorem rawControlUntil_succ
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (round : Fin productionSamplingSlots) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (round.val + 1) (Nat.succ_le_of_lt round.isLt) =
      rawStep shape causalSecret completion witness coins round.val
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers round.val round.isLt.le)
        (answers round) := by
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers round.val 1 (Nat.succ_le_of_lt round.isLt)
  simpa [iterateFrom, iterateList, window] using hadd

theorem regular_post_fiat_query_length_strict
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (left right : Fin productionSamplingSlots)
    (hleftLower : blindStateOffset ≤ left.val)
    (hleftNotState : ¬ isPowStateRound left.val)
    (hlt : left.val < right.val) (leftPoint rightPoint : List Byte)
    (hleftFiat : VeiledFlock.ProductionFraming.isFiatShamirPoint leftPoint)
    (hrightFiat : VeiledFlock.ProductionFraming.isFiatShamirPoint rightPoint)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  let leftControl := rawControlUntil shape causalSecret completion witness coins
    prelude answers left left.isLt.le
  let rightControl := rawControlUntil shape causalSecret completion witness coins
    prelude answers right right.isLt.le
  have hleftLength := rawQuery_afterZerocheck_fiat_length_le shape causalSecret
    completion witness coins left leftControl leftPoint hleftLower hleftFiat
    hleft
  have hrightLower : blindStateOffset ≤ right.val := hleftLower.trans (by omega)
  have hrightLength := rawQuery_afterZerocheck_fiat_length_ge shape causalSecret
    completion witness coins right rightControl rightPoint hrightLower hrightFiat
    hright
  have hstep := rawStep_afterZerocheck_fiat_add_eighteen shape causalSecret
    completion witness coins left leftControl (answers left) leftPoint
    hleftLower hleftNotState hleftFiat hleft
  have hsucc := rawControlUntil_succ shape causalSecret completion witness coins
    prelude answers left
  have hmono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers (left.val + 1) right.val (by omega)
    right.isLt.le
  dsimp only [leftControl, rightControl] at hleftLength hrightLength hstep
  rw [hsucc] at hmono
  omega

theorem iterateFrom_blindGrinding_transcript_length_mono
    {shape : BatchShape} (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock) :
    control.transcript.length ≤
      (iterateFrom blindGrindingStep start rounds control answers).transcript.length := by
  induction rounds with
  | zero => simp [iterateFrom, iterateList]
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      exact (ih (fun index ↦ answers index.castSucc)).trans
        (blindGrindingStep_transcript_length_mono _ _ _)

theorem iterateFrom_blindGrinding_done_add_seventeen
    {shape : BatchShape} (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hstartDone : control.stageDone = false)
    (hdone : (iterateFrom blindGrindingStep start rounds control answers).stageDone =
      true) :
    control.transcript.length + 17 ≤
      (iterateFrom blindGrindingStep start rounds control answers).transcript.length := by
  induction rounds with
  | zero => simp [iterateFrom, iterateList, hstartDone] at hdone
  | succ rounds ih =>
      rw [iterateFrom_succ_last] at hdone ⊢
      let before := iterateFrom blindGrindingStep start rounds control
        (fun index ↦ answers index.castSucc)
      by_cases hbeforeDone : before.stageDone = true
      · have hprefix := ih (fun index ↦ answers index.castSucc) hbeforeDone
        exact hprefix.trans
          (blindGrindingStep_transcript_length_mono _ _ _)
      · have hbeforeFalse : before.stageDone = false := by
          exact Bool.eq_false_of_not_eq_true hbeforeDone
        have hprefix := iterateFrom_blindGrinding_transcript_length_mono start
          rounds control (fun index ↦ answers index.castSucc)
        by_cases hgood : blindGrindingGood shape (answers (Fin.last rounds))
        · simp [blindGrindingStep, before, hbeforeFalse, hgood,
            VeiledFlock.ProductionGrinding.afterGrind_length]
          omega
        · simp [blindGrindingStep, before, hbeforeFalse, hgood] at hdone
          split at hdone <;> simp_all

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
  let withState := rawStep shape causalSecret completion witness coins
    blindStateOffset before (answers ⟨blindStateOffset, by decide⟩)
  have hwithEq : withState =
      { before with
        powState := some (answers ⟨blindStateOffset, by decide⟩)
        stageDone := false
        stageBlocks := [] } := by
    exact rawStep_blindState shape causalSecret completion witness coins before
      (answers ⟨blindStateOffset, by decide⟩) hbefore
  have hwithStatus : withState.status = .live := by
    rw [hwithEq]
    exact hbefore
  have hwithDone : withState.stageDone = false := by simp [hwithEq]
  have hwithTranscript : withState.transcript = before.transcript := by
    simp [hwithEq]
  let grindAnswers :=
    window blindGrindingOffset maxBlindTrials (by decide) answers
  have hloop := blindGrindingLoop_live_done_of_exists maxBlindTrials withState
    grindAnswers (by rfl) hwithStatus hexists
  have hadd := iterateFrom_blindGrinding_done_add_seventeen
    blindGrindingOffset maxBlindTrials withState grindAnswers hwithDone hloop.2
  have hstate :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset (by decide) = withState := by
    have hs := rawControlUntil_succ shape causalSecret completion witness coins
      prelude answers ⟨blindStateOffset, by decide⟩
    simpa [blindGrindingOffset, blindStateWidth] using hs
  have hfinal := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers blindGrindingOffset maxBlindTrials (by decide)
  have hrawEq := iterateFrom_eq_blindGrinding shape causalSecret completion
    witness coins maxBlindTrials withState grindAnswers (by rfl) hwithStatus
  have hfinalLength :
      (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindChallengeOffset (by decide)).transcript.length =
        (iterateFrom blindGrindingStep blindGrindingOffset maxBlindTrials
          withState grindAnswers).transcript.length := by
    calc
      _ = (iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset maxBlindTrials
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindGrindingOffset (by decide))
          (window blindGrindingOffset maxBlindTrials (by decide)
            answers)).transcript.length := by
              exact congrArg (fun result ↦ result.transcript.length)
                (by simpa [blindChallengeOffset, blindGrindingWidth] using hfinal)
      _ = (iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset maxBlindTrials withState
          grindAnswers).transcript.length := by rw [hstate]
      _ = (iterateFrom blindGrindingStep blindGrindingOffset maxBlindTrials
          withState grindAnswers).transcript.length := by
            exact congrArg (fun result ↦ result.transcript.length) hrawEq
  change before.transcript.length + 17 ≤ _
  rw [hfinalLength, ← hwithTranscript]
  exact hadd

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
  have hleftLength := rawQuery_afterZerocheck_fiat_length_le shape causalSecret
    completion witness coins blindStateOffset
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      blindStateOffset (by decide)) leftPoint (by rfl) hleftFiat hleft
  have hrightLength := rawQuery_afterZerocheck_fiat_length_ge shape causalSecret
    completion witness coins right
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      right right.isLt.le) rightPoint (by omega) hrightFiat hright
  omega
-/


end VeiledFlock.ProductionSamplingSchedulePostFreshness

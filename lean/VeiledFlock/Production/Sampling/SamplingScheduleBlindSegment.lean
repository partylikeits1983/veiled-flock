import VeiledFlock.Production.Sampling.SamplingLayoutBounds
import VeiledFlock.Production.Sampling.SamplingScheduleBlindExplicit
import VeiledFlock.Production.Sampling.SamplingSchedulePostFreshness

/-!
# Opaque blind-grinding segment

The public cap is large enough that repeatedly exposing the recursive
`iterateFrom` term causes expensive definitional reduction.  This definition
keeps that exact execution opaque; the projection theorems below still prove
its relationship to the literal production control.
-/

namespace VeiledFlock.ProductionSamplingScheduleBlindSegment

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingLayoutBounds
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindExplicit
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

noncomputable def blindSegmentResult
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (before : Control shape) (stateAnswer : OracleBlock)
    (answers : Fin maxBlindTrials → OracleBlock) : Control shape :=
  iterateFrom (rawStep shape causalSecret completion witness coins)
    blindGrindingOffset maxBlindTrials
    (rawStep shape causalSecret completion witness coins blindStateOffset
      before stateAnswer) answers

set_option maxRecDepth 10000 in
theorem blindSegmentResult_add_seventeen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (before : Control shape) (stateAnswer : OracleBlock)
    (answers : Fin maxBlindTrials → OracleBlock)
    (hstatus : before.status = .live)
    (hexists : ∃ trial : Fin maxBlindTrials,
      blindGrindingGood (answers trial)) :
    before.transcript.length + 17 ≤
      (blindSegmentResult shape causalSecret completion witness coins before
        stateAnswer answers).transcript.length := by
  unfold blindSegmentResult
  exact rawBlindGrinding_add_seventeen_explicit shape causalSecret completion
    witness coins before stateAnswer answers hstatus hexists

set_option maxRecDepth 10000 in
theorem rawControlUntil_blind_eq_segment
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hbefore : (rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset blindStateOffset_le_slots).status = .live) :
    let before := rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset blindStateOffset_le_slots
    rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset blindChallengeOffset_le_slots =
      blindSegmentResult shape causalSecret completion witness coins before
        (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩)
        (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
          answers) := by
  dsimp only
  have hstate := rawControlUntil_succ shape causalSecret completion witness coins
    prelude answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩
  have hfinal := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers blindGrindingOffset maxBlindTrials blindGrinding_window_fits
  unfold blindSegmentResult
  have hstate' :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset blindGrindingOffset_le_slots =
        rawStep shape causalSecret completion witness coins blindStateOffset
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindStateOffset blindStateOffset_le_slots)
          (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩) := by
    simpa only [blindGrindingOffset_eq_state_succ] using hstate
  have hfinal' :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindChallengeOffset blindChallengeOffset_le_slots =
        iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset maxBlindTrials
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindGrindingOffset blindGrindingOffset_le_slots)
          (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
            answers) := by
    simpa only [blindChallengeOffset_eq_grinding_end] using hfinal
  calc
    _ = iterateFrom (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset maxBlindTrials
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindGrindingOffset blindGrindingOffset_le_slots)
        (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
          answers) := hfinal'
    _ = _ := congrArg
      (fun initial ↦ iterateFrom
        (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset maxBlindTrials initial
        (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
          answers)) hstate'

end VeiledFlock.ProductionSamplingScheduleBlindSegment

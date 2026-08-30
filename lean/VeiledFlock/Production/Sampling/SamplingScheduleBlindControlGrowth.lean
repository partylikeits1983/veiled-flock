import VeiledFlock.Production.Sampling.SamplingScheduleBlindSegmentLength

/-! # Blind-grinding growth in the whole raw control -/

namespace VeiledFlock.ProductionSamplingScheduleBlindControlGrowth

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
open VeiledFlock.ProductionSamplingScheduleBlindSegment
open VeiledFlock.ProductionSamplingScheduleBlindSegmentLength
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawControlUntil_blind_add_seventeen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hbefore : (rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset blindStateOffset_le_slots).status = .live)
    (hexists : ∃ trial : Fin maxBlindTrials,
      blindGrindingGood
        (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
          answers trial)) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindStateOffset blindStateOffset_le_slots).transcript.length + 17 ≤
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset blindChallengeOffset_le_slots).transcript.length := by
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset blindStateOffset_le_slots
  let segment := blindSegmentResult shape causalSecret completion witness coins
    before (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩)
    (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits answers)
  have hbound : before.transcript.length + 17 ≤ segment.transcript.length :=
    blindSegmentResult_add_seventeen shape causalSecret completion witness coins
      before (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩)
      (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
        answers) hbefore hexists
  have hlength := rawControlUntil_blind_length_eq_segment shape causalSecret completion
    witness coins prelude answers hbefore
  change before.transcript.length + 17 ≤ _
  calc
    _ ≤ segment.transcript.length := hbound
    _ = _ := hlength.symm

end VeiledFlock.ProductionSamplingScheduleBlindControlGrowth

import VeiledFlock.ProductionSamplingScheduleBlindSegment

/-! # Length projection of the opaque blind segment -/

namespace VeiledFlock.ProductionSamplingScheduleBlindSegmentLength

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
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawControlUntil_blind_length_eq_segment
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hbefore : (rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset blindStateOffset_le_slots).status = .live) :
    let before := rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset blindStateOffset_le_slots
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset blindChallengeOffset_le_slots).transcript.length =
      (blindSegmentResult shape causalSecret completion witness coins before
        (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩)
        (window blindGrindingOffset maxBlindTrials blindGrinding_window_fits
          answers)).transcript.length := by
  exact congrArg (fun result ↦ result.transcript.length)
    (rawControlUntil_blind_eq_segment shape causalSecret completion witness
      coins prelude answers hbefore)

end VeiledFlock.ProductionSamplingScheduleBlindSegmentLength

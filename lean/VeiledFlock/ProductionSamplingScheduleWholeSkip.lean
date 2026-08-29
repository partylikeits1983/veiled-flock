import VeiledFlock.ProductionSamplingScheduleSemantics

namespace VeiledFlock.ProductionSamplingScheduleWhole

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
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem rawControlUntil_skip
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        equalityOffset (by decide) =
      afterSkipControl shape prelude
        (window 0 equalitySkipBlocks (by decide) answers) := by
  change rawControlUntil shape causalSecret completion witness coins prelude
      answers (0 + equalitySkipBlocks) _ = _
  calc
    _ = iterateFrom (rawStep shape causalSecret completion witness coins) 0
        equalitySkipBlocks
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers 0 _)
        (window 0 equalitySkipBlocks (by decide) answers) :=
      rawControlUntil_add shape causalSecret completion witness coins prelude
        answers 0 equalitySkipBlocks (by decide)
    _ = iterateFrom (rawStep shape causalSecret completion witness coins) 0
        equalitySkipBlocks (initialControl shape prelude)
        (window 0 equalitySkipBlocks (by decide) answers) := by rfl
    _ = afterSkipControl shape prelude
        (window 0 equalitySkipBlocks (by decide) answers) :=
      rawSkipPhase_eq shape causalSecret completion witness coins prelude _

end VeiledFlock.ProductionSamplingScheduleWhole

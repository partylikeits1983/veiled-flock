import VeiledFlock.Production.Sampling.SamplingScheduleWholeEquality

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

theorem rawControlUntil_zerocheck_live_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hbefore :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers zerocheckOffset (by decide)).status = .live ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers zerocheckOffset (by decide)).equalityPoint.isSome = true) :
    let result := rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset (by decide)
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  dsimp only
  have hlocal :
      let result := iterateFrom
        (rawStep shape causalSecret completion witness coins)
        zerocheckOffset maxProgrammedPoints
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers zerocheckOffset (by decide))
        (window zerocheckOffset zerocheckWidth (by decide) answers)
      result.status = .live ∧ result.equalityPoint.isSome = true :=
    rawZerocheck_live_some shape causalSecret completion witness coins
      maxProgrammedPoints _
      (window zerocheckOffset zerocheckWidth (by decide) answers) (by rfl)
      hbefore.1 hbefore.2
  have heq : rawControlUntil shape causalSecret completion witness coins prelude
      answers blindStateOffset (by decide) =
      iterateFrom (rawStep shape causalSecret completion witness coins)
        zerocheckOffset zerocheckWidth
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers zerocheckOffset (by decide))
        (window zerocheckOffset zerocheckWidth (by decide) answers) := by
    change rawControlUntil shape causalSecret completion witness coins prelude
      answers (zerocheckOffset + zerocheckWidth) _ = _
    exact rawControlUntil_add shape causalSecret completion witness coins
      prelude answers zerocheckOffset zerocheckWidth (by decide)
  constructor
  · exact (congrArg Control.status heq).trans hlocal.1
  · exact (congrArg (fun control ↦ control.equalityPoint.isSome) heq).trans
      hlocal.2

end VeiledFlock.ProductionSamplingScheduleWhole

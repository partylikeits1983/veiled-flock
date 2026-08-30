import VeiledFlock.Production.Sampling.SamplingScheduleWholeSkip

namespace VeiledFlock.ProductionSamplingScheduleWhole

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
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem rawControlUntil_equality_live_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (haccepted : ∃ attempt : Fin rejectionTrials,
      accepted (sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (equalityFlatEquiv
          (window equalityOffset equalityWidth (by decide) answers) attempt)))) :
    let result := rawControlUntil shape causalSecret completion witness coins
      prelude answers zerocheckOffset (by decide)
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  have hskipEq := rawControlUntil_skip shape causalSecret completion witness
    coins prelude answers
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers equalityOffset (by decide)
  have hbeforeStatus : before.status = .live := by
    change (rawControlUntil shape causalSecret completion witness coins prelude
      answers equalityOffset _).status = .live
    rw [hskipEq]
    exact afterSkipControl_status shape prelude _
  have hbeforeSkip : before.skip.isSome = true := by
    change (rawControlUntil shape causalSecret completion witness coins prelude
      answers equalityOffset _).skip.isSome = true
    rw [hskipEq]
    exact afterSkipControl_skip_isSome shape prelude _
  have hlocal := rawEquality_live_some shape causalSecret completion witness
    coins before (window equalityOffset equalityWidth (by decide) answers)
    hbeforeStatus hbeforeSkip haccepted
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers equalityOffset equalityWidth (by decide)
  change
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (equalityOffset + equalityWidth) _).status = .live ∧
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (equalityOffset + equalityWidth) _).equalityPoint.isSome = true
  rw [hadd]
  exact hlocal

end VeiledFlock.ProductionSamplingScheduleWhole

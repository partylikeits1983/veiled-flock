import VeiledFlock.ProductionSamplingScheduleBeforeInjective
import VeiledFlock.ProductionSamplingSchedulePostFiatInjective

/-! # Separation from pre-zerocheck to post-zerocheck Fiat queries -/

namespace VeiledFlock.ProductionSamplingScheduleBeforePostFreshness

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
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
open VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness

theorem before_zerocheck_query_length_lt_post_fiat_query_length
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : Fin productionSamplingSlots)
    (hleftUpper : left.val < zerocheckOffset)
    (hrightLower : blindStateOffset ≤ right.val)
    (leftPoint rightPoint : List Byte)
    (hrightFiat : isFiatShamirPoint rightPoint)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  let last := zerocheckOffset + (programmedPoints shape - 1)
  have hpoints : 0 < programmedPoints shape := by
    cases shape <;> decide
  have hleftLast : left.val ≤ last := by
    dsimp only [last]
    omega
  have hlastLt : last < productionSamplingSlots := by
    have := zerocheckActiveEnd_le_slots shape
    dsimp only [last]
    omega
  have hleftMono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers left.val last hleftLast hlastLt.le
  have hgrowth := rawControlUntil_active_zerocheck_growth shape causalSecret
    completion witness coins prelude answers hgood
  have hendRight : zerocheckOffset + programmedPoints shape ≤ right.val := by
    have hmax :=
      VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness.programmedPoints_le_max
        shape
    have hblind : zerocheckOffset + maxProgrammedPoints = blindStateOffset := rfl
    omega
  have hrightMono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers
    (zerocheckOffset + programmedPoints shape) right.val hendRight right.isLt.le
  have hleftLength := rawQuery_beforeZerocheck_length_eq shape causalSecret
    completion witness coins left
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      left left.isLt.le) leftPoint hleftUpper hleft
  have hrightLength := rawQuery_afterZerocheck_fiat_length_eq shape causalSecret
    completion witness coins right
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      right right.isLt.le) rightPoint hrightLower hrightFiat hright
  dsimp only [last] at hleftMono hgrowth
  have hell : 1 ≤ VeiledFlock.ProductionMaskLayout.ell := by decide
  omega

end VeiledFlock.ProductionSamplingScheduleBeforePostFreshness

import VeiledFlock.ProductionSamplingScheduleBeforePostFreshness

/-! # Injectivity of every Fiat--Shamir query in the literal schedule -/

namespace VeiledFlock.ProductionSamplingScheduleFiatInjective

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
open VeiledFlock.ProductionSamplingScheduleBeforeInjective
open VeiledFlock.ProductionSamplingScheduleBeforePostFreshness
open VeiledFlock.ProductionSamplingSchedulePostFiatInjective
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole
open VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness

set_option maxRecDepth 10000 in
theorem rawQuery_fiat_injective
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : Fin productionSamplingSlots) (hlt : left.val < right.val)
    (leftPoint rightPoint : List Byte)
    (hleftFiat : isFiatShamirPoint leftPoint)
    (hrightFiat : isFiatShamirPoint rightPoint)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint ≠ rightPoint := by
  intro heq
  by_cases hleftBefore : left.val < zerocheckOffset
  · by_cases hrightBefore : right.val < zerocheckOffset
    · exact rawQuery_before_zerocheck_injective shape causalSecret completion
        witness coins prelude answers hgood left right hlt hleftBefore
        hrightBefore leftPoint rightPoint hleft hright heq
    have hrightZero : zerocheckOffset ≤ right.val := by omega
    by_cases hrightZeroUpper : right.val < blindStateOffset
    · have hlength :=
        beforeZerocheck_query_length_lt_zerocheck_query_length shape
          causalSecret completion witness coins prelude answers left right
          hleftBefore hrightZero hrightZeroUpper leftPoint rightPoint hleft hright
      rw [heq] at hlength
      omega
    have hrightPost : blindStateOffset ≤ right.val := by omega
    have hlength := before_zerocheck_query_length_lt_post_fiat_query_length
      shape causalSecret completion witness coins prelude answers hgood left
      right hleftBefore hrightPost leftPoint rightPoint hrightFiat hleft hright
    rw [heq] at hlength
    omega
  have hleftZero : zerocheckOffset ≤ left.val := by omega
  by_cases hleftZeroUpper : left.val < blindStateOffset
  · by_cases hrightZeroUpper : right.val < blindStateOffset
    · have hlength := zerocheck_query_length_strict shape causalSecret
        completion witness coins prelude answers left right hleftZero
        hleftZeroUpper (by omega) hrightZeroUpper hlt leftPoint rightPoint hleft
        hright
      rw [heq] at hlength
      omega
    have hlength := zerocheck_query_length_lt_post_fiat_query_length shape
      causalSecret completion witness coins prelude answers hgood left right
      hleftZero hleftZeroUpper (by omega) leftPoint rightPoint hrightFiat hleft
      hright
    rw [heq] at hlength
    omega
  have hlength := post_fiat_query_length_strict shape causalSecret completion
    witness coins prelude answers hgood left right (by omega) hlt leftPoint
    rightPoint hleftFiat hrightFiat hleft hright
  rw [heq] at hlength
  omega

end VeiledFlock.ProductionSamplingScheduleFiatInjective

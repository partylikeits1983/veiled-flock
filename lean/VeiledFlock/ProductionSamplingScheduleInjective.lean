import VeiledFlock.ProductionSamplingSchedulePowOrigin

/-! # Pairwise injectivity of the complete literal production schedule -/

namespace VeiledFlock.ProductionSamplingScheduleInjective

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
open VeiledFlock.ProductionSamplingScheduleFiatInjective
open VeiledFlock.ProductionSamplingSchedulePowOrigin
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem rawQuery_pow_round_injective
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : Fin productionSamplingSlots)
    (leftPoint rightPoint : List Byte)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint)
    (hleftNonFiat : ¬ isFiatShamirPoint leftPoint)
    (hrightNonFiat : ¬ isFiatShamirPoint rightPoint)
    (heq : leftPoint = rightPoint) :
    left.val = right.val := by
  rcases rawQuery_pow_origin shape causalSecret completion witness coins prelude
    hprelude answers hgood left leftPoint hleft hleftNonFiat with
    ⟨leftOrigin, hleftRound, hleftPoint⟩
  rcases rawQuery_pow_origin shape causalSecret completion witness coins prelude
    hprelude answers hgood right rightPoint hright hrightNonFiat with
    ⟨rightOrigin, hrightRound, hrightPoint⟩
  let leftQuery : PowQuery :=
    { state := answers (powStateIndex leftOrigin.site)
      nonce := BitVec.ofNat 64 leftOrigin.nonce }
  let rightQuery : PowQuery :=
    { state := answers (powStateIndex rightOrigin.site)
      nonce := BitVec.ofNat 64 rightOrigin.nonce }
  have hencoded : encodePowQuery leftQuery = encodePowQuery rightQuery := by
    simpa [leftQuery, rightQuery, ProductionPowOrigin.point, encodePowQuery] using
      hleftPoint.symm.trans (heq.trans hrightPoint)
  have hqueryEq := encodePowQuery_injective hencoded
  have hstateEq :
      answers (powStateIndex leftOrigin.site) =
        answers (powStateIndex rightOrigin.site) := by
    exact congrArg PowQuery.state hqueryEq
  have hsiteEq : leftOrigin.site = rightOrigin.site :=
    (powStateAnswers_injective_of_not_globalBad shape answers hgood) hstateEq
  have hnonceBits :
      (BitVec.ofNat 64 leftOrigin.nonce : Word64) =
        BitVec.ofNat 64 rightOrigin.nonce := by
    exact congrArg PowQuery.nonce hqueryEq
  have hnonceEq : leftOrigin.nonce = rightOrigin.nonce :=
    word64_ofNat_injective_below leftOrigin.nonce_lt rightOrigin.nonce_lt
      hnonceBits
  have horiginEq : leftOrigin = rightOrigin := by
    cases leftOrigin
    cases rightOrigin
    simp_all
  rw [hleftRound, hrightRound, horiginEq]

set_option maxRecDepth 10000 in
theorem rawQuery_complete_injective
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : Fin productionSamplingSlots) (hlt : left.val < right.val)
    (leftPoint rightPoint : List Byte)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint ≠ rightPoint := by
  intro heq
  by_cases hleftFiat : isFiatShamirPoint leftPoint
  · by_cases hrightFiat : isFiatShamirPoint rightPoint
    · exact rawQuery_fiat_injective shape causalSecret completion witness coins
        prelude answers hgood left right hlt leftPoint rightPoint hleftFiat
        hrightFiat hleft hright heq
    rcases rawQuery_pow_origin shape causalSecret completion witness coins prelude
      hprelude answers hgood right rightPoint hright hrightFiat with
      ⟨origin, _, horiginPoint⟩
    exact fiatShamir_ne_pow hleftFiat
      (answers (powStateIndex origin.site)) (BitVec.ofNat 64 origin.nonce)
      (heq.trans (by simpa [ProductionPowOrigin.point] using horiginPoint))
  · by_cases hrightFiat : isFiatShamirPoint rightPoint
    · rcases rawQuery_pow_origin shape causalSecret completion witness coins
        prelude hprelude answers hgood left leftPoint hleft hleftFiat with
        ⟨origin, _, horiginPoint⟩
      exact fiatShamir_ne_pow hrightFiat
        (answers (powStateIndex origin.site)) (BitVec.ofNat 64 origin.nonce)
        (heq.symm.trans (by
          simpa [ProductionPowOrigin.point] using horiginPoint))
    have hroundEq := rawQuery_pow_round_injective shape causalSecret completion
      witness coins prelude hprelude answers hgood left right leftPoint
      rightPoint hleft hright hleftFiat hrightFiat heq
    omega

end VeiledFlock.ProductionSamplingScheduleInjective

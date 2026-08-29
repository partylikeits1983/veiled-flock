import VeiledFlock.ProductionSamplingSchedulePostFiatInjective

/-! # Separation from zerocheck queries to later Fiat--Shamir inputs -/

namespace VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole

theorem programmedPoints_positive (shape : BatchShape) :
    0 < programmedPoints shape := by
  cases shape <;> decide

theorem programmedPoints_le_max (shape : BatchShape) :
    programmedPoints shape ≤ maxProgrammedPoints := by
  cases shape <;> decide

theorem zerocheckActiveEnd_le_slots (shape : BatchShape) :
    zerocheckOffset + programmedPoints shape ≤ productionSamplingSlots := by
  have hpoints := programmedPoints_le_max shape
  have hblind : zerocheckOffset + maxProgrammedPoints = blindStateOffset := rfl
  have hslots : blindStateOffset < productionSamplingSlots := by
    rw [productionSamplingSlots_eq]
    decide
  omega

set_option maxRecDepth 10000 in
theorem rawControlUntil_before_last_zerocheck_live_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    let last := zerocheckOffset + (programmedPoints shape - 1)
    let fit : last ≤ productionSamplingSlots := by
      have := zerocheckActiveEnd_le_slots shape
      omega
    let control := rawControlUntil shape causalSecret completion witness coins
      prelude answers last fit
    control.status = .live ∧ control.equalityPoint.isSome = true := by
  dsimp only
  have hequality := rawControlUntil_equality_live_some shape causalSecret
    completion witness coins prelude answers
    (equality_accepted_of_not_globalBad shape answers hgood)
  have hrounds : programmedPoints shape - 1 ≤ maxProgrammedPoints := by
    have := programmedPoints_le_max shape
    omega
  have hfit : zerocheckOffset + (programmedPoints shape - 1) ≤
      productionSamplingSlots := by
    have := zerocheckActiveEnd_le_slots shape
    omega
  have hlocal := rawZerocheck_live_some shape causalSecret completion witness
    coins (programmedPoints shape - 1)
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      zerocheckOffset (Nat.le_trans (Nat.le_add_right _ _) hfit))
    (window zerocheckOffset (programmedPoints shape - 1) hfit answers)
    hrounds hequality.1 hequality.2
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers zerocheckOffset (programmedPoints shape - 1) hfit
  rw [hadd]
  exact hlocal

set_option maxRecDepth 10000 in
theorem rawControlUntil_active_zerocheck_growth
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    let last := zerocheckOffset + (programmedPoints shape - 1)
    let lastFit : last < productionSamplingSlots := by
      have := zerocheckActiveEnd_le_slots shape
      exact lt_of_lt_of_le (Nat.lt_succ_self last) (by
        have hp := programmedPoints_positive shape
        omega)
    let before := rawControlUntil shape causalSecret completion witness coins
      prelude answers last lastFit.le
    before.transcript.length +
        2 * (10 + 16 * VeiledFlock.ProductionMaskLayout.ell) + 2 +
        programmedPoints shape * 54 ≤
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (zerocheckOffset + programmedPoints shape)
          (zerocheckActiveEnd_le_slots shape)).transcript.length := by
  dsimp only
  let last := zerocheckOffset + (programmedPoints shape - 1)
  have hp := programmedPoints_positive shape
  have hend : last + 1 = zerocheckOffset + programmedPoints shape := by
    dsimp only [last]
    omega
  have hlastLt : last < productionSamplingSlots := by
    have := zerocheckActiveEnd_le_slots shape
    omega
  have hprefix := rawControlUntil_before_last_zerocheck_live_some shape
    causalSecret completion witness coins prelude answers hgood
  have hsucc := rawControlUntil_succ shape causalSecret completion witness coins
    prelude answers ⟨last, hlastLt⟩
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers last hlastLt.le
  have htrial : programmedPoints shape - 1 < maxProgrammedPoints := by
    have := programmedPoints_le_max shape
    omega
  have hstep := rawStep_zerocheck shape causalSecret completion witness coins
    (programmedPoints shape - 1) htrial before (answers ⟨last, hlastLt⟩)
    hprefix.1
  have hprefixSome : before.equalityPoint.isSome = true := by
    dsimp only [before]
    exact hprefix.2
  cases heq : before.equalityPoint with
  | none => simp [heq] at hprefixSome
  | some equalityPoint =>
      have hsite : programmedPoints shape - 1 < programmedPoints shape := by
        omega
      have hlast : programmedPoints shape - 1 + 1 = programmedPoints shape := by
        omega
      have hlength :
          (zerocheckStep shape causalSecret completion witness coins last before
            (answers ⟨last, hlastLt⟩)).transcript.length =
          before.transcript.length +
            2 * (10 + 16 * VeiledFlock.ProductionMaskLayout.ell) + 2 +
            programmedPoints shape * 54 := by
        simp [zerocheckStep, last, heq, hsite, hlast,
          VeiledFlock.ProductionSamplingSchedule.afterZerocheck_length]
      have hsuccLength := congrArg (fun control ↦ control.transcript.length)
        hsucc
      rw [hstep, hlength] at hsuccLength
      simpa only [hend] using hsuccLength.symm.le

set_option maxRecDepth 10000 in
theorem zerocheck_query_length_lt_post_fiat_query_length
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : Fin productionSamplingSlots)
    (hleftLower : zerocheckOffset ≤ left.val)
    (hleftUpper : left.val < blindStateOffset)
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
  have hleftSite : left.val - zerocheckOffset < programmedPoints shape := by
    have hquery := hleft
    have hskip : ¬left.val < equalitySkipBlocks := by
      have : equalitySkipBlocks ≤ zerocheckOffset := by decide
      omega
    have hequality : ¬left.val < zerocheckOffset := by omega
    by_cases hstatus :
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers left left.isLt.le).status != .live
    · simp [rawQuery, hstatus] at hquery
    · cases heq :
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers left left.isLt.le).equalityPoint with
      | none =>
          simp [rawQuery, hstatus, hskip, hequality, hleftUpper, heq] at hquery
      | some point =>
          by_contra hnot
          simp [rawQuery, hstatus, hskip, hequality, hleftUpper, heq, hnot]
            at hquery
  let last := zerocheckOffset + (programmedPoints shape - 1)
  have hleftLast : left.val ≤ last := by
    dsimp only [last]
    have hp := programmedPoints_positive shape
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
    have := programmedPoints_le_max shape
    have hblind : zerocheckOffset + maxProgrammedPoints = blindStateOffset := rfl
    omega
  have hrightMono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers
    (zerocheckOffset + programmedPoints shape) right.val hendRight right.isLt.le
  have hleftLength := rawQuery_zerocheck_length_eq shape causalSecret completion
    witness coins left
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      left left.isLt.le) leftPoint hleftLower hleftUpper hleft
  have hrightLength := rawQuery_afterZerocheck_fiat_length_eq shape causalSecret
    completion witness coins right
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      right right.isLt.le) rightPoint hrightLower hrightFiat hright
  dsimp only [last] at hleftMono hgrowth
  omega

end VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness

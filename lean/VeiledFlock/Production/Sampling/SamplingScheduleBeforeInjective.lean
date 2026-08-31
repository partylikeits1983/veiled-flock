import VeiledFlock.Production.Sampling.SamplingScheduleEqualityQuery

/-! # Injectivity of all pre-zerocheck production queries -/

namespace VeiledFlock.ProductionSamplingScheduleBeforeInjective

open VeiledFlock.ChallengeSampling
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
open VeiledFlock.ProductionSamplingScheduleEqualityActive
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingScheduleEqualityQuery
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole
open VeiledFlock.ProductionTranscriptFraming

set_option maxRecDepth 10000 in
theorem rawControlUntil_skip_prefix_fields
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (round : ℕ)
    (hround : round < equalitySkipBlocks) :
    let control := rawControlUntil shape causalSecret completion witness coins
      prelude answers round (by
        have : equalitySkipBlocks ≤ productionSamplingSlots := by decide
        omega)
    control.status = .live ∧ control.transcript = prelude := by
  norm_num [equalitySkipBlocks] at hround
  interval_cases round <;>
    simp [rawControlUntil, iterateFrom, iterateList, rawStep, initialControl,
      equalitySkipBlocks]

theorem rawControlUntil_equality_zero_transcript_strict
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) :
    prelude.length <
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers equalityOffset (by decide)).transcript.length := by
  rw [rawControlUntil_skip]
  simp [afterSkipControl, initialControl, afterSlice_length]
  omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_before_zerocheck_injective
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : Fin productionSamplingSlots) (hlt : left.val < right.val)
    (hleftUpper : left.val < zerocheckOffset)
    (hrightUpper : right.val < zerocheckOffset)
    (leftPoint rightPoint : List Byte)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint ≠ rightPoint := by
  intro heq
  by_cases hrightSkip : right.val < equalitySkipBlocks
  · have hleftSkip : left.val < equalitySkipBlocks := hlt.trans hrightSkip
    have hleftControl := rawControlUntil_skip_prefix_fields shape causalSecret
      completion witness coins prelude answers left hleftSkip
    have hrightControl := rawControlUntil_skip_prefix_fields shape causalSecret
      completion witness coins prelude answers right hrightSkip
    have hleftPoint : leftPoint =
        slicePoint prelude 6 (BitVec.ofNat 64 left.val) := by
      simpa [rawQuery, hleftSkip, hleftControl.1, hleftControl.2] using hleft.symm
    have hrightPoint : rightPoint =
        slicePoint prelude 6 (BitVec.ofNat 64 right.val) := by
      simpa [rawQuery, hrightSkip, hrightControl.1, hrightControl.2] using
        hright.symm
    have hcounter := slicePoint_counter_injective prelude 6
      (hleftPoint.symm.trans (heq.trans hrightPoint))
    have hroundEq := word64_ofNat_injective_below
      (left.isLt.trans (by rw [productionSamplingSlots_eq]; norm_num))
      (right.isLt.trans (by rw [productionSamplingSlots_eq]; norm_num)) hcounter
    omega
  have hrightLower : equalityOffset ≤ right.val := by
    norm_num [equalityOffset, equalitySkipBlocks] at hrightSkip ⊢
    omega
  by_cases hleftSkip : left.val < equalitySkipBlocks
  · have hleftControl := rawControlUntil_skip_prefix_fields shape causalSecret
      completion witness coins prelude answers left hleftSkip
    have hleftLength := rawQuery_beforeZerocheck_length_eq shape causalSecret
      completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) leftPoint hleftUpper hleft
    have hrightLength := rawQuery_beforeZerocheck_length_eq shape causalSecret
      completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) rightPoint hrightUpper hright
    have hrightMeta := rawQuery_active_equality_metadata shape causalSecret
      completion witness coins prelude answers hgood right rightPoint hrightLower
      hrightUpper hright
    dsimp only at hrightMeta
    let rightOffset := right.val - equalityOffset
    let rightAttempt := rightOffset / equalityAttemptBlocks
    let rightCounter := rightOffset % equalityAttemptBlocks
    have hrightRound :
        right.val = equalityOffset + rightAttempt * 7 + rightCounter :=
      hrightMeta.1
    have hrightBound :
        rightAttempt ≤ firstEqualityAccepted shape answers hgood :=
      hrightMeta.2.1
    have hrightCap : rightAttempt ≤ rejectionTrials :=
      hrightBound.trans
        (firstEqualityAccepted_lt shape answers hgood).le
    have hrightActive := rawControlUntil_active_equality_fields shape causalSecret
      completion witness coins prelude answers hgood rightAttempt rightCounter
      hrightMeta.2.1 hrightMeta.2.2.1
    have hrightTranscript :
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers right right.isLt.le).transcript =
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + rightAttempt * 7)
            (equalityBoundary_fits rightAttempt hrightCap)).transcript := by
      simpa only [← hrightRound] using hrightActive.2.2
    have hzeroStrict := rawControlUntil_equality_zero_transcript_strict shape
      causalSecret completion witness coins prelude answers
    have hboundaryMono :=
      VeiledFlock.ProductionSamplingScheduleFreshness.rawControlUntil_transcript_length_mono
        shape causalSecret completion witness coins prelude answers equalityOffset
        (equalityOffset + rightAttempt * 7) (by omega)
        (equalityBoundary_fits rightAttempt hrightCap)
    rw [hleftControl.2] at hleftLength
    rw [hrightTranscript] at hrightLength
    rw [heq] at hleftLength
    omega
  have hleftLower : equalityOffset ≤ left.val := by
    norm_num [equalityOffset, equalitySkipBlocks] at hleftSkip ⊢
    omega
  have hleftMeta := rawQuery_active_equality_metadata shape causalSecret
    completion witness coins prelude answers hgood left leftPoint hleftLower
    hleftUpper hleft
  have hrightMeta := rawQuery_active_equality_metadata shape causalSecret
    completion witness coins prelude answers hgood right rightPoint hrightLower
    hrightUpper hright
  dsimp only at hleftMeta hrightMeta
  let leftOffset := left.val - equalityOffset
  let leftAttempt := leftOffset / equalityAttemptBlocks
  let leftCounter := leftOffset % equalityAttemptBlocks
  let rightOffset := right.val - equalityOffset
  let rightAttempt := rightOffset / equalityAttemptBlocks
  let rightCounter := rightOffset % equalityAttemptBlocks
  have hleftRound :
      left.val = equalityOffset + leftAttempt * 7 + leftCounter := hleftMeta.1
  have hrightRound :
      right.val = equalityOffset + rightAttempt * 7 + rightCounter :=
    hrightMeta.1
  have hleftBound :
      leftAttempt ≤ firstEqualityAccepted shape answers hgood := hleftMeta.2.1
  have hrightBound :
      rightAttempt ≤ firstEqualityAccepted shape answers hgood :=
    hrightMeta.2.1
  have hleftCap : leftAttempt ≤ rejectionTrials :=
    hleftBound.trans (firstEqualityAccepted_lt shape answers hgood).le
  have hrightCap : rightAttempt ≤ rejectionTrials :=
    hrightBound.trans (firstEqualityAccepted_lt shape answers hgood).le
  have hleftActive := rawControlUntil_active_equality_fields shape causalSecret
    completion witness coins prelude answers hgood leftAttempt leftCounter
    hleftMeta.2.1 hleftMeta.2.2.1
  have hrightActive := rawControlUntil_active_equality_fields shape causalSecret
    completion witness coins prelude answers hgood rightAttempt rightCounter
    hrightMeta.2.1 hrightMeta.2.2.1
  have hleftTranscript :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le).transcript =
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (equalityOffset + leftAttempt * 7)
          (equalityBoundary_fits leftAttempt hleftCap)).transcript := by
    simpa only [← hleftRound] using hleftActive.2.2
  have hrightTranscript :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le).transcript =
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (equalityOffset + rightAttempt * 7)
          (equalityBoundary_fits rightAttempt hrightCap)).transcript := by
    simpa only [← hrightRound] using hrightActive.2.2
  have hattemptOrder : leftAttempt ≤ rightAttempt := by
    have hleftMod : leftCounter < 7 := by
      dsimp only [leftCounter, leftOffset]
      norm_num [equalityAttemptBlocks]
      exact Nat.mod_lt _ (by decide)
    have hrightMod : rightCounter < 7 := by
      dsimp only [rightCounter, rightOffset]
      norm_num [equalityAttemptBlocks]
      exact Nat.mod_lt _ (by decide)
    omega
  rcases hattemptOrder.eq_or_lt with hattemptEq | hattemptLt
  ·
    have htranscript :
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers left left.isLt.le).transcript =
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers right right.isLt.le).transcript := by
      rw [hleftTranscript, hrightTranscript]
      simp only [hattemptEq]
    have hpointEq :
        slicePoint
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers left left.isLt.le).transcript
            (m shape - kSkip - 7) (BitVec.ofNat 64 leftCounter) =
          slicePoint
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers right right.isLt.le).transcript
            (m shape - kSkip - 7) (BitVec.ofNat 64 rightCounter) :=
      hleftMeta.2.2.2.symm.trans (heq.trans hrightMeta.2.2.2)
    have hpointEq' :
        slicePoint
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers left left.isLt.le).transcript
            (m shape - kSkip - 7) (BitVec.ofNat 64 leftCounter) =
          slicePoint
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers left left.isLt.le).transcript
            (m shape - kSkip - 7) (BitVec.ofNat 64 rightCounter) := by
      rw [← htranscript] at hpointEq
      exact hpointEq
    have hcounterBits := slicePoint_counter_injective
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le).transcript (m shape - kSkip - 7) hpointEq'
    have hcounterEq := word64_ofNat_injective_below
      (show leftCounter < 2 ^ 64 by
        dsimp only [leftCounter, leftOffset]
        exact (Nat.mod_lt _ (by decide)).trans (by decide))
      (show rightCounter < 2 ^ 64 by
        dsimp only [rightCounter, rightOffset]
        exact (Nat.mod_lt _ (by decide)).trans (by decide)) hcounterBits
    omega
  · have hboundaryStrict :=
      rawControlUntil_equality_boundaries_transcript_strict shape causalSecret
        completion witness coins prelude answers hgood leftAttempt rightAttempt
        hattemptLt hrightBound
    have hcontrolStrict :
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers left left.isLt.le).transcript.length <
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers right right.isLt.le).transcript.length := by
      rw [hleftTranscript, hrightTranscript]
      exact hboundaryStrict
    have hleftLength := rawQuery_beforeZerocheck_length_eq shape causalSecret
      completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) leftPoint hleftUpper hleft
    have hrightLength := rawQuery_beforeZerocheck_length_eq shape causalSecret
      completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) rightPoint hrightUpper hright
    rw [heq] at hleftLength
    omega

end VeiledFlock.ProductionSamplingScheduleBeforeInjective

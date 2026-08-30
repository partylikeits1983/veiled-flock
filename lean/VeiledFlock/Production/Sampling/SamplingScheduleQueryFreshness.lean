import VeiledFlock.Production.Sampling.SamplingScheduleFreshness

/-!
# Exact query-length separation for the production sampling schedule

The duplicate-suppressing probability experiment may be identified with the
literal production oracle execution only after proving that every live
Fiat--Shamir input is fresh.  This module records the exact length formulas
used by that proof.  PoW inputs are treated separately through their encoded
state and nonce.
-/

namespace VeiledFlock.ProductionSamplingScheduleQueryFreshness

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleAudit
open VeiledFlock.ProductionSamplingScheduleClassification
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionZerocheckSchedule
open VeiledFlock.TranscriptSchedule
open VeiledFlock.UniquePositionSampling

theorem slicePoint_counter_injective (transcript : List Byte) (length : ℕ) :
    Function.Injective (slicePoint transcript length) := by
  intro left right heq
  unfold slicePoint at heq
  exact encodeLEList_injective (List.append_cancel_left heq)

theorem word64_ofNat_injective_below {left right : ℕ}
    (hleft : left < 2 ^ 64) (hright : right < 2 ^ 64)
    (heq : (BitVec.ofNat 64 left : ProductionFraming.Word64) =
      BitVec.ofNat 64 right) :
    left = right := by
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hnat
  exact hnat

theorem zerocheckRealByteSchedule_point_length_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (transcript : List Byte) (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (answers : History (Outcome := OracleBlock) round) :
    (zerocheckRealByteSchedule shape causalSecret completion transcript witness
      coins round answers).length =
      transcript.length +
        2 * (10 + 16 * VeiledFlock.ProductionMaskLayout.ell) + 2 +
        round * 54 + 8 := by
  let masked :=
    VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  let step := scalarRoundStep consumeScalar
    (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
    (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2)
    (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2)
  change (appendSchedule (start shape transcript masked) step round
    answers).length = _
  simp only [appendSchedule, List.length_append, counterZero_length]
  rw [appendState_length (start shape transcript masked) step 54]
  · rw [start_length]
  · exact scalarRoundStep_length consumeScalar consumeScalar_length
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (encodeField_length
        VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
        causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2)
      (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
        causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_beforeZerocheck_length_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (point : List Byte)
    (hround : round < zerocheckOffset)
    (hquery : rawQuery shape causalSecret completion witness coins round
      control = some point) :
    point.length = control.transcript.length + 18 := by
  classical
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hskip : round < equalitySkipBlocks
  · simp [rawQuery, hstatus, hskip] at hquery
    subst point
    simp
  have hequality : round < zerocheckOffset := hround
  let offset := round - equalityOffset
  let counter := offset % equalityAttemptBlocks
  by_cases hsome : control.equalityPoint.isSome
  · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome] at hquery
  by_cases hcounter : counter < equalityBlockCount shape
  · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome,
      hcounter] at hquery
    subst point
    simp
  · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome,
      hcounter] at hquery

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_zerocheck_length_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (point : List Byte)
    (hlower : zerocheckOffset ≤ round) (hupper : round < blindStateOffset)
    (hquery : rawQuery shape causalSecret completion witness coins round
      control = some point) :
    point.length = control.transcript.length +
      2 * (10 + 16 * VeiledFlock.ProductionMaskLayout.ell) + 2 +
      (round - zerocheckOffset) * 54 + 8 := by
  classical
  have hskipBound : equalitySkipBlocks ≤ zerocheckOffset := by decide
  have hskip : ¬ round < equalitySkipBlocks := by omega
  have hequality : ¬ round < zerocheckOffset := by omega
  have hzero : round < blindStateOffset := hupper
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  cases heq : control.equalityPoint with
  | none =>
      simp [rawQuery, hstatus, hskip, hequality, hzero, heq] at hquery
  | some equalityPoint =>
      by_cases hsite : round - zerocheckOffset < programmedPoints shape
      · simp [rawQuery, hstatus, hskip, hequality, hzero, heq, hsite] at hquery
        subst point
        exact zerocheckRealByteSchedule_point_length_eq shape causalSecret
          completion control.transcript witness coins
          (round - zerocheckOffset)
          (historyFromList control.zerocheckAnswers
            (round - zerocheckOffset))
      · exfalso
        simpa [rawQuery, hstatus, hskip, hequality, hzero, heq, hsite] using
          hquery

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_afterZerocheck_fiat_length_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (point : List Byte)
    (hround : blindStateOffset ≤ round)
    (hfiat : isFiatShamirPoint point)
    (hquery : rawQuery shape causalSecret completion witness coins round
      control = some point) :
    point.length = control.transcript.length + 10 := by
  classical
  have hskipBound : equalitySkipBlocks ≤ blindStateOffset := by decide
  have hzeroBound : zerocheckOffset ≤ blindStateOffset := by decide
  have hskip : ¬ round < equalitySkipBlocks := by omega
  have hequality : ¬ round < zerocheckOffset := by omega
  have hzero : ¬ round < blindStateOffset := by omega
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hblindState : round < blindGrindingOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState] at hquery
    subst point
    simp
  by_cases hblindGrind : round < blindChallengeOffset
  · by_cases hdone : control.stageDone
    · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hdone] at hquery
    · cases hpow : control.powState with
      | none =>
          simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
            hblindGrind, hdone, hpow] at hquery
      | some state =>
          simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
            hblindGrind, hdone, hpow] at hquery
          subst point
          exact False.elim (fiatShamir_ne_pow hfiat state _ rfl)
  by_cases hblind : round < multiplicationAlphaOffset
  · have hpoint := nonzeroStageQuery_some blindChallengeOffset round control
      point (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind] using hquery)
    subst point
    simp
  by_cases halpha : round < outerChallengeOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.2.symm
    subst point
    simp
  by_cases houterChallenge : round < outerPositionsOffset
  · have hpoint := nonzeroStageQuery_some outerChallengeOffset round control
      point (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge] using hquery)
    subst point
    simp
  by_cases houterPositions : round < linearPositionsOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.symm
    subst point
    simp
  by_cases hlinearPositions : round < linearRhoOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.symm
    subst point
    simp
  by_cases hlinearRho : round < hadamardPositionsOffset
  · have hpoint := nonzeroStageQuery_some linearRhoOffset round control point
      (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho] using hquery)
    subst point
    simp
  by_cases hhadamardPositions : round < hadamardRhoOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.symm
    subst point
    simp
  by_cases hhadamardRho : round < productCoefficientOffset
  · have hpoint := nonzeroStageQuery_some hadamardRhoOffset round control point
      (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho] using
          hquery)
    subst point
    simp
  by_cases hproduct : round < ligeritoOffset
  · have hpoint := nonzeroStageQuery_some productCoefficientOffset round
      control point (by simpa [rawQuery, hstatus, hskip, hequality, hzero,
        hblindState, hblindGrind, hblind, halpha, houterChallenge,
        houterPositions, hlinearPositions, hlinearRho, hhadamardPositions,
        hhadamardRho, hproduct] using hquery)
    subst point
    simp
  by_cases hligerito : round < productionSamplingSlots
  · let offset := round - ligeritoOffset
    let within := offset % ligeritoSiteWidth
    by_cases hstate : within = 0
    · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
        hproduct, hligerito, offset, within, hstate] at hquery
      subst point
      simp
    · by_cases hdone : control.stageDone
      · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
          hblindGrind, hblind, halpha, houterChallenge, houterPositions,
          hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
          hproduct, hligerito, offset, within, hstate, hdone] at hquery
      · cases hpow : control.powState with
        | none =>
            simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
              hblindGrind, hblind, halpha, houterChallenge, houterPositions,
              hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
              hproduct, hligerito, offset, within, hstate, hdone, hpow] at hquery
        | some state =>
            simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
              hblindGrind, hblind, halpha, houterChallenge, houterPositions,
              hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
              hproduct, hligerito, offset, within, hstate, hdone, hpow] at hquery
            subst point
            exact False.elim (fiatShamir_ne_pow hfiat state _ rfl)
  · simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct, hligerito] using hquery

theorem zerocheck_query_length_strict
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : VeiledFlock.ProductionSamplingBadTape.SamplingAnswerTape)
    (left right : Fin productionSamplingSlots)
    (hleftLower : zerocheckOffset ≤ left.val)
    (hleftUpper : left.val < blindStateOffset)
    (hrightLower : zerocheckOffset ≤ right.val)
    (hrightUpper : right.val < blindStateOffset)
    (hlt : left.val < right.val) (leftPoint rightPoint : List Byte)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  let leftControl := rawControlUntil shape causalSecret completion witness coins
    prelude answers left left.isLt.le
  let rightControl := rawControlUntil shape causalSecret completion witness coins
    prelude answers right right.isLt.le
  have hleftLength := rawQuery_zerocheck_length_eq shape causalSecret completion
    witness coins left leftControl leftPoint hleftLower hleftUpper hleft
  have hrightLength := rawQuery_zerocheck_length_eq shape causalSecret completion
    witness coins right rightControl rightPoint hrightLower hrightUpper hright
  have hmono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers left right hlt.le right.isLt.le
  dsimp only [leftControl, rightControl] at hleftLength hrightLength
  omega

theorem beforeZerocheck_query_length_lt_zerocheck_query_length
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : VeiledFlock.ProductionSamplingBadTape.SamplingAnswerTape)
    (left right : Fin productionSamplingSlots)
    (hleftRound : left.val < zerocheckOffset)
    (hrightLower : zerocheckOffset ≤ right.val)
    (hrightUpper : right.val < blindStateOffset)
    (leftPoint rightPoint : List Byte)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  let leftControl := rawControlUntil shape causalSecret completion witness coins
    prelude answers left left.isLt.le
  let rightControl := rawControlUntil shape causalSecret completion witness coins
    prelude answers right right.isLt.le
  have hleftLength := rawQuery_beforeZerocheck_length_eq shape causalSecret
    completion witness coins left leftControl leftPoint hleftRound hleft
  have hrightLength := rawQuery_zerocheck_length_eq shape causalSecret completion
    witness coins right rightControl rightPoint hrightLower hrightUpper hright
  have hlt : left.val < right.val := hleftRound.trans_le hrightLower
  have hmono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers left right hlt.le right.isLt.le
  have hell : 1 ≤ VeiledFlock.ProductionMaskLayout.ell := by decide
  dsimp only [leftControl, rightControl] at hleftLength hrightLength
  omega

theorem acceptScalar_active_transcript_length_eq
    {shape : BatchShape} (failed : Finset GhashField) (round start : ℕ)
    (control : Control shape) (answer : OracleBlock)
    (hactive : round - start = 0 ∨ control.stageDone = false) :
    (acceptScalar failed round start control answer).transcript.length =
      control.transcript.length + 18 := by
  classical
  by_cases hzero : round - start = 0
  · by_cases hfailed :
        VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
    · simp [acceptScalar, hzero, hfailed, afterScalar_length]
      split <;> simp_all [afterScalar_length]
    · simp [acceptScalar, hzero, hfailed, afterScalar_length]
  · have hdone : control.stageDone = false := hactive.resolve_left hzero
    by_cases hfailed :
        VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
    · simp [acceptScalar, hzero, hdone, hfailed, afterScalar_length]
      split <;> simp_all [afterScalar_length]
    · simp [acceptScalar, hzero, hdone, hfailed, afterScalar_length]

theorem acceptPositions_active_transcript_length_eq
    {shape : BatchShape} (project : GhashField → ℕ)
    (target start round : ℕ) (control : Control shape)
    (answer : OracleBlock)
    (hactive : round - start = 0 ∨ control.stageDone = false) :
    (acceptPositions project target start round control answer).transcript.length =
      control.transcript.length + 18 := by
  classical
  by_cases hzero : round - start = 0
  · simp [acceptPositions, hzero, afterScalar_length]
    split <;> simp_all [afterScalar_length]
    split <;> simp_all [afterScalar_length]
  · have hdone : control.stageDone = false := hactive.resolve_left hzero
    simp [acceptPositions, hzero, hdone, afterScalar_length]
    split <;> simp_all [afterScalar_length]
    split <;> simp_all [afterScalar_length]

def isPowStateRound (round : ℕ) : Prop :=
  round = blindStateOffset ∨
    (ligeritoOffset ≤ round ∧
      (round - ligeritoOffset) % ligeritoSiteWidth = 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawStep_afterZerocheck_fiat_add_eighteen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) (point : List Byte)
    (hround : blindStateOffset ≤ round)
    (hnotState : ¬ isPowStateRound round)
    (hfiat : isFiatShamirPoint point)
    (hquery : rawQuery shape causalSecret completion witness coins round
      control = some point) :
    (rawStep shape causalSecret completion witness coins round control
      answer).transcript.length = control.transcript.length + 18 := by
  classical
  have hskipBound : equalitySkipBlocks ≤ blindStateOffset := by decide
  have hzeroBound : zerocheckOffset ≤ blindStateOffset := by decide
  have hskip : ¬ round < equalitySkipBlocks := by omega
  have hequality : ¬ round < zerocheckOffset := by omega
  have hzero : ¬ round < blindStateOffset := by omega
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hblindState : round < blindGrindingOffset
  · have hroundEq : round = blindStateOffset := by
      have hwidth : blindGrindingOffset = blindStateOffset + 1 := by decide
      omega
    exact False.elim (hnotState (Or.inl hroundEq))
  by_cases hblindGrind : round < blindChallengeOffset
  · by_cases hdone : control.stageDone
    · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hdone] at hquery
    · cases hpow : control.powState with
      | none =>
          simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
            hblindGrind, hdone, hpow] at hquery
      | some state =>
          simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
            hblindGrind, hdone, hpow] at hquery
          subst point
          exact False.elim (fiatShamir_ne_pow hfiat state _ rfl)
  by_cases hblind : round < multiplicationAlphaOffset
  · have hactive : round - blindChallengeOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, nonzeroStageQuery] at hdetails
      exact hdetails.2.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind] using
        acceptScalar_active_transcript_length_eq zeroFailure round
          blindChallengeOffset control answer hactive
  by_cases halpha : round < outerChallengeOffset
  · have hactive : round - multiplicationAlphaOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha] at hdetails
      exact hdetails.2.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha] using
        acceptScalar_active_transcript_length_eq zeroOrOneFailure round
          multiplicationAlphaOffset control answer hactive
  by_cases houterChallenge : round < outerPositionsOffset
  · have hactive : round - outerChallengeOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge,
        nonzeroStageQuery] at hdetails
      exact hdetails.2.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge] using
        acceptScalar_active_transcript_length_eq zeroFailure round
          outerChallengeOffset control answer hactive
  by_cases houterPositions : round < linearPositionsOffset
  · have hactive : round - outerPositionsOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions] at hdetails
      exact hdetails.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions] using
        acceptPositions_active_transcript_length_eq
          (fun value ↦
            (VeiledFlock.ProductionPositionProjection.rustLowPosition
              (m shape - 11) value).val)
          (outerL0QueryCount shape) outerPositionsOffset round control answer
          hactive
  by_cases hlinearPositions : round < linearRhoOffset
  · have hactive : round - linearPositionsOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions] at hdetails
      exact hdetails.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions] using
        acceptPositions_active_transcript_length_eq
          (fun value ↦
            (VeiledFlock.ProductionPositionProjection.rustLowPosition
              13 value).val)
          veilQueryCount linearPositionsOffset round control answer hactive
  by_cases hlinearRho : round < hadamardPositionsOffset
  · have hactive : round - linearRhoOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, nonzeroStageQuery] at hdetails
      exact hdetails.2.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho] using
        acceptScalar_active_transcript_length_eq zeroFailure round
          linearRhoOffset control answer hactive
  by_cases hhadamardPositions : round < hadamardRhoOffset
  · have hactive : round - hadamardPositionsOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions] at hdetails
      exact hdetails.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions] using
        acceptPositions_active_transcript_length_eq
          (fun value ↦
            (VeiledFlock.ProductionPositionProjection.rustLowPosition
              11 value).val)
          veilQueryCount hadamardPositionsOffset round control answer hactive
  by_cases hhadamardRho : round < productCoefficientOffset
  · have hactive : round - hadamardRhoOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
        nonzeroStageQuery] at hdetails
      exact hdetails.2.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho] using
        acceptScalar_active_transcript_length_eq zeroFailure round
          hadamardRhoOffset control answer hactive
  by_cases hproduct : round < ligeritoOffset
  · have hactive : round - productCoefficientOffset = 0 ∨
        control.stageDone = false := by
      have hdetails := hquery
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
        hproduct, nonzeroStageQuery] at hdetails
      exact hdetails.2.1
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct] using
        acceptScalar_active_transcript_length_eq zeroFailure round
          productCoefficientOffset control answer hactive
  by_cases hligerito : round < productionSamplingSlots
  · let offset := round - ligeritoOffset
    let within := offset % ligeritoSiteWidth
    by_cases hstate : within = 0
    · exact False.elim (hnotState (Or.inr ⟨by omega, hstate⟩))
    · by_cases hdone : control.stageDone
      · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
          hblindGrind, hblind, halpha, houterChallenge, houterPositions,
          hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
          hproduct, hligerito, offset, within, hstate, hdone] at hquery
      · cases hpow : control.powState with
        | none =>
            simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
              hblindGrind, hblind, halpha, houterChallenge, houterPositions,
              hlinearPositions, hlinearRho, hhadamardPositions,
              hhadamardRho, hproduct, hligerito, offset, within, hstate,
              hdone, hpow] at hquery
        | some state =>
            simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
              hblindGrind, hblind, halpha, houterChallenge, houterPositions,
              hlinearPositions, hlinearRho, hhadamardPositions,
              hhadamardRho, hproduct, hligerito, offset, within, hstate,
              hdone, hpow] at hquery
            subst point
            exact False.elim (fiatShamir_ne_pow hfiat state _ rfl)
  · simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct, hligerito] using hquery

end VeiledFlock.ProductionSamplingScheduleQueryFreshness

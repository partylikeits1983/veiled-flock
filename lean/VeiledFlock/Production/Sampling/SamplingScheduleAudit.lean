import VeiledFlock.Production.Sampling.SamplingOracleSplit
import VeiledFlock.Production.Nizk.NizkViewCoupling

/-!
# Deterministic audit of the production sampling schedule

This module discharges the byte-length and domain-classification premises of
`ProductionSamplingOracleSplit` from the concrete state machine itself.
-/

namespace VeiledFlock.ProductionSamplingScheduleAudit

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingOracleSplit
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionZerocheckSchedule
open VeiledFlock.TranscriptSchedule
open VeiledFlock.UniquePositionSampling

theorem acceptScalar_transcript_length_le {shape : BatchShape}
    (failed : Finset GhashField) (round start : ℕ) (control : Control shape)
    (answer : OracleBlock) :
    (acceptScalar failed round start control answer).transcript.length ≤
      control.transcript.length + 18 := by
  classical
  by_cases hzero : round - start = 0
  · by_cases hfailed :
        VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
    · simp [acceptScalar, hzero, hfailed]
      split <;> simp_all [afterScalar_length]
    · simp [acceptScalar, hzero, hfailed, afterScalar_length]
  · by_cases hdone : control.stageDone
    · simp [acceptScalar, hzero, hdone]
    · by_cases hfailed :
          VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
      · simp [acceptScalar, hzero, hdone, hfailed]
        split <;> simp_all [afterScalar_length]
      · simp [acceptScalar, hzero, hdone, hfailed, afterScalar_length]

theorem acceptPositions_transcript_length_le {shape : BatchShape}
    (project : GhashField → ℕ) (target start round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (acceptPositions project target start round control answer).transcript.length ≤
      control.transcript.length + 18 := by
  classical
  by_cases hzero : round - start = 0
  · simp [acceptPositions, hzero]
    split <;> simp_all [afterScalar_length]
    split <;> simp_all [afterScalar_length]
  · by_cases hdone : control.stageDone
    · simp [acceptPositions, hzero, hdone]
    · by_cases haccept : target ≤
          (insert (project
            (VeiledFlock.ProductionScalarProjection.scalarFromBlock answer))
            control.positions).card
      · simp [acceptPositions, hzero, hdone, haccept, afterScalar_length]
      · simp [acceptPositions, hzero, hdone, haccept]
        split <;> simp_all [afterScalar_length]

theorem equalityStep_transcript_length_le (shape : BatchShape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (equalityStep shape round control answer).transcript.length ≤
      control.transcript.length + 4096 := by
  classical
  by_cases hsome : control.equalityPoint.isSome
  · simp [equalityStep, hsome]
  · let counter := (round - equalityOffset) % equalityAttemptBlocks
    by_cases hcounter : counter < equalityBlockCount shape
    · let base : Control shape := if counter = 0 then
          { control with equalityBlocks := [] }
        else control
      have hbase : base.transcript = control.transcript := by
        by_cases hcounterZero : counter = 0 <;> simp [base, hcounterZero]
      let blocks := base.equalityBlocks ++ [answer]
      let outer := sliceFromBlocks (m shape - kSkip - 7) blocks
      by_cases hlast : counter + 1 = equalityBlockCount shape
      · by_cases haccept : accepted outer
        · cases hskip : base.skip with
          | none => simp [equalityStep, hsome, counter, hcounter, base,
              blocks, outer, hlast, haccept, hskip, hbase]
          | some skip =>
              simp [equalityStep, hsome, counter, hcounter, base, blocks,
                outer, hlast, haccept, hskip, hbase, afterSlice_length]
              cases shape <;> norm_num [m, kSkip]
        · simp [equalityStep, hsome, counter, hcounter, base, blocks, outer,
            hlast, haccept, hbase]
          split <;> simp_all [afterSlice_length] <;>
            (cases shape <;> norm_num [m, kSkip])
      · simp [equalityStep, hsome, counter, hcounter, base,  hlast,
          hbase]
    · simp [equalityStep, hsome, counter, hcounter]

theorem zerocheckStep_transcript_length_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (zerocheckStep shape causalSecret completion witness coins round control
      answer).transcript.length ≤ control.transcript.length + 4096 := by
  classical
  cases heq : control.equalityPoint with
  | none => simp [zerocheckStep, heq]
  | some equalityPoint =>
      by_cases hsite : round - zerocheckOffset < programmedPoints shape
      · by_cases hlast : round - zerocheckOffset + 1 = programmedPoints shape
        · simp [zerocheckStep, heq, hsite, hlast,
            VeiledFlock.ProductionSamplingSchedule.afterZerocheck_length]
          cases shape <;>
            norm_num [programmedPoints,
              VeiledFlock.ProductionMaskLayout.ell, kSkip, m]
        · simp [zerocheckStep, heq, hsite, hlast]
      · simp [zerocheckStep, heq, hsite]

theorem blindGrindingStep_transcript_length_le {shape : BatchShape}
    (round : ℕ) (control : Control shape) (answer : OracleBlock) :
    (blindGrindingStep round control answer).transcript.length ≤
      control.transcript.length + 17 := by
  classical
  by_cases hdone : control.stageDone
  · simp [blindGrindingStep, hdone]
  · by_cases hgood : blindGrindingGood answer
    · simp [blindGrindingStep, hdone, hgood, afterGrind_length]
    · simp [blindGrindingStep, hdone, hgood]
      split <;> simp_all

theorem ligeritoStep_transcript_length_le {shape : BatchShape}
    (round : ℕ) (control : Control shape) (answer : OracleBlock) :
    (ligeritoStep round control answer).transcript.length ≤
      control.transcript.length + 17 := by
  classical
  by_cases hstate : (round - ligeritoOffset) % ligeritoSiteWidth = 0
  · simp [ligeritoStep, hstate]
  · by_cases hdone : control.stageDone
    · simp [ligeritoStep, hstate, hdone]
    · by_cases hgood : rustLeadingZeroBitsAtLeast maxLigeritoBits
          (by decide) answer
      · simp [ligeritoStep, hstate, hdone, hgood]
        split <;> simp_all [afterGrind_length]
      · simp [ligeritoStep, hstate, hdone, hgood]
        split <;> simp_all

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
/-- Every raw coordinate increases the live transcript by at most 4096
bytes.  Inactive coordinates and failed PoW attempts increase it by zero. -/
theorem rawStep_transcript_length_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (rawStep shape causalSecret completion witness coins round control answer).transcript.length ≤
      control.transcript.length + 4096 := by
  classical
  by_cases hstatus : control.status != .live
  · simp [rawStep, hstatus]
  by_cases hskip : round < equalitySkipBlocks
  · by_cases hlast : round + 1 = equalitySkipBlocks
    · simp [rawStep, hstatus, hskip, hlast, afterSlice_length]
    · simp [rawStep, hstatus, hskip, hlast]
  by_cases hequality : round < zerocheckOffset
  · simpa [rawStep, hstatus, hskip, hequality] using
      equalityStep_transcript_length_le shape round control answer
  by_cases hzero : round < blindStateOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero] using
      zerocheckStep_transcript_length_le shape causalSecret completion witness
        coins round control answer
  by_cases hblindState : round < blindGrindingOffset
  · simp [rawStep, hstatus, hskip, hequality, hzero, hblindState]
  by_cases hblindGrind : round < blindChallengeOffset
  · have h := blindGrindingStep_transcript_length_le (shape := shape) round
      control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind] using h.trans (by omega)
  by_cases hblind : round < multiplicationAlphaOffset
  · have h := acceptScalar_transcript_length_le zeroFailure round
      blindChallengeOffset control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind] using h.trans (by omega)
  by_cases halpha : round < outerChallengeOffset
  · have h := acceptScalar_transcript_length_le zeroOrOneFailure round
      multiplicationAlphaOffset control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha] using h.trans (by omega)
  by_cases houterChallenge : round < outerPositionsOffset
  · have h := acceptScalar_transcript_length_le zeroFailure round
      outerChallengeOffset control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge] using h.trans (by omega)
  by_cases houterPositions : round < linearPositionsOffset
  · have h := acceptPositions_transcript_length_le
      (fun value ↦ (rustLowPosition (m shape - 11) value).val)
      (outerL0QueryCount shape) outerPositionsOffset round control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions] using
        h.trans (by omega)
  by_cases hlinearPositions : round < linearRhoOffset
  · have h := acceptPositions_transcript_length_le
      (fun value ↦ (rustLowPosition 13 value).val) veilQueryCount
      linearPositionsOffset round control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions] using h.trans (by omega)
  by_cases hlinearRho : round < hadamardPositionsOffset
  · have h := acceptScalar_transcript_length_le zeroFailure round
      linearRhoOffset control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho] using h.trans (by omega)
  by_cases hhadamardPositions : round < hadamardRhoOffset
  · have h := acceptPositions_transcript_length_le
      (fun value ↦ (rustLowPosition 11 value).val) veilQueryCount
      hadamardPositionsOffset round control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions] using
        h.trans (by omega)
  by_cases hhadamardRho : round < productCoefficientOffset
  · have h := acceptScalar_transcript_length_le zeroFailure round
      hadamardRhoOffset control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho] using
        h.trans (by omega)
  by_cases hproduct : round < ligeritoOffset
  · have h := acceptScalar_transcript_length_le zeroFailure round
      productCoefficientOffset control answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct] using h.trans (by omega)
  by_cases hligerito : round < productionSamplingSlots
  · have h := ligeritoStep_transcript_length_le (shape := shape) round control
      answer
    simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct, hligerito] using h.trans (by omega)
  simp [rawStep, hstatus, hskip, hequality, hzero, hblindState, hblindGrind,
    hblind, halpha, houterChallenge, houterPositions, hlinearPositions,
    hlinearRho, hhadamardPositions, hhadamardRho, hproduct, hligerito]

theorem zerocheckRealByteSchedule_point_length_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (transcript : List Byte) (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (answers : History (Outcome := OracleBlock) round)
    (hround : round < programmedPoints shape) :
    (zerocheckRealByteSchedule shape causalSecret completion transcript witness
      coins round answers).length ≤ transcript.length + 4096 := by
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
    answers).length ≤ transcript.length + 4096
  simp only [appendSchedule, List.length_append, counterZero_length]
  rw [appendState_length (start shape transcript masked) step 54]
  · rw [start_length]
    have hround' : round ≤ programmedPoints shape - 1 := by omega
    cases shape <;>
      norm_num [programmedPoints, VeiledFlock.ProductionMaskLayout.ell, kSkip,
        m] at hround' ⊢ <;> omega
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

theorem nonzeroStageQuery_some {shape : BatchShape} (startRound round : ℕ)
    (control : Control shape) (point : List Byte)
    (hquery : nonzeroStageQuery startRound round control = some point) :
    point = scalarPoint control.transcript := by
  simp [nonzeroStageQuery] at hquery
  exact hquery.2.2.symm

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_length_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (point : List Byte)
    (hquery : rawQuery shape causalSecret completion witness coins round
      control = some point) :
    point.length ≤ control.transcript.length + 4096 := by
  classical
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hskip : round < equalitySkipBlocks
  · simp [rawQuery, hstatus, hskip] at hquery
    subst point
    simp
  by_cases hequality : round < zerocheckOffset
  · let offset := round - equalityOffset
    let counter := offset % equalityAttemptBlocks
    by_cases hsome : control.equalityPoint.isSome
    · simp [rawQuery, hstatus, hskip, hequality,   hsome] at hquery
    by_cases hcounter : counter < equalityBlockCount shape
    · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome,
        hcounter] at hquery
      subst point
      simp
    · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome,
        hcounter] at hquery
  by_cases hzero : round < blindStateOffset
  · let offset := round - zerocheckOffset
    cases heq : control.equalityPoint with
    | none =>
        simp [rawQuery, hstatus, hskip, hequality, hzero,  heq] at hquery
    | some equalityPoint =>
        by_cases hsite : offset < programmedPoints shape
        · simp [rawQuery, hstatus, hskip, hequality, hzero, offset, heq,
            hsite] at hquery
          subst point
          exact zerocheckRealByteSchedule_point_length_le shape causalSecret
            completion control.transcript witness coins offset
              (historyFromList control.zerocheckAnswers offset) hsite
        · simp [rawQuery, hstatus, hskip, hequality, hzero, offset, heq,
            hsite] at hquery
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
          simp
  by_cases hblind : round < multiplicationAlphaOffset
  · have hpoint := nonzeroStageQuery_some blindChallengeOffset round control
      point (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind] using hquery)
    subst point
    simp
  by_cases halpha : round < outerChallengeOffset
  · have hpoint : point = scalarPoint control.transcript := by
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha] at hquery
      exact hquery.2.2.symm
    subst point
    simp
  by_cases houterChallenge : round < outerPositionsOffset
  · have hpoint := nonzeroStageQuery_some outerChallengeOffset round control
      point (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge] using hquery)
    subst point
    simp
  by_cases houterPositions : round < linearPositionsOffset
  · have hpoint : point = scalarPoint control.transcript := by
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions] at hquery
      exact hquery.2.symm
    subst point
    simp
  by_cases hlinearPositions : round < linearRhoOffset
  · have hpoint : point = scalarPoint control.transcript := by
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions] at hquery
      exact hquery.2.symm
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
  · have hpoint : point = scalarPoint control.transcript := by
      simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions] at hquery
      exact hquery.2.symm
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
  · have hpoint := nonzeroStageQuery_some productCoefficientOffset round control
      point (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
        hproduct] using hquery)
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
    by_cases hdone : control.stageDone
    · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
        hproduct, hligerito, offset, within, hstate, hdone] at hquery
    cases hpow : control.powState with
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
        simp
  simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState, hblindGrind,
    hblind, halpha, houterChallenge, houterPositions, hlinearPositions,
    hlinearRho, hhadamardPositions, hhadamardRho, hproduct, hligerito] at hquery

def ControlLengthBound {shape : BatchShape} (prelude : List Byte) (round : ℕ)
    (control : Control shape) : Prop :=
  control.transcript.length ≤ prelude.length + round * 4096

set_option maxRecDepth 10000 in
theorem scheduledStep_lengthBound
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (prelude : List Byte) (round : ℕ) (control : ScheduledControl shape)
    (answer : OracleBlock)
    (hbound : ControlLengthBound prelude round control.raw) :
    ControlLengthBound prelude (round + 1)
      (scheduledStep shape causalSecret completion witness coins round control
        answer).raw := by
  classical
  unfold scheduledStep
  split
  · exact (rawStep_transcript_length_le shape causalSecret completion witness
      coins round control.raw answer).trans (by
        unfold ControlLengthBound at hbound
        omega)
  · split
    · simp only [ControlLengthBound] at hbound ⊢
      omega
    · exact (rawStep_transcript_length_le shape causalSecret completion witness
        coins round control.raw answer).trans (by
          unfold ControlLengthBound at hbound
          omega)

set_option maxRecDepth 10000 in
theorem scheduledControlAfter_lengthBound
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    {rounds : ℕ} (answers : History (Outcome := OracleBlock) rounds) :
    ControlLengthBound prelude rounds
      (scheduledControlAfter shape causalSecret completion witness coins
        prelude answers).raw := by
  induction rounds with
  | zero => simp [ControlLengthBound, scheduledControlAfter,
      initialScheduledControl, initialControl]
  | succ rounds ih =>
      exact scheduledStep_lengthBound shape causalSecret completion witness
        coins prelude rounds _ _ (ih _)

/-- A public ceiling large enough for every query reached by the fixed
production schedule.  The bound is deliberately coarse; the exact per-stage
growth facts above justify it without inspecting secret values. -/
def SamplingScheduleBudget (prelude : List Byte) (maxPointLength : ℕ) : Prop :=
  prelude.length + productionSamplingSlots * 4096 + 4096 ≤ maxPointLength

set_option maxRecDepth 20000 in
theorem freshSchedule_fits_of_budget
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (maxPointLength : ℕ)
    (hbudget : SamplingScheduleBudget prelude maxPointLength) :
    ScheduleFits shape causalSecret completion witness coins prelude
      maxPointLength := by
  classical
  intro round answers point hquery
  simp only [freshSchedule] at hquery
  split at hquery
  · simp at hquery
  · rename_i raw hraw
    split at hquery
    · simp at hquery
    · have hpoint : raw = point := Option.some.inj hquery
      subst point
      have hrawLength := rawQuery_length_le shape causalSecret completion
        witness coins round
          (scheduledControlAfter shape causalSecret completion witness coins
            prelude answers).raw raw hraw
      have hcontrol := scheduledControlAfter_lengthBound shape causalSecret
        completion witness coins prelude answers
      unfold ControlLengthBound at hcontrol
      unfold SamplingScheduleBudget at hbudget
      have hround : round.val < productionSamplingSlots := round.isLt
      omega

end VeiledFlock.ProductionSamplingScheduleAudit

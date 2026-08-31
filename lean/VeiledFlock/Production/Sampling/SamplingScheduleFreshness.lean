import VeiledFlock.Production.Sampling.SamplingScheduleWholeSuccess

/-!
# Freshness of the literal production sampling schedule

This module proves the deterministic query-input facts needed to identify the
duplicate-suppressing probability schedule with the literal production
execution.  Fiat--Shamir transcript growth is handled separately from PoW
state freshness; the latter is exactly the explicit `powStateCollision` event
already present in `globalBad`.
-/

namespace VeiledFlock.ProductionSamplingScheduleFreshness

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
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.UniquePositionSampling

theorem acceptScalar_transcript_length_mono {shape : BatchShape}
    (failed : Finset GhashField) (round start : ℕ) (control : Control shape)
    (answer : OracleBlock) :
    control.transcript.length ≤
      (acceptScalar failed round start control answer).transcript.length := by
  classical
  by_cases hzero : round - start = 0
  · by_cases hfailed :
      VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
    · simp [acceptScalar, hzero, hfailed]
      split <;> simp_all
    · simp [acceptScalar, hzero, hfailed]
  · by_cases hdone : control.stageDone
    · simp [acceptScalar, hzero, hdone]
    · by_cases hfailed :
        VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
      · simp [acceptScalar, hzero, hdone, hfailed]
        split <;> simp_all
      · simp [acceptScalar, hzero, hdone, hfailed]

theorem acceptPositions_transcript_length_mono {shape : BatchShape}
    (project : GhashField → ℕ) (target start round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    control.transcript.length ≤
      (acceptPositions project target start round control answer).transcript.length := by
  classical
  by_cases hzero : round - start = 0
  · simp [acceptPositions, hzero]
    split <;> simp_all
    split <;> simp_all
  · by_cases hdone : control.stageDone
    · simp [acceptPositions, hzero, hdone]
    · simp [acceptPositions, hzero, hdone]
      split <;> simp_all
      split <;> simp_all

theorem equalityStep_transcript_length_mono (shape : BatchShape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    control.transcript.length ≤
      (equalityStep shape round control answer).transcript.length := by
  classical
  by_cases hsome : control.equalityPoint.isSome
  · simp [equalityStep, hsome]
  · let counter := (round - equalityOffset) % equalityAttemptBlocks
    by_cases hcounter : counter < equalityBlockCount shape
    · let base : Control shape := if counter = 0 then
        { control with equalityBlocks := [] }
      else control
      have hbase : base.transcript = control.transcript := by
        by_cases hzero : counter = 0 <;> simp [base, hzero]
      let blocks := base.equalityBlocks ++ [answer]
      let outer := sliceFromBlocks (m shape - kSkip - 7) blocks
      by_cases hlast : counter + 1 = equalityBlockCount shape
      · by_cases haccept : accepted outer
        · cases hskip : base.skip with
          | none => simp [equalityStep, hsome, counter, hcounter, base, blocks,
              outer, hlast, haccept, hskip, hbase]
          | some skip =>
              simp [equalityStep, hsome, counter, hcounter, base, blocks,
                outer, hlast, haccept, hskip, hbase]
              omega
        · simp [equalityStep, hsome, counter, hcounter, base, blocks, outer,
            hlast, haccept, hbase]
          split <;> simp_all <;> omega
      · simp [equalityStep, hsome, counter, hcounter, base,  hlast,
          hbase]
    · simp [equalityStep, hsome, counter, hcounter]

theorem zerocheckStep_transcript_length_mono
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    control.transcript.length ≤
      (zerocheckStep shape causalSecret completion witness coins round control
        answer).transcript.length := by
  classical
  cases heq : control.equalityPoint with
  | none => simp [zerocheckStep, heq]
  | some equalityPoint =>
      by_cases hsite : round - zerocheckOffset < programmedPoints shape
      · by_cases hlast : round - zerocheckOffset + 1 = programmedPoints shape
        · simp [zerocheckStep, heq, hsite, hlast,
            VeiledFlock.ProductionSamplingSchedule.afterZerocheck_length]
          omega
        · simp [zerocheckStep, heq, hsite, hlast]
      · simp [zerocheckStep, heq, hsite]

theorem blindGrindingStep_transcript_length_mono {shape : BatchShape}
    (round : ℕ) (control : Control shape) (answer : OracleBlock) :
    control.transcript.length ≤
      (blindGrindingStep round control answer).transcript.length := by
  classical
  by_cases hdone : control.stageDone
  · simp [blindGrindingStep, hdone]
  · by_cases hgood : blindGrindingGood answer
    · simp [blindGrindingStep, hdone, hgood]
    · simp [blindGrindingStep, hdone, hgood]
      split <;> simp_all

theorem ligeritoStep_transcript_length_mono {shape : BatchShape}
    (round : ℕ) (control : Control shape) (answer : OracleBlock) :
    control.transcript.length ≤
      (ligeritoStep round control answer).transcript.length := by
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

theorem acceptScalar_transcript_length_eq_or_add_seventeen_le
    {shape : BatchShape} (failed : Finset GhashField) (round start : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (acceptScalar failed round start control answer).transcript.length =
        control.transcript.length ∨
      control.transcript.length + 17 ≤
        (acceptScalar failed round start control answer).transcript.length := by
  classical
  by_cases hzero : round - start = 0
  · by_cases hfailed :
        VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
    · simp [acceptScalar, hzero, hfailed]
      split <;> simp_all
    · simp [acceptScalar, hzero, hfailed, afterScalar_length]
  · by_cases hdone : control.stageDone
    · simp [acceptScalar, hzero, hdone]
    · by_cases hfailed :
          VeiledFlock.ProductionScalarProjection.scalarFromBlock answer ∈ failed
      · simp [acceptScalar, hzero, hdone, hfailed]
        split <;> simp_all
      · simp [acceptScalar, hzero, hdone, hfailed, afterScalar_length]

theorem acceptPositions_transcript_length_eq_or_add_seventeen_le
    {shape : BatchShape} (project : GhashField → ℕ)
    (target start round : ℕ) (control : Control shape)
    (answer : OracleBlock) :
    (acceptPositions project target start round control answer).transcript.length =
        control.transcript.length ∨
      control.transcript.length + 17 ≤
        (acceptPositions project target start round control answer).transcript.length := by
  classical
  by_cases hzero : round - start = 0
  · simp [acceptPositions, hzero]
    split <;> simp_all ; split <;> simp_all
  · by_cases hdone : control.stageDone
    · simp [acceptPositions, hzero, hdone]
    · simp [acceptPositions, hzero, hdone]
      split <;> simp_all ; split <;> simp_all

theorem ligeritoStep_transcript_length_eq_or_add_seventeen_le
    {shape : BatchShape} (round : ℕ) (control : Control shape)
    (answer : OracleBlock) :
    (ligeritoStep round control answer).transcript.length =
        control.transcript.length ∨
      control.transcript.length + 17 ≤
        (ligeritoStep round control answer).transcript.length := by
  classical
  by_cases hstate : (round - ligeritoOffset) % ligeritoSiteWidth = 0
  · simp [ligeritoStep, hstate]
  · by_cases hdone : control.stageDone
    · simp [ligeritoStep, hstate, hdone]
    · by_cases hgood : rustLeadingZeroBitsAtLeast maxLigeritoBits
          (by decide) answer
      · simp [ligeritoStep, hstate, hdone, hgood]
        split <;> simp_all
      · simp [ligeritoStep, hstate, hdone, hgood]
        split <;> simp_all

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawStep_transcript_length_mono
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    control.transcript.length ≤
      (rawStep shape causalSecret completion witness coins round control
        answer).transcript.length := by
  classical
  by_cases hstatus : control.status != .live
  · simp [rawStep, hstatus]
  by_cases hskip : round < equalitySkipBlocks
  · by_cases hlast : round + 1 = equalitySkipBlocks
    · simp [rawStep, hstatus, hskip, hlast]
      omega
    · simp [rawStep, hstatus, hskip, hlast]
  by_cases hequality : round < zerocheckOffset
  · simpa [rawStep, hstatus, hskip, hequality] using
      equalityStep_transcript_length_mono shape round control answer
  by_cases hzero : round < blindStateOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero] using
      zerocheckStep_transcript_length_mono shape causalSecret completion witness
        coins round control answer
  by_cases hblindState : round < blindGrindingOffset
  · simp [rawStep, hstatus, hskip, hequality, hzero, hblindState]
  by_cases hblindGrind : round < blindChallengeOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind] using
        blindGrindingStep_transcript_length_mono round control answer
  by_cases hblind : round < multiplicationAlphaOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind] using
        acceptScalar_transcript_length_mono zeroFailure round
          blindChallengeOffset control answer
  by_cases halpha : round < outerChallengeOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha] using
        acceptScalar_transcript_length_mono zeroOrOneFailure round
          multiplicationAlphaOffset control answer
  by_cases houterChallenge : round < outerPositionsOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge] using
        acceptScalar_transcript_length_mono zeroFailure round
          outerChallengeOffset control answer
  by_cases houterPositions : round < linearPositionsOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions] using
        acceptPositions_transcript_length_mono
          (fun value ↦ (VeiledFlock.ProductionPositionProjection.rustLowPosition
            (m shape - 11) value).val)
          (outerL0QueryCount shape) outerPositionsOffset round control answer
  by_cases hlinearPositions : round < linearRhoOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions] using acceptPositions_transcript_length_mono
        (fun value ↦ (VeiledFlock.ProductionPositionProjection.rustLowPosition
          13 value).val) veilQueryCount linearPositionsOffset round control answer
  by_cases hlinearRho : round < hadamardPositionsOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho] using
        acceptScalar_transcript_length_mono zeroFailure round linearRhoOffset
          control answer
  by_cases hhadamardPositions : round < hadamardRhoOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions] using
        acceptPositions_transcript_length_mono
          (fun value ↦ (VeiledFlock.ProductionPositionProjection.rustLowPosition
            11 value).val) veilQueryCount hadamardPositionsOffset round control
          answer
  by_cases hhadamardRho : round < productCoefficientOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho] using
        acceptScalar_transcript_length_mono zeroFailure round hadamardRhoOffset
          control answer
  by_cases hproduct : round < ligeritoOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct] using acceptScalar_transcript_length_mono zeroFailure round
        productCoefficientOffset control answer
  by_cases hligerito : round < productionSamplingSlots
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct, hligerito] using
        ligeritoStep_transcript_length_mono round control answer
  simp [rawStep, hstatus, hskip, hequality, hzero, hblindState, hblindGrind,
    hblind, halpha, houterChallenge, houterPositions, hlinearPositions,
    hlinearRho, hhadamardPositions, hhadamardRho, hproduct, hligerito]

/- A production transition either leaves the transcript length unchanged or
advances it by at least the 17-byte PoW-absorption frame.  This gap is what
separates Fiat--Shamir query families belonging to different live stages. -/
set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawStep_transcript_length_eq_or_add_seventeen_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (rawStep shape causalSecret completion witness coins round control
          answer).transcript.length = control.transcript.length ∨
      control.transcript.length + 17 ≤
        (rawStep shape causalSecret completion witness coins round control
          answer).transcript.length := by
  classical
  by_cases hstatus : control.status != .live
  · simp [rawStep, hstatus]
  by_cases hskip : round < equalitySkipBlocks
  · by_cases hlast : round + 1 = equalitySkipBlocks
    · right
      simp [rawStep, hstatus, hskip, hlast]
    · simp [rawStep, hstatus, hskip, hlast]
  by_cases hequality : round < zerocheckOffset
  · by_cases hsome : control.equalityPoint.isSome
    · simp [rawStep, hstatus, hskip, hequality, equalityStep, hsome]
    · let counter := (round - equalityOffset) % equalityAttemptBlocks
      by_cases hcounter : counter < equalityBlockCount shape
      · let base : Control shape := if counter = 0 then
            { control with equalityBlocks := [] }
          else control
        have hbase : base.transcript = control.transcript := by
          by_cases hzero : counter = 0 <;> simp [base, hzero]
        let blocks := base.equalityBlocks ++ [answer]
        let outer := sliceFromBlocks (m shape - kSkip - 7) blocks
        by_cases hlast : counter + 1 = equalityBlockCount shape
        · by_cases haccept : accepted outer
          · cases hskipValue : base.skip with
            | none =>
                simp [rawStep, hstatus, hskip, hequality, equalityStep, hsome,
                  counter, hcounter, base, blocks, outer, hlast, haccept,
                  hskipValue, hbase]
            | some skipValue =>
                right
                simp [rawStep, hstatus, hskip, hequality, equalityStep, hsome,
                  counter, hcounter, base, blocks, outer, hlast, haccept,
                  hskipValue, hbase]
                cases shape <;> norm_num [m, kSkip]
          · by_cases hcap :
                (round - equalityOffset) / equalityAttemptBlocks + 1 =
                  rejectionTrials
            · right
              simp [rawStep, hstatus, hskip, hequality, equalityStep, hsome,
                counter, hcounter, base, blocks, outer, hlast, haccept, hbase,
                hcap]
              cases shape <;> norm_num [m, kSkip]
            · right
              simp [rawStep, hstatus, hskip, hequality, equalityStep, hsome,
                counter, hcounter, base, blocks, outer, hlast, haccept, hbase,
                hcap]
              cases shape <;> norm_num [m, kSkip]
        · simp [rawStep, hstatus, hskip, hequality, equalityStep, hsome,
            counter, hcounter, base,  hlast, hbase]
      · simp [rawStep, hstatus, hskip, hequality, equalityStep, hsome,
          counter, hcounter]
  by_cases hzero : round < blindStateOffset
  · cases heq : control.equalityPoint with
    | none => simp [rawStep, hstatus, hskip, hequality, hzero, zerocheckStep,
        heq]
    | some equalityPoint =>
        by_cases hsite : round - zerocheckOffset < programmedPoints shape
        · by_cases hlast : round - zerocheckOffset + 1 =
              programmedPoints shape
          · right
            simp [rawStep, hstatus, hskip, hequality, hzero, zerocheckStep,
              heq, hsite, hlast,
              VeiledFlock.ProductionSamplingSchedule.afterZerocheck_length]
            omega
          · simp [rawStep, hstatus, hskip, hequality, hzero,
              zerocheckStep, heq, hsite, hlast]
        · simp [rawStep, hstatus, hskip, hequality, hzero, zerocheckStep,
            heq, hsite]
  by_cases hblindState : round < blindGrindingOffset
  · simp [rawStep, hstatus, hskip, hequality, hzero, hblindState]
  by_cases hblindGrind : round < blindChallengeOffset
  · by_cases hdone : control.stageDone
    · simp [rawStep, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, blindGrindingStep, hdone]
    · by_cases hgood : blindGrindingGood answer
      · right
        simp [rawStep, hstatus, hskip, hequality, hzero, hblindState,
          hblindGrind, blindGrindingStep, hdone, hgood, afterGrind_length]
      · simp [rawStep, hstatus, hskip, hequality, hzero, hblindState,
          hblindGrind, blindGrindingStep, hdone, hgood]
        split <;> simp_all
  by_cases hblind : round < multiplicationAlphaOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind] using
        acceptScalar_transcript_length_eq_or_add_seventeen_le zeroFailure round
          blindChallengeOffset control answer
  by_cases halpha : round < outerChallengeOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha] using
        acceptScalar_transcript_length_eq_or_add_seventeen_le zeroOrOneFailure
          round multiplicationAlphaOffset control answer
  by_cases houterChallenge : round < outerPositionsOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge] using
        acceptScalar_transcript_length_eq_or_add_seventeen_le zeroFailure round
          outerChallengeOffset control answer
  by_cases houterPositions : round < linearPositionsOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions] using
        acceptPositions_transcript_length_eq_or_add_seventeen_le
          (fun value ↦ (VeiledFlock.ProductionPositionProjection.rustLowPosition
            (m shape - 11) value).val)
          (outerL0QueryCount shape) outerPositionsOffset round control answer
  by_cases hlinearPositions : round < linearRhoOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions] using
        acceptPositions_transcript_length_eq_or_add_seventeen_le
          (fun value ↦ (VeiledFlock.ProductionPositionProjection.rustLowPosition
            13 value).val) veilQueryCount linearPositionsOffset round control
          answer
  by_cases hlinearRho : round < hadamardPositionsOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho] using
        acceptScalar_transcript_length_eq_or_add_seventeen_le zeroFailure round
          linearRhoOffset control answer
  by_cases hhadamardPositions : round < hadamardRhoOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions] using
        acceptPositions_transcript_length_eq_or_add_seventeen_le
          (fun value ↦ (VeiledFlock.ProductionPositionProjection.rustLowPosition
            11 value).val) veilQueryCount hadamardPositionsOffset round control
          answer
  by_cases hhadamardRho : round < productCoefficientOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho] using
        acceptScalar_transcript_length_eq_or_add_seventeen_le zeroFailure round
          hadamardRhoOffset control answer
  by_cases hproduct : round < ligeritoOffset
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct] using
        acceptScalar_transcript_length_eq_or_add_seventeen_le zeroFailure round
          productCoefficientOffset control answer
  by_cases hligerito : round < productionSamplingSlots
  · simpa [rawStep, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct, hligerito] using
        ligeritoStep_transcript_length_eq_or_add_seventeen_le round control
          answer
  simp [rawStep, hstatus, hskip, hequality, hzero, hblindState, hblindGrind,
    hblind, halpha, houterChallenge, houterPositions, hlinearPositions,
    hlinearRho, hhadamardPositions, hhadamardRho, hproduct, hligerito]

theorem iterateFrom_rawStep_transcript_length_eq_or_add_seventeen_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (start rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock) :
    (iterateFrom (rawStep shape causalSecret completion witness coins) start
          rounds control answers).transcript.length = control.transcript.length ∨
      control.transcript.length + 17 ≤
        (iterateFrom (rawStep shape causalSecret completion witness coins) start
          rounds control answers).transcript.length := by
  induction rounds with
  | zero => simp [iterateFrom, iterateList]
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      let before := iterateFrom
        (rawStep shape causalSecret completion witness coins) start rounds
        control (fun index ↦ answers index.castSucc)
      have hprefix := ih (fun index ↦ answers index.castSucc)
      have hstep := rawStep_transcript_length_eq_or_add_seventeen_le shape
        causalSecret completion witness coins (start + rounds) before
        (answers (Fin.last rounds))
      have hmono := rawStep_transcript_length_mono shape causalSecret completion
        witness coins (start + rounds) before (answers (Fin.last rounds))
      dsimp only [before] at hstep hmono ⊢
      rcases hprefix with hprefix | hprefix
      · rcases hstep with hstep | hstep
        · exact Or.inl (hstep.trans hprefix)
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)

theorem rawControlUntil_add_transcript_length_eq_or_add_seventeen_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (start width : ℕ)
    (hfit : start + width ≤ productionSamplingSlots) :
    let before := rawControlUntil shape causalSecret completion witness coins
      prelude answers start (Nat.le_trans (Nat.le_add_right start width) hfit)
    let after := rawControlUntil shape causalSecret completion witness coins
      prelude answers (start + width) hfit
    after.transcript.length = before.transcript.length ∨
      before.transcript.length + 17 ≤ after.transcript.length := by
  rw [rawControlUntil_add shape causalSecret completion witness coins prelude
    answers start width hfit]
  exact iterateFrom_rawStep_transcript_length_eq_or_add_seventeen_le shape
    causalSecret completion witness coins start width _ _

theorem rawControlUntil_transcript_length_mono
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (left right : ℕ)
    (hle : left ≤ right) (hfit : right ≤ productionSamplingSlots) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        left (hle.trans hfit)).transcript.length ≤
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        right hfit).transcript.length := by
  have hsum : left + (right - left) = right := Nat.add_sub_of_le hle
  have hgap := rawControlUntil_add_transcript_length_eq_or_add_seventeen_le
    shape causalSecret completion witness coins prelude answers left
      (right - left) (by simpa [hsum] using hfit)
  simpa only [hsum] using hgap.elim (fun heq ↦ heq.ge) (fun h ↦ h.trans'
    (Nat.le_add_right _ _))

theorem iterateFrom_rawStep_fiat
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (start rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hfiat : VeiledFlock.ProductionSamplingScheduleClassification.ControlFiat
      control) :
    VeiledFlock.ProductionSamplingScheduleClassification.ControlFiat
      (iterateFrom (rawStep shape causalSecret completion witness coins) start
        rounds control answers) := by
  induction rounds with
  | zero => simpa [iterateFrom, iterateList]
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      exact VeiledFlock.ProductionSamplingScheduleClassification.rawStep_fiat
        shape causalSecret completion witness coins (start + rounds) _ _
        (ih (fun index ↦ answers index.castSucc))

theorem rawControlUntil_fiat
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude) (answers : SamplingAnswerTape)
    (rounds : ℕ) (hrounds : rounds ≤ productionSamplingSlots) :
    VeiledFlock.ProductionSamplingScheduleClassification.ControlFiat
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers rounds hrounds) := by
  apply iterateFrom_rawStep_fiat shape causalSecret completion witness coins
    0 rounds (initialControl shape prelude) _
  simpa [VeiledFlock.ProductionSamplingScheduleClassification.ControlFiat,
    initialControl] using hprelude

theorem controlAfter_priorAnswers_eq_rawControlUntil
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (site : Fin productionSamplingSlots) :
    controlAfter shape causalSecret completion witness coins prelude
        (priorAnswers answers site) =
      rawControlUntil shape causalSecret completion witness coins prelude
        answers site site.isLt.le := by
  rw [controlAfter_eq_iterateFrom]
  rfl

theorem schedule_eq_rawQuery_rawControlUntil
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (site : Fin productionSamplingSlots) :
    schedule shape causalSecret completion witness coins prelude site
        (priorAnswers answers site) =
      rawQuery shape causalSecret completion witness coins site
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers site site.isLt.le) := by
  simp only [schedule]
  rw [controlAfter_priorAnswers_eq_rawControlUntil]

end VeiledFlock.ProductionSamplingScheduleFreshness

import VeiledFlock.Production.Sampling.SamplingOperationalTrace
import VeiledFlock.Production.Sampling.SamplingTraceTailComplete

/-! # Complete executable production-trace refinement -/

namespace VeiledFlock.ProductionSamplingTraceComplete

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingOperationalProbability
open VeiledFlock.ProductionSamplingOperationalTrace
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionSamplingTracePrefix
open VeiledFlock.ProductionSamplingTraceTailComplete
open VeiledFlock.ProductionSamplingTraceZerocheck
open VeiledFlock.ProductionTranscriptFraming

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem productionRealTrace_some_of_raw_agreement
    {W : Type*} {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape)
    (table : BoundedBytes maxPointLength → OracleBlock)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins
      (preEqualityTranscript (productionStatementDigest statement) r1csDigest
        coins.proofNonce coins.treeNonces.outer coins.treeNonces.veilLinear
        coins.treeNonces.veilHadamard
        (outerRoot shape baseMessage witness coins (answerBounded fallback table))
        (linearRoot shape coins (answerBounded fallback table)))
      answers (answerBounded fallback table)) :
    ∃ trace,
      productionRealTrace shape fallback r1csDigest causalSecret completion
        baseMessage statement witness coins table = some trace := by
  classical
  let oracle := answerBounded fallback table
  let outerCommitment := outerRoot shape baseMessage witness coins oracle
  let linearCommitment := linearRoot shape coins oracle
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest coins.proofNonce coins.treeNonces.outer
    coins.treeNonces.veilLinear coins.treeNonces.veilHadamard outerCommitment
    linearCommitment
  have hagrees' : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle := by
    simpa only [prelude, oracle, outerCommitment, linearCommitment] using hagrees
  let first := firstEqualityAccepted shape answers hgood
  let skip := sampleSlice oracle prelude 6
  let outer := sliceFromBlocks (m shape - kSkip - 7)
    (List.ofFn (equalityAttemptAnswers answers
      ⟨first, firstEqualityAccepted_lt shape answers hgood⟩))
  let equalityPoint :
      VeiledFlock.ProductionEqualitySampler.EqualitySample
        (m shape - kSkip - 7) :=
    (skip, outer,
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers zerocheckOffset (by decide)).transcript)
  have hequality : sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
      rejectionTrials prelude = some equalityPoint := by
    simpa only [first, skip, outer, equalityPoint] using
      raw_zerocheck_start_transcript_eq_equality_sample shape causalSecret
        completion witness coins prelude answers hgood oracle hagrees'
  have hrun : AdaptiveOracleProgramming.run
      (zerocheckRealByteSchedule shape causalSecret completion equalityPoint.2.2
        witness coins) oracle (programmedPoints shape) =
      window zerocheckOffset (programmedPoints shape)
        (zerocheckActiveEnd_le_slots shape) answers := by
    simpa only [equalityPoint] using
      zerocheck_run_eq_answer_window shape causalSecret completion witness coins
        prelude answers hgood oracle hagrees'
  have hfields := rawControlUntil_zerocheck_prefix_fields shape causalSecret
    completion witness coins prelude answers hgood (programmedPoints shape)
      (by rfl)
  have hpadding := raw_zerocheck_padding_stable shape causalSecret completion
    witness coins prelude answers hfields.1 hfields.2.1
  have hactive := raw_active_zerocheck_transcript_eq shape causalSecret
    completion witness coins prelude answers hgood
  have hpost :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset
          VeiledFlock.ProductionSamplingLayoutBounds.blindStateOffset_le_slots).transcript =
        afterZerocheck shape causalSecret completion equalityPoint.2.2 witness
          coins
          (window zerocheckOffset (programmedPoints shape)
            (zerocheckActiveEnd_le_slots shape) answers) := by
    rw [congrArg Control.transcript hpadding]
    simpa only [equalityPoint] using hactive
  rcases sampleProductionTail_some_of_raw_agreement shape causalSecret completion
      witness coins prelude answers hgood oracle hagrees' equalityPoint
      (afterZerocheck shape causalSecret completion equalityPoint.2.2 witness
        coins
        (window zerocheckOffset (programmedPoints shape)
          (zerocheckActiveEnd_le_slots shape) answers)) hpost with
    ⟨tail, htail⟩
  refine ⟨{
    outerCommitment := outerCommitment
    linearCommitment := linearCommitment
    equalityPoint := equalityPoint
    answers := window zerocheckOffset (programmedPoints shape)
      (zerocheckActiveEnd_le_slots shape) answers
    tail := tail }, ?_⟩
  simp only [productionRealTrace]
  change
    (match sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
        veilSamplingTrials prelude with
      | none => none
      | some sampledEqualityPoint =>
          let sampledAnswers := AdaptiveOracleProgramming.run
            (zerocheckRealByteSchedule shape causalSecret completion
              sampledEqualityPoint.2.2 witness coins) oracle
            (programmedPoints shape)
          match sampleProductionTail shape oracle sampledEqualityPoint
              (afterZerocheck shape causalSecret completion
                sampledEqualityPoint.2.2 witness coins sampledAnswers) with
          | none => none
          | some sampledTail => some (show ProductionExecutionTrace shape from {
              outerCommitment := outerCommitment
              linearCommitment := linearCommitment
              equalityPoint := sampledEqualityPoint
              answers := sampledAnswers
              tail := sampledTail })) = _
  rw [show veilSamplingTrials = rejectionTrials by rfl, hequality]
  simp only
  rw [hrun, htail]

end VeiledFlock.ProductionSamplingTraceComplete

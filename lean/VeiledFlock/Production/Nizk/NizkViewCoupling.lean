import VeiledFlock.Production.Nizk.NizkCoupling

/-!
# Complete production adversary-view coupling

Concrete execution lemmas connecting the witness-free VEIL+FLOCK simulator to
one successful real production trace over the shared adaptive oracle state.
-/

namespace VeiledFlock.ProductionNizkCoupling
open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.TranscriptSchedule

theorem afterZerocheck_isFiatShamir
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (absorbedPrefix : List Byte) (hfiat : isFiatShamirPoint absorbedPrefix)
    (witness : W) (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    isFiatShamirPoint (afterZerocheck shape causalSecret completion
      absorbedPrefix witness coins answers) := by
  let transcript :=
    VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  let start := ProductionZerocheckSchedule.start shape absorbedPrefix transcript
  let step := scalarRoundStep consumeScalar
    (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
    (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2)
    (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2)
  obtain ⟨suffix, hsuffix⟩ := appendState_hasPrefix start step
    (programmedPoints shape) answers
  unfold afterZerocheck
  rw [hsuffix]
  have hnonempty : absorbedPrefix ≠ [] := by
    intro hempty
    simp [isFiatShamirPoint, hempty] at hfiat
  simpa [start, isFiatShamirPoint, ProductionZerocheckSchedule.start,
    hnonempty] using hfiat

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem productionSimulatedProof_of_trace
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape) (maxStartLength : ℕ)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (statement : ProductionStatement shape) (left right : W)
    (hpublic : publicStatement shape publicPositions baseMessage left =
      publicStatement shape publicPositions baseMessage right)
    (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ProductionCouplingInput shape maxStartLength)
    (hstart :
      let moved := productionMerkleCoinOracleEquivAt shape input.1
        causalSecret baseMessage publicPositions weights context left right
        trace.answers trace.tail.rest houter hlinear hhadamard input
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        trace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret trace.answers
          (right, moved.1.outer.1, moved.1.outer.2.1)
          moved.1.outer.2.2)).length ≤ maxStartLength)
    (facts : ProductionTraceFacts shape fallback r1csDigest causalSecret
      completion baseMessage statement left input.1 input.2 trace)
    (state : SharedOracleState (ProductionMaxPointLength shape maxStartLength))
    (hstate : state.table =
      (productionCoupledInputAt shape maxStartLength causalSecret baseMessage
        publicPositions weights context left right trace houter hlinear
        hhadamard input hstart).2)
    (hok :
      let coupled := productionCoupledInputAt shape maxStartLength causalSecret
        baseMessage publicPositions weights context left right trace houter
        hlinear hhadamard input hstart
      let schedule := zerocheckSimulatedByteSchedule shape causalSecret
        trace.equalityPoint.2.2 right coupled.1 trace.answers
      (programSharedByteSchedule schedule trace.answers state).1 = .ok ()) :
    let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
      baseMessage publicPositions weights context left right trace.answers
      trace.tail.rest houter hlinear hhadamard input
    let coupled := productionCoupledInputAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context left right trace houter
      hlinear hhadamard input hstart
    (productionSimulatedProof shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context (fun _ => right) statement
      coupled.1 state).1 =
        some (productionTraceProof shape fallback causalSecret baseMessage
          publicPositions weights context left input.1 input.2 trace) ∧
    (productionSimulatedProof shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context (fun _ => right) statement
      coupled.1 state).2.table = moved.2 := by
  dsimp only
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let coupled := productionCoupledInputAt shape maxStartLength causalSecret
    baseMessage publicPositions weights context left right trace houter hlinear
    hhadamard input hstart
  let schedule := zerocheckSimulatedByteSchedule shape causalSecret
    trace.equalityPoint.2.2 right coupled.1 trace.answers
  let programmed := programSharedByteSchedule schedule trace.answers state
  have hequality := productionCoupledInputAt_equalityPoint shape maxStartLength
    fallback r1csDigest causalSecret completion baseMessage publicPositions
    weights context statement left right trace houter hlinear hhadamard hnodes
    input hstart facts
  have htraceFiat : isFiatShamirPoint trace.equalityPoint.2.2 := by
    let prelude := preEqualityTranscript (productionStatementDigest statement)
      r1csDigest input.1.proofNonce input.1.treeNonces.outer
      input.1.treeNonces.veilLinear input.1.treeNonces.veilHadamard
      trace.outerCommitment trace.linearCommitment
    have hprelude : isFiatShamirPoint prelude :=
      preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _
    exact sampleEqualityPointPrefix_some_isFiatShamir
      (answerBounded fallback input.2) (m shape - kSkip - 7)
      veilSamplingTrials prelude hprelude trace.equalityPoint
      facts.equalityPoint
  have hrestore := productionProgramming_restores_moved shape maxStartLength
    fallback causalSecret completion baseMessage publicPositions weights
    context left right hpublic trace houter hlinear hhadamard input hstart
    facts.answers htraceFiat state hstate hok
  have hmovedCoins := productionMerkleCoinOracleEquivAt_coins shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard input
  let realAfter := afterZerocheck shape causalSecret completion
    trace.equalityPoint.2.2 left input.1 trace.answers
  have hrealAfterFiat : isFiatShamirPoint realAfter :=
    afterZerocheck_isFiatShamir shape causalSecret completion
      trace.equalityPoint.2.2 htraceFiat left input.1 trace.answers
  have hafterTransport := afterSimulatedZerocheck_coinEquiv shape causalSecret
    completion baseMessage publicPositions weights context left right hpublic
    trace.equalityPoint.2.2 trace.answers trace.tail.rest input.1
  have hsimAfter : afterSimulatedZerocheck shape causalSecret
      trace.equalityPoint.2.2 right coupled.1 trace.answers = realAfter := by
    have hcoupled : coupled.1 = withSimulatedAnswers shape moved.1
        trace.answers := by rfl
    rw [hcoupled]
    have hsame : afterSimulatedZerocheck shape causalSecret
        trace.equalityPoint.2.2 right
          (withSimulatedAnswers shape moved.1 trace.answers) trace.answers =
        afterSimulatedZerocheck shape causalSecret trace.equalityPoint.2.2
          right moved.1 trace.answers := by rfl
    rw [hsame, hmovedCoins]
    exact hafterTransport
  have htailMoved : sampleProductionTail shape
      (answerBounded fallback moved.2) trace.equalityPoint realAfter =
        some trace.tail := by
    rw [sampleProductionTail_oracle_congr shape
      (answerBounded fallback input.2) (answerBounded fallback moved.2)
      trace.equalityPoint realAfter hrealAfterFiat]
    · exact facts.tail
    · intro point hfiat
      exact productionMerkleCoinOracleEquivAt_answer_fiat_all shape input.1
        causalSecret baseMessage publicPositions weights context left right
        trace.answers trace.tail.rest houter hlinear hhadamard fallback input
        point hfiat
    · intro powState nonce
      exact productionMerkleCoinOracleEquivAt_answer_pow_all shape input.1
        causalSecret baseMessage publicPositions weights context left right
        trace.answers trace.tail.rest houter hlinear hhadamard fallback input
        powState nonce
  have hproof := productionProofOfTrace_coinOracleEquiv shape causalSecret
    baseMessage publicPositions weights context left right hpublic trace houter
    hlinear hhadamard hnodes fallback input
  have hcoupledProof : productionProofOfTrace shape causalSecret baseMessage
      publicPositions weights context right coupled.1
      (answerBounded fallback moved.2) trace =
      productionProofOfTrace shape causalSecret baseMessage publicPositions
        weights context right moved.1 (answerBounded fallback moved.2) trace := by
    rfl
  have hproofFinal : productionProofOfTrace shape causalSecret baseMessage
      publicPositions weights context right coupled.1
      (answerBounded fallback moved.2) trace =
      productionTraceProof shape fallback causalSecret baseMessage
        publicPositions weights context left input.1 input.2 trace := by
    rw [hcoupledProof]
    exact hproof
  have htailSim : sampleProductionTail shape
      (sharedByteOracle fallback programmed.2) trace.equalityPoint
      (afterSimulatedZerocheck shape causalSecret trace.equalityPoint.2.2
        right coupled.1 coupled.1.simulatedAnswers) = some trace.tail := by
    rw [show sharedByteOracle fallback programmed.2 =
        answerBounded fallback moved.2 by
      funext point
      simp only [sharedByteOracle]
      rw [hrestore]]
    rw [show coupled.1.simulatedAnswers = trace.answers by rfl]
    rw [hsimAfter]
    exact htailMoved
  have horacleState : sharedByteOracle fallback state =
      answerBounded fallback coupled.2 := by
    funext point
    simp only [sharedByteOracle]
    rw [← hstate]
  have hequalityState :
      let oracle := sharedByteOracle fallback state
      let outerCommitment := outerRoot shape baseMessage right coupled.1 oracle
      let linearCommitment := linearRoot shape coupled.1 oracle
      let prelude := preEqualityTranscript (productionStatementDigest statement)
        r1csDigest coupled.1.proofNonce coupled.1.treeNonces.outer
        coupled.1.treeNonces.veilLinear coupled.1.treeNonces.veilHadamard
        outerCommitment linearCommitment
      sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
        veilSamplingTrials prelude = some trace.equalityPoint := by
    rw [horacleState]
    exact hequality
  have hcommitments := productionCoupledInputAt_commitments shape
    maxStartLength fallback r1csDigest causalSecret completion baseMessage
    publicPositions weights context statement left right trace houter hlinear
    hhadamard hnodes input hstart facts
  have hprogramOracle : sharedByteOracle fallback programmed.2 =
      answerBounded fallback moved.2 := by
    funext point
    simp only [sharedByteOracle]
    rw [hrestore]
  have houterState : outerRoot shape baseMessage right coupled.1
      (sharedByteOracle fallback state) = trace.outerCommitment := by
    rw [horacleState]
    exact hcommitments.1
  have hlinearState : linearRoot shape coupled.1
      (sharedByteOracle fallback state) = trace.linearCommitment := by
    rw [horacleState]
    exact hcommitments.2
  have hfinish : finishProductionProof shape causalSecret baseMessage
      publicPositions weights context right coupled.1 trace.equalityPoint
      coupled.1.simulatedAnswers trace.tail
      (sharedByteOracle fallback programmed.2)
      (outerRoot shape baseMessage right coupled.1
        (sharedByteOracle fallback state))
      (linearRoot shape coupled.1 (sharedByteOracle fallback state)) =
      productionProofOfTrace shape causalSecret baseMessage publicPositions
        weights context right coupled.1 (answerBounded fallback moved.2)
        trace := by
    rw [show coupled.1.simulatedAnswers = trace.answers by rfl]
    rw [hprogramOracle, houterState, hlinearState]
    rfl
  have hproofExecuted : finishProductionProof shape causalSecret baseMessage
      publicPositions weights context right coupled.1 trace.equalityPoint
      coupled.1.simulatedAnswers trace.tail
      (sharedByteOracle fallback programmed.2)
      (outerRoot shape baseMessage right coupled.1
        (sharedByteOracle fallback state))
      (linearRoot shape coupled.1 (sharedByteOracle fallback state)) =
      productionTraceProof shape fallback causalSecret baseMessage
        publicPositions weights context left input.1 input.2 trace :=
    hfinish.trans hproofFinal
  have hrun := productionSimulatedProof_of_success shape fallback r1csDigest
    causalSecret completion baseMessage publicPositions weights context
    (fun _ => right) statement coupled.1 state trace.equalityPoint
    hequalityState hok trace.tail htailSim
  rw [hrun]
  constructor
  · exact congrArg some hproofExecuted
  · exact hrestore

end VeiledFlock.ProductionNizkCoupling

import VeiledFlock.Production.Sampling.SamplingTraceTail

/-! # Complete executable production-tail refinement -/

namespace VeiledFlock.ProductionSamplingTraceTailComplete

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionSamplingTraceLigerito
open VeiledFlock.ProductionSamplingTraceScalar
open VeiledFlock.ProductionSamplingTraceTail
open VeiledFlock.ProductionSamplingTraceTailBlindRun
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionUniquePositionSampler
open VeiledFlock.UniquePositionSampling

theorem sampleScalarUntil_predicate_eq
    (goodLeft goodRight : GhashField → Prop)
    (decideLeft : DecidablePred goodLeft)
    (decideRight : DecidablePred goodRight)
    (oracle : List Byte → OracleBlock) (trials : ℕ) (transcript : List Byte)
    (hgood : goodLeft = goodRight) :
    @sampleScalarUntil goodLeft decideLeft oracle trials transcript =
      @sampleScalarUntil goodRight decideRight oracle trials transcript := by
  subst goodRight
  have hdecide : decideLeft = decideRight := Subsingleton.elim _ _
  subst decideRight
  rfl

theorem rawControlUntil_eq_of_round_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (left right : ℕ)
    (hleft : left ≤ productionSamplingSlots)
    (hright : right ≤ productionSamplingSlots) (hround : left = right) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        left hleft =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        right hright := by
  subst right
  have hproof : hleft = hright := Subsingleton.elim _ _
  subst hright
  rfl

theorem connectScalarStage
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (stage : ScalarStage) (previousRound : ℕ)
    (previousTranscript : List Byte)
    (hround : previousRound = scalarStageStart stage)
    {hpreviousFit : previousRound ≤ productionSamplingSlots}
    {hstageFit : scalarStageStart stage ≤ productionSamplingSlots}
    {result : GhashField × List Byte}
    (hprevious :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        previousRound hpreviousFit).transcript = previousTranscript)
    (hresult : sampleScalarUntil (scalarStageGood stage) oracle rejectionTrials
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart stage) hstageFit).transcript = some result) :
    sampleScalarUntil (scalarStageGood stage) oracle rejectionTrials
      previousTranscript = some result := by
  rw [← hprevious]
  rw [rawControlUntil_eq_of_round_eq shape causalSecret completion witness coins
    prelude answers previousRound (scalarStageStart stage) hpreviousFit hstageFit
    hround]
  exact hresult

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem sampleProductionTail_some_of_raw_agreement
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (equalityPoint : VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7))
    (transcript : List Byte)
    (htranscript :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset
          VeiledFlock.ProductionSamplingLayoutBounds.blindStateOffset_le_slots).transcript =
        transcript) :
    ∃ tail,
      sampleProductionTail shape oracle equalityPoint transcript = some tail := by
  classical
  have statuses := tailStageStatuses_of_not_globalBad shape causalSecret
    completion witness coins prelude answers hgood
  rcases runBlindGrinding_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees transcript htranscript
      statuses.blindState with
    ⟨blindNonce, hblindPow, hafterBlind⟩

  rcases runScalarStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .blindChallenge
      statuses.blindChallenge with
    ⟨blindResult, hblindResult, hblindTranscript⟩
  rcases blindResult with ⟨blindChallenge, afterBlind⟩
  have hblindResult' : sampleScalarUntil nonzero oracle rejectionTrials
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset
        VeiledFlock.ProductionSamplingLayoutBounds.blindChallengeOffset_le_slots).transcript =
        some (blindChallenge, afterBlind) := by
    have hcontrol := rawControlUntil_eq_of_round_eq shape causalSecret completion
      witness coins prelude answers (scalarStageStart .blindChallenge)
      blindChallengeOffset (by decide)
      VeiledFlock.ProductionSamplingLayoutBounds.blindChallengeOffset_le_slots
      (by rfl)
    rw [hcontrol] at hblindResult
    exact (sampleScalarUntil_predicate_eq nonzero
      (scalarStageGood .blindChallenge) _ _ oracle rejectionTrials _
      (by rfl)).trans hblindResult
  have hblindTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart .blindChallenge + rejectionTrials) (by decide)).transcript =
          afterBlind := by simpa only using hblindTranscript
  have hblindSample : sampleNonzero oracle veilSamplingTrials
      (afterGrind transcript blindNonce) = some (blindChallenge, afterBlind) := by
    unfold sampleNonzero
    rw [← hafterBlind]
    simpa [veilSamplingTrials, rejectionTrials, scalarStageGood,
      scalarStageStart] using hblindResult'

  rcases runScalarStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .multiplicationAlpha
      statuses.multiplicationAlpha with
    ⟨alphaResult, halphaResult, halphaTranscript⟩
  rcases alphaResult with ⟨multiplicationAlpha, afterAlpha⟩
  have halphaTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart .multiplicationAlpha + rejectionTrials)
          (by decide)).transcript = afterAlpha := by
    simpa only using halphaTranscript
  have halphaSample : sampleNotZeroOrOne oracle veilSamplingTrials afterBlind =
      some (multiplicationAlpha, afterAlpha) := by
    unfold sampleNotZeroOrOne
    have hconnected := connectScalarStage shape causalSecret completion witness
      coins prelude answers oracle .multiplicationAlpha
      (scalarStageStart .blindChallenge + rejectionTrials) afterBlind (by rfl)
      hblindTranscript' halphaResult
    exact (sampleScalarUntil_predicate_eq notZeroOrOne
      (scalarStageGood .multiplicationAlpha) _ _ oracle rejectionTrials _
      (by rfl)).trans (by simpa [veilSamplingTrials] using hconnected)

  rcases runScalarStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .outerChallenge
      statuses.outerChallenge with
    ⟨outerChallengeResult, houterChallengeResult, houterChallengeTranscript⟩
  rcases outerChallengeResult with ⟨outerChallenge, afterOuterChallenge⟩
  have houterChallengeTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart .outerChallenge + rejectionTrials)
          (by decide)).transcript = afterOuterChallenge := by
    simpa only using houterChallengeTranscript
  have houterChallengeSample : sampleNonzero oracle veilSamplingTrials afterAlpha =
      some (outerChallenge, afterOuterChallenge) := by
    unfold sampleNonzero
    have hconnected := connectScalarStage shape causalSecret completion witness
      coins prelude answers oracle .outerChallenge
      (scalarStageStart .multiplicationAlpha + rejectionTrials) afterAlpha
      (by rfl) halphaTranscript' houterChallengeResult
    exact (sampleScalarUntil_predicate_eq nonzero
      (scalarStageGood .outerChallenge) _ _ oracle rejectionTrials _
      (by rfl)).trans (by simpa [veilSamplingTrials] using hconnected)

  rcases runPositionStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .outer
      (rustLowPosition (m shape - 11)) (by intro; rfl) statuses.outerPositions with
    ⟨outerResult, houterResult, houterTranscript⟩
  rcases outerResult with ⟨outerSet, afterOuterPositions⟩
  have houterTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (positionStageStart .outer + samplingTrials) (by decide)).transcript =
          afterOuterPositions := by simpa only using houterTranscript
  have houterSample : sampleUniquePositions (rustLowPosition (m shape - 11))
      (outerL0QueryCount shape) veilSamplingTrials oracle afterOuterChallenge =
        some (outerSet, afterOuterPositions) := by
    unfold sampleUniquePositions
    rw [← houterChallengeTranscript']
    simpa [positionStageTarget, positionStageStart, scalarStageStart,
      veilSamplingTrials, samplingTrials, rejectionTrials, outerPositionsOffset,
      outerChallengeOffset] using houterResult

  rcases runPositionStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .linear (rustLowPosition 13)
      (by intro; rfl) statuses.linearPositions with
    ⟨linearResult, hlinearResult, hlinearTranscript⟩
  rcases linearResult with ⟨linearSetPow, afterLinearPositions⟩
  have hlinearTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (positionStageStart .linear + samplingTrials) (by decide)).transcript =
          afterLinearPositions := by simpa only using hlinearTranscript
  have hlinearSample : sampleUniquePositions (rustLowPosition 13) veilQueryCount
      veilSamplingTrials oracle afterOuterPositions =
        some (linearSetPow, afterLinearPositions) := by
    unfold sampleUniquePositions
    rw [← houterTranscript']
    simpa [positionStageTarget, positionStageStart, veilSamplingTrials,
      samplingTrials, rejectionTrials, linearPositionsOffset,
      outerPositionsOffset] using hlinearResult

  rcases runScalarStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .linearRho statuses.linearRho with
    ⟨linearRhoResult, hlinearRhoResult, hlinearRhoTranscript⟩
  rcases linearRhoResult with ⟨linearRho, afterLinearRho⟩
  have hlinearRhoTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart .linearRho + rejectionTrials) (by decide)).transcript =
          afterLinearRho := by simpa only using hlinearRhoTranscript
  have hlinearRhoSample : sampleNonzero oracle veilSamplingTrials
      afterLinearPositions = some (linearRho, afterLinearRho) := by
    unfold sampleNonzero
    have hconnected := connectScalarStage shape causalSecret completion witness
      coins prelude answers oracle .linearRho
      (positionStageStart .linear + samplingTrials) afterLinearPositions
      (by rfl) hlinearTranscript' hlinearRhoResult
    exact (sampleScalarUntil_predicate_eq nonzero
      (scalarStageGood .linearRho) _ _ oracle rejectionTrials _
      (by rfl)).trans (by simpa [veilSamplingTrials] using hconnected)

  rcases runPositionStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .hadamard (rustLowPosition 11)
      (by intro; rfl) statuses.hadamardPositions with
    ⟨hadamardResult, hhadamardResult, hhadamardTranscript⟩
  rcases hadamardResult with ⟨hadamardSetPow, afterHadamardPositions⟩
  have hhadamardTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (positionStageStart .hadamard + samplingTrials) (by decide)).transcript =
          afterHadamardPositions := by simpa only using hhadamardTranscript
  have hhadamardSample : sampleUniquePositions (rustLowPosition 11)
      veilQueryCount veilSamplingTrials oracle afterLinearRho =
        some (hadamardSetPow, afterHadamardPositions) := by
    unfold sampleUniquePositions
    rw [← hlinearRhoTranscript']
    simpa [positionStageTarget, positionStageStart, scalarStageStart,
      veilSamplingTrials, samplingTrials, rejectionTrials,
      hadamardPositionsOffset, linearRhoOffset] using hhadamardResult

  rcases runScalarStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .hadamardRho statuses.hadamardRho
    with ⟨hadamardRhoResult, hhadamardRhoResult, hhadamardRhoTranscript⟩
  rcases hadamardRhoResult with ⟨hadamardRho, afterHadamardRho⟩
  have hhadamardRhoTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart .hadamardRho + rejectionTrials) (by decide)).transcript =
          afterHadamardRho := by simpa only using hhadamardRhoTranscript
  have hhadamardRhoSample : sampleNonzero oracle veilSamplingTrials
      afterHadamardPositions = some (hadamardRho, afterHadamardRho) := by
    unfold sampleNonzero
    have hconnected := connectScalarStage shape causalSecret completion witness
      coins prelude answers oracle .hadamardRho
      (positionStageStart .hadamard + samplingTrials) afterHadamardPositions
      (by rfl) hhadamardTranscript' hhadamardRhoResult
    exact (sampleScalarUntil_predicate_eq nonzero
      (scalarStageGood .hadamardRho) _ _ oracle rejectionTrials _
      (by rfl)).trans (by simpa [veilSamplingTrials] using hconnected)

  rcases runScalarStage_of_not_globalBad shape causalSecret completion witness
      coins prelude answers hgood oracle hagrees .productCoefficient
      statuses.productCoefficient with
    ⟨productResult, hproductResult, hproductTranscript⟩
  rcases productResult with ⟨productCoefficient, afterProduct⟩
  have hproductTranscript' :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart .productCoefficient + rejectionTrials)
          (by decide)).transcript = afterProduct := by
    simpa only using hproductTranscript
  have hproductSample : sampleNonzero oracle veilSamplingTrials
      afterHadamardRho = some (productCoefficient, afterProduct) := by
    unfold sampleNonzero
    have hconnected := connectScalarStage shape causalSecret completion witness
      coins prelude answers oracle .productCoefficient
      (scalarStageStart .hadamardRho + rejectionTrials) afterHadamardRho
      (by rfl) hhadamardRhoTranscript' hproductResult
    exact (sampleScalarUntil_predicate_eq nonzero
      (scalarStageGood .productCoefficient) _ _ oracle rejectionTrials _
      (by rfl)).trans (by simpa [veilSamplingTrials] using hconnected)

  have hligeritoExists := exists_ligeritoGrinding_answer_of_not_globalBad shape
    answers hgood
  rcases grindLigeritoSites_from_index_some shape causalSecret completion witness
      coins prelude answers oracle hagrees statuses.ligerito hligeritoExists
      0 (ligeritoPositiveFoldGrindingSites shape) (by omega) afterProduct
      (by simpa [scalarStageStart, productCoefficientOffset, ligeritoOffset]
        using hproductTranscript') with
    ⟨ligeritoNonces, finalTranscript, hligeritoSample, hfinalTranscript⟩

  let raw : ProductionTailRaw shape := {
    outerSet := outerSet
    linearSetPow := linearSetPow
    hadamardSetPow := hadamardSetPow
    blindChallenge := blindChallenge
    multiplicationAlpha := multiplicationAlpha
    outerChallenge := outerChallenge
    linearRho := linearRho
    hadamardRho := hadamardRho
    productCoefficient := productCoefficient
    blindGrindingNonce := blindNonce
    ligeritoGrindingNonces := ligeritoNonces
    finalTranscript := finalTranscript }
  have hraw : sampleProductionTailRaw shape oracle transcript = some raw := by
    simp only [sampleProductionTailRaw]
    simp only [hblindPow, hblindSample, halphaSample, houterChallengeSample,
      houterSample, hlinearSample, hlinearRhoSample, hhadamardSample,
      hhadamardRhoSample, hproductSample, hligeritoSample]
    rfl

  have houterSetCard : outerSet.card = outerL0QueryCount shape :=
    collectUnique_some_card (rustLowPosition (m shape - 11))
      (outerL0QueryCount shape) veilSamplingTrials oracle afterOuterChallenge
      ∅ outerSet afterOuterPositions (by simpa [sampleUniquePositions] using
        houterSample)
  have hlinearSetCard : linearSetPow.card = veilQueryCount :=
    collectUnique_some_card (rustLowPosition 13) veilQueryCount
      veilSamplingTrials oracle afterOuterPositions ∅ linearSetPow
      afterLinearPositions (by simpa [sampleUniquePositions] using hlinearSample)
  have hhadamardSetCard : hadamardSetPow.card = veilQueryCount :=
    collectUnique_some_card (rustLowPosition 11) veilQueryCount
      veilSamplingTrials oracle afterLinearRho ∅ hadamardSetPow
      afterHadamardPositions (by simpa [sampleUniquePositions] using
        hhadamardSample)
  have hblindNe : blindChallenge ≠ 0 :=
    sampleNonzero_some_ne_zero oracle veilSamplingTrials
      (afterGrind transcript blindNonce) blindChallenge afterBlind hblindSample
  have halphaNe := sampleNotZeroOrOne_some oracle veilSamplingTrials afterBlind
    multiplicationAlpha afterAlpha halphaSample
  have houterNe : outerChallenge ≠ 0 :=
    sampleNonzero_some_ne_zero oracle veilSamplingTrials afterAlpha
      outerChallenge afterOuterChallenge houterChallengeSample
  have hlinearNe : linearRho ≠ 0 :=
    sampleNonzero_some_ne_zero oracle veilSamplingTrials afterLinearPositions
      linearRho afterLinearRho hlinearRhoSample
  have hhadamardNe : hadamardRho ≠ 0 :=
    sampleNonzero_some_ne_zero oracle veilSamplingTrials afterHadamardPositions
      hadamardRho afterHadamardRho hhadamardRhoSample
  have hproductNe : productCoefficient ≠ 0 :=
    sampleNonzero_some_ne_zero oracle veilSamplingTrials afterHadamardRho
      productCoefficient afterProduct hproductSample
  have hfinish : ∃ tail, finishProductionTailRaw shape equalityPoint raw =
      some tail := by
    unfold finishProductionTailRaw
    simp [raw, houterSetCard, hlinearSetCard, hhadamardSetCard, houterNe,
      hblindNe, halphaNe.1, halphaNe.2, hlinearNe, hhadamardNe, hproductNe]
  rcases hfinish with ⟨tail, htail⟩
  refine ⟨tail, ?_⟩
  unfold sampleProductionTail
  rw [hraw]
  exact htail

end VeiledFlock.ProductionSamplingTraceTailComplete

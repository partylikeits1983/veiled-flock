import VeiledFlock.Production.Sampling.SamplingTraceTailBlindRun

/-! # Complete production tail refinement -/

namespace VeiledFlock.ProductionSamplingTraceTail

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
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole
open VeiledFlock.ProductionSamplingTraceBlind
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionSamplingTraceLigerito
open VeiledFlock.ProductionSamplingTracePositions
open VeiledFlock.ProductionSamplingTraceScalar
open VeiledFlock.ProductionSamplingTraceTailBlind
open VeiledFlock.ProductionSamplingTraceTailBlindOracle
open VeiledFlock.ProductionSamplingTraceTailBlindRun
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionUniquePositionSampler
open VeiledFlock.UniquePositionSampling

set_option maxRecDepth 10000 in
theorem rawControlUntil_positionStage_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (stage : PositionStage)
    (hbefore : (rawControlUntil shape causalSecret completion witness coins
      prelude answers (positionStageStart stage) (by
        cases stage <;> rw [productionSamplingSlots_eq] <;> decide)).status =
      .live)
    (hcard : positionStageTarget shape stage ≤
      (observedNatPositions
        (fun block ↦ positionStageProject shape stage (scalarFromBlock block))
        (window (positionStageStart stage) samplingTrials (by
          cases stage <;> rw [productionSamplingSlots_eq] <;> decide)
          answers)).card) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (positionStageStart stage + samplingTrials) (by
        cases stage <;> rw [productionSamplingSlots_eq] <;> decide)).stageDone =
      true := by
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers (positionStageStart stage) samplingTrials (by
      cases stage <;> rw [productionSamplingSlots_eq] <;> decide)
  rw [hadd]
  exact (rawPositionStage_live_done shape causalSecret completion witness coins
    stage _ _ hbefore hcard).2

theorem scalarStage_exists_direct (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (stage : ScalarStage) :
    ∃ trial : Fin rejectionTrials,
      scalarStageGood stage
        (scalarFromBlock
          (answers ⟨scalarStageStart stage + trial.val, by
            have hstart : scalarStageStart stage + rejectionTrials ≤
                productionSamplingSlots := by cases stage <;> decide
            omega⟩)) := by
  rcases scalarStage_good_of_not_globalBad shape answers hgood stage with
    ⟨trial, htrial⟩
  refine ⟨trial, ?_⟩
  rw [scalarStageGood_iff_not_mem]
  simpa [FixedWindowProbability.window] using htrial

/-
set_option maxHeartbeats 10000 in
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
        answers blindStateOffset (by decide)).transcript = transcript) :
    ∃ tail,
      sampleProductionTail shape oracle equalityPoint transcript = some tail := by
  classical
  have hequality := rawControlUntil_equality_live_some shape causalSecret
    completion witness coins prelude answers
    (equality_accepted_of_not_globalBad shape answers hgood)
  have hzero := rawControlUntil_zerocheck_live_some shape causalSecret
    completion witness coins prelude answers hequality
  have hblindStart : (rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset (by decide)).status = .live := hzero.1
  have hblindExists := exists_blindGrinding_answer_of_not_globalBad shape
    answers hgood
  have hblindEnd := rawControlUntil_blind_live_done shape causalSecret completion
    witness coins prelude answers hblindStart hblindExists
  have hblindChallengeStatus := hblindEnd.1
  have hblindChallengeGood := scalarStage_good_of_not_globalBad shape answers
    hgood .blindChallenge
  have hblindChallengeEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .blindChallenge
    hblindChallengeStatus hblindChallengeGood
  have halphaStatus : (rawControlUntil shape causalSecret completion witness coins
      prelude answers multiplicationAlphaOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, multiplicationAlphaOffset] using
      hblindChallengeEnd
  have halphaGood := scalarStage_good_of_not_globalBad shape answers hgood
    .multiplicationAlpha
  have halphaEnd := rawControlUntil_scalarStage_live shape causalSecret completion
    witness coins prelude answers .multiplicationAlpha halphaStatus halphaGood
  have houterChallengeStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers outerChallengeOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, outerChallengeOffset] using halphaEnd
  have houterChallengeGood := scalarStage_good_of_not_globalBad shape answers
    hgood .outerChallenge
  have houterChallengeEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .outerChallenge
    houterChallengeStatus houterChallengeGood
  have houterPositionsStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers outerPositionsOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, outerPositionsOffset] using houterChallengeEnd
  have houterCard := positionStage_card_of_not_globalBad shape answers hgood .outer
  have houterPositionsEnd := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .outer
    houterPositionsStatus houterCard
  have hlinearPositionsStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers linearPositionsOffset (by decide)).status =
      .live := by
    simpa only [positionStageStart, linearPositionsOffset, samplingTrials,
      rejectionTrials] using houterPositionsEnd
  have hlinearCard := positionStage_card_of_not_globalBad shape answers hgood .linear
  have hlinearPositionsEnd := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .linear
    hlinearPositionsStatus hlinearCard
  have hlinearRhoStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers linearRhoOffset (by decide)).status = .live := by
    simpa only [positionStageStart, linearRhoOffset, samplingTrials,
      rejectionTrials] using hlinearPositionsEnd
  have hlinearRhoGood := scalarStage_good_of_not_globalBad shape answers hgood
    .linearRho
  have hlinearRhoEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .linearRho hlinearRhoStatus
    hlinearRhoGood
  have hhadamardPositionsStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers hadamardPositionsOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, hadamardPositionsOffset] using hlinearRhoEnd
  have hhadamardCard := positionStage_card_of_not_globalBad shape answers hgood
    .hadamard
  have hhadamardPositionsEnd := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .hadamard
    hhadamardPositionsStatus hhadamardCard
  have hhadamardRhoStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers hadamardRhoOffset (by decide)).status = .live := by
    simpa only [positionStageStart, hadamardRhoOffset, samplingTrials,
      rejectionTrials] using hhadamardPositionsEnd
  have hhadamardRhoGood := scalarStage_good_of_not_globalBad shape answers hgood
    .hadamardRho
  have hhadamardRhoEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .hadamardRho hhadamardRhoStatus
    hhadamardRhoGood
  have hproductStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers productCoefficientOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, productCoefficientOffset] using hhadamardRhoEnd
  have hproductGood := scalarStage_good_of_not_globalBad shape answers hgood
    .productCoefficient
  have hproductEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .productCoefficient hproductStatus
    hproductGood
  have hligeritoStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers ligeritoOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, ligeritoOffset] using hproductEnd

  let blindStart := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset (by decide)
  let blindSite : Fin productionSamplingSlots := ⟨blindStateOffset, by decide⟩
  have hblindQuery : rawQuery shape causalSecret completion witness coins
      blindSite blindStart = some (scalarPoint blindStart.transcript) := by
    simpa only [blindSite, blindStart] using rawQuery_blindState shape
      causalSecret completion witness coins blindStart hblindStart
  have hblindStateAnswer : oracle (scalarPoint transcript) = answers blindSite := by
    rw [← htranscript]
    exact (hagrees blindSite _ hblindQuery).symm
  have hblindSucc := rawControlUntil_succ shape causalSecret completion witness
    coins prelude answers blindSite
  have hblindStep := rawStep_blindState shape causalSecret completion witness
    coins blindStart (answers blindSite) hblindStart
  rw [hblindStep] at hblindSucc
  let blindWithState := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindGrindingOffset (by decide)
  have hblindWithState : blindWithState =
      { blindStart with powState := some (answers blindSite)
          stageDone := false, stageBlocks := [] } := by
    simpa only [blindWithState, blindSite, blindStart, blindGrindingOffset,
      blindStateWidth] using hblindSucc
  have hblindGrindStatus : blindWithState.status = .live := by
    rw [hblindWithState]
    exact hblindStart
  have hblindGrindDone : blindWithState.stageDone = false := by
    simp [hblindWithState]
  have hblindGrindState : blindWithState.powState = some (answers blindSite) := by
    simp [hblindWithState]
  have hblindDirect : ∃ offset : Fin maxBlindTrials,
      blindGrindingGood
        (answers ⟨blindGrindingOffset + offset.val, by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega⟩) := by
    rcases hblindExists with ⟨trial, htrial⟩
    refine ⟨trial, ?_⟩
    simpa [FixedWindowProbability.window] using htrial
  rcases grindFrom_blind_stage_some shape causalSecret completion witness coins
      prelude answers oracle hagrees (answers blindSite) 0 maxBlindTrials
      (by omega) hblindGrindStatus hblindGrindDone hblindGrindState hblindDirect
    with ⟨blindNonce, hblindNonce, hafterBlind⟩
  have hblindPow : grindPowBounded blindGrindingGood oracle
      (answers blindSite) maxBlindTrials = some blindNonce := by
    simpa only [grindPowBounded] using hblindNonce
  have hblindPow' : grindPowBounded blindGrindingGood oracle
      (oracle (scalarPoint transcript)) maxBlindTrials = some blindNonce := by
    rw [hblindStateAnswer]
    exact hblindPow

  have runScalar : ∀ stage : ScalarStage,
      ∀ hstatus : (rawControlUntil shape causalSecret completion witness coins
        prelude answers (scalarStageStart stage) (by
          cases stage <;> decide)).status = .live,
      ∃ result,
        sampleScalarUntil (scalarStageGood stage) oracle rejectionTrials
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers (scalarStageStart stage) (by
                cases stage <;> decide)).transcript = some result ∧
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (scalarStageStart stage + rejectionTrials) (by
            cases stage <;> decide)).transcript = result.2 := by
    intro stage hstatus
    apply sampleScalarUntil_stage_some shape causalSecret completion witness coins
      prelude answers oracle hagrees stage 0 rejectionTrials (by omega) hstatus
      (Or.inl rfl)
    rcases scalarStage_exists_direct shape answers hgood stage with ⟨trial, ht⟩
    exact ⟨trial, by simpa using ht⟩

  rcases runScalar .blindChallenge hblindChallengeStatus with
    ⟨blindResult, hblindResult, hblindTranscript⟩
  rcases blindResult with ⟨blindChallenge, afterBlind⟩
  have hblindSample : sampleNonzero oracle veilSamplingTrials
      (afterGrind transcript blindNonce) = some (blindChallenge, afterBlind) := by
    unfold sampleNonzero
    simpa [veilSamplingTrials, rejectionTrials, scalarStageGood] using
      (hblindResult.trans (by rw [← hafterBlind]))
  rcases runScalar .multiplicationAlpha halphaStatus with
    ⟨alphaResult, halphaResult, halphaTranscript⟩
  rcases alphaResult with ⟨multiplicationAlpha, afterAlpha⟩
  have halphaSample : sampleNotZeroOrOne oracle veilSamplingTrials afterBlind =
      some (multiplicationAlpha, afterAlpha) := by
    unfold sampleNotZeroOrOne
    simpa [veilSamplingTrials, rejectionTrials, scalarStageGood] using
      (halphaResult.trans (by rw [← hblindTranscript]))
  rcases runScalar .outerChallenge houterChallengeStatus with
    ⟨outerChallengeResult, houterChallengeResult, houterChallengeTranscript⟩
  rcases outerChallengeResult with ⟨outerChallenge, afterOuterChallenge⟩
  have houterChallengeSample : sampleNonzero oracle veilSamplingTrials afterAlpha =
      some (outerChallenge, afterOuterChallenge) := by
    unfold sampleNonzero
    simpa [veilSamplingTrials, rejectionTrials, scalarStageGood] using
      (houterChallengeResult.trans (by rw [← halphaTranscript]))

  have runPositions : ∀ (stage : PositionStage) (domain : ℕ)
      (position : GhashField → Fin domain)
      (hproject : ∀ value,
        positionStageProject shape stage value = (position value).val)
      (hstatus : (rawControlUntil shape causalSecret completion witness coins
        prelude answers (positionStageStart stage) (by
          cases stage <;> decide)).status = .live),
      ∃ result,
        collectUnique position (positionStageTarget shape stage) oracle
            samplingTrials
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers (positionStageStart stage) (by
                cases stage <;> decide)).transcript ∅ = some result ∧
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (positionStageStart stage + samplingTrials) (by
            cases stage <;> decide)).transcript = result.2 := by
    intro stage domain position hproject hstatus
    have hcard := positionStage_card_of_not_globalBad shape answers hgood stage
    have hdone := rawControlUntil_positionStage_done shape causalSecret completion
      witness coins prelude answers stage hstatus hcard
    apply collectUnique_stage_some shape causalSecret completion witness coins
      prelude answers oracle hagrees stage position hproject ∅ 0 samplingTrials
      (by omega) hstatus (Or.inl rfl) (Or.inl rfl) (by intro; rfl)
      (by cases stage <;> simp [positionStageTarget] <;> omega) hdone

  rcases runPositions .outer (2 ^ (m shape - 11))
      (rustLowPosition (m shape - 11)) (by intro; rfl)
      houterPositionsStatus with ⟨outerResult, houterResult, houterTranscript⟩
  rcases outerResult with ⟨outerSet, afterOuterPositions⟩
  have houterSample : sampleUniquePositions (rustLowPosition (m shape - 11))
      (outerL0QueryCount shape) veilSamplingTrials oracle afterOuterChallenge =
        some (outerSet, afterOuterPositions) := by
    unfold sampleUniquePositions
    simpa [positionStageTarget, veilSamplingTrials, samplingTrials] using
      (houterResult.trans (by rw [← houterChallengeTranscript]))
  rcases runPositions .linear (2 ^ 13) (rustLowPosition 13) (by intro; rfl)
      hlinearPositionsStatus with ⟨linearResult, hlinearResult, hlinearTranscript⟩
  rcases linearResult with ⟨linearSetPow, afterLinearPositions⟩
  have hlinearSample : sampleUniquePositions (rustLowPosition 13) veilQueryCount
      veilSamplingTrials oracle afterOuterPositions =
        some (linearSetPow, afterLinearPositions) := by
    unfold sampleUniquePositions
    simpa [positionStageTarget, veilSamplingTrials, samplingTrials] using
      (hlinearResult.trans (by rw [← houterTranscript]))
  rcases runScalar .linearRho hlinearRhoStatus with
    ⟨linearRhoResult, hlinearRhoResult, hlinearRhoTranscript⟩
  rcases linearRhoResult with ⟨linearRho, afterLinearRho⟩
  have hlinearRhoSample : sampleNonzero oracle veilSamplingTrials
      afterLinearPositions = some (linearRho, afterLinearRho) := by
    unfold sampleNonzero
    simpa [veilSamplingTrials, rejectionTrials, scalarStageGood] using
      (hlinearRhoResult.trans (by rw [← hlinearTranscript]))
  rcases runPositions .hadamard (2 ^ 11) (rustLowPosition 11) (by intro; rfl)
      hhadamardPositionsStatus with
    ⟨hadamardResult, hhadamardResult, hhadamardTranscript⟩
  rcases hadamardResult with ⟨hadamardSetPow, afterHadamardPositions⟩
  have hhadamardSample : sampleUniquePositions (rustLowPosition 11)
      veilQueryCount veilSamplingTrials oracle afterLinearRho =
        some (hadamardSetPow, afterHadamardPositions) := by
    unfold sampleUniquePositions
    simpa [positionStageTarget, veilSamplingTrials, samplingTrials] using
      (hhadamardResult.trans (by rw [← hlinearRhoTranscript]))
  rcases runScalar .hadamardRho hhadamardRhoStatus with
    ⟨hadamardRhoResult, hhadamardRhoResult, hhadamardRhoTranscript⟩
  rcases hadamardRhoResult with ⟨hadamardRho, afterHadamardRho⟩
  have hhadamardRhoSample : sampleNonzero oracle veilSamplingTrials
      afterHadamardPositions = some (hadamardRho, afterHadamardRho) := by
    unfold sampleNonzero
    simpa [veilSamplingTrials, rejectionTrials, scalarStageGood] using
      (hhadamardRhoResult.trans (by rw [← hhadamardTranscript]))
  rcases runScalar .productCoefficient hproductStatus with
    ⟨productResult, hproductResult, hproductTranscript⟩
  rcases productResult with ⟨productCoefficient, afterProduct⟩
  have hproductSample : sampleNonzero oracle veilSamplingTrials
      afterHadamardRho = some (productCoefficient, afterProduct) := by
    unfold sampleNonzero
    simpa [veilSamplingTrials, rejectionTrials, scalarStageGood] using
      (hproductResult.trans (by rw [← hhadamardRhoTranscript]))

  have hligeritoExists := exists_ligeritoGrinding_answer_of_not_globalBad shape
    answers hgood
  have hproductBoundary :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers ligeritoOffset (by decide)).transcript = afterProduct := by
    exact hproductTranscript
  rcases grindLigeritoSites_from_index_some shape causalSecret completion
      witness coins prelude answers oracle hagrees hligeritoStatus hligeritoExists
      0 maxLigeritoSites (by omega) afterProduct
      (by simpa only [Nat.zero_mul, Nat.add_zero] using hproductBoundary) with
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
    rw [hblindPow', hblindSample, halphaSample, houterChallengeSample,
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

-/

structure TailStageStatuses
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) : Prop where
  blindState : (rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset (by decide)).status = .live
  blindChallenge : (rawControlUntil shape causalSecret completion witness coins
    prelude answers blindChallengeOffset (by decide)).status = .live
  multiplicationAlpha : (rawControlUntil shape causalSecret completion witness
    coins prelude answers multiplicationAlphaOffset (by decide)).status = .live
  outerChallenge : (rawControlUntil shape causalSecret completion witness coins
    prelude answers outerChallengeOffset (by decide)).status = .live
  outerPositions : (rawControlUntil shape causalSecret completion witness coins
    prelude answers outerPositionsOffset (by decide)).status = .live
  linearPositions : (rawControlUntil shape causalSecret completion witness coins
    prelude answers linearPositionsOffset (by decide)).status = .live
  linearRho : (rawControlUntil shape causalSecret completion witness coins
    prelude answers linearRhoOffset (by decide)).status = .live
  hadamardPositions : (rawControlUntil shape causalSecret completion witness coins
    prelude answers hadamardPositionsOffset (by decide)).status = .live
  hadamardRho : (rawControlUntil shape causalSecret completion witness coins
    prelude answers hadamardRhoOffset (by decide)).status = .live
  productCoefficient : (rawControlUntil shape causalSecret completion witness
    coins prelude answers productCoefficientOffset (by decide)).status = .live
  ligerito : (rawControlUntil shape causalSecret completion witness coins
    prelude answers ligeritoOffset (by decide)).status = .live

set_option maxRecDepth 10000 in
theorem tailStageStatuses_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    TailStageStatuses shape causalSecret completion witness coins prelude
      answers := by
  have hequality := rawControlUntil_equality_live_some shape causalSecret
    completion witness coins prelude answers
    (equality_accepted_of_not_globalBad shape answers hgood)
  have hzero := rawControlUntil_zerocheck_live_some shape causalSecret
    completion witness coins prelude answers hequality
  have hblindStart := hzero.1
  have hblindExists := exists_blindGrinding_answer_of_not_globalBad shape
    answers hgood
  have hblindEnd := rawControlUntil_blind_live_done shape causalSecret completion
    witness coins prelude answers hblindStart hblindExists
  have hblindChallengeStatus := hblindEnd.1
  have hblindChallengeEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .blindChallenge
    hblindChallengeStatus
    (scalarStage_good_of_not_globalBad shape answers hgood .blindChallenge)
  have halphaStatus : (rawControlUntil shape causalSecret completion witness coins
      prelude answers multiplicationAlphaOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, multiplicationAlphaOffset] using
      hblindChallengeEnd
  have halphaEnd := rawControlUntil_scalarStage_live shape causalSecret completion
    witness coins prelude answers .multiplicationAlpha halphaStatus
    (scalarStage_good_of_not_globalBad shape answers hgood .multiplicationAlpha)
  have houterChallengeStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers outerChallengeOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, outerChallengeOffset] using halphaEnd
  have houterChallengeEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .outerChallenge houterChallengeStatus
    (scalarStage_good_of_not_globalBad shape answers hgood .outerChallenge)
  have houterPositionsStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers outerPositionsOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, outerPositionsOffset] using houterChallengeEnd
  have houterPositionsEnd := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .outer
    houterPositionsStatus
    (positionStage_card_of_not_globalBad shape answers hgood .outer)
  have hlinearPositionsStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers linearPositionsOffset (by decide)).status =
      .live := by
    simpa only [positionStageStart, linearPositionsOffset, samplingTrials,
      rejectionTrials] using houterPositionsEnd
  have hlinearPositionsEnd := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .linear
    hlinearPositionsStatus
    (positionStage_card_of_not_globalBad shape answers hgood .linear)
  have hlinearRhoStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers linearRhoOffset (by decide)).status = .live := by
    simpa only [positionStageStart, linearRhoOffset, samplingTrials,
      rejectionTrials] using hlinearPositionsEnd
  have hlinearRhoEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .linearRho hlinearRhoStatus
    (scalarStage_good_of_not_globalBad shape answers hgood .linearRho)
  have hhadamardPositionsStatus : (rawControlUntil shape causalSecret completion
      witness coins prelude answers hadamardPositionsOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, hadamardPositionsOffset] using hlinearRhoEnd
  have hhadamardPositionsEnd := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .hadamard
    hhadamardPositionsStatus
    (positionStage_card_of_not_globalBad shape answers hgood .hadamard)
  have hhadamardRhoStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers hadamardRhoOffset (by decide)).status = .live := by
    simpa only [positionStageStart, hadamardRhoOffset, samplingTrials,
      rejectionTrials] using hhadamardPositionsEnd
  have hhadamardRhoEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .hadamardRho hhadamardRhoStatus
    (scalarStage_good_of_not_globalBad shape answers hgood .hadamardRho)
  have hproductStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers productCoefficientOffset (by decide)).status =
      .live := by
    simpa only [scalarStageStart, productCoefficientOffset] using hhadamardRhoEnd
  have hproductEnd := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .productCoefficient hproductStatus
    (scalarStage_good_of_not_globalBad shape answers hgood .productCoefficient)
  have hligeritoStatus : (rawControlUntil shape causalSecret completion witness
      coins prelude answers ligeritoOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, ligeritoOffset] using hproductEnd
  exact {
    blindState := hblindStart
    blindChallenge := hblindChallengeStatus
    multiplicationAlpha := halphaStatus
    outerChallenge := houterChallengeStatus
    outerPositions := houterPositionsStatus
    linearPositions := hlinearPositionsStatus
    linearRho := hlinearRhoStatus
    hadamardPositions := hhadamardPositionsStatus
    hadamardRho := hhadamardRhoStatus
    productCoefficient := hproductStatus
    ligerito := hligeritoStatus }

set_option maxRecDepth 10000 in
theorem runScalarStage_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (stage : ScalarStage)
    (hstatus : (rawControlUntil shape causalSecret completion witness coins
      prelude answers (scalarStageStart stage) (by
        cases stage <;> decide)).status = .live) :
    ∃ result,
      sampleScalarUntil (scalarStageGood stage) oracle rejectionTrials
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (scalarStageStart stage) (by
              cases stage <;> decide)).transcript = some result ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (scalarStageStart stage + rejectionTrials) (by
          cases stage <;> decide)).transcript = result.2 := by
  apply sampleScalarUntil_stage_some shape causalSecret completion witness coins
    prelude answers oracle hagrees stage 0 rejectionTrials (by omega) hstatus
    (Or.inl rfl)
  rcases scalarStage_exists_direct shape answers hgood stage with ⟨trial, ht⟩
  exact ⟨trial, by simpa using ht⟩

set_option maxRecDepth 10000 in
theorem runPositionStage_of_not_globalBad
    {W : Type*} {domain : ℕ} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (stage : PositionStage) (position : GhashField → Fin domain)
    (hproject : ∀ value,
      positionStageProject shape stage value = (position value).val)
    (hstatus : (rawControlUntil shape causalSecret completion witness coins
      prelude answers (positionStageStart stage) (by
        cases stage <;> decide)).status = .live) :
    ∃ result,
      collectUnique position (positionStageTarget shape stage) oracle
          samplingTrials
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (positionStageStart stage) (by
              cases stage <;> decide)).transcript ∅ = some result ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + samplingTrials) (by
          cases stage <;> decide)).transcript = result.2 := by
  have hcard := positionStage_card_of_not_globalBad shape answers hgood stage
  have hdone := rawControlUntil_positionStage_done shape causalSecret completion
    witness coins prelude answers stage hstatus hcard
  have htargetPositive : 0 < positionStageTarget shape stage := by
    cases stage with
    | outer => exact outerL0QueryCount_positive shape
    | linear => norm_num [positionStageTarget, veilQueryCount]
    | hadamard => norm_num [positionStageTarget, veilQueryCount]
  apply collectUnique_stage_some shape causalSecret completion witness coins
    prelude answers oracle hagrees stage position hproject ∅ 0 samplingTrials
    (by omega) hstatus (Or.inl rfl) (Or.inl rfl) (by intro; rfl)
    (by simpa using htargetPositive) hdone

end VeiledFlock.ProductionSamplingTraceTail

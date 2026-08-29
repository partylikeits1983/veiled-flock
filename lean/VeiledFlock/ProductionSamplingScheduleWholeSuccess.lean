import VeiledFlock.ProductionSamplingScheduleWholeBlind

/-!
# Whole raw production schedule succeeds outside the explicit ledger

The theorem in this file is the deterministic heart of the operational
failure bound: every equality, zerocheck, rejection, position, and grinding
stage of the literal production state machine reaches success whenever the
fixed answer tape is outside `globalBad`.
-/

namespace VeiledFlock.ProductionSamplingScheduleWhole

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawControlUntil_ligerito_live_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      ligeritoOffset (by decide)).status = .live := by
  have hequality := rawControlUntil_equality_live_some shape causalSecret
    completion witness coins prelude answers
    (equality_accepted_of_not_globalBad shape answers hgood)
  have hzero := rawControlUntil_zerocheck_live_some shape causalSecret
    completion witness coins prelude answers hequality
  have hblind := rawControlUntil_blind_live_done shape causalSecret completion
    witness coins prelude answers hzero.1
    (exists_blindGrinding_answer_of_not_globalBad shape answers hgood)
  have hblindChallengeRaw := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .blindChallenge hblind.1
    (scalarStage_good_of_not_globalBad shape answers hgood .blindChallenge)
  have hblindChallenge :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers multiplicationAlphaOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, multiplicationAlphaOffset] using
      hblindChallengeRaw
  have hmultiplicationRaw := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .multiplicationAlpha
    hblindChallenge
    (scalarStage_good_of_not_globalBad shape answers hgood .multiplicationAlpha)
  have hmultiplication :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers outerChallengeOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, outerChallengeOffset] using hmultiplicationRaw
  have houterChallengeRaw := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .outerChallenge hmultiplication
    (scalarStage_good_of_not_globalBad shape answers hgood .outerChallenge)
  have houterChallenge :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers outerPositionsOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, outerPositionsOffset] using houterChallengeRaw
  have houterPositionsRaw := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .outer houterChallenge
    (positionStage_card_of_not_globalBad shape answers hgood .outer)
  have houterPositions :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers linearPositionsOffset (by decide)).status = .live := by
    simpa only [positionStageStart, linearPositionsOffset,
      VeiledFlock.UniquePositionSampling.samplingTrials,
      VeiledFlock.ChallengeSampling.rejectionTrials] using
      houterPositionsRaw
  have hlinearPositionsRaw := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .linear houterPositions
    (positionStage_card_of_not_globalBad shape answers hgood .linear)
  have hlinearPositions :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers linearRhoOffset (by decide)).status = .live := by
    simpa only [positionStageStart, linearRhoOffset,
      VeiledFlock.UniquePositionSampling.samplingTrials,
      VeiledFlock.ChallengeSampling.rejectionTrials] using hlinearPositionsRaw
  have hlinearRhoRaw := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .linearRho hlinearPositions
    (scalarStage_good_of_not_globalBad shape answers hgood .linearRho)
  have hlinearRho :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers hadamardPositionsOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, hadamardPositionsOffset] using hlinearRhoRaw
  have hhadamardPositionsRaw := rawControlUntil_positionStage_live shape
    causalSecret completion witness coins prelude answers .hadamard hlinearRho
    (positionStage_card_of_not_globalBad shape answers hgood .hadamard)
  have hhadamardPositions :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers hadamardRhoOffset (by decide)).status = .live := by
    simpa only [positionStageStart, hadamardRhoOffset,
      VeiledFlock.UniquePositionSampling.samplingTrials,
      VeiledFlock.ChallengeSampling.rejectionTrials] using
      hhadamardPositionsRaw
  have hhadamardRhoRaw := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .hadamardRho hhadamardPositions
    (scalarStage_good_of_not_globalBad shape answers hgood .hadamardRho)
  have hhadamardRho :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers productCoefficientOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, productCoefficientOffset] using hhadamardRhoRaw
  have hproductRaw := rawControlUntil_scalarStage_live shape causalSecret
    completion witness coins prelude answers .productCoefficient hhadamardRho
    (scalarStage_good_of_not_globalBad shape answers hgood .productCoefficient)
  have hligerito :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers ligeritoOffset (by decide)).status = .live := by
    simpa only [scalarStageStart, ligeritoOffset] using hproductRaw
  exact hligerito

set_option maxRecDepth 10000 in
theorem rawControlUntil_success_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      productionSamplingSlots (by rfl)).status = .success := by
  exact rawControlUntil_ligerito_success shape causalSecret completion witness
    coins prelude answers
    (rawControlUntil_ligerito_live_of_not_globalBad shape causalSecret completion
      witness coins prelude answers hgood)
    (exists_ligeritoGrinding_answer_of_not_globalBad shape answers hgood)

theorem controlAfter_success_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    (controlAfter shape causalSecret completion witness coins prelude
      answers).status = .success := by
  rw [controlAfter_eq_rawControlUntil]
  exact rawControlUntil_success_of_not_globalBad shape causalSecret completion
    witness coins prelude answers hgood

end VeiledFlock.ProductionSamplingScheduleWhole

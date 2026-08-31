import VeiledFlock.Production.Sampling.SamplingScheduleWholeZerocheck

/-!
# Whole-prefix semantics of the production sampling schedule

Small opaque bridge lemmas compose the already-proved per-stage semantics
without expanding the complete production schedule during kernel checking.
-/

namespace VeiledFlock.ProductionSamplingScheduleWhole

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.UniquePositionSampling

theorem rawControlUntil_scalarStage_live
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (stage : ScalarStage)
    (hbefore : (rawControlUntil shape causalSecret completion witness coins
      prelude answers (scalarStageStart stage) (by
        cases stage <;> rw [productionSamplingSlots_eq] <;> decide)).status =
      .live)
    (hgood : ∃ trial : Fin rejectionTrials,
      scalarFromBlock (window (scalarStageStart stage) rejectionTrials (by
        cases stage <;> rw [productionSamplingSlots_eq] <;> decide)
        answers trial) ∉ scalarStageFailure stage) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (scalarStageStart stage + rejectionTrials) (by
        cases stage <;> rw [productionSamplingSlots_eq] <;> decide)).status =
      .live := by
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers (scalarStageStart stage) rejectionTrials (by
      cases stage <;> rw [productionSamplingSlots_eq] <;> decide)
  rw [hadd]
  exact (rawScalarStage_live_done shape causalSecret completion witness coins
    stage _ _ hbefore hgood).1


set_option maxRecDepth 10000 in
theorem rawControlUntil_positionStage_live
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
        cases stage <;> rw [productionSamplingSlots_eq] <;> decide)).status =
      .live := by
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers (positionStageStart stage) samplingTrials (by
      cases stage <;> rw [productionSamplingSlots_eq] <;> decide)
  rw [hadd]
  exact (rawPositionStage_live_done shape causalSecret completion witness coins
    stage _ _ hbefore hcard).1

end VeiledFlock.ProductionSamplingScheduleWhole

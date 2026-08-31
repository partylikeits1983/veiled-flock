import VeiledFlock.Production.Sampling.SamplingOperationalProbability
import VeiledFlock.Production.Sampling.SamplingScheduleCollisionFree
import VeiledFlock.Production.Sampling.SamplingScheduleWholeSuccess

/-!
# Operational sampling answers follow the literal production schedule

Outside the explicit finite sampling ledger, duplicate suppression is inert.
Consequently every active literal production query receives exactly the answer
stored at that point in the single shared bounded oracle table.
-/

namespace VeiledFlock.ProductionSamplingOperationalTrace

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingOperationalProbability
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleCollisionFree
open VeiledFlock.ProductionSamplingScheduleSemantics

variable {AdversaryCoins : Type*}

theorem expandedSamplingAnswers_raw_active
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins)
    (hgood : expandedSamplingAnswers shape maxStartLength fallback r1csDigest
      statement witness causalSecret completion hbudget input ∉ globalBad shape)
    (site : Fin productionSamplingSlots) (point : List Byte)
    (hquery : rawQuery shape causalSecret completion witness input.1.1 site
      (rawControlUntil shape causalSecret completion witness input.1.1
        (samplingPrelude shape maxStartLength fallback r1csDigest statement
          witness input.1.1
            (samplingExpandedSplit shape maxStartLength input).2.2.1)
        (expandedSamplingAnswers shape maxStartLength fallback r1csDigest
          statement witness causalSecret completion hbudget input)
        site site.isLt.le) = some point) :
    expandedSamplingAnswers shape maxStartLength fallback r1csDigest statement
        witness causalSecret completion hbudget input site =
      answerBounded fallback input.1.2.1 point := by
  let answers := expandedSamplingAnswers shape maxStartLength fallback
    r1csDigest statement witness causalSecret completion hbudget input
  let prelude := samplingPrelude shape maxStartLength fallback r1csDigest
    statement witness input.1.1
      (samplingExpandedSplit shape maxStartLength input).2.2.1
  have hprelude : isFiatShamirPoint prelude :=
    samplingPrelude_isFiatShamir shape maxStartLength fallback r1csDigest
      statement witness input.1.1
        (samplingExpandedSplit shape maxStartLength input).2.2.1
  have hfresh : freshSchedule shape causalSecret completion witness input.1.1
      prelude site (priorAnswers answers site) = some point := by
    rw [freshSchedule_eq_rawQuery_of_not_globalBad shape causalSecret completion
      witness input.1.1 prelude hprelude answers hgood site]
    exact hquery
  exact expandedSamplingAnswers_active shape maxStartLength fallback r1csDigest
    statement witness causalSecret completion hbudget input site point hfresh

theorem expandedScheduledControl_success
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins)
    (hgood : expandedSamplingAnswers shape maxStartLength fallback r1csDigest
      statement witness causalSecret completion hbudget input ∉ globalBad shape) :
    (scheduledControlUntil shape causalSecret completion witness input.1.1
      (samplingPrelude shape maxStartLength fallback r1csDigest statement
        witness input.1.1
          (samplingExpandedSplit shape maxStartLength input).2.2.1)
      (expandedSamplingAnswers shape maxStartLength fallback r1csDigest
        statement witness causalSecret completion hbudget input)
      productionSamplingSlots (by rfl)).raw.status = .success := by
  let answers := expandedSamplingAnswers shape maxStartLength fallback
    r1csDigest statement witness causalSecret completion hbudget input
  let prelude := samplingPrelude shape maxStartLength fallback r1csDigest
    statement witness input.1.1
      (samplingExpandedSplit shape maxStartLength input).2.2.1
  have hprelude : isFiatShamirPoint prelude :=
    samplingPrelude_isFiatShamir shape maxStartLength fallback r1csDigest
      statement witness input.1.1
        (samplingExpandedSplit shape maxStartLength input).2.2.1
  rw [scheduledControlUntil_raw_of_not_globalBad shape causalSecret completion
    witness input.1.1 prelude hprelude answers hgood]
  exact VeiledFlock.ProductionSamplingScheduleWhole.rawControlUntil_success_of_not_globalBad
    shape causalSecret completion witness input.1.1 prelude answers hgood

end VeiledFlock.ProductionSamplingOperationalTrace

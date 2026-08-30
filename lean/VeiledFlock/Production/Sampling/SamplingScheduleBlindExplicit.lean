import VeiledFlock.Production.Sampling.SamplingScheduleBlindFreshness

/-! # Explicit blind-grinding transcript bound -/

namespace VeiledFlock.ProductionSamplingScheduleBlindExplicit

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawBlindGrinding_add_seventeen_explicit
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (stateAnswer : OracleBlock)
    (answers : Fin maxBlindTrials → OracleBlock)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin maxBlindTrials,
      blindGrindingGood (answers trial)) :
    control.transcript.length + 17 ≤
      (iterateFrom (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset maxBlindTrials
        (rawStep shape causalSecret completion witness coins blindStateOffset
          control stateAnswer) answers).transcript.length := by
  exact rawBlindGrinding_add_seventeen shape causalSecret completion witness
    coins control stateAnswer answers hstatus hexists

end VeiledFlock.ProductionSamplingScheduleBlindExplicit

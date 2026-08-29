import VeiledFlock.ProductionSamplingScheduleBlindControlFreshness

/-! # Opaque projections of the blind-state transition -/

namespace VeiledFlock.ProductionSamplingScheduleBlindStateProjection

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawStep_blindState_status
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    (rawStep shape causalSecret completion witness coins blindStateOffset
      control answer).status = .live := by
  rw [rawStep_blindState shape causalSecret completion witness coins control
    answer hstatus]
  exact hstatus

set_option maxRecDepth 10000 in
theorem rawStep_blindState_stageDone
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    (rawStep shape causalSecret completion witness coins blindStateOffset
      control answer).stageDone = false := by
  rw [rawStep_blindState shape causalSecret completion witness coins control
    answer hstatus]

set_option maxRecDepth 10000 in
theorem rawStep_blindState_powState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    (rawStep shape causalSecret completion witness coins blindStateOffset
      control answer).powState = some answer := by
  rw [rawStep_blindState shape causalSecret completion witness coins control
    answer hstatus]

set_option maxRecDepth 10000 in
theorem rawStep_blindState_transcript
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    (rawStep shape causalSecret completion witness coins blindStateOffset
      control answer).transcript = control.transcript := by
  rw [rawStep_blindState shape causalSecret completion witness coins control
    answer hstatus]

end VeiledFlock.ProductionSamplingScheduleBlindStateProjection

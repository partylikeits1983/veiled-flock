import VeiledFlock.Production.Sampling.SamplingScheduleEqualityAcceptedBoundary

/-! # Active prefixes inside one production equality attempt -/

namespace VeiledFlock.ProductionSamplingScheduleEqualityPrefix

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem equalityStep_before_last_fields
    (shape : BatchShape) (attempt counter : ℕ) (control : Control shape)
    (answer : OracleBlock)
    (hcounter : counter + 1 < equalityBlockCount shape)
    (hstatus : control.status = .live)
    (hnone : control.equalityPoint = none) :
    let result := equalityStep shape
      (equalityOffset + attempt * equalityAttemptBlocks + counter)
      control answer
    result.status = .live ∧ result.equalityPoint = none ∧
      result.transcript = control.transcript := by
  have hcount := equalityBlockCount_le_seven shape
  have hcounterSix : counter < equalityAttemptBlocks := by
    norm_num [equalityAttemptBlocks] at hcount ⊢
    omega
  have hoff :
      equalityOffset + attempt * equalityAttemptBlocks + counter -
          equalityOffset =
        attempt * equalityAttemptBlocks + counter := by omega
  have hmod :
      (attempt * equalityAttemptBlocks + counter) %
          equalityAttemptBlocks = counter := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hcounterSix]
  have hactive : counter < equalityBlockCount shape := by omega
  have hnotLast : counter + 1 ≠ equalityBlockCount shape := by omega
  by_cases hzero : counter = 0
  · subst counter
    have hpositive : 0 < equalityBlockCount shape := by omega
    have hnotOne : 1 ≠ equalityBlockCount shape := by omega
    simp [equalityStep,   hpositive, hnotOne, hnone, hstatus]
  · simp [equalityStep, hoff, hmod, hactive, hnotLast, hnone, hstatus,
      hzero]

set_option maxRecDepth 10000 in
theorem equalityPrefix_control_fields
    (shape : BatchShape) (attempt : ℕ) (control : Control shape)
    (counter : ℕ) (answers : Fin counter → OracleBlock)
    (hcounter : counter < equalityBlockCount shape)
    (hstatus : control.status = .live)
    (hnone : control.equalityPoint = none) :
    let result := iterateFrom (equalityStep shape)
      (equalityOffset + attempt * 7) counter control
      answers
    result.status = .live ∧ result.equalityPoint = none ∧
      result.transcript = control.transcript := by
  induction counter with
  | zero => exact ⟨hstatus, hnone, rfl⟩
  | succ counter ih =>
      rw [iterateFrom_succ_last]
      have hprefix := ih (fun index ↦ answers index.castSucc) (by omega)
      have hstep := equalityStep_before_last_fields shape attempt counter _
        (answers (Fin.last counter)) hcounter hprefix.1 hprefix.2.1
      exact ⟨hstep.1, hstep.2.1, hstep.2.2.trans hprefix.2.2⟩

end VeiledFlock.ProductionSamplingScheduleEqualityPrefix

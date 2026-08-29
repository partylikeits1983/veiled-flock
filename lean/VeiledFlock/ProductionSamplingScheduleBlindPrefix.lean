import VeiledFlock.ProductionSamplingScheduleBlindSegment

/-! # Opaque prefixes of the production blind-grinding segment -/

namespace VeiledFlock.ProductionSamplingScheduleBlindPrefix

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingLayoutBounds
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

noncomputable def blindPrefixResult
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (before : Control shape) (stateAnswer : OracleBlock)
    (rounds : ℕ) (answers : Fin rounds → OracleBlock) : Control shape :=
  iterateFrom (rawStep shape causalSecret completion witness coins)
    blindGrindingOffset rounds
    (rawStep shape causalSecret completion witness coins blindStateOffset
      before stateAnswer) answers

set_option maxRecDepth 10000 in
theorem rawControlUntil_blind_prefix_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (rounds : ℕ)
    (hrounds : rounds ≤ maxBlindTrials) :
    let before := rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset blindStateOffset_le_slots
    let hfit : blindGrindingOffset + rounds ≤ productionSamplingSlots := by
      exact (Nat.add_le_add_left hrounds blindGrindingOffset).trans
        blindGrinding_window_fits
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (blindGrindingOffset + rounds) hfit =
      blindPrefixResult shape causalSecret completion witness coins before
        (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩) rounds
        (window blindGrindingOffset rounds hfit answers) := by
  dsimp only
  have hstate := rawControlUntil_succ shape causalSecret completion witness coins
    prelude answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩
  have hstate' :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset blindGrindingOffset_le_slots =
        rawStep shape causalSecret completion witness coins blindStateOffset
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindStateOffset blindStateOffset_le_slots)
          (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩) := by
    simpa only [blindGrindingOffset_eq_state_succ] using hstate
  have hfit : blindGrindingOffset + rounds ≤ productionSamplingSlots :=
    (Nat.add_le_add_left hrounds blindGrindingOffset).trans
      blindGrinding_window_fits
  have hfinal := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers blindGrindingOffset rounds hfit
  unfold blindPrefixResult
  calc
    _ = iterateFrom (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset rounds
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindGrindingOffset blindGrindingOffset_le_slots)
        (window blindGrindingOffset rounds hfit answers) := hfinal
    _ = _ := congrArg
      (fun initial ↦ iterateFrom
        (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset rounds initial
        (window blindGrindingOffset rounds hfit answers)) hstate'

set_option maxRecDepth 10000 in
theorem blindPrefixResult_eq_blindGrinding
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (before : Control shape)
    (stateAnswer : OracleBlock) (rounds : ℕ)
    (answers : Fin rounds → OracleBlock) (hrounds : rounds ≤ maxBlindTrials)
    (hstatus : before.status = .live) :
    blindPrefixResult shape causalSecret completion witness coins before
        stateAnswer rounds answers =
      iterateFrom blindGrindingStep blindGrindingOffset rounds
        (rawStep shape causalSecret completion witness coins blindStateOffset
          before stateAnswer) answers := by
  have hstep := rawStep_blindState shape causalSecret completion witness coins
    before stateAnswer hstatus
  have hwithStatus :
      (rawStep shape causalSecret completion witness coins blindStateOffset
        before stateAnswer).status = .live := by
    rw [hstep]
    exact hstatus
  unfold blindPrefixResult
  exact iterateFrom_eq_blindGrinding shape causalSecret completion witness coins
    rounds _ answers hrounds hwithStatus

end VeiledFlock.ProductionSamplingScheduleBlindPrefix

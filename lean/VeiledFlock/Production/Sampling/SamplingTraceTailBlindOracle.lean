import VeiledFlock.Production.Sampling.SamplingTraceTailBlind
import VeiledFlock.Production.Sampling.SamplingScheduleBlindPrefix

/-! # Adaptive oracle agreement for the production blind-grinding prefix -/

namespace VeiledFlock.ProductionSamplingTraceTailBlindOracle

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingLayoutBounds
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindStateProjection
open VeiledFlock.ProductionSamplingScheduleBlindPrefix
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingTraceBlind
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionSamplingTraceTailBlind

set_option maxRecDepth 10000 in
theorem blindGrinding_oracle_answer_of_prefix_bad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots).status = .live)
    (offset : Fin maxBlindTrials)
    (hprior : ∀ prior : Fin maxBlindTrials, prior.val < offset.val →
      ¬ blindGrindingGood shape
        (answers (blindGrindingTapeSite prior))) :
    oracle (encodePowPoint (answers blindStateTapeSite)
        (BitVec.ofNat 64 offset.val)) =
      answers (blindGrindingTapeSite offset) := by
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset blindStateOffset_le_slots
  change before.status = .live at hstatus
  let blindSite : Fin productionSamplingSlots := blindStateTapeSite
  let withState := rawStep shape causalSecret completion witness coins
    blindStateOffset before (answers blindSite)
  have hwithStatus : withState.status = .live :=
    rawStep_blindState_status shape causalSecret completion witness coins before
      (answers blindSite) hstatus
  have hwithActive : withState.stageDone = false :=
    rawStep_blindState_stageDone shape causalSecret completion witness coins
      before (answers blindSite) hstatus
  have hwithState : withState.powState = some (answers blindSite) :=
    rawStep_blindState_powState shape causalSecret completion witness coins before
      (answers blindSite) hstatus
  have hfit : blindGrindingOffset + offset.val ≤ productionSamplingSlots := by
    have hwindow := blindGrinding_window_fits
    omega
  let prefixAnswers : Fin offset.val → OracleBlock :=
    window blindGrindingOffset offset.val hfit answers
  have hprefixBad : ∀ index,
      ¬ blindGrindingGood shape (prefixAnswers index) := by
    intro index
    let prior : Fin maxBlindTrials := ⟨index.val, index.isLt.trans offset.isLt⟩
    have h := hprior prior index.isLt
    simpa [prefixAnswers, prior, blindGrindingTapeSite,
      FixedWindowProbability.window] using h
  have hprefix := iterateFrom_blindGrinding_active_of_all_bad offset.val
    offset.isLt withState (answers blindSite) prefixAnswers hwithStatus
    hwithActive hwithState hprefixBad
  have hrawPrefix :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          (blindGrindingOffset + offset.val) hfit =
        iterateFrom blindGrindingStep blindGrindingOffset offset.val withState
          prefixAnswers := by
    calc
      _ = blindPrefixResult shape causalSecret completion witness coins before
          (answers blindSite) offset.val prefixAnswers := by
            simpa only [before, blindSite, blindStateTapeSite, prefixAnswers]
              using rawControlUntil_blind_prefix_eq shape causalSecret completion
                witness coins prelude answers offset.val offset.isLt.le
      _ = _ := blindPrefixResult_eq_blindGrinding shape causalSecret completion
        witness coins before (answers blindSite) offset.val prefixAnswers
        offset.isLt.le hstatus
  let current := rawControlUntil shape causalSecret completion witness coins
    prelude answers (blindGrindingOffset + offset.val) hfit
  have hcurrentStatus : current.status = .live := by
    rw [show current = iterateFrom blindGrindingStep blindGrindingOffset
      offset.val withState prefixAnswers from hrawPrefix]
    exact hprefix.1
  have hcurrentActive : current.stageDone = false := by
    rw [show current = iterateFrom blindGrindingStep blindGrindingOffset
      offset.val withState prefixAnswers from hrawPrefix]
    exact hprefix.2.1
  have hcurrentState : current.powState = some (answers blindSite) := by
    rw [show current = iterateFrom blindGrindingStep blindGrindingOffset
      offset.val withState prefixAnswers from hrawPrefix]
    exact hprefix.2.2.1
  let site : Fin productionSamplingSlots := blindGrindingTapeSite offset
  have hquery : rawQuery shape causalSecret completion witness coins site current =
      some (encodePowPoint (answers blindSite) (BitVec.ofNat 64 offset.val)) := by
    simpa only [site, current, blindGrindingTapeSite_val] using
      rawQuery_blindGrinding_active shape causalSecret completion witness coins
        offset.val offset.isLt current (answers blindSite) hcurrentStatus
        hcurrentActive hcurrentState
  exact (hagrees site _ hquery).symm

end VeiledFlock.ProductionSamplingTraceTailBlindOracle

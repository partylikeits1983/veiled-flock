import VeiledFlock.ProductionSamplingTraceTailBlindOracle

/-! # Complete executable blind-grinding refinement -/

namespace VeiledFlock.ProductionSamplingTraceTailBlindRun

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingLayoutBounds
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindPrefix
open VeiledFlock.ProductionSamplingScheduleBlindStateProjection
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionSamplingTraceTailBlind
open VeiledFlock.ProductionSamplingTraceTailBlindOracle

set_option maxRecDepth 10000 in
theorem runBlindGrinding_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (transcript : List Byte)
    (htranscript :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots).transcript = transcript)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots).status = .live) :
    ∃ nonce,
      grindPowBounded blindGrindingGood oracle
          (oracle (scalarPoint transcript)) maxBlindTrials = some nonce ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindChallengeOffset blindChallengeOffset_le_slots).transcript =
          afterGrind transcript nonce := by
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset blindStateOffset_le_slots
  change before.transcript = transcript at htranscript
  change before.status = .live at hstatus
  let blindSite : Fin productionSamplingSlots := blindStateTapeSite
  let state : Nonce256 := answers blindSite
  let withState := rawStep shape causalSecret completion witness coins
    blindStateOffset before state
  have hwithStatus : withState.status = .live :=
    rawStep_blindState_status shape causalSecret completion witness coins before
      state hstatus
  have hwithActive : withState.stageDone = false :=
    rawStep_blindState_stageDone shape causalSecret completion witness coins
      before state hstatus
  have hwithState : withState.powState = some state :=
    rawStep_blindState_powState shape causalSecret completion witness coins before
      state hstatus
  have hwithTranscript : withState.transcript = transcript :=
    (rawStep_blindState_transcript shape causalSecret completion witness coins
      before state hstatus).trans htranscript
  let grindAnswers : Fin maxBlindTrials → OracleBlock :=
    window blindGrindingOffset maxBlindTrials blindGrinding_window_fits answers
  have horacle : ∀ offset : Fin maxBlindTrials,
      (∀ prior : Fin maxBlindTrials, prior.val < offset.val →
        ¬ blindGrindingGood (grindAnswers prior)) →
      oracle (encodePowPoint state (BitVec.ofNat 64 offset.val)) =
        grindAnswers offset := by
    intro offset hprior
    have h := blindGrinding_oracle_answer_of_prefix_bad shape causalSecret
      completion witness coins prelude answers oracle hagrees hstatus offset (by
        intro prior hlt
        have hp := hprior prior hlt
        simpa [grindAnswers, blindGrindingTapeSite,
          FixedWindowProbability.window] using hp)
    simpa [state, blindSite, blindStateTapeSite, grindAnswers,
      blindGrindingTapeSite, FixedWindowProbability.window] using h
  have hexists : ∃ offset : Fin maxBlindTrials,
      blindGrindingGood (grindAnswers offset) := by
    rcases exists_blindGrinding_answer_of_not_globalBad shape answers hgood with
      ⟨offset, hoffset⟩
    exact ⟨offset, by simpa [grindAnswers] using hoffset⟩
  have horacleZero : ∀ offset : Fin maxBlindTrials,
      (∀ prior : Fin maxBlindTrials, prior.val < offset.val →
        ¬ blindGrindingGood (grindAnswers prior)) →
      oracle (encodePowPoint state (BitVec.ofNat 64 (0 + offset.val))) =
        grindAnswers offset := by simpa using horacle
  rcases grindFrom_blindLoop_some oracle state 0 maxBlindTrials (by omega)
      withState grindAnswers hwithStatus hwithActive hwithState horacleZero
      hexists with
    ⟨nonce, hgrind, hiter⟩
  have hrawPrefix := rawControlUntil_blind_prefix_eq shape causalSecret completion
    witness coins prelude answers maxBlindTrials (by rfl)
  have hprefixLoop := blindPrefixResult_eq_blindGrinding shape causalSecret
    completion witness coins before state maxBlindTrials grindAnswers (by rfl)
    hstatus
  have hrawLoop :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset blindChallengeOffset_le_slots).transcript =
      (iterateFrom blindGrindingStep blindGrindingOffset maxBlindTrials
        withState grindAnswers).transcript := by
    have hcontrol :
        rawControlUntil shape causalSecret completion witness coins prelude answers
            blindChallengeOffset blindChallengeOffset_le_slots =
          iterateFrom blindGrindingStep blindGrindingOffset maxBlindTrials
            withState grindAnswers := by
      calc
        _ = blindPrefixResult shape causalSecret completion witness coins before
            state maxBlindTrials grindAnswers := by
              simpa only [before, state, blindSite, blindStateTapeSite,
                grindAnswers, blindChallengeOffset_eq_grinding_end] using hrawPrefix
        _ = _ := by simpa only [withState] using hprefixLoop
    exact congrArg Control.transcript hcontrol
  have hstateAnswer : oracle (scalarPoint transcript) = state := by
    let site : Fin productionSamplingSlots := blindStateTapeSite
    have hquery : rawQuery shape causalSecret completion witness coins site before =
        some (scalarPoint before.transcript) := by
      simpa only [site, blindStateTapeSite] using rawQuery_blindState shape
        causalSecret completion witness coins before hstatus
    calc
      oracle (scalarPoint transcript) = oracle (scalarPoint before.transcript) := by
        exact congrArg oracle (congrArg scalarPoint htranscript.symm)
      _ = answers site := (hagrees site _ hquery).symm
      _ = state := by rfl
  have hiter' :
      (iterateFrom blindGrindingStep blindGrindingOffset maxBlindTrials
        withState grindAnswers).transcript =
          afterGrind withState.transcript nonce := by
    simpa only [Nat.add_zero] using hiter
  refine ⟨nonce, ?_, ?_⟩
  · rw [hstateAnswer]
    simpa only [grindPowBounded] using hgrind
  · rw [hrawLoop, hiter', hwithTranscript]

end VeiledFlock.ProductionSamplingTraceTailBlindRun

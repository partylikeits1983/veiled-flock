import VeiledFlock.Production.Sampling.SamplingTracePrefix
import VeiledFlock.Production.Sampling.SamplingScheduleBlindStateProjection
import VeiledFlock.Production.Sampling.SamplingSchedulePowState

/-! # Blind-grinding bridge for the complete production tail -/

namespace VeiledFlock.ProductionSamplingTraceTailBlind

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingLayoutBounds
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindStateProjection
open VeiledFlock.ProductionSamplingSchedulePowState
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingTraceBlind
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionTranscriptFraming

def blindStateTapeSite : Fin productionSamplingSlots :=
  ⟨blindStateOffset, blindStateOffset_lt_slots⟩

def blindGrindingTapeSite (offset : Fin maxBlindTrials) :
    Fin productionSamplingSlots :=
  ⟨blindGrindingOffset + offset.val, by
    have hwindow := blindGrinding_window_fits
    omega⟩

@[simp]
theorem blindGrindingTapeSite_val (offset : Fin maxBlindTrials) :
    (blindGrindingTapeSite offset).val = blindGrindingOffset + offset.val := rfl

set_option maxRecDepth 10000 in
theorem rawQuery_blindState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (control : Control shape)
    (hstatus : control.status = .live) :
    rawQuery shape causalSecret completion witness coins blindStateOffset
        control = some (scalarPoint control.transcript) := by
  simp [rawQuery, hstatus]
  norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
    equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
    blindStateOffset, blindStateWidth, blindGrindingOffset,
    maxProgrammedPoints]

theorem iterateFrom_blindGrinding_eq_of_done
    {shape : BatchShape} (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock) (hdone : control.stageDone = true) :
    iterateFrom blindGrindingStep start rounds control answers = control := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      rw [ih (fun index ↦ answers index.castSucc)]
      simp [blindGrindingStep, hdone]

theorem iterateFrom_succ_first {State Answer : Type*}
    (step : ℕ → State → Answer → State) (start rounds : ℕ)
    (state : State) (answers : Fin (rounds + 1) → Answer) :
    iterateFrom step start (rounds + 1) state answers =
      iterateFrom step (start + 1) rounds
        (step start state (answers 0)) (fun index ↦ answers index.succ) := by
  unfold iterateFrom
  rw [List.ofFn_succ]
  rfl

set_option maxRecDepth 10000 in
theorem grindFrom_blindLoop_some
    {shape : BatchShape} (oracle : List Byte → OracleBlock)
    (state : Nonce256) (trial remaining : ℕ)
    (hsum : trial + remaining = maxBlindTrials)
    (control : Control shape) (answers : Fin remaining → OracleBlock)
    (hstatus : control.status = .live)
    (hactive : control.stageDone = false)
    (hstate : control.powState = some state)
    (horacle : ∀ offset : Fin remaining,
      (∀ prior : Fin remaining, prior.val < offset.val →
        ¬ blindGrindingGood (answers prior)) →
      oracle (encodePowPoint state (BitVec.ofNat 64 (trial + offset.val))) =
        answers offset)
    (hexists : ∃ offset : Fin remaining, blindGrindingGood (answers offset)) :
    ∃ nonce,
      grindFrom blindGrindingGood oracle state trial remaining = some nonce ∧
      (iterateFrom blindGrindingStep (blindGrindingOffset + trial) remaining
        control answers).transcript = afterGrind control.transcript nonce := by
  induction remaining generalizing trial control with
  | zero => simp at hexists
  | succ remaining ih =>
      let head : OracleBlock := answers 0
      let next := blindGrindingStep (blindGrindingOffset + trial) control head
      let tailAnswers : Fin remaining → OracleBlock := fun index ↦ answers index.succ
      have horacleHead :
          oracle (encodePowPoint state (BitVec.ofNat 64 trial)) = head := by
        simpa [head] using horacle 0 (by
          intro prior hlt
          exact (Nat.not_lt_zero prior.val hlt).elim)
      by_cases hgood : blindGrindingGood head
      · let nonce : Word64 := BitVec.ofNat 64 trial
        have hgrind : grindFrom blindGrindingGood oracle state trial
            (remaining + 1) = some nonce := by
          simp only [grindFrom, nonce]
          rw [horacleHead]
          simp [hgood]
        have hnextDone : next.stageDone = true := by
          simp [next, blindGrindingStep, hactive, hgood]
        have hnextTranscript : next.transcript =
            afterGrind control.transcript nonce := by
          simp [next, blindGrindingStep, hactive, hgood, nonce]
        have hsplit := iterateFrom_succ_first blindGrindingStep
          (blindGrindingOffset + trial) remaining control answers
        have hstable := iterateFrom_blindGrinding_eq_of_done
          (blindGrindingOffset + trial + 1) remaining next tailAnswers hnextDone
        refine ⟨nonce, hgrind, ?_⟩
        rw [hsplit]
        change (iterateFrom blindGrindingStep
          (blindGrindingOffset + trial + 1) remaining next tailAnswers).transcript = _
        rw [hstable]
        exact hnextTranscript
      · have hremainingPos : 0 < remaining := by
          by_contra hzero
          have hremainingZero : remaining = 0 := by omega
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetZero : offset.val = 0 := by omega
          have hoffsetEq : offset = 0 := Fin.ext hoffsetZero
          rw [hoffsetEq] at hoffset
          exact hgood (by simpa [head] using hoffset)
        have hnotCap : trial + 1 ≠ maxBlindTrials := by omega
        have hnextStatus : next.status = .live := by
          simp [next, blindGrindingStep, hactive, hgood, hnotCap, hstatus]
        have hnextActive : next.stageDone = false := by
          simp [next, blindGrindingStep, hactive, hgood, hnotCap]
        have hnextState : next.powState = some state := by
          simp [next, blindGrindingStep, hactive, hgood, hnotCap, hstate]
        have hnextTranscript : next.transcript = control.transcript := by
          simp [next, blindGrindingStep, hactive, hgood, hnotCap]
        have htailOracle : ∀ offset : Fin remaining,
            (∀ prior : Fin remaining, prior.val < offset.val →
              ¬ blindGrindingGood (tailAnswers prior)) →
            oracle (encodePowPoint state
              (BitVec.ofNat 64 ((trial + 1) + offset.val))) =
              tailAnswers offset := by
          intro offset hprior
          have hprefix : ∀ prior : Fin (remaining + 1),
              prior.val < offset.succ.val →
                ¬ blindGrindingGood (answers prior) := by
            intro prior hlt
            by_cases hzero : prior.val = 0
            · have hpriorZero : prior = 0 := Fin.ext hzero
              rw [hpriorZero]
              simpa [head] using hgood
            · let tailPrior : Fin remaining := ⟨prior.val - 1, by omega⟩
              have htailPrior : tailPrior.succ = prior := by
                apply Fin.ext
                simp [tailPrior]
                omega
              have htailLt : tailPrior.val < offset.val := by
                have hpriorVal : tailPrior.val + 1 = prior.val := by
                  simp [tailPrior]
                  omega
                have hoffsetVal : offset.succ.val = offset.val + 1 := rfl
                omega
              rw [← htailPrior]
              simpa [tailAnswers] using hprior tailPrior htailLt
          simpa [tailAnswers, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using horacle offset.succ hprefix
        have htailExists : ∃ offset : Fin remaining,
            blindGrindingGood (tailAnswers offset) := by
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetPos : 0 < offset.val := by
            by_contra hzero
            have hoffsetZero : offset.val = 0 := by omega
            have hoffsetEq : offset = 0 := Fin.ext hoffsetZero
            rw [hoffsetEq] at hoffset
            exact hgood (by simpa [head] using hoffset)
          let prior : Fin remaining := ⟨offset.val - 1, by omega⟩
          refine ⟨prior, ?_⟩
          have hindex : prior.succ = offset := by
            apply Fin.ext
            simp [prior]
            omega
          simpa [tailAnswers, hindex] using hoffset
        rcases ih (trial + 1) (by omega) next tailAnswers hnextStatus hnextActive
            hnextState htailOracle htailExists with
          ⟨nonce, hgrind, hiter⟩
        refine ⟨nonce, ?_, ?_⟩
        · simp only [grindFrom]
          rw [horacleHead]
          simp [hgood]
          exact hgrind
        · rw [iterateFrom_succ_first]
          change (iterateFrom blindGrindingStep
            (blindGrindingOffset + (trial + 1)) remaining next
              tailAnswers).transcript = _
          rw [hiter, hnextTranscript]

set_option maxRecDepth 10000 in
theorem iterateFrom_blindGrinding_active_of_all_bad
    {shape : BatchShape} (rounds : ℕ) (hrounds : rounds < maxBlindTrials)
    (control : Control shape) (state : Nonce256)
    (answers : Fin rounds → OracleBlock)
    (hstatus : control.status = .live)
    (hactive : control.stageDone = false)
    (hstate : control.powState = some state)
    (hbad : ∀ index, ¬ blindGrindingGood (answers index)) :
    let result := iterateFrom blindGrindingStep blindGrindingOffset rounds
      control answers
    result.status = .live ∧ result.stageDone = false ∧
      result.powState = some state ∧ result.transcript = control.transcript := by
  induction rounds with
  | zero => simp [iterateFrom, iterateList, hstatus, hactive, hstate]
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      have hprefix := ih (by omega) (fun index ↦ answers index.castSucc)
        (fun index ↦ hbad index.castSucc)
      have hlastBad : ¬ blindGrindingGood (answers (Fin.last rounds)) :=
        hbad (Fin.last rounds)
      have hnotCap :
          rounds + 1 ≠ maxBlindTrials := by omega
      simp [blindGrindingStep, hprefix.2.1, hlastBad, hnotCap,
        hprefix.1, hprefix.2.2.1, hprefix.2.2.2]

/-
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
      ¬ blindGrindingGood
        (answers (blindGrindingTapeSite prior))) :
    oracle (encodePowPoint
        (answers blindStateTapeSite)
        (BitVec.ofNat 64 offset.val)) =
      answers (blindGrindingTapeSite offset) := by
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset blindStateOffset_le_slots
  let blindSite : Fin productionSamplingSlots :=
    blindStateTapeSite
  let withState := rawStep shape causalSecret completion witness coins
    blindStateOffset before (answers blindSite)
  have hwithEq : withState =
      { before with
          powState := some (answers blindSite)
          stageDone := false
          stageBlocks := [] } :=
    rawStep_blindState shape causalSecret completion witness coins before
      (answers blindSite) hstatus
  have hwithStatus : withState.status = .live := by
    rw [hwithEq]
    exact hstatus
  have hwithActive : withState.stageDone = false := by simp [hwithEq]
  have hwithState : withState.powState = some (answers blindSite) := by
    simp [hwithEq]
  have hwithTranscript : withState.transcript = before.transcript := by
    simp [hwithEq]
  have hfit : blindGrindingOffset + offset.val ≤ productionSamplingSlots := by
    have := blindGrinding_window_fits
    omega
  let prefixAnswers : Fin offset.val → OracleBlock :=
    window blindGrindingOffset offset.val hfit answers
  have hprefixBad : ∀ index,
      ¬ blindGrindingGood (prefixAnswers index) := by
    intro index
    let prior : Fin maxBlindTrials := ⟨index.val, index.isLt.trans offset.isLt⟩
    have h := hprior prior index.isLt
    simpa [prefixAnswers, prior, blindGrindingTapeSite,
      FixedWindowProbability.window] using h
  have hprefix := iterateFrom_blindGrinding_active_of_all_bad offset.val
    offset.isLt withState (answers blindSite) prefixAnswers hwithStatus
    hwithActive hwithState hprefixBad
  have hstateRaw := rawControlUntil_succ shape causalSecret completion witness
    coins prelude answers blindSite
  have hstateRaw' :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset blindGrindingOffset_le_slots = withState := by
    simpa only [blindSite, before, withState,
      blindGrindingOffset_eq_state_succ] using hstateRaw
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers blindGrindingOffset offset.val hfit
  have hrawPrefix :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          (blindGrindingOffset + offset.val) hfit =
        iterateFrom blindGrindingStep blindGrindingOffset offset.val withState
          prefixAnswers := by
    calc
      _ = iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset offset.val
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindGrindingOffset blindGrindingOffset_le_slots)
          prefixAnswers := by simpa only [prefixAnswers] using hadd
      _ = iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset offset.val withState prefixAnswers := by
            rw [hstateRaw']
      _ = _ := iterateFrom_eq_blindGrinding shape causalSecret completion witness
        coins offset.val withState prefixAnswers offset.isLt.le hwithStatus
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
    simpa only [site, current] using rawQuery_blindGrinding_active shape
      causalSecret completion witness coins offset.val offset.isLt current
      (answers blindSite) hcurrentStatus hcurrentActive hcurrentState
  exact (hagrees site _ hquery).symm
-/

/-
set_option maxHeartbeats 10000 in
set_option maxRecDepth 10000 in
theorem blindGrinding_start_of_agreement
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (transcript : List Byte)
    (htranscript :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots).transcript = transcript)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots).status = .live) :
    let blindSite : Fin productionSamplingSlots :=
      ⟨blindStateOffset, blindStateOffset_lt_slots⟩
    let blindWithState := rawControlUntil shape causalSecret completion witness
      coins prelude answers blindGrindingOffset blindGrindingOffset_le_slots
    oracle (scalarPoint transcript) = answers blindSite ∧
      blindWithState.status = .live ∧
      blindWithState.stageDone = false ∧
      blindWithState.powState = some (answers blindSite) ∧
      blindWithState.transcript = transcript := by
  let blindStart := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset blindStateOffset_le_slots
  let blindSite : Fin productionSamplingSlots :=
    ⟨blindStateOffset, blindStateOffset_lt_slots⟩
  have hblindQuery : rawQuery shape causalSecret completion witness coins
      blindSite blindStart = some (scalarPoint blindStart.transcript) := by
    simpa only [blindSite, blindStart] using rawQuery_blindState shape
      causalSecret completion witness coins blindStart hstatus
  have hblindStateAnswer : oracle (scalarPoint transcript) = answers blindSite := by
    calc
      oracle (scalarPoint transcript) =
          oracle (scalarPoint blindStart.transcript) := by
            congr 2
            exact htranscript.symm
      _ = answers blindSite := (hagrees blindSite _ hblindQuery).symm
  have hblindSucc := rawControlUntil_succ shape causalSecret completion witness
    coins prelude answers blindSite
  have hblindStep := rawStep_blindState shape causalSecret completion witness
    coins blindStart (answers blindSite) hstatus
  let blindWithState := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindGrindingOffset blindGrindingOffset_le_slots
  refine ⟨hblindStateAnswer, ?_, ?_, ?_, ?_⟩
  · have hsuccStatus := congrArg Control.status hblindSucc
    have hstepStatus :
        (rawStep shape causalSecret completion witness coins blindStateOffset
          blindStart (answers blindSite)).status = .live := by
      rw [hblindStep]
      exact hstatus
    simpa only [blindWithState, blindSite, blindGrindingOffset_eq_state_succ]
      using hsuccStatus.trans hstepStatus
  · have hsuccDone := congrArg Control.stageDone hblindSucc
    have hstepDone :
        (rawStep shape causalSecret completion witness coins blindStateOffset
          blindStart (answers blindSite)).stageDone = false := by
      rw [hblindStep]
    simpa only [blindWithState, blindSite, blindGrindingOffset_eq_state_succ]
      using hsuccDone.trans hstepDone
  · exact rawControlUntil_blind_powState shape causalSecret completion witness
      coins prelude answers blindGrindingOffset (by omega) (by omega) hstatus
  · have hsuccTranscript := congrArg Control.transcript hblindSucc
    have hstepTranscript :
        (rawStep shape causalSecret completion witness coins blindStateOffset
          blindStart (answers blindSite)).transcript = blindStart.transcript :=
      rawStep_blindState_transcript shape causalSecret completion witness coins
        blindStart (answers blindSite) hstatus
    simpa only [blindWithState, blindSite, blindStart,
      blindGrindingOffset_eq_state_succ] using
        hsuccTranscript.trans (hstepTranscript.trans htranscript)
-/

/-
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
        answers blindStateOffset (by decide)).transcript = transcript)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset (by decide)).status = .live) :
    ∃ nonce,
      grindPowBounded blindGrindingGood oracle
          (oracle (scalarPoint transcript)) maxBlindTrials = some nonce ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindChallengeOffset (by decide)).transcript =
          afterGrind transcript nonce := by
  let blindStart := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset (by decide)
  let blindSite : Fin productionSamplingSlots := ⟨blindStateOffset, by decide⟩
  have hblindQuery : rawQuery shape causalSecret completion witness coins
      blindSite blindStart = some (scalarPoint blindStart.transcript) := by
    simpa only [blindSite, blindStart] using rawQuery_blindState shape
      causalSecret completion witness coins blindStart hstatus
  have hblindStateAnswer : oracle (scalarPoint transcript) = answers blindSite := by
    calc
      oracle (scalarPoint transcript) =
          oracle (scalarPoint blindStart.transcript) := by
            congr 2
            exact htranscript.symm
      _ = answers blindSite := (hagrees blindSite _ hblindQuery).symm
  have hblindSucc := rawControlUntil_succ shape causalSecret completion witness
    coins prelude answers blindSite
  have hblindStep := rawStep_blindState shape causalSecret completion witness
    coins blindStart (answers blindSite) hstatus
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
    exact hstatus
  have hblindGrindDone : blindWithState.stageDone = false := by
    simp [hblindWithState]
  have hblindGrindState : blindWithState.powState = some (answers blindSite) := by
    simp [hblindWithState]
  have hblindWithStateTranscript : blindWithState.transcript = transcript := by
    rw [hblindWithState]
    exact htranscript
  have hblindDirect : ∃ offset : Fin maxBlindTrials,
      blindGrindingGood
        (answers ⟨blindGrindingOffset + offset.val, by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega⟩) := by
    rcases exists_blindGrinding_answer_of_not_globalBad shape answers hgood with
      ⟨trial, htrial⟩
    refine ⟨trial, ?_⟩
    simpa [FixedWindowProbability.window] using htrial
  rcases grindFrom_blind_stage_some shape causalSecret completion witness coins
      prelude answers oracle hagrees (answers blindSite) 0 maxBlindTrials
      (by omega) hblindGrindStatus hblindGrindDone hblindGrindState hblindDirect
    with ⟨nonce, hnonce, hafter⟩
  refine ⟨nonce, ?_, ?_⟩
  · rw [hblindStateAnswer]
    simpa only [grindPowBounded] using hnonce
  · change (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindChallengeOffset (by decide)).transcript =
        afterGrind blindWithState.transcript nonce at hafter
    rw [hblindWithStateTranscript] at hafter
    exact hafter
-/

end VeiledFlock.ProductionSamplingTraceTailBlind

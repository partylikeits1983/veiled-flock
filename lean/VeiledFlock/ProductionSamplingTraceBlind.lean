import VeiledFlock.ProductionSamplingTracePositions

/-! # First-success blind-grinding refinement -/

namespace VeiledFlock.ProductionSamplingTraceBlind

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionTranscriptFraming

set_option maxRecDepth 10000 in
theorem rawQuery_blindGrinding_active
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (trial : ℕ) (htrial : trial < maxBlindTrials)
    (control : Control shape) (state : Nonce256)
    (hstatus : control.status = .live)
    (hactive : control.stageDone = false)
    (hstate : control.powState = some state) :
    rawQuery shape causalSecret completion witness coins
        (blindGrindingOffset + trial) control =
      some (encodePowPoint state (BitVec.ofNat 64 trial)) := by
  simp [rawQuery, hstatus]
  norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
    equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
    blindStateOffset, blindStateWidth, blindGrindingOffset,
    blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
    rejectionTrials, maxBlindTrials, maxProgrammedPoints] at htrial ⊢
  simp (disch := omega) only [if_pos, if_neg, hactive, hstate, Option.map_some]
  simp only [Bool.false_eq_true, if_false]

set_option maxRecDepth 10000 in
theorem rawControlUntil_blind_stable_of_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (trial remaining : ℕ)
    (hsum : trial + remaining = maxBlindTrials)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (blindGrindingOffset + trial) (by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega)).status = .live)
    (hdone :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (blindGrindingOffset + trial) (by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega)).stageDone = true) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset (by decide) =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        (blindGrindingOffset + trial) (by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega) := by
  induction remaining generalizing trial with
  | zero =>
      have htrial : trial = maxBlindTrials := by omega
      simpa [blindChallengeOffset, blindGrindingWidth, htrial]
  | succ remaining ih =>
      let site : Fin productionSamplingSlots :=
        ⟨blindGrindingOffset + trial, by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (blindGrindingOffset + trial) site.isLt.le
      have hstatus' : current.status = .live := hstatus
      have hdone' : current.stageDone = true := hdone
      have htrial : trial < maxBlindTrials := by omega
      have hsucc := rawControlUntil_succ shape causalSecret completion witness
        coins prelude answers site
      have hstep := rawStep_blindGrinding shape causalSecret completion witness
        coins trial htrial current (answers site) hstatus'
      rw [hstep] at hsucc
      have hstepEq : blindGrindingStep (blindGrindingOffset + trial) current
          (answers site) = current := by
        simp [blindGrindingStep, hdone']
      rw [hstepEq] at hsucc
      let next := rawControlUntil shape causalSecret completion witness coins
        prelude answers (blindGrindingOffset + (trial + 1)) (by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega)
      have hnext : next = current := by
        simpa only [next, current, site, Nat.add_assoc] using hsucc
      have hnextStatus : next.status = .live := by rw [hnext]; exact hstatus
      have hnextDone : next.stageDone = true := by rw [hnext]; exact hdone
      rw [ih (trial + 1) (by omega) hnextStatus hnextDone]
      exact hnext

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- The executable first-success grind and the literal operational control
reach the same nonce-updated transcript. -/
theorem grindFrom_blind_stage_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (state : Nonce256) (trial remaining : ℕ)
    (hcap : trial + remaining ≤ maxBlindTrials)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (blindGrindingOffset + trial) (by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega)).status = .live)
    (hactive :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (blindGrindingOffset + trial) (by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega)).stageDone = false)
    (hstate :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (blindGrindingOffset + trial) (by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega)).powState = some state)
    (hexists : ∃ offset : Fin remaining,
      blindGrindingGood
        (answers ⟨blindGrindingOffset + trial + offset.val, by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega⟩)) :
    ∃ nonce,
      grindFrom blindGrindingGood oracle state trial remaining = some nonce ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindChallengeOffset (by decide)).transcript =
        afterGrind
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (blindGrindingOffset + trial) (by
              have : blindGrindingOffset + maxBlindTrials ≤
                  productionSamplingSlots := by decide
              omega)).transcript nonce := by
  induction remaining generalizing trial with
  | zero => simp at hexists
  | succ remaining ih =>
      let site : Fin productionSamplingSlots :=
        ⟨blindGrindingOffset + trial, by
          have : blindGrindingOffset + maxBlindTrials ≤
              productionSamplingSlots := by decide
          omega⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (blindGrindingOffset + trial) site.isLt.le
      have hstatus' : current.status = .live := hstatus
      have hactive' : current.stageDone = false := hactive
      have hstate' : current.powState = some state := hstate
      have htrial : trial < maxBlindTrials := by
        rcases hexists with ⟨offset, _⟩
        omega
      have hquery : rawQuery shape causalSecret completion witness coins site
          current = some (encodePowPoint state (BitVec.ofNat 64 trial)) := by
        simpa only [site, current] using rawQuery_blindGrinding_active shape
          causalSecret completion witness coins trial htrial current state
          hstatus' hactive' hstate'
      have horacle : oracle (encodePowPoint state (BitVec.ofNat 64 trial)) =
          answers site := (hagrees site _ hquery).symm
      by_cases hgood : blindGrindingGood (answers site)
      · let nonce : Word64 := BitVec.ofNat 64 trial
        have hgrind : grindFrom blindGrindingGood oracle state trial
            (remaining + 1) = some nonce := by
          simp only [grindFrom, nonce]
          rw [horacle]
          simp [hgood]
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers site
        have hstep := rawStep_blindGrinding shape causalSecret completion witness
          coins trial htrial current (answers site) hstatus'
        rw [hstep] at hsucc
        let next := rawControlUntil shape causalSecret completion witness coins
          prelude answers (blindGrindingOffset + (trial + 1)) (by
            have : blindGrindingOffset + maxBlindTrials ≤
                productionSamplingSlots := by decide
            omega)
        have hsucc' : next = blindGrindingStep
            (blindGrindingOffset + trial) current (answers site) := by
          simpa only [next, site, Nat.add_assoc] using hsucc
        have hnextStatus : next.status = .live := by
          rw [hsucc']
          exact (blindGrindingStep_live_done_of_good _ _ _ hstatus' hgood).1
        have hnextDone : next.stageDone = true := by
          rw [hsucc']
          exact (blindGrindingStep_live_done_of_good _ _ _ hstatus' hgood).2
        have hnextTranscript : next.transcript =
            afterGrind current.transcript nonce := by
          rw [hsucc']
          simp [blindGrindingStep, hactive', hgood, nonce]
        have hstable := rawControlUntil_blind_stable_of_done shape causalSecret
          completion witness coins prelude answers (trial + 1)
          (maxBlindTrials - (trial + 1)) (by omega) hnextStatus hnextDone
        refine ⟨nonce, hgrind, ?_⟩
        rw [congrArg Control.transcript hstable]
        exact hnextTranscript
      · have hremainingPos : 0 < remaining := by
          by_contra hzero
          have hremainingZero : remaining = 0 := by omega
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetZero : offset.val = 0 := by omega
          exact hgood (by simpa [site, hoffsetZero] using hoffset)
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers site
        have hstep := rawStep_blindGrinding shape causalSecret completion witness
          coins trial htrial current (answers site) hstatus'
        rw [hstep] at hsucc
        let next := rawControlUntil shape causalSecret completion witness coins
          prelude answers (blindGrindingOffset + (trial + 1)) (by
            have : blindGrindingOffset + maxBlindTrials ≤
                productionSamplingSlots := by decide
            omega)
        have hsucc' : next = blindGrindingStep
            (blindGrindingOffset + trial) current (answers site) := by
          simpa only [next, site, Nat.add_assoc] using hsucc
        have hnotCap : trial + 1 ≠ maxBlindTrials := by
          rcases hexists with ⟨offset, hoffset⟩
          by_contra heq
          have hremainingZero : remaining = 0 := by omega
          have hoffsetZero : offset.val = 0 := by omega
          exact hgood (by simpa [site, hoffsetZero] using hoffset)
        have hnextStatus : next.status = .live := by
          rw [hsucc']
          simp [blindGrindingStep, hactive', hgood, hnotCap, hstatus']
        have hnextActive : next.stageDone = false := by
          rw [hsucc']
          simp [blindGrindingStep, hactive', hgood, hnotCap]
        have hnextState : next.powState = some state := by
          rw [hsucc']
          simp [blindGrindingStep, hactive', hgood, hnotCap, hstate']
        have hnextTranscript : next.transcript = current.transcript := by
          rw [hsucc']
          simp [blindGrindingStep, hactive', hgood, hnotCap]
        have hnextExists : ∃ offset : Fin remaining,
            blindGrindingGood
              (answers ⟨blindGrindingOffset + (trial + 1) + offset.val, by
                have : blindGrindingOffset + maxBlindTrials ≤
                    productionSamplingSlots := by decide
                omega⟩) := by
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetPos : 0 < offset.val := by
            by_contra hzero
            have hoffsetZero : offset.val = 0 := by omega
            exact hgood (by simpa [site, hoffsetZero] using hoffset)
          let prior : Fin remaining := ⟨offset.val - 1, by omega⟩
          refine ⟨prior, ?_⟩
          have hindex :
              (⟨blindGrindingOffset + (trial + 1) + prior.val, by
                have : blindGrindingOffset + maxBlindTrials ≤
                    productionSamplingSlots := by decide
                omega⟩ : Fin productionSamplingSlots) =
              ⟨blindGrindingOffset + trial + offset.val, by
                have : blindGrindingOffset + maxBlindTrials ≤
                    productionSamplingSlots := by decide
                omega⟩ := by
            apply Fin.ext
            dsimp only [prior]
            omega
          rw [hindex]
          exact hoffset
        rcases ih (trial + 1) (by omega) hnextStatus hnextActive hnextState
            hnextExists with ⟨nonce, hgrind, htranscript⟩
        refine ⟨nonce, ?_, ?_⟩
        · simp only [grindFrom]
          rw [horacle]
          simp [hgood]
          exact hgrind
        · rw [← hnextTranscript]
          exact htranscript

end VeiledFlock.ProductionSamplingTraceBlind

import VeiledFlock.Production.Sampling.SamplingTraceScalar

/-! # Distinct-position refinement for the operational production trace -/

namespace VeiledFlock.ProductionSamplingTracePositions

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionUniquePositionSampler
open VeiledFlock.UniquePositionSampling

noncomputable def valSet {domain : ℕ} (selected : Finset (Fin domain)) :
    Finset ℕ :=
  selected.map ⟨Fin.val, Fin.val_injective⟩

@[simp]
theorem valSet_card {domain : ℕ} (selected : Finset (Fin domain)) :
    (valSet selected).card = selected.card := by
  simp [valSet]

@[simp]
theorem valSet_insert {domain : ℕ} (value : Fin domain)
    (selected : Finset (Fin domain)) :
    valSet (insert value selected) = insert value.val (valSet selected) := by
  classical
  simp [valSet]

theorem acceptPositions_active_positions {shape : BatchShape}
    (project : GhashField → ℕ) (target start trial : ℕ)
    (control : Control shape) (answer : OracleBlock)
    (hactive : trial = 0 ∨ control.stageDone = false) :
    (acceptPositions project target start (start + trial) control
      answer).positions =
      insert (project (scalarFromBlock answer))
        (if trial = 0 then ∅ else control.positions) := by
  classical
  by_cases hzero : trial = 0
  · subst trial
    simp [acceptPositions]
    split <;> (try split) <;> rfl
  · have hdone : control.stageDone = false := hactive.resolve_left hzero
    simp [acceptPositions, hzero, hdone]
    split <;> (try split) <;> rfl

theorem acceptPositions_active_transcript {shape : BatchShape}
    (project : GhashField → ℕ) (target start trial : ℕ)
    (control : Control shape) (answer : OracleBlock)
    (hactive : trial = 0 ∨ control.stageDone = false) :
    (acceptPositions project target start (start + trial) control
      answer).transcript = afterScalar control.transcript answer := by
  classical
  by_cases hzero : trial = 0
  · subst trial
    simp [acceptPositions]
    split <;> (try split) <;> rfl
  · have hdone : control.stageDone = false := hactive.resolve_left hzero
    simp [acceptPositions, hzero, hdone]
    split <;> (try split) <;> rfl

theorem acceptPositions_active_done_false {shape : BatchShape}
    (project : GhashField → ℕ) (target start trial : ℕ)
    (control : Control shape) (answer : OracleBlock)
    (hactive : trial = 0 ∨ control.stageDone = false)
    (hnotDone : ¬ target ≤
      (insert (project (scalarFromBlock answer))
        (if trial = 0 then ∅ else control.positions)).card) :
    (acceptPositions project target start (start + trial) control
      answer).stageDone = false := by
  classical
  by_cases hzero : trial = 0
  · subst trial
    have hnotDone' : ¬ target ≤ 1 := by simpa using hnotDone
    simp [acceptPositions, hnotDone']
    split <;> rfl
  · have hdone : control.stageDone = false := hactive.resolve_left hzero
    have hnotDone' : ¬ target ≤
        (insert (project (scalarFromBlock answer)) control.positions).card := by
      simpa [hzero] using hnotDone
    simp [acceptPositions, hzero, hdone, hnotDone']
    split <;> rfl

theorem acceptPositions_active_status_live {shape : BatchShape}
    (project : GhashField → ℕ) (target start trial : ℕ)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hactive : trial = 0 ∨ control.stageDone = false)
    (hnotDone : ¬ target ≤
      (insert (project (scalarFromBlock answer))
        (if trial = 0 then ∅ else control.positions)).card)
    (hbeforeCap : trial + 1 ≠ samplingTrials) :
    (acceptPositions project target start (start + trial) control
      answer).status = .live := by
  classical
  by_cases hzero : trial = 0
  · subst trial
    have hone : 1 ≠ samplingTrials := by decide
    have hnotDone' : ¬ target ≤ 1 := by simpa using hnotDone
    simp [acceptPositions, hnotDone', hstatus, hone]
  · have hdone : control.stageDone = false := hactive.resolve_left hzero
    have hnotDone' : ¬ target ≤
        (insert (project (scalarFromBlock answer)) control.positions).card := by
      simpa [hzero] using hnotDone
    simp [acceptPositions, hzero, hdone, hnotDone', hstatus, hbeforeCap]

set_option maxRecDepth 10000 in
theorem rawQuery_positionStage_active
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (stage : PositionStage) (trial : ℕ) (htrial : trial < samplingTrials)
    (control : Control shape) (hstatus : control.status = .live)
    (hactive : trial = 0 ∨ control.stageDone = false) :
    rawQuery shape causalSecret completion witness coins
        (positionStageStart stage + trial) control =
      some (scalarPoint control.transcript) := by
  cases stage with
  | outer =>
      simp only [positionStageStart]
      simp [rawQuery, hstatus]
      norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
        equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
        blindStateOffset, blindStateWidth, blindGrindingOffset,
        blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
        outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
        rejectionTrials, samplingTrials, maxBlindTrials,
        maxProgrammedPoints] at htrial ⊢
      rcases hactive with hzero | hdone
      · subst trial
        simp
      · by_cases hzero : trial = 0
        · subst trial
          simp
        · simp (disch := omega) only [if_pos, if_neg, hzero, false_or,
            hdone]
          simp only [if_true]

  | linear =>
      simp only [positionStageStart]
      simp [rawQuery, hstatus]
      norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
        equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
        blindStateOffset, blindStateWidth, blindGrindingOffset,
        blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
        outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
        linearRhoOffset, rejectionTrials, samplingTrials, maxBlindTrials,
        maxProgrammedPoints] at htrial ⊢
      rcases hactive with hzero | hdone
      · subst trial
        simp
      · by_cases hzero : trial = 0
        · subst trial
          simp
        · simp (disch := omega) only [if_pos, if_neg, hzero, false_or,
            hdone]
          simp only [if_true]

  | hadamard =>
      simp only [positionStageStart]
      simp [rawQuery, hstatus]
      norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
        equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
        blindStateOffset, blindStateWidth, blindGrindingOffset,
        blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
        outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
        linearRhoOffset, hadamardPositionsOffset, hadamardRhoOffset,
        rejectionTrials, samplingTrials, maxBlindTrials,
        maxProgrammedPoints] at htrial ⊢
      rcases hactive with hzero | hdone
      · subst trial
        simp
      · by_cases hzero : trial = 0
        · subst trial
          simp
        · simp (disch := omega) only [if_pos, if_neg, hzero, false_or,
            hdone]
          simp only [if_true]

set_option maxRecDepth 10000 in
theorem rawControlUntil_positions_stable_of_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (stage : PositionStage)
    (trial remaining : ℕ) (hsum : trial + remaining = samplingTrials)
    (hpositive : 0 < trial)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + trial) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).status = .live)
    (hdone :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + trial) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).stageDone = true) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (positionStageStart stage + samplingTrials) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          exact hstart) =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        (positionStageStart stage + trial) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega) := by
  induction remaining generalizing trial with
  | zero =>
      have htrial : trial = samplingTrials := by omega
      subst trial
      rfl
  | succ remaining ih =>
      have htrial : trial < samplingTrials := by omega
      let site : Fin productionSamplingSlots :=
        ⟨positionStageStart stage + trial, by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (positionStageStart stage + trial) site.isLt.le
      have hstatus' : current.status = .live := hstatus
      have hdone' : current.stageDone = true := hdone
      have hsucc := rawControlUntil_succ shape causalSecret completion witness
        coins prelude answers site
      have hstep := rawStep_positionStage shape causalSecret completion witness
        coins stage trial htrial current (answers site) hstatus'
      rw [hstep] at hsucc
      have haccept : acceptPositions (positionStageProject shape stage)
          (positionStageTarget shape stage) (positionStageStart stage)
          (positionStageStart stage + trial) current (answers site) = current :=
        acceptPositions_eq_of_done _ _ _ _ current (answers site) hdone'
          (by omega)
      rw [haccept] at hsucc
      let next := rawControlUntil shape causalSecret completion witness coins
        prelude answers (positionStageStart stage + (trial + 1)) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)
      have hnext : next = current := by
        simpa only [next, current, site, Nat.add_assoc] using hsucc
      have hnextStatus : next.status = .live := by rw [hnext]; exact hstatus'
      have hnextDone : next.stageDone = true := by rw [hnext]; exact hdone'
      rw [ih (trial + 1) (by omega) (by omega) hnextStatus hnextDone]
      exact hnext

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- Exact success of a production unique-position loop.  `selected` is the
sampler's finite-domain set while `Control.positions` is its injective natural
projection; `valSet` records their equality without losing cardinality. -/
theorem collectUnique_stage_some
    {W : Type*} {domain : ℕ} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (stage : PositionStage) (position : GhashField → Fin domain)
    (hproject : ∀ value,
      positionStageProject shape stage value = (position value).val)
    (selected : Finset (Fin domain)) (trial remaining : ℕ)
    (hsum : trial + remaining = samplingTrials)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + trial) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).status = .live)
    (hactive : trial = 0 ∨
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + trial) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).stageDone = false)
    (halign : trial = 0 ∨
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + trial) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).positions = valSet selected)
    (hstartEmpty : trial = 0 → selected = ∅)
    (hcardLt : selected.card < positionStageTarget shape stage)
    (hfinalDone :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + samplingTrials) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          exact hstart)).stageDone = true) :
    ∃ result,
      collectUnique position (positionStageTarget shape stage) oracle remaining
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (positionStageStart stage + trial) (by
              have hstart : positionStageStart stage + samplingTrials ≤
                  productionSamplingSlots := by cases stage <;> decide
              omega)).transcript selected = some result ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (positionStageStart stage + samplingTrials) (by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          exact hstart)).transcript = result.2 := by
  induction remaining generalizing trial selected with
  | zero =>
      have htrial : trial = samplingTrials := by omega
      have htrialPos : trial ≠ 0 := by
        rw [htrial]
        decide
      have hcurrentDone :
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (positionStageStart stage + trial) (by
              have hstart : positionStageStart stage + samplingTrials ≤
                  productionSamplingSlots := by cases stage <;> decide
              omega)).stageDone = true := by
        simpa [htrial] using hfinalDone
      have hfalse := hactive.resolve_left htrialPos
      rw [hcurrentDone] at hfalse
      simp at hfalse
  | succ remaining ih =>
      let site : Fin productionSamplingSlots :=
        ⟨positionStageStart stage + trial, by
          have hstart : positionStageStart stage + samplingTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (positionStageStart stage + trial) site.isLt.le
      have hstatus' : current.status = .live := hstatus
      by_cases hselected : selected.card = positionStageTarget shape stage
      · omega
      · have htrial : trial < samplingTrials := by omega
        change ∃ result,
          collectUnique position (positionStageTarget shape stage) oracle
              (remaining + 1) current.transcript selected = some result ∧
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers (positionStageStart stage + samplingTrials) (by
                have hstart : positionStageStart stage + samplingTrials ≤
                    productionSamplingSlots := by cases stage <;> decide
                exact hstart)).transcript = result.2
        have hquery : rawQuery shape causalSecret completion witness coins site
            current = some (scalarPoint current.transcript) := by
          simpa only [site, current] using rawQuery_positionStage_active shape
            causalSecret completion witness coins stage trial htrial current
            hstatus hactive
        have horacle : oracle (scalarPoint current.transcript) = answers site :=
          (hagrees site _ hquery).symm
        have hsample : sampleScalar oracle current.transcript =
            (scalarFromBlock (answers site),
              afterScalar current.transcript (answers site)) := by
          simp [sampleScalar, scalarFromBlock, horacle]
        let value := position (scalarFromBlock (answers site))
        let nextSelected := insert value selected
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers site
        have hstep := rawStep_positionStage shape causalSecret completion witness
          coins stage trial htrial current (answers site) hstatus
        rw [hstep] at hsucc
        let next := rawControlUntil shape causalSecret completion witness coins
          prelude answers (positionStageStart stage + (trial + 1)) (by
            have hstart : positionStageStart stage + samplingTrials ≤
                productionSamplingSlots := by cases stage <;> decide
            omega)
        have hsucc' : next = acceptPositions (positionStageProject shape stage)
            (positionStageTarget shape stage) (positionStageStart stage)
            (positionStageStart stage + trial) current (answers site) := by
          simpa only [next, site, Nat.add_assoc] using hsucc
        have hcurrentPositions :
            (if trial = 0 then ∅ else current.positions) = valSet selected := by
          by_cases hzero : trial = 0
          · subst trial
            simp [hstartEmpty rfl, valSet]
          · simpa [hzero] using halign.resolve_left hzero
        have hbaseDone :
            (if trial = 0 then false else current.stageDone) = false := by
          by_cases hzero : trial = 0
          · simp [hzero]
          · simpa [hzero] using hactive.resolve_left hzero
        have hnextNat :
            insert (positionStageProject shape stage
              (scalarFromBlock (answers site)))
                (if trial = 0 then ∅ else current.positions) =
              valSet nextSelected := by
          rw [hproject, hcurrentPositions]
          simp [nextSelected, value]
        have hnextPositions : next.positions = valSet nextSelected := by
          rw [hsucc']
          rw [acceptPositions_active_positions _ _ _ trial current
            (answers site) hactive]
          exact hnextNat
        have hnextTranscript : next.transcript =
            afterScalar current.transcript (answers site) := by
          rw [hsucc']
          exact acceptPositions_active_transcript _ _ _ trial current
            (answers site) hactive
        have hnextLe : nextSelected.card ≤
            positionStageTarget shape stage := by
          dsimp only [nextSelected]
          calc
            (insert value selected).card ≤ selected.card + 1 :=
              Finset.card_insert_le value selected
            _ ≤ positionStageTarget shape stage := by omega
        by_cases hnextSelected :
            nextSelected.card = positionStageTarget shape stage
        · have htargetNat : positionStageTarget shape stage ≤
              (insert (positionStageProject shape stage
                (scalarFromBlock (answers site)))
                  (if trial = 0 then ∅ else current.positions)).card := by
            rw [hnextNat, valSet_card, hnextSelected]
          have hnextLiveDone : next.status = .live ∧
              next.stageDone = true := by
            rw [hsucc']
            classical
            unfold acceptPositions
            have hoffset : positionStageStart stage + trial -
                positionStageStart stage = trial := by omega
            rw [hoffset]
            by_cases hzero : trial = 0
            · have htargetNat' := htargetNat
              simp [hzero] at htargetNat'
              simp [hzero, htargetNat', hstatus']
            · have hdone : current.stageDone = false :=
                hactive.resolve_left hzero
              have htargetNat' := htargetNat
              simp [hzero] at htargetNat'
              simp [hzero, hdone, htargetNat', hstatus']
          have hstable := rawControlUntil_positions_stable_of_done shape
            causalSecret completion witness coins prelude answers stage
            (trial + 1) remaining (by omega) (by omega) hnextLiveDone.1
            hnextLiveDone.2
          refine ⟨(nextSelected,
              afterScalar current.transcript (answers site)), ?_, ?_⟩
          · simp only [collectUnique, hselected, if_false]
            rw [hsample]
            change collectUnique position (positionStageTarget shape stage) oracle
              remaining (afterScalar current.transcript (answers site))
                nextSelected = _
            cases remaining <;> simp [collectUnique, hnextSelected]
          · rw [congrArg Control.transcript hstable, hnextTranscript]
        · have htarget : ¬ positionStageTarget shape stage ≤
              nextSelected.card := by omega
          have hnextDone : next.stageDone = false := by
            rw [hsucc']
            apply acceptPositions_active_done_false _ _ _ trial current
              (answers site) hactive
            rw [hnextNat, valSet_card]
            exact htarget
          have hremainingPos : 0 < remaining := by
            by_contra hzero
            have hremainingZero : remaining = 0 := by omega
            have hdone : next.stageDone = true := by
              have hroundEq : trial + 1 = samplingTrials := by omega
              simpa only [next, hroundEq] using hfinalDone
            rw [hnextDone] at hdone
            simp at hdone
          have hnextStatus : next.status = .live := by
            rw [hsucc']
            have hbeforeCap : trial + 1 ≠ samplingTrials := by omega
            apply acceptPositions_active_status_live _ _ _ trial current
              (answers site) hstatus' hactive
            · rw [hnextNat, valSet_card]
              exact htarget
            · exact hbeforeCap
          have hnextLt : nextSelected.card <
              positionStageTarget shape stage := by omega
          rcases ih nextSelected (trial + 1) (by omega) hnextStatus
              (Or.inr hnextDone) (Or.inr hnextPositions) (by omega) hnextLt
              hfinalDone with
            ⟨result, hresult, hfinal⟩
          refine ⟨result, ?_, hfinal⟩
          simp only [collectUnique, hselected, if_false]
          rw [hsample]
          rw [← hnextTranscript]
          exact hresult

end VeiledFlock.ProductionSamplingTracePositions

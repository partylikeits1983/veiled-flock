import VeiledFlock.Production.Sampling.SamplingTraceZerocheck

/-! # Scalar-rejection refinement for the operational production trace -/

namespace VeiledFlock.ProductionSamplingTraceScalar

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

theorem rawControlUntil_round_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) {left right : ℕ}
    (hleft : left ≤ productionSamplingSlots)
    (hright : right ≤ productionSamplingSlots)
    (hround : left = right) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        left hleft =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        right hright := by
  subst right
  rfl

/-- The predicate used by the executable sampler at each scalar stage. -/
def scalarStageGood : ScalarStage → GhashField → Prop
  | .multiplicationAlpha => notZeroOrOne
  | _ => nonzero

noncomputable instance (stage : ScalarStage) :
    DecidablePred (scalarStageGood stage) := by
  cases stage <;> unfold scalarStageGood <;> infer_instance

@[simp]
theorem scalarStageGood_iff_not_mem (stage : ScalarStage)
    (value : GhashField) :
    scalarStageGood stage value ↔ value ∉ scalarStageFailure stage := by
  cases stage <;>
    simp [scalarStageGood, scalarStageFailure, nonzero, notZeroOrOne,
      zeroFailure, zeroOrOneFailure]

theorem nonzeroStageQuery_active {shape : BatchShape}
    (start trial : ℕ) (control : Control shape)
    (htrial : trial < rejectionTrials)
    (hactive : trial = 0 ∨ control.stageDone = false) :
    nonzeroStageQuery start (start + trial) control =
      some (scalarPoint control.transcript) := by
  unfold nonzeroStageQuery
  have hrange : start ≤ start + trial ∧
      start + trial < start + rejectionTrials := by omega
  rw [dif_pos hrange]
  have hoffset : start + trial - start = trial := by omega
  rw [hoffset]
  rcases hactive with hzero | hdone
  · simp [hzero]
  · by_cases hzero : trial = 0
    · simp [hzero]
    · simp [hzero, hdone]

set_option maxRecDepth 10000 in
theorem rawQuery_scalarStage_active
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (stage : ScalarStage) (trial : ℕ) (htrial : trial < rejectionTrials)
    (control : Control shape) (hstatus : control.status = .live)
    (hactive : trial = 0 ∨ control.stageDone = false) :
    rawQuery shape causalSecret completion witness coins
        (scalarStageStart stage + trial) control =
      some (scalarPoint control.transcript) := by
  cases stage with
  | blindChallenge =>
      simp only [scalarStageStart]
      rw [show rawQuery shape causalSecret completion witness coins
          (blindChallengeOffset + trial) control =
          nonzeroStageQuery blindChallengeOffset
            (blindChallengeOffset + trial) control by
        simp [rawQuery, hstatus]
        norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
          equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
          blindStateOffset, blindStateWidth, blindGrindingOffset,
          blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
          rejectionTrials, maxBlindTrials, maxProgrammedPoints] at htrial ⊢
        simp (disch := omega) only [if_pos, if_neg]]
      exact nonzeroStageQuery_active blindChallengeOffset trial control htrial
        hactive
  | multiplicationAlpha =>
      simp only [scalarStageStart]
      simp [rawQuery, hstatus]
      norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
        equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
        blindStateOffset, blindStateWidth, blindGrindingOffset,
        blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
        outerChallengeOffset, rejectionTrials, maxBlindTrials,
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
  | outerChallenge =>
      simp only [scalarStageStart]
      rw [show rawQuery shape causalSecret completion witness coins
          (outerChallengeOffset + trial) control =
          nonzeroStageQuery outerChallengeOffset
            (outerChallengeOffset + trial) control by
        simp [rawQuery, hstatus]
        norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
          equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
          blindStateOffset, blindStateWidth, blindGrindingOffset,
          blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
          outerChallengeOffset, outerPositionsOffset, rejectionTrials,
          maxBlindTrials, maxProgrammedPoints] at htrial ⊢
        simp (disch := omega) only [if_pos, if_neg]]
      exact nonzeroStageQuery_active outerChallengeOffset trial control htrial
        hactive
  | linearRho =>
      simp only [scalarStageStart]
      rw [show rawQuery shape causalSecret completion witness coins
          (linearRhoOffset + trial) control =
          nonzeroStageQuery linearRhoOffset (linearRhoOffset + trial) control by
        simp [rawQuery, hstatus]
        norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
          equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
          blindStateOffset, blindStateWidth, blindGrindingOffset,
          blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
          outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
          linearRhoOffset, hadamardPositionsOffset, rejectionTrials,
          maxBlindTrials, maxProgrammedPoints] at htrial ⊢
        simp (disch := omega) only [if_pos, if_neg]]
      exact nonzeroStageQuery_active linearRhoOffset trial control htrial hactive
  | hadamardRho =>
      simp only [scalarStageStart]
      rw [show rawQuery shape causalSecret completion witness coins
          (hadamardRhoOffset + trial) control =
          nonzeroStageQuery hadamardRhoOffset
            (hadamardRhoOffset + trial) control by
        simp [rawQuery, hstatus]
        norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
          equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
          blindStateOffset, blindStateWidth, blindGrindingOffset,
          blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
          outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
          linearRhoOffset, hadamardPositionsOffset, hadamardRhoOffset,
          productCoefficientOffset, rejectionTrials, maxBlindTrials,
          maxProgrammedPoints] at htrial ⊢
        simp (disch := omega) only [if_pos, if_neg]]
      exact nonzeroStageQuery_active hadamardRhoOffset trial control htrial
        hactive
  | productCoefficient =>
      simp only [scalarStageStart]
      rw [show rawQuery shape causalSecret completion witness coins
          (productCoefficientOffset + trial) control =
          nonzeroStageQuery productCoefficientOffset
            (productCoefficientOffset + trial) control by
        simp [rawQuery, hstatus]
        norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
          equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
          blindStateOffset, blindStateWidth, blindGrindingOffset,
          blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
          outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
          linearRhoOffset, hadamardPositionsOffset, hadamardRhoOffset,
          productCoefficientOffset, ligeritoOffset, rejectionTrials,
          maxBlindTrials, maxProgrammedPoints] at htrial ⊢
        simp (disch := omega) only [if_pos, if_neg]]
      exact nonzeroStageQuery_active productCoefficientOffset trial control
        htrial hactive

set_option maxRecDepth 10000 in
theorem rawControlUntil_scalar_stable_of_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (stage : ScalarStage)
    (trial remaining : ℕ) (hcap : trial + remaining ≤ rejectionTrials)
    (hpositive : 0 < trial)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (scalarStageStart stage + trial) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).status = .live)
    (hdone :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (scalarStageStart stage + trial) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).stageDone = true) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart stage + (trial + remaining)) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega) =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        (scalarStageStart stage + trial) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega) := by
  induction remaining generalizing trial with
  | zero => simp
  | succ remaining ih =>
      have htrial : trial < rejectionTrials := by omega
      let site : Fin productionSamplingSlots :=
        ⟨scalarStageStart stage + trial, by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (scalarStageStart stage + trial) site.isLt.le
      have hstatus' : current.status = .live := hstatus
      have hdone' : current.stageDone = true := hdone
      have hsucc := rawControlUntil_succ shape causalSecret completion witness
        coins prelude answers site
      have hstep := rawStep_scalarStage shape causalSecret completion witness
        coins stage trial htrial current (answers site) hstatus'
      rw [hstep] at hsucc
      have haccept : acceptScalar (scalarStageFailure stage)
          (scalarStageStart stage + trial) (scalarStageStart stage) current
          (answers site) = current := by
        classical
        unfold acceptScalar
        have hoffset : scalarStageStart stage + trial -
            scalarStageStart stage = trial := by omega
        rw [hoffset]
        simp [Nat.ne_of_gt hpositive, hdone']
      rw [haccept] at hsucc
      let next := rawControlUntil shape causalSecret completion witness coins
        prelude answers (scalarStageStart stage + (trial + 1)) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)
      have hnext : next = current := by
        simpa only [next, current, site, Nat.add_assoc] using hsucc
      have hnextStatus : next.status = .live := by rw [hnext]; exact hstatus'
      have hnextDone : next.stageDone = true := by rw [hnext]; exact hdone'
      have htail := ih (trial + 1) (by omega) (by omega) hnextStatus hnextDone
      calc
        rawControlUntil shape causalSecret completion witness coins prelude
            answers (scalarStageStart stage + (trial + (remaining + 1))) _ =
            rawControlUntil shape causalSecret completion witness coins prelude
              answers (scalarStageStart stage + ((trial + 1) + remaining)) _ := by
                congr 1; omega
        _ = next := htail
        _ = current := hnext

set_option maxRecDepth 10000 in
/-- The exact bounded scalar sampler succeeds whenever the corresponding
literal production-stage answer window contains an accepted block.  The proof
follows the real recursive sampler and obtains every answer through the one
shared-oracle agreement theorem; no independent sampler oracle is assumed. -/
theorem sampleScalarUntil_stage_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (stage : ScalarStage) (trial remaining : ℕ)
    (hcap : trial + remaining ≤ rejectionTrials)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (scalarStageStart stage + trial) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by
            cases stage <;> decide
          omega)).status = .live)
    (hactive : trial = 0 ∨
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (scalarStageStart stage + trial) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by
            cases stage <;> decide
          omega)).stageDone = false)
    (hexists : ∃ offset : Fin remaining,
      scalarStageGood stage
        (scalarFromBlock
          (answers ⟨scalarStageStart stage + trial + offset.val, by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by
            cases stage <;> decide
          omega⟩))) :
    ∃ result,
      sampleScalarUntil (scalarStageGood stage) oracle remaining
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (scalarStageStart stage + trial) (by
              have hstart : scalarStageStart stage + rejectionTrials ≤
                  productionSamplingSlots := by
                cases stage <;> decide
              omega)).transcript = some result ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (scalarStageStart stage + (trial + remaining)) (by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by cases stage <;> decide
          omega)).transcript = result.2 := by
  induction remaining generalizing trial with
  | zero => simp at hexists
  | succ remaining ih =>
      let site : Fin productionSamplingSlots :=
        ⟨scalarStageStart stage + trial, by
          have hstart : scalarStageStart stage + rejectionTrials ≤
              productionSamplingSlots := by
            cases stage <;> decide
          omega⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (scalarStageStart stage + trial) site.isLt.le
      have hstatus' : current.status = .live := hstatus
      have htrial : trial < rejectionTrials := by
        rcases hexists with ⟨offset, _⟩
        omega
      have hquery : rawQuery shape causalSecret completion witness coins site
          current = some (scalarPoint current.transcript) := by
        simpa only [site, current] using rawQuery_scalarStage_active shape
          causalSecret completion witness coins stage trial htrial current
          hstatus hactive
      have horacle : oracle (scalarPoint current.transcript) = answers site :=
        (hagrees site _ hquery).symm
      have hsample : sampleScalar oracle current.transcript =
          (scalarFromBlock (answers site),
            afterScalar current.transcript (answers site)) := by
        simp [sampleScalar, scalarFromBlock, horacle]
      by_cases hfirst : scalarStageGood stage (scalarFromBlock (answers site))
      · have haccepted : scalarFromBlock (answers site) ∉
            scalarStageFailure stage := by
          simpa [scalarStageGood_iff_not_mem] using hfirst
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers site
        have hstep := rawStep_scalarStage shape causalSecret completion witness
          coins stage trial htrial current (answers site) hstatus
        rw [hstep] at hsucc
        let next := rawControlUntil shape causalSecret completion witness coins
          prelude answers (scalarStageStart stage + (trial + 1)) (by
            have hstart : scalarStageStart stage + rejectionTrials ≤
                productionSamplingSlots := by cases stage <;> decide
            omega)
        have hsucc' : next = acceptScalar (scalarStageFailure stage)
            (scalarStageStart stage + trial) (scalarStageStart stage) current
            (answers site) := by
          simpa only [next, site, Nat.add_assoc] using hsucc
        have hnextLiveDone : next.status = .live ∧
            next.stageDone = true := by
          rw [hsucc']
          exact acceptScalar_live_done_of_good (scalarStageFailure stage)
            (scalarStageStart stage + trial) (scalarStageStart stage) current
            (answers site) hstatus' haccepted
        have hnextTranscript : next.transcript =
            afterScalar current.transcript (answers site) := by
          rw [hsucc']
          classical
          unfold acceptScalar
          have hoffset : scalarStageStart stage + trial -
              scalarStageStart stage = trial := by omega
          rw [hoffset]
          by_cases hzero : trial = 0
          · simp [hzero, haccepted]
          · have hdone : current.stageDone = false :=
              hactive.resolve_left hzero
            simp [hzero, hdone, haccepted]
        have hstable := rawControlUntil_scalar_stable_of_done shape
          causalSecret completion witness coins prelude answers stage
          (trial + 1) remaining (by omega) (by omega) hnextLiveDone.1
          hnextLiveDone.2
        have hstable' :
            rawControlUntil shape causalSecret completion witness coins prelude
                answers (scalarStageStart stage + (trial + (remaining + 1))) (by
                  have hstart : scalarStageStart stage + rejectionTrials ≤
                      productionSamplingSlots := by cases stage <;> decide
                  omega) = next := by
          have htransport := rawControlUntil_round_eq shape causalSecret
            completion witness coins prelude answers
            (left := scalarStageStart stage + (trial + (remaining + 1)))
            (right := scalarStageStart stage + ((trial + 1) + remaining))
            (by
              have hstart : scalarStageStart stage + rejectionTrials ≤
                  productionSamplingSlots := by cases stage <;> decide
              omega)
            (by
              have hstart : scalarStageStart stage + rejectionTrials ≤
                  productionSamplingSlots := by cases stage <;> decide
              omega)
            (by omega)
          exact htransport.trans hstable
        refine ⟨(sampleScalar oracle current.transcript), ?_, ?_⟩
        · simp only [sampleScalarUntil]
          rw [hsample]
          simp only [hfirst, if_pos]
        · rw [congrArg Control.transcript hstable', hnextTranscript, hsample]
      · have hremainingPos : 0 < remaining := by
          by_contra hzero
          have : remaining = 0 := Nat.eq_zero_of_not_pos hzero
          subst remaining
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetZero : offset.val = 0 := by omega
          exact hfirst (by simpa [site, hoffsetZero] using hoffset)
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers site
        have hstep := rawStep_scalarStage shape causalSecret completion witness
          coins stage trial htrial current (answers site) hstatus
        rw [hstep] at hsucc
        let next := rawControlUntil shape causalSecret completion witness coins
          prelude answers (scalarStageStart stage + (trial + 1)) (by
            have hstart : scalarStageStart stage + rejectionTrials ≤
                productionSamplingSlots := by
              cases stage <;> decide
            omega)
        have hsucc' : next = acceptScalar (scalarStageFailure stage)
            (scalarStageStart stage + trial) (scalarStageStart stage) current
            (answers site) := by
          simpa only [next, site, Nat.add_assoc] using hsucc
        have hfailed : scalarFromBlock (answers site) ∈
            scalarStageFailure stage := by
          simpa [scalarStageGood_iff_not_mem] using hfirst
        have hnotCap : trial + 1 ≠ rejectionTrials := by
          rcases hexists with ⟨offset, hoffset⟩
          by_contra heq
          have hremainingZero : remaining = 0 := by omega
          have hoffsetZero : offset.val = 0 := by omega
          exact hfirst (by simpa [site, hoffsetZero] using hoffset)
        have hnextStatus : next.status = .live := by
          rw [hsucc']
          by_cases hzero : trial = 0
          · have hone : 1 ≠ rejectionTrials := by decide
            simp [acceptScalar, hzero, hfailed, hstatus', hone]
          · have hdone : current.stageDone = false := hactive.resolve_left hzero
            simp [acceptScalar, hzero, hdone, hfailed, hstatus', hnotCap]
        have hnextDone : next.stageDone = false := by
          rw [hsucc']
          by_cases hzero : trial = 0
          · have hone : 1 ≠ rejectionTrials := by decide
            simp [acceptScalar, hzero, hfailed, hone]
          · have hdone : current.stageDone = false := hactive.resolve_left hzero
            simp [acceptScalar, hzero, hdone, hfailed, hnotCap]
        have hnextTranscript : next.transcript =
            afterScalar current.transcript (answers site) := by
          rw [hsucc']
          by_cases hzero : trial = 0
          · have hone : 1 ≠ rejectionTrials := by decide
            simp [acceptScalar, hzero, hfailed, hone]
          · have hdone : current.stageDone = false := hactive.resolve_left hzero
            simp [acceptScalar, hzero, hdone, hfailed, hnotCap]
        have hnextExists : ∃ offset : Fin remaining,
            scalarStageGood stage
              (scalarFromBlock
                (answers ⟨scalarStageStart stage + (trial + 1) + offset.val, by
                have hstart : scalarStageStart stage + rejectionTrials ≤
                    productionSamplingSlots := by
                  cases stage <;> decide
                omega⟩)) := by
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetPos : 0 < offset.val := by
            by_contra hzero
            have hoffsetZero : offset.val = 0 := by omega
            exact hfirst (by simpa [site, hoffsetZero] using hoffset)
          let prior : Fin remaining := ⟨offset.val - 1, by omega⟩
          refine ⟨prior, ?_⟩
          have hindex :
              (⟨scalarStageStart stage + trial + offset.val, by
                have hstart : scalarStageStart stage + rejectionTrials ≤
                    productionSamplingSlots := by
                  cases stage <;> decide
                omega⟩ : Fin productionSamplingSlots) =
              ⟨scalarStageStart stage + (trial + 1) + prior.val, by
                have hstart : scalarStageStart stage + rejectionTrials ≤
                    productionSamplingSlots := by
                  cases stage <;> decide
                omega⟩ := by
            apply Fin.ext
            dsimp only [prior]
            omega
          simpa only [← hindex] using hoffset
        rcases ih (trial + 1) (by omega) hnextStatus (Or.inr hnextDone)
            hnextExists with ⟨result, hresult, hfinal⟩
        refine ⟨result, ?_, ?_⟩
        · simp only [sampleScalarUntil]
          rw [hsample]
          simp only [hfirst, if_false]
          rw [← hnextTranscript]
          exact hresult
        · have htransport := rawControlUntil_round_eq shape causalSecret
            completion witness coins prelude answers
            (left := scalarStageStart stage + (trial + (remaining + 1)))
            (right := scalarStageStart stage + ((trial + 1) + remaining))
            (by
              have hstart : scalarStageStart stage + rejectionTrials ≤
                  productionSamplingSlots := by cases stage <;> decide
              omega)
            (by
              have hstart : scalarStageStart stage + rejectionTrials ≤
                  productionSamplingSlots := by cases stage <;> decide
              omega)
            (by omega)
          exact (congrArg Control.transcript htransport).trans hfinal

end VeiledFlock.ProductionSamplingTraceScalar

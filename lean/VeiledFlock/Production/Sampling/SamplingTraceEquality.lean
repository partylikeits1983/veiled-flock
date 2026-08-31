import VeiledFlock.Production.Sampling.SamplingOperationalTrace

/-! # Equality-sampler refinement for the operational schedule -/

namespace VeiledFlock.ProductionSamplingTraceEquality

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.ChallengeSampling
open VeiledFlock.Field128Serialization
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBeforeInjective
open VeiledFlock.ProductionSamplingScheduleEqualityActive
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.ProductionTranscriptFraming

theorem sampleSlice_eq_sliceFromBlocks
    (oracle : List Byte → OracleBlock) (transcript : List Byte)
    (length : ℕ) (blocks : List OracleBlock)
    (hanswer : ∀ index : Fin length,
      oracle (slicePoint transcript length
        (BitVec.ofNat 64 (index.val / 2))) =
      blocks.getD (index.val / 2) default) :
    sampleSlice oracle transcript length = sliceFromBlocks length blocks := by
  funext index
  unfold sampleSlice sliceField sliceFromBlocks
  rw [hanswer index]
  by_cases heven : index.val % 2 = 0
  · simp [blockFieldsEquiv, heven]
  · have hmod : index.val % 2 = 1 := by omega
    simp [blockFieldsEquiv,  hmod]

/-- The one shared oracle agrees with the answer tape at every query issued by
the literal production state machine.  The operational experiment discharges
this property using `expandedSamplingAnswers_raw_active`. -/
def RawAnswersOracleAgreement
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock) : Prop :=
  ∀ (site : Fin productionSamplingSlots) point,
    rawQuery shape causalSecret completion witness coins site
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers site site.isLt.le) = some point →
      answers site = oracle point

set_option maxRecDepth 10000 in
theorem production_skip_sample_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle) :
    sampleSlice oracle prelude 6 =
      sliceFromBlocks 6
        (List.ofFn (window 0 equalitySkipBlocks (by decide) answers)) := by
  apply sampleSlice_eq_sliceFromBlocks
  intro index
  let counter : Fin productionSamplingSlots :=
    ⟨index.val / 2, by
      have hi := index.isLt
      rw [productionSamplingSlots_eq]
      omega⟩
  have hcounter : counter.val < equalitySkipBlocks := by
    dsimp only [counter]
    have hi := index.isLt
    norm_num [equalitySkipBlocks] at hi ⊢
    omega
  have hcontrol := rawControlUntil_skip_prefix_fields shape causalSecret
    completion witness coins prelude answers counter.val hcounter
  have hquery : rawQuery shape causalSecret completion witness coins counter
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers counter counter.isLt.le) =
        some (slicePoint prelude 6 (BitVec.ofNat 64 (index.val / 2))) := by
    simpa [rawQuery, hcounter, hcontrol.1, hcontrol.2, counter]
  have hlist : index.val / 2 <
      (List.ofFn (window 0 equalitySkipBlocks (by decide) answers)).length := by
    rw [List.length_ofFn]
    exact hcounter
  have hget :
      (List.ofFn (window 0 equalitySkipBlocks (by decide) answers)).getD
          (index.val / 2) default = answers counter := by
    rw [List.getD_eq_getElem _ _ hlist, List.getElem_ofFn]
    apply congrArg answers
    apply Fin.ext
    simp [ counter]
  exact (hagrees counter _ hquery).symm.trans hget.symm

set_option maxRecDepth 10000 in
theorem production_equality_attempt_sample_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (attempt : ℕ)
    (hattempt : attempt ≤ firstEqualityAccepted shape answers hgood) :
    let boundary := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + attempt * 7)
        (equalityBoundary_fits attempt
          (hattempt.trans
            (firstEqualityAccepted_lt shape answers hgood).le))
    sampleSlice oracle boundary.transcript (m shape - kSkip - 7) =
      sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (equalityAttemptAnswers answers
          ⟨attempt, lt_of_le_of_lt hattempt
            (firstEqualityAccepted_lt shape answers hgood)⟩)) := by
  dsimp only
  apply sampleSlice_eq_sliceFromBlocks
  intro index
  let counter := index.val / 2
  have hcounter : counter < equalityBlockCount shape := by
    cases shape <;> fin_cases index <;> decide
  have hfields := rawControlUntil_active_equality_fields shape causalSecret
    completion witness coins prelude answers hgood attempt counter hattempt
    hcounter
  let site : Fin productionSamplingSlots :=
    ⟨equalityOffset + attempt * 7 + counter, by
      have ha : attempt < rejectionTrials := lt_of_le_of_lt hattempt
        (firstEqualityAccepted_lt shape answers hgood)
      have hc : counter < 7 :=
        hcounter.trans_le (equalityBlockCount_le_seven shape)
      rw [productionSamplingSlots_eq]
      norm_num [equalityOffset, equalitySkipBlocks, rejectionTrials] at ha ⊢
      omega⟩
  have hquery : rawQuery shape causalSecret completion witness coins site
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers site site.isLt.le) =
      some (slicePoint
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + attempt * 7)
            (equalityBoundary_fits attempt
              (hattempt.trans
                (firstEqualityAccepted_lt shape answers hgood).le))).transcript
        (m shape - kSkip - 7) (BitVec.ofNat 64 counter)) := by
    have hstatus :
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers site site.isLt.le).status = .live := by
      simpa [site] using hfields.1
    have hnone :
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers site site.isLt.le).equalityPoint = none := by
      simpa [site] using hfields.2.1
    have htranscript :
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers site site.isLt.le).transcript =
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + attempt * 7)
            (equalityBoundary_fits attempt
              (hattempt.trans
                (firstEqualityAccepted_lt shape answers hgood).le))).transcript := by
      simpa [site] using hfields.2.2
    have hskip : ¬ site.val < equalitySkipBlocks := by
      norm_num [site, equalityOffset, equalitySkipBlocks]
      omega
    have hequality : site.val < zerocheckOffset := by
      have ha : attempt < rejectionTrials := lt_of_le_of_lt hattempt
        (firstEqualityAccepted_lt shape answers hgood)
      have hc : counter < 7 :=
        hcounter.trans_le (equalityBlockCount_le_seven shape)
      norm_num [site, zerocheckOffset, equalityWidth, equalityAttemptBlocks,
        equalityOffset] at ⊢
      omega
    have hoffset : site.val - equalityOffset = attempt * 7 + counter := by
      simp only [site]
      omega
    have hmod : (attempt * 7 + counter) % equalityAttemptBlocks = counter := by
      have hc : counter < 7 :=
        hcounter.trans_le (equalityBlockCount_le_seven shape)
      norm_num [equalityAttemptBlocks]
      omega
    simp [rawQuery, hstatus, hskip, hequality, hnone, hoffset, hmod,
      hcounter, htranscript]
  have hlist : index.val / 2 <
      (List.ofFn (equalityAttemptAnswers answers
        ⟨attempt, lt_of_le_of_lt hattempt
          (firstEqualityAccepted_lt shape answers hgood)⟩)).length := by
    rw [List.length_ofFn]
    exact hcounter.trans_le (equalityBlockCount_le_seven shape)
  have hget :
      (List.ofFn (equalityAttemptAnswers answers
        ⟨attempt, lt_of_le_of_lt hattempt
          (firstEqualityAccepted_lt shape answers hgood)⟩)).getD
          (index.val / 2) default = answers site := by
    rw [List.getD_eq_getElem _ _ hlist, List.getElem_ofFn]
    rfl
  exact (hagrees site _ hquery).symm.trans hget.symm

set_option maxRecDepth 10000 in
theorem equalityAttempt_transcript_eq_afterSlice
    (shape : BatchShape) (attempt : ℕ) (control : Control shape)
    (blocks : Fin 7 → OracleBlock)
    (hstatus : control.status = .live)
    (hnone : control.equalityPoint = none)
    (hskip : control.skip.isSome = true) :
    (iterateFrom (equalityStep shape)
      (equalityOffset + attempt * equalityAttemptBlocks) 7 control
      blocks).transcript =
        afterSlice control.transcript
          (sliceFromBlocks (m shape - kSkip - 7) (List.ofFn blocks)) := by
  have hoff (counter : ℕ) :
      equalityOffset + attempt * 7 + counter - equalityOffset =
        attempt * 7 + counter := by omega
  have hoff2 : equalityOffset + attempt * 7 + 1 + 1 - equalityOffset =
      attempt * 7 + 2 := by omega
  have hoff3 : equalityOffset + attempt * 7 + 1 + 1 + 1 - equalityOffset =
      attempt * 7 + 3 := by omega
  have hoff4 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 -
      equalityOffset = attempt * 7 + 4 := by omega
  have hoff5 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 + 1 -
      equalityOffset = attempt * 7 + 5 := by omega
  have hoff6 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 + 1 + 1 -
      equalityOffset = attempt * 7 + 6 := by omega
  have hslice := sliceFrom_equalityLiveBlocks shape blocks
  cases hskipValue : control.skip with
  | none => simp [hskipValue] at hskip
  | some skip =>
      cases shape <;>
        simp [iterateFrom, iterateList, equalityStep, equalityBlockCount,
          equalityAttemptBlocks, m, kSkip, rejectionTrials, hoff, hoff2,
          hoff3, hoff4, hoff5, hoff6,   hnone, hstatus,
          hskipValue] <;>
        split <;> simp_all <;>
        (try split) <;> (try simp_all) <;>
        try { exact congrArg (afterSlice control.transcript) hslice }

set_option maxRecDepth 10000 in
theorem production_equality_boundary_succ_transcript
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (attempt : ℕ)
    (hattempt : attempt ≤ firstEqualityAccepted shape answers hgood) :
    let before := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + attempt * 7)
        (equalityBoundary_fits attempt
          (hattempt.trans
            (firstEqualityAccepted_lt shape answers hgood).le))
    let after := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + (attempt + 1) * 7)
        (equalityBoundary_fits (attempt + 1) (by
          have hfirst := firstEqualityAccepted_lt shape answers hgood
          omega))
    after.transcript = afterSlice before.transcript
      (sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (equalityAttemptAnswers answers
          ⟨attempt, lt_of_le_of_lt hattempt
            (firstEqualityAccepted_lt shape answers hgood)⟩))) := by
  dsimp only
  have hattemptLt : attempt < rejectionTrials := lt_of_le_of_lt hattempt
    (firstEqualityAccepted_lt shape answers hgood)
  have hbefore := rawControlUntil_equality_boundary_live_none shape causalSecret
    completion witness coins prelude answers hgood attempt hattempt
  let blocks := equalityAttemptAnswers answers ⟨attempt, hattemptLt⟩
  have hlocalStatus :
      (iterateFrom (equalityStep shape) (equalityOffset + attempt * 7) 7
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + attempt * 7)
            (equalityBoundary_fits attempt hattemptLt.le)) blocks).status =
        .live := by
    by_cases hfirst : attempt = firstEqualityAccepted shape answers hgood
    · subst attempt
      exact (equalityAttempt_live_some_of_accepted shape
        (firstEqualityAccepted shape answers hgood)
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers
            (equalityOffset + firstEqualityAccepted shape answers hgood * 7)
            (equalityBoundary_fits
              (firstEqualityAccepted shape answers hgood)
              (firstEqualityAccepted_lt shape answers hgood).le))
        blocks hbefore.1 hbefore.2.1 hbefore.2.2
        (firstEqualityAccepted_spec shape answers hgood).choose_spec).1
    · have hbeforeFirst : attempt <
          firstEqualityAccepted shape answers hgood := by omega
      exact (equalityAttempt_live_none_of_rejected_before_cap shape attempt
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + attempt * 7)
            (equalityBoundary_fits attempt hattemptLt.le)) blocks hbefore.1
        hbefore.2.1
        (before_firstEqualityAccepted_rejects shape answers hgood attempt
          hbeforeFirst hattemptLt)
        (by
          have hfirstLt := firstEqualityAccepted_lt shape answers hgood
          omega)).1
  have hstep := rawControlUntil_equality_boundary_step shape causalSecret
    completion witness coins prelude answers attempt hattemptLt hlocalStatus
  rw [hstep]
  exact equalityAttempt_transcript_eq_afterSlice shape attempt _ blocks
    hbefore.1 hbefore.2.1 hbefore.2.2

set_option maxRecDepth 10000 in
theorem sampleUntilAccepted_from_equality_boundary_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (distance attempt : ℕ)
    (hsum : attempt + distance = firstEqualityAccepted shape answers hgood) :
    let boundary := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + attempt * 7)
        (equalityBoundary_fits attempt (by
          have hfirst := firstEqualityAccepted_lt shape answers hgood
          omega))
    ∃ result,
      sampleUntilAccepted oracle (m shape - kSkip - 7)
          (rejectionTrials - attempt) boundary.transcript = some result := by
  induction distance generalizing attempt with
  | zero =>
      have hattempt : attempt = firstEqualityAccepted shape answers hgood := by
        omega
      subst attempt
      let first := firstEqualityAccepted shape answers hgood
      let boundary := rawControlUntil shape causalSecret completion witness coins
        prelude answers (equalityOffset + first * 7)
          (equalityBoundary_fits first
            (firstEqualityAccepted_lt shape answers hgood).le)
      have hsample := production_equality_attempt_sample_eq shape causalSecret
        completion witness coins prelude answers hgood oracle hagrees first
        (by rfl)
      have haccepts := (firstEqualityAccepted_spec shape answers hgood).choose_spec
      have haccepts' : accepted
          (sampleSlice oracle boundary.transcript (m shape - kSkip - 7)) := by
        rw [hsample]
        simpa [first] using haccepts
      have htrials : rejectionTrials - first =
          (rejectionTrials - first - 1) + 1 := by
        have := firstEqualityAccepted_lt shape answers hgood
        omega
      refine ⟨(sampleSlice oracle boundary.transcript
        (m shape - kSkip - 7),
          afterSlice boundary.transcript
            (sampleSlice oracle boundary.transcript
              (m shape - kSkip - 7))), ?_⟩
      rw [htrials]
      simp only [sampleUntilAccepted]
      rw [if_pos haccepts']
  | succ distance ih =>
      have hattempt : attempt < firstEqualityAccepted shape answers hgood := by
        omega
      have hattemptLt : attempt < rejectionTrials :=
        hattempt.trans (firstEqualityAccepted_lt shape answers hgood)
      let boundary := rawControlUntil shape causalSecret completion witness coins
        prelude answers (equalityOffset + attempt * 7)
          (equalityBoundary_fits attempt hattemptLt.le)
      let nextBoundary := rawControlUntil shape causalSecret completion witness
        coins prelude answers (equalityOffset + (attempt + 1) * 7)
          (equalityBoundary_fits (attempt + 1) (by omega))
      have hsample := production_equality_attempt_sample_eq shape causalSecret
        completion witness coins prelude answers hgood oracle hagrees attempt
        hattempt.le
      have hrejected := before_firstEqualityAccepted_rejects shape answers hgood
        attempt hattempt hattemptLt
      have hnext := production_equality_boundary_succ_transcript shape
        causalSecret completion witness coins prelude answers hgood attempt
        hattempt.le
      have hsumNext : attempt + 1 + distance =
          firstEqualityAccepted shape answers hgood := by omega
      rcases ih (attempt + 1) hsumNext with ⟨result, hresult⟩
      refine ⟨result, ?_⟩
      have htrials : rejectionTrials - attempt =
          (rejectionTrials - (attempt + 1)) + 1 := by omega
      rw [htrials]
      simp only [sampleUntilAccepted]
      rw [hsample]
      simp only [hrejected, if_false]
      rw [← hnext]
      exact hresult

theorem sampleEqualityPointPrefix_some_of_raw_agreement
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle) :
    ∃ equalityPoint,
      sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
        rejectionTrials prelude = some equalityPoint := by
  let skipBlocks := List.ofFn
    (window 0 equalitySkipBlocks (by decide) answers)
  let afterSkip := rawControlUntil shape causalSecret completion witness coins
    prelude answers equalityOffset (by decide)
  have hskipSample := production_skip_sample_eq shape causalSecret completion
    witness coins prelude answers oracle hagrees
  have hskipControl := VeiledFlock.ProductionSamplingScheduleWhole.rawControlUntil_skip
    shape causalSecret completion witness coins prelude answers
  have hafterSkip : afterSkip.transcript =
      afterSlice prelude (sampleSlice oracle prelude 6) := by
    dsimp only [afterSkip]
    rw [hskipControl]
    simp only [afterSkipControl]
    rw [hskipSample]
  have hsum : 0 + firstEqualityAccepted shape answers hgood =
      firstEqualityAccepted shape answers hgood := by omega
  rcases sampleUntilAccepted_from_equality_boundary_some shape causalSecret
    completion witness coins prelude answers hgood oracle hagrees
    (firstEqualityAccepted shape answers hgood) 0 hsum with
    ⟨result, hresult⟩
  rcases result with ⟨outer, finalTranscript⟩
  change sampleUntilAccepted oracle (m shape - kSkip - 7) rejectionTrials
      afterSkip.transcript = some (outer, finalTranscript) at hresult
  refine ⟨(sampleSlice oracle prelude 6, outer, finalTranscript), ?_⟩
  simp only [sampleEqualityPointPrefix]
  rw [← hafterSkip]
  rw [hresult]

set_option maxRecDepth 10000 in
theorem sampleUntilAccepted_from_equality_boundary_eq_first
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (distance attempt : ℕ)
    (hsum : attempt + distance = firstEqualityAccepted shape answers hgood) :
    let first := firstEqualityAccepted shape answers hgood
    let boundary := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + attempt * 7)
        (equalityBoundary_fits attempt (by
          have hfirst := firstEqualityAccepted_lt shape answers hgood
          omega))
    let firstBoundary := rawControlUntil shape causalSecret completion witness
      coins prelude answers (equalityOffset + first * 7)
        (equalityBoundary_fits first
          (firstEqualityAccepted_lt shape answers hgood).le)
    let firstOuter := sliceFromBlocks (m shape - kSkip - 7)
      (List.ofFn (equalityAttemptAnswers answers
        ⟨first, firstEqualityAccepted_lt shape answers hgood⟩))
    sampleUntilAccepted oracle (m shape - kSkip - 7)
        (rejectionTrials - attempt) boundary.transcript =
      some (firstOuter, afterSlice firstBoundary.transcript firstOuter) := by
  induction distance generalizing attempt with
  | zero =>
      have hattempt : attempt = firstEqualityAccepted shape answers hgood := by
        omega
      subst attempt
      let first := firstEqualityAccepted shape answers hgood
      let boundary := rawControlUntil shape causalSecret completion witness coins
        prelude answers (equalityOffset + first * 7)
          (equalityBoundary_fits first
            (firstEqualityAccepted_lt shape answers hgood).le)
      let firstOuter := sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (equalityAttemptAnswers answers
          ⟨first, firstEqualityAccepted_lt shape answers hgood⟩))
      have hsample := production_equality_attempt_sample_eq shape causalSecret
        completion witness coins prelude answers hgood oracle hagrees first
        (by rfl)
      have haccepts := (firstEqualityAccepted_spec shape answers hgood).choose_spec
      have haccepts' : accepted
          (sampleSlice oracle boundary.transcript (m shape - kSkip - 7)) := by
        rw [hsample]
        simpa [first] using haccepts
      have htrials : rejectionTrials - first =
          (rejectionTrials - first - 1) + 1 := by
        have := firstEqualityAccepted_lt shape answers hgood
        omega
      rw [htrials]
      simp only [sampleUntilAccepted]
      rw [if_pos haccepts']
      rw [hsample]
  | succ distance ih =>
      have hattempt : attempt < firstEqualityAccepted shape answers hgood := by
        omega
      have hattemptLt : attempt < rejectionTrials :=
        hattempt.trans (firstEqualityAccepted_lt shape answers hgood)
      let boundary := rawControlUntil shape causalSecret completion witness coins
        prelude answers (equalityOffset + attempt * 7)
          (equalityBoundary_fits attempt hattemptLt.le)
      have hsample := production_equality_attempt_sample_eq shape causalSecret
        completion witness coins prelude answers hgood oracle hagrees attempt
        hattempt.le
      have hrejected := before_firstEqualityAccepted_rejects shape answers hgood
        attempt hattempt hattemptLt
      have hnext := production_equality_boundary_succ_transcript shape
        causalSecret completion witness coins prelude answers hgood attempt
        hattempt.le
      have hsumNext : attempt + 1 + distance =
          firstEqualityAccepted shape answers hgood := by omega
      have hresult := ih (attempt + 1) hsumNext
      have htrials : rejectionTrials - attempt =
          (rejectionTrials - (attempt + 1)) + 1 := by omega
      rw [htrials]
      simp only [sampleUntilAccepted]
      rw [hsample, if_neg hrejected, ← hnext]
      exact hresult

theorem sampleEqualityPointPrefix_eq_some_raw
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle) :
    let first := firstEqualityAccepted shape answers hgood
    let skip := sampleSlice oracle prelude 6
    let firstBoundary := rawControlUntil shape causalSecret completion witness
      coins prelude answers (equalityOffset + first * 7)
        (equalityBoundary_fits first
          (firstEqualityAccepted_lt shape answers hgood).le)
    let outer := sliceFromBlocks (m shape - kSkip - 7)
      (List.ofFn (equalityAttemptAnswers answers
        ⟨first, firstEqualityAccepted_lt shape answers hgood⟩))
    sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
        rejectionTrials prelude =
      some (skip, outer, afterSlice firstBoundary.transcript outer) := by
  dsimp only
  let afterSkip := rawControlUntil shape causalSecret completion witness coins
    prelude answers equalityOffset (by decide)
  have hskipSample := production_skip_sample_eq shape causalSecret completion
    witness coins prelude answers oracle hagrees
  have hskipControl := VeiledFlock.ProductionSamplingScheduleWhole.rawControlUntil_skip
    shape causalSecret completion witness coins prelude answers
  have hafterSkip : afterSkip.transcript =
      afterSlice prelude (sampleSlice oracle prelude 6) := by
    dsimp only [afterSkip]
    rw [hskipControl]
    simp only [afterSkipControl]
    rw [hskipSample]
  have hsum : 0 + firstEqualityAccepted shape answers hgood =
      firstEqualityAccepted shape answers hgood := by omega
  have hresult := sampleUntilAccepted_from_equality_boundary_eq_first shape
    causalSecret completion witness coins prelude answers hgood oracle hagrees
    (firstEqualityAccepted shape answers hgood) 0 hsum
  change sampleUntilAccepted oracle (m shape - kSkip - 7) rejectionTrials
      afterSkip.transcript = _ at hresult
  simp only [sampleEqualityPointPrefix]
  rw [← hafterSkip, hresult]

end VeiledFlock.ProductionSamplingTraceEquality

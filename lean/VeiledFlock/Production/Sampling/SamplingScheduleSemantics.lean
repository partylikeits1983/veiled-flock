import VeiledFlock.Production.Sampling.SamplingScheduleClassification

/-!
# Deterministic semantics of the bounded production sampling schedule

This module turns non-membership in the concrete fixed-answer bad ledger into
the deterministic success facts needed by the literal production samplers.
It contains no probability or coupling assumptions.
-/

namespace VeiledFlock.ProductionSamplingScheduleSemantics

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.Birthday
open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.EndToEnd
open VeiledFlock.Field128Ghash
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.UniquePositionSampling

/-! ## Fixed-range iteration -/

/-- List-backed implementation of consecutive indexed transitions. -/
def iterateList {State Answer : Type*}
    (step : ℕ → State → Answer → State) :
    ℕ → State → List Answer → State
  | _, state, [] => state
  | start, state, answer :: answers =>
      iterateList step (start + 1) (step start state answer) answers

theorem iterateList_append {State Answer : Type*}
    (step : ℕ → State → Answer → State) (start : ℕ)
    (state : State) (left right : List Answer) :
    iterateList step start state (left ++ right) =
      iterateList step (start + left.length)
        (iterateList step start state left) right := by
  induction left generalizing start state with
  | nil => simp [iterateList]
  | cons answer left ih =>
      simp only [List.cons_append, iterateList, List.length_cons]
      rw [ih]
      congr 1
      omega

/-- Execute a state transition on the consecutive rounds
`start, ..., start + rounds - 1`. -/
def iterateFrom {State Answer : Type*}
    (step : ℕ → State → Answer → State) (start rounds : ℕ)
    (state : State) (answers : Fin rounds → Answer) : State :=
  iterateList step start state (List.ofFn answers)

theorem iterateFrom_add {State Answer : Type*}
    (step : ℕ → State → Answer → State) (start left right : ℕ)
    (state : State) (answers : Fin (left + right) → Answer) :
    iterateFrom step start (left + right) state answers =
      iterateFrom step (start + left) right
        (iterateFrom step start left state
          (fun index ↦ answers (Fin.castAdd right index)))
        (fun index ↦ answers (Fin.natAdd left index)) := by
  unfold iterateFrom
  rw [show List.ofFn answers =
      List.ofFn (fun index : Fin left ↦ answers (Fin.castAdd right index)) ++
        List.ofFn (fun index : Fin right ↦ answers (Fin.natAdd left index)) by
    rw [← List.ofFn_fin_append]
    rw [Fin.append_castAdd_natAdd]]
  rw [iterateList_append, List.length_ofFn]

theorem iterateFrom_succ_last {State Answer : Type*}
    (step : ℕ → State → Answer → State) (start rounds : ℕ)
    (state : State) (answers : Fin (rounds + 1) → Answer) :
    iterateFrom step start (rounds + 1) state answers =
      step (start + rounds)
        (iterateFrom step start rounds state
          (fun index ↦ answers index.castSucc))
        (answers (Fin.last rounds)) := by
  rw [iterateFrom_add step start rounds 1]
  simp [iterateFrom, iterateList]
  congr 2

theorem iterateFrom_cast {State Answer : Type*}
    (step : ℕ → State → Answer → State) (start left right : ℕ)
    (state : State) (answers : Fin left → Answer) (hsize : left = right) :
    iterateFrom step start left state answers =
      iterateFrom step start right state
        (fun index ↦ answers (Fin.cast hsize.symm index)) := by
  subst right
  rfl

theorem controlAfter_eq_iterateFrom
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (prelude : List Byte) {rounds : ℕ}
    (answers : History (Outcome := OracleBlock) rounds) :
    controlAfter shape causalSecret completion witness coins prelude answers =
      iterateFrom
        (rawStep shape causalSecret completion witness coins) 0 rounds
        (initialControl shape prelude) answers := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [controlAfter, iterateFrom_succ_last]
      simp only [Nat.zero_add]
      rw [ih]

/-- The maximum-width equality parser used by the finite ledger agrees on
every live prefix coordinate with the parser used by the production state
machine. -/
theorem sliceFromBlocks_ofFn_eq_equalityAttempt
    {length : ℕ}
    (hlength : length ≤ ChallengeSampling.maxEqualityPointOuterCoordinates)
    (blocks : Fin 7 → OracleBlock) (index : Fin length) :
    sliceFromBlocks length (List.ofFn blocks) index =
      equalityAttemptEquiv blocks (Fin.castLE hlength index) := by
  have hblock : index.val / 2 < (List.ofFn blocks).length := by
    rw [List.length_ofFn]
    have hindex := index.isLt
    norm_num [ChallengeSampling.maxEqualityPointOuterCoordinates,
      equalityAttemptBlocks] at hlength ⊢
    omega
  unfold sliceFromBlocks
  rw [List.getD_eq_getElem (List.ofFn blocks) default hblock,
    List.getElem_ofFn]
  exact (equalityAttemptEquiv_apply blocks
    (Fin.castLE hlength index)).symm

theorem nonzero_window_fits (site : Fin maxNonzeroChallengeSites) :
    nonzeroOffset site + rejectionTrials ≤ productionSamplingSlots := by
  fin_cases site <;> rw [productionSamplingSlots_eq] <;> decide

theorem ligeritoGrinding_window_fits (site : Fin maxLigeritoSites) :
    ligeritoOffset + site.val * ligeritoSiteWidth + 1 + maxLigeritoTrials ≤
      productionSamplingSlots := by
  fin_cases site <;> rw [productionSamplingSlots_eq] <;> decide

theorem exists_equality_attempt_of_not_globalBad (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    ∃ attempt : Fin rejectionTrials,
      equalityAttemptsEquiv rejectionTrials
          (equalityFlatEquiv
            (window equalityOffset equalityWidth (by
              rw [productionSamplingSlots_eq]
              decide) answers)) attempt ∉
        equalityPointVectorFailure := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood (.equality)
  rw [badAt, mem_windowBad_iff] at hnot
  unfold equalityFlatAbort at hnot
  rw [mem_transportBad_iff, mem_equalityBlockAbortRuns_iff,
    mem_abortRuns_iff] at hnot
  push Not at hnot
  exact hnot

theorem equality_attempt_prefix_accepted
    {length : ℕ}
    (hlength : length ≤ ChallengeSampling.maxEqualityPointOuterCoordinates)
    (blocks : Fin 7 → OracleBlock)
    (hgood : equalityAttemptEquiv blocks ∉ equalityPointVectorFailure) :
    accepted (sliceFromBlocks length (List.ofFn blocks)) := by
  intro index hone
  apply hgood
  rw [equalityPointVectorFailure,
    VeiledFlock.RepeatedEvents.mem_anyBad_iff]
  refine ⟨Fin.castLE hlength index, ?_⟩
  rw [← sliceFromBlocks_ofFn_eq_equalityAttempt hlength blocks index,
    hone]
  simp [oneFailure]

/-- Outside the global ledger event, at least one answer in each nonzero
challenge reservation is accepted. -/
theorem exists_nonzero_answer_of_not_globalBad (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (site : Fin maxNonzeroChallengeSites) :
    ∃ trial : Fin rejectionTrials,
      scalarFromBlock
          (window (nonzeroOffset site) rejectionTrials
            (nonzero_window_fits site) answers trial) ∉
        zeroFailure := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood (.nonzero site)
  rw [badAt, mem_windowBad_iff, mem_scalarBlockAbortRuns_iff] at hnot
  push Not at hnot
  simpa [VeiledFlock.FixedWindowProbability.window] using hnot

theorem exists_multiplicationAlpha_answer_of_not_globalBad
    (shape : BatchShape) (answers : SamplingAnswerTape)
    (hgood : answers ∉ globalBad shape) :
    ∃ trial : Fin rejectionTrials,
      scalarFromBlock
          (window multiplicationAlphaOffset rejectionTrials (by
            rw [productionSamplingSlots_eq]
            decide) answers trial) ∉ zeroOrOneFailure := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood
    (.multiplicationAlpha)
  rw [badAt, mem_windowBad_iff, mem_scalarBlockAbortRuns_iff] at hnot
  push Not at hnot
  simpa [VeiledFlock.FixedWindowProbability.window] using hnot

theorem exists_blindGrinding_answer_of_not_globalBad
    (shape : BatchShape) (answers : SamplingAnswerTape)
    (hgood : answers ∉ globalBad shape) :
    ∃ trial : Fin maxBlindTrials,
      blindGrindingGood
        (window blindGrindingOffset maxBlindTrials (by
          rw [productionSamplingSlots_eq]
          decide) answers trial) := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood
    (.blindGrinding)
  rw [badAt, mem_windowBad_iff, mem_blockAbortRuns_iff] at hnot
  push Not at hnot
  simpa [VeiledFlock.FixedWindowProbability.window, blindGrindingGood] using hnot

theorem exists_ligeritoGrinding_answer_of_not_globalBad
    (shape : BatchShape) (answers : SamplingAnswerTape)
    (hgood : answers ∉ globalBad shape) (site : Fin maxLigeritoSites) :
    ∃ trial : Fin maxLigeritoTrials,
      rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (window (ligeritoOffset + site.val * ligeritoSiteWidth + 1)
          maxLigeritoTrials (ligeritoGrinding_window_fits site) answers trial) := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood
    (.ligeritoGrinding site)
  rw [badAt, mem_windowBad_iff, mem_blockAbortRuns_iff] at hnot
  push Not at hnot
  simpa [VeiledFlock.FixedWindowProbability.window, Nat.add_assoc] using hnot

theorem outerPositions_card_ge_of_not_globalBad
    (shape : BatchShape) (answers : SamplingAnswerTape)
    (hgood : answers ∉ globalBad shape) :
    outerL0QueryCount shape ≤
      (observedPositions (fun trial : Fin samplingTrials ↦
        rustLowPosition (m shape - 11)
          (scalarFromBlock
            (window outerPositionsOffset samplingTrials (by
              rw [productionSamplingSlots_eq]
              decide) answers trial)))).card := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood (.outerPositions)
  rw [badAt, mem_windowBad_iff, mem_positionBlockAbortRuns_iff] at hnot
  simpa [VeiledFlock.FixedWindowProbability.window] using Nat.le_of_not_gt hnot

theorem linearPositions_card_ge_of_not_globalBad
    (shape : BatchShape) (answers : SamplingAnswerTape)
    (hgood : answers ∉ globalBad shape) :
    queryCount ≤
      (observedPositions (fun trial : Fin samplingTrials ↦
        rustLowPosition 13
          (scalarFromBlock
            (window linearPositionsOffset samplingTrials (by
              rw [productionSamplingSlots_eq]
              decide) answers trial)))).card := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood (.linearPositions)
  rw [badAt, mem_windowBad_iff, mem_positionBlockAbortRuns_iff] at hnot
  simpa [VeiledFlock.FixedWindowProbability.window] using Nat.le_of_not_gt hnot

theorem hadamardPositions_card_ge_of_not_globalBad
    (shape : BatchShape) (answers : SamplingAnswerTape)
    (hgood : answers ∉ globalBad shape) :
    queryCount ≤
      (observedPositions (fun trial : Fin samplingTrials ↦
        rustLowPosition 11
          (scalarFromBlock
            (window hadamardPositionsOffset samplingTrials (by
              rw [productionSamplingSlots_eq]
              decide) answers trial)))).card := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood
    (.hadamardPositions)
  rw [badAt, mem_windowBad_iff, mem_positionBlockAbortRuns_iff] at hnot
  simpa [VeiledFlock.FixedWindowProbability.window] using Nat.le_of_not_gt hnot

/-! ## Scalar-stage operational semantics -/

theorem acceptScalar_status_live_of_before_cap
    {shape : BatchShape} (failed : Finset GhashField)
    (round start : ℕ) (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hbefore : round - start + 1 < rejectionTrials) :
    (acceptScalar failed round start control answer).status = .live := by
  classical
  have hcap : round - start + 1 ≠ rejectionTrials := by omega
  by_cases hzero : round - start = 0
  · by_cases hfail : scalarFromBlock answer ∈ failed
    · have hone : 1 ≠ rejectionTrials := by decide
      simp [acceptScalar, hzero, hstatus, hfail, hone]
    · simp [acceptScalar, hzero, hstatus, hfail]
  · by_cases hdone : control.stageDone = true
    · simp [acceptScalar, hzero, hdone, hstatus]
    · by_cases hfail : scalarFromBlock answer ∈ failed <;>
        simp [acceptScalar, hzero, hdone, hstatus, hcap, hfail]

theorem acceptScalar_live_done_of_good
    {shape : BatchShape} (failed : Finset GhashField)
    (round start : ℕ) (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hgood : scalarFromBlock answer ∉ failed) :
    (acceptScalar failed round start control answer).status = .live ∧
      (acceptScalar failed round start control answer).stageDone = true := by
  classical
  by_cases hzero : round - start = 0
  · simp [acceptScalar, hzero, hgood, hstatus]
  · by_cases hdone : control.stageDone = true
    · simp [acceptScalar, hzero, hdone, hstatus]
    · simp [acceptScalar, hzero, hdone, hgood, hstatus]

theorem acceptScalar_preserves_live_done
    {shape : BatchShape} (failed : Finset GhashField)
    (round start : ℕ) (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hdone : control.stageDone = true)
    (hpositive : round - start ≠ 0) :
    (acceptScalar failed round start control answer).status = .live ∧
      (acceptScalar failed round start control answer).stageDone = true := by
  classical
  simp [acceptScalar, hpositive, hstatus, hdone]

theorem scalarLoop_status_live_of_lt
    {shape : BatchShape} (failed : Finset GhashField)
    (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hrounds : rounds < rejectionTrials)
    (hstatus : control.status = .live) :
    (iterateFrom (fun round ↦ acceptScalar failed round start) start rounds
      control answers).status = .live := by
  induction rounds with
  | zero => simpa [iterateFrom, iterateList] using hstatus
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      apply acceptScalar_status_live_of_before_cap failed _ start
      · exact ih (answers := fun index ↦ answers index.castSucc)
          (hrounds := by omega)
      · omega

theorem scalarLoop_live_done_of_exists
    {shape : BatchShape} (failed : Finset GhashField)
    (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hrounds : rounds ≤ rejectionTrials)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin rounds,
      scalarFromBlock (answers trial) ∉ failed) :
    (iterateFrom (fun round ↦ acceptScalar failed round start) start rounds
      control answers).status = .live ∧
    (iterateFrom (fun round ↦ acceptScalar failed round start) start rounds
      control answers).stageDone = true := by
  induction rounds with
  | zero => simp at hexists
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      by_cases hlast : scalarFromBlock (answers (Fin.last rounds)) ∈ failed
      · have hearlier : ∃ trial : Fin rounds,
            scalarFromBlock (answers trial.castSucc) ∉ failed := by
          rcases hexists with ⟨trial, htrial⟩
          refine ⟨Fin.castLT trial (by
            by_contra heq
            have : trial = Fin.last rounds := Fin.eq_last_of_not_lt heq
            subst trial
            exact htrial hlast), htrial⟩
        have hprefix := ih
          (answers := fun index ↦ answers index.castSucc)
          (hrounds := by omega) (hexists := hearlier)
        have hroundspos : 0 < rounds := by
          rcases hearlier with ⟨trial, _⟩
          exact Nat.zero_lt_of_lt trial.isLt
        have hsub : start + rounds - start = rounds := by omega
        exact acceptScalar_preserves_live_done failed _ start _ _
          hprefix.1 hprefix.2 (by rw [hsub]; omega)
      · have hprefix := scalarLoop_status_live_of_lt failed start rounds control
          (fun index ↦ answers index.castSucc) (by omega) hstatus
        exact acceptScalar_live_done_of_good failed _ start _ _ hprefix hlast

theorem iterateFrom_eq_scalarLoop
    {shape : BatchShape} (failed : Finset GhashField)
    (step : ℕ → Control shape → OracleBlock → Control shape)
    (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hrounds : rounds ≤ rejectionTrials)
    (hstatus : control.status = .live)
    (hstep : ∀ (trial : ℕ), trial < rejectionTrials →
      ∀ (current : Control shape) (answer : OracleBlock),
        current.status = .live →
        step (start + trial) current answer =
          acceptScalar failed (start + trial) start current answer) :
    iterateFrom step start rounds control answers =
      iterateFrom (fun round ↦ acceptScalar failed round start) start rounds
        control answers := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last, iterateFrom_succ_last,
        ih (hrounds := by omega)]
      rw [hstep rounds (by omega)]
      exact scalarLoop_status_live_of_lt failed start rounds control
        (fun index ↦ answers index.castSucc) (by omega) hstatus

/-- The six bounded scalar-rejection stages in the literal production
schedule. -/
inductive ScalarStage
  | blindChallenge
  | multiplicationAlpha
  | outerChallenge
  | linearRho
  | hadamardRho
  | productCoefficient
  deriving DecidableEq, Fintype

def scalarStageStart : ScalarStage → ℕ
  | .blindChallenge => blindChallengeOffset
  | .multiplicationAlpha => multiplicationAlphaOffset
  | .outerChallenge => outerChallengeOffset
  | .linearRho => linearRhoOffset
  | .hadamardRho => hadamardRhoOffset
  | .productCoefficient => productCoefficientOffset

noncomputable def scalarStageFailure : ScalarStage → Finset GhashField
  | .multiplicationAlpha => zeroOrOneFailure
  | _ => zeroFailure

set_option maxRecDepth 10000 in
theorem rawStep_scalarStage
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (stage : ScalarStage) (trial : ℕ) (htrial : trial < rejectionTrials)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins
        (scalarStageStart stage + trial) control answer =
      acceptScalar (scalarStageFailure stage)
        (scalarStageStart stage + trial) (scalarStageStart stage) control answer := by
  cases stage <;>
    simp only [scalarStageStart, scalarStageFailure] <;>
    simp [rawStep, hstatus] <;>
    norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
      equalityAttemptBlocks,
      zerocheckOffset, zerocheckWidth, blindStateOffset, blindStateWidth,
      blindGrindingOffset, blindGrindingWidth, blindChallengeOffset,
      multiplicationAlphaOffset, outerChallengeOffset,
      outerPositionsOffset, linearPositionsOffset, linearRhoOffset,
      hadamardPositionsOffset, hadamardRhoOffset,
      productCoefficientOffset, ligeritoOffset, ligeritoWidth,
      ligeritoSiteWidth, productionSamplingSlots, rejectionTrials,
      maxBlindTrials, maxLigeritoTrials, maxLigeritoSites,
      maxProgrammedPoints] at htrial ⊢ <;>
    simp (disch := omega) only [if_pos, if_neg]

theorem rawScalarStage_live_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (stage : ScalarStage) (control : Control shape)
    (answers : Fin rejectionTrials → OracleBlock)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin rejectionTrials,
      scalarFromBlock (answers trial) ∉ scalarStageFailure stage) :
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      (scalarStageStart stage) rejectionTrials control answers
    result.status = .live ∧ result.stageDone = true := by
  dsimp
  rw [iterateFrom_eq_scalarLoop (scalarStageFailure stage)
    (rawStep shape causalSecret completion witness coins)
    (scalarStageStart stage) rejectionTrials control answers
    (by rfl) hstatus (rawStep_scalarStage shape causalSecret completion
      witness coins stage)]
  exact scalarLoop_live_done_of_exists (scalarStageFailure stage)
    (scalarStageStart stage) rejectionTrials control answers (by rfl)
    hstatus hexists

/-! ## Distinct-position-stage operational semantics -/

def observedNatPositions {Answer : Type*} {rounds : ℕ}
    (project : Answer → ℕ) (answers : Fin rounds → Answer) :
    Finset ℕ :=
  Finset.univ.image (fun trial ↦ project (answers trial))

theorem observedNatPositions_succ {rounds : ℕ}
    (project : OracleBlock → ℕ) (answers : Fin (rounds + 1) → OracleBlock) :
    observedNatPositions project answers =
      insert (project (answers (Fin.last rounds)))
        (observedNatPositions project
          (fun trial : Fin rounds ↦ answers trial.castSucc)) := by
  classical
  ext position
  simp only [observedNatPositions, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_insert]
  constructor
  · rintro ⟨trial, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last trial with ⟨prior, rfl⟩ | rfl
    · exact Or.inr ⟨prior, rfl⟩
    · exact Or.inl rfl
  · rintro (hlast | ⟨trial, rfl⟩)
    · exact ⟨Fin.last rounds, hlast.symm⟩
    · exact ⟨trial.castSucc, rfl⟩

theorem observedNatPositions_card_eq
    {domain rounds : ℕ} (run : Fin rounds → Fin domain) :
    (observedNatPositions (fun block : Fin domain ↦ block.val) run).card =
      (observedPositions run).card := by
  classical
  unfold observedNatPositions observedPositions
  have hset : Finset.univ.image (fun trial ↦ (run trial).val) =
      (Finset.univ.image run).image (fun block : Fin domain ↦ block.val) := by
    ext position
    simp
  rw [hset, Finset.card_image_of_injective]
  exact Fin.val_injective

theorem acceptPositions_preserves_live_done
    {shape : BatchShape} (project : GhashField → ℕ)
    (target round start : ℕ) (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hdone : control.stageDone = true)
    (hpositive : round - start ≠ 0) :
    let result := acceptPositions project target start round control answer
    result.status = .live ∧ result.stageDone = true := by
  classical
  simp [acceptPositions, hpositive, hstatus, hdone]

theorem acceptPositions_eq_of_done
    {shape : BatchShape} (project : GhashField → ℕ)
    (target round start : ℕ) (control : Control shape) (answer : OracleBlock)
    (hdone : control.stageDone = true)
    (hpositive : round - start ≠ 0) :
    acceptPositions project target start round control answer = control := by
  classical
  simp [acceptPositions, hpositive, hdone]

theorem positionLoop_prefix_invariant
    {shape : BatchShape} (project : GhashField → ℕ) (target start rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hpositive : 0 < rounds) (hrounds : rounds < samplingTrials)
    (hstatus : control.status = .live) :
    let result := iterateFrom
      (fun round control answer ↦
        acceptPositions project target start round control answer)
      start rounds control answers
    result.status = .live ∧
      (result.stageDone = true → target ≤ result.positions.card) ∧
      (result.stageDone = false →
        result.positions = observedNatPositions
          (fun block ↦ project (scalarFromBlock block)) answers) := by
  induction rounds with
  | zero => omega
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      by_cases hroundszero : rounds = 0
      · subst rounds
        have hcap : 1 ≠ samplingTrials := by decide
        simp only [iterateFrom, List.ofFn_zero, iterateList]
        simp [acceptPositions, observedNatPositions, hstatus, hcap]
        split <;> simp_all
      · have hprefix := ih (fun index ↦ answers index.castSucc)
          (Nat.pos_of_ne_zero hroundszero) (by omega)
        dsimp only at hprefix
        let priorControl := (iterateFrom
          (fun round control answer ↦
            acceptPositions project target start round control answer)
          start rounds control (fun index ↦ answers index.castSucc) : Control shape)
        change priorControl.status = .live ∧
          (priorControl.stageDone = true → target ≤ priorControl.positions.card) ∧
          (priorControl.stageDone = false →
            priorControl.positions = observedNatPositions
              (fun block ↦ project (scalarFromBlock block))
              (fun index : Fin rounds ↦ answers index.castSucc)) at hprefix
        change
          (acceptPositions project target start (start + rounds) priorControl
              (answers (Fin.last rounds))).status = .live ∧
          ((acceptPositions project target start (start + rounds) priorControl
              (answers (Fin.last rounds))).stageDone = true →
            target ≤ (acceptPositions project target start (start + rounds)
              priorControl (answers (Fin.last rounds))).positions.card) ∧
          ((acceptPositions project target start (start + rounds) priorControl
              (answers (Fin.last rounds))).stageDone = false →
            (acceptPositions project target start (start + rounds) priorControl
              (answers (Fin.last rounds))).positions =
                observedNatPositions
                  (fun block ↦ project (scalarFromBlock block)) answers)
        have hsub : start + rounds - start = rounds := by omega
        have hoff : start + rounds - start ≠ 0 := by
          rw [hsub]
          exact hroundszero
        by_cases hdone : priorControl.stageDone = true
        · rw [acceptPositions_eq_of_done project target (start + rounds) start
            priorControl (answers (Fin.last rounds)) hdone hoff]
          refine ⟨hprefix.1, hprefix.2.1, ?_⟩
          intro hfalse
          simp [hdone] at hfalse
        · have hpositions := hprefix.2.2 (Bool.eq_false_of_not_eq_true hdone)
          let nextPositions : Finset ℕ := insert
            (project (scalarFromBlock (answers (Fin.last rounds)))) priorControl.positions
          by_cases htarget : target ≤ nextPositions.card
          · simp [acceptPositions, hroundszero, hdone, hprefix.1,
              nextPositions, htarget]
          · have hcap : rounds + 1 ≠ samplingTrials := by omega
            have hobs := observedNatPositions_succ
              (fun block ↦ project (scalarFromBlock block)) answers
            have heq : acceptPositions project target start (start + rounds)
                priorControl (answers (Fin.last rounds)) =
                { priorControl with
                  transcript := VeiledFlock.ProductionTranscriptFraming.afterScalar
                    priorControl.transcript (answers (Fin.last rounds))
                  positions := nextPositions
                  stageBlocks := priorControl.stageBlocks ++
                    [answers (Fin.last rounds)] } := by
              simp [acceptPositions, hroundszero, hdone, nextPositions,
                htarget, hcap]
            rw [heq]
            refine ⟨hprefix.1, ?_, ?_⟩
            · simp [hdone]
            · intro _
              simpa [nextPositions, hpositions] using hobs.symm

theorem positionLoop_status_live_of_lt
    {shape : BatchShape} (project : GhashField → ℕ) (target start rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hrounds : rounds < samplingTrials)
    (hstatus : control.status = .live) :
    (iterateFrom
      (fun round control answer ↦
        acceptPositions project target start round control answer)
      start rounds control answers).status = .live := by
  by_cases hzero : rounds = 0
  · subst rounds
    simpa [iterateFrom, iterateList] using hstatus
  · exact (positionLoop_prefix_invariant project target start rounds control
      answers (Nat.pos_of_ne_zero hzero) hrounds hstatus).1

theorem positionLoop_live_done_of_card
    {shape : BatchShape} (project : GhashField → ℕ) (target start total : ℕ)
    (control : Control shape) (answers : Fin total → OracleBlock)
    (htotal : total = samplingTrials)
    (hstatus : control.status = .live)
    (hcard : target ≤ (observedNatPositions
      (fun block ↦ project (scalarFromBlock block)) answers).card) :
    let result := iterateFrom
      (fun round control answer ↦
        acceptPositions project target start round control answer)
      start total control answers
    result.status = .live ∧ result.stageDone = true := by
  cases total with
  | zero => simp [samplingTrials] at htotal
  | succ rounds =>
      rw [iterateFrom_succ_last]
      have hroundspos : 0 < rounds := by
        norm_num [samplingTrials] at htotal
        omega
      have hprefix := positionLoop_prefix_invariant project target start rounds
        control (fun index ↦ answers index.castSucc) hroundspos (by omega) hstatus
      let priorControl := (iterateFrom
        (fun round control answer ↦
          acceptPositions project target start round control answer)
        start rounds control (fun index ↦ answers index.castSucc) : Control shape)
      change priorControl.status = .live ∧
        (priorControl.stageDone = true → target ≤ priorControl.positions.card) ∧
        (priorControl.stageDone = false →
          priorControl.positions = observedNatPositions
            (fun block ↦ project (scalarFromBlock block))
            (fun index : Fin rounds ↦ answers index.castSucc)) at hprefix
      change
        (acceptPositions project target start (start + rounds) priorControl
          (answers (Fin.last rounds))).status = .live ∧
        (acceptPositions project target start (start + rounds) priorControl
          (answers (Fin.last rounds))).stageDone = true
      have hsub : start + rounds - start = rounds := by omega
      have hoff : start + rounds - start ≠ 0 := by rw [hsub]; omega
      by_cases hdone : priorControl.stageDone = true
      · rw [acceptPositions_eq_of_done project target (start + rounds) start
          priorControl (answers (Fin.last rounds)) hdone hoff]
        exact ⟨hprefix.1, hdone⟩
      · have hpositions := hprefix.2.2 (Bool.eq_false_of_not_eq_true hdone)
        have hobs := observedNatPositions_succ
          (fun block ↦ project (scalarFromBlock block)) answers
        have htarget : target ≤
            (insert (project (scalarFromBlock (answers (Fin.last rounds))))
              priorControl.positions).card := by
          rw [hpositions, ← hobs]
          exact hcard
        simp [acceptPositions, hroundspos.ne', hdone, hprefix.1, htarget]

theorem iterateFrom_eq_positionLoop
    {shape : BatchShape} (project : GhashField → ℕ) (target : ℕ)
    (step : ℕ → Control shape → OracleBlock → Control shape)
    (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hrounds : rounds ≤ samplingTrials)
    (hstatus : control.status = .live)
    (hstep : ∀ (trial : ℕ), trial < samplingTrials →
      ∀ (current : Control shape) (answer : OracleBlock),
        current.status = .live →
        step (start + trial) current answer =
          acceptPositions project target start (start + trial) current answer) :
    iterateFrom step start rounds control answers =
      iterateFrom
        (fun round control answer ↦
          acceptPositions project target start round control answer)
        start rounds control answers := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last, iterateFrom_succ_last,
        ih (hrounds := by omega)]
      rw [hstep rounds (by omega)]
      exact positionLoop_status_live_of_lt project target start rounds control
        (fun index ↦ answers index.castSucc) (by omega) hstatus

inductive PositionStage
  | outer
  | linear
  | hadamard
  deriving DecidableEq, Fintype

def positionStageStart : PositionStage → ℕ
  | .outer => outerPositionsOffset
  | .linear => linearPositionsOffset
  | .hadamard => hadamardPositionsOffset

noncomputable def positionStageProject (shape : BatchShape) :
    PositionStage → GhashField → ℕ
  | .outer => fun value ↦ (rustLowPosition (m shape - 11) value).val
  | .linear => fun value ↦ (rustLowPosition 13 value).val
  | .hadamard => fun value ↦ (rustLowPosition 11 value).val

def positionStageTarget (shape : BatchShape) : PositionStage → ℕ
  | .outer => outerL0QueryCount shape
  | .linear => veilQueryCount
  | .hadamard => veilQueryCount

set_option maxRecDepth 10000 in
theorem rawStep_positionStage
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (stage : PositionStage) (trial : ℕ) (htrial : trial < samplingTrials)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins
        (positionStageStart stage + trial) control answer =
      acceptPositions (positionStageProject shape stage)
        (positionStageTarget shape stage) (positionStageStart stage)
        (positionStageStart stage + trial) control answer := by
  cases stage <;>
    simp only [positionStageStart, positionStageProject, positionStageTarget] <;>
    simp [rawStep, hstatus] <;>
    norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
      equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
      blindStateOffset, blindStateWidth, blindGrindingOffset,
      blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
      outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
      linearRhoOffset, hadamardPositionsOffset, hadamardRhoOffset,
      productCoefficientOffset, ligeritoOffset, ligeritoWidth,
      ligeritoSiteWidth, productionSamplingSlots, rejectionTrials,
      samplingTrials, maxBlindTrials, maxLigeritoTrials, maxLigeritoSites,
      maxProgrammedPoints] at htrial ⊢ <;>
    simp (disch := omega) only [if_pos, if_neg]

theorem rawPositionStage_live_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (stage : PositionStage) (control : Control shape)
    (answers : Fin samplingTrials → OracleBlock)
    (hstatus : control.status = .live)
    (hcard : positionStageTarget shape stage ≤
      (observedNatPositions
        (fun block ↦ positionStageProject shape stage (scalarFromBlock block))
        answers).card) :
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      (positionStageStart stage) samplingTrials control answers
    result.status = .live ∧ result.stageDone = true := by
  dsimp
  rw [iterateFrom_eq_positionLoop (positionStageProject shape stage)
    (positionStageTarget shape stage)
    (rawStep shape causalSecret completion witness coins)
    (positionStageStart stage) samplingTrials control answers
    (by rfl) hstatus (rawStep_positionStage shape causalSecret completion
      witness coins stage)]
  exact positionLoop_live_done_of_card (positionStageProject shape stage)
    (positionStageTarget shape stage) (positionStageStart stage) samplingTrials
    control answers rfl hstatus hcard

/-! ## Blind-grinding operational semantics -/

theorem blindGrindingStep_status_live_of_before_cap
    {shape : BatchShape} (round : ℕ) (control : Control shape)
    (answer : OracleBlock) (hstatus : control.status = .live)
    (hbefore : round - blindGrindingOffset + 1 < maxBlindTrials) :
    (blindGrindingStep round control answer).status = .live := by
  classical
  by_cases hdone : control.stageDone = true
  · simp [blindGrindingStep, hdone, hstatus]
  · have hcap : round - blindGrindingOffset + 1 ≠ maxBlindTrials := by omega
    by_cases hgood : blindGrindingGood answer <;>
      simp [blindGrindingStep, hdone, hgood, hstatus, hcap]

theorem blindGrindingStep_live_done_of_good
    {shape : BatchShape} (round : ℕ) (control : Control shape)
    (answer : OracleBlock) (hstatus : control.status = .live)
    (hgood : blindGrindingGood answer) :
    let result := blindGrindingStep round control answer
    result.status = .live ∧ result.stageDone = true := by
  classical
  by_cases hdone : control.stageDone = true <;>
    simp [blindGrindingStep, hdone, hgood, hstatus]

theorem blindGrindingStep_preserves_live_done
    {shape : BatchShape} (round : ℕ) (control : Control shape)
    (answer : OracleBlock) (hstatus : control.status = .live)
    (hdone : control.stageDone = true) :
    let result := blindGrindingStep round control answer
    result.status = .live ∧ result.stageDone = true := by
  simp [blindGrindingStep, hdone, hstatus]

theorem blindGrindingLoop_status_live_of_lt
    {shape : BatchShape} (rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock) (hrounds : rounds < maxBlindTrials)
    (hstatus : control.status = .live) :
    (iterateFrom blindGrindingStep blindGrindingOffset rounds control answers).status =
      .live := by
  induction rounds with
  | zero => simpa [iterateFrom, iterateList] using hstatus
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      apply blindGrindingStep_status_live_of_before_cap
      · exact ih (answers := fun index ↦ answers index.castSucc)
          (hrounds := by omega)
      · omega

theorem blindGrindingLoop_live_done_of_exists
    {shape : BatchShape} (rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock) (hrounds : rounds ≤ maxBlindTrials)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin rounds, blindGrindingGood (answers trial)) :
    let result := iterateFrom blindGrindingStep blindGrindingOffset rounds
      control answers
    result.status = .live ∧ result.stageDone = true := by
  induction rounds with
  | zero => simp at hexists
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      by_cases hlast : blindGrindingGood (answers (Fin.last rounds))
      · exact blindGrindingStep_live_done_of_good _ _ _
          (blindGrindingLoop_status_live_of_lt rounds control
            (fun index ↦ answers index.castSucc) (by omega) hstatus) hlast
      · have hearlier : ∃ trial : Fin rounds,
            blindGrindingGood (answers trial.castSucc) := by
          rcases hexists with ⟨trial, htrial⟩
          refine ⟨Fin.castLT trial (by
            by_contra heq
            have : trial = Fin.last rounds := Fin.eq_last_of_not_lt heq
            subst trial
            exact hlast htrial), htrial⟩
        have hprefix := ih (answers := fun index ↦ answers index.castSucc)
          (hrounds := by omega) (hexists := hearlier)
        exact blindGrindingStep_preserves_live_done _ _ _ hprefix.1 hprefix.2

set_option maxRecDepth 10000 in
theorem rawStep_blindGrinding
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (trial : ℕ) (htrial : trial < maxBlindTrials)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins
        (blindGrindingOffset + trial) control answer =
      blindGrindingStep (blindGrindingOffset + trial) control answer := by
  simp [rawStep, hstatus]
  norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
    equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
    blindStateOffset, blindStateWidth, blindGrindingOffset,
    blindGrindingWidth, blindChallengeOffset, multiplicationAlphaOffset,
    outerChallengeOffset, outerPositionsOffset, linearPositionsOffset,
    linearRhoOffset, hadamardPositionsOffset, hadamardRhoOffset,
    productCoefficientOffset, ligeritoOffset, ligeritoWidth,
    ligeritoSiteWidth, productionSamplingSlots, rejectionTrials,
    maxBlindTrials, maxLigeritoTrials, maxLigeritoSites,
    maxProgrammedPoints] at htrial ⊢
  simp (disch := omega) only [if_pos, if_neg]

theorem rawStep_blindState
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins blindStateOffset
        control answer =
      { control with
          powState := some answer
          stageDone := false
          stageBlocks := [] } := by
  simp [rawStep, hstatus]
  norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
    equalityAttemptBlocks, zerocheckOffset, zerocheckWidth,
    blindStateOffset, blindStateWidth, blindGrindingOffset,
    maxProgrammedPoints]

theorem iterateFrom_eq_blindGrinding
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock) (hrounds : rounds ≤ maxBlindTrials)
    (hstatus : control.status = .live) :
    iterateFrom (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset rounds control answers =
      iterateFrom blindGrindingStep blindGrindingOffset rounds control answers := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last, iterateFrom_succ_last,
        ih (hrounds := by omega)]
      rw [rawStep_blindGrinding shape causalSecret completion witness coins
        rounds (by omega)]
      exact blindGrindingLoop_status_live_of_lt rounds control
        (fun index ↦ answers index.castSucc) (by omega) hstatus

theorem rawBlindGrinding_live_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (stateAnswer : OracleBlock)
    (answers : Fin maxBlindTrials → OracleBlock)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin maxBlindTrials,
      blindGrindingGood (answers trial)) :
    let withState := rawStep shape causalSecret completion witness coins
      blindStateOffset control stateAnswer
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      blindGrindingOffset maxBlindTrials withState answers
    result.status = .live ∧ result.stageDone = true := by
  dsimp
  rw [rawStep_blindState shape causalSecret completion witness coins control
    stateAnswer hstatus]
  let withState : Control shape :=
    { control with
        powState := some stateAnswer
        stageDone := false
        stageBlocks := [] }
  have hstate : withState.status = .live := by simp [withState, hstatus]
  rw [iterateFrom_eq_blindGrinding shape causalSecret completion witness coins
    maxBlindTrials withState answers (by rfl) hstate]
  exact blindGrindingLoop_live_done_of_exists maxBlindTrials withState answers
    (by rfl) hstate hexists

/-! ## Skip, equality-point, and zerocheck operational semantics -/

def equalityLiveBlocks (shape : BatchShape) (blocks : Fin 7 → OracleBlock) :
    List OracleBlock :=
  List.ofFn (fun index : Fin (equalityBlockCount shape) ↦
    blocks (Fin.castLE (equalityBlockCount_le_seven shape) index))

theorem sliceFrom_equalityLiveBlocks (shape : BatchShape)
    (blocks : Fin 7 → OracleBlock) :
    sliceFromBlocks (m shape - kSkip - 7) (equalityLiveBlocks shape blocks) =
      sliceFromBlocks (m shape - kSkip - 7) (List.ofFn blocks) := by
  funext index
  cases shape <;> fin_cases index <;> rfl

theorem equalityLiveBlocks_eq_take (shape : BatchShape)
    (blocks : Fin 7 → OracleBlock) :
    equalityLiveBlocks shape blocks =
      (List.ofFn blocks).take (equalityBlockCount shape) := by
  unfold equalityLiveBlocks
  exact Fin.ofFn_take_eq_take_ofFn (equalityBlockCount_le_seven shape) blocks

set_option maxRecDepth 10000 in
theorem equalityAttempt_live_some_of_accepted
    (shape : BatchShape) (attempt : ℕ) (control : Control shape)
    (blocks : Fin 7 → OracleBlock)
    (hstatus : control.status = .live)
    (hnone : control.equalityPoint = none)
    (hskip : control.skip.isSome = true)
    (haccepted : accepted
      (sliceFromBlocks (m shape - kSkip - 7) (List.ofFn blocks))) :
    let result := iterateFrom (equalityStep shape)
      (equalityOffset + attempt * equalityAttemptBlocks) 7 control blocks
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  have hoff (counter : ℕ) :
      equalityOffset + attempt * 7 + counter - equalityOffset =
        attempt * 7 + counter := by omega
  have hoff2 : equalityOffset + attempt * 7 + 1 + 1 - equalityOffset =
      attempt * 7 + 2 := by omega
  have hoff3 : equalityOffset + attempt * 7 + 1 + 1 + 1 - equalityOffset =
      attempt * 7 + 3 := by omega
  have hoff4 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 - equalityOffset =
      attempt * 7 + 4 := by omega
  have hoff5 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 + 1 -
      equalityOffset = attempt * 7 + 5 := by omega
  have hoff6 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 + 1 + 1 -
      equalityOffset = attempt * 7 + 6 := by omega
  have hdiv4 : (attempt * 7 + 4) / 7 = attempt := by omega
  have hdiv5 : (attempt * 7 + 5) / 7 = attempt := by omega
  have hdiv6 : (attempt * 7 + 6) / 7 = attempt := by omega
  have hslice := sliceFrom_equalityLiveBlocks shape blocks
  cases hskipValue : control.skip with
  | none => simp [hskipValue] at hskip
  | some skip =>
      cases shape <;>
        simp [iterateFrom, iterateList, equalityStep, equalityBlockCount,
          equalityAttemptBlocks,
          m, kSkip, rejectionTrials,
          hoff, hoff2, hoff3, hoff4, hoff5, hoff6, hdiv4, hdiv5, hdiv6,
          equalityLiveBlocks,  hnone, hstatus, hskipValue]
          at haccepted hslice ⊢ <;>
        simp_all

set_option maxRecDepth 10000 in
theorem equalityAttempt_live_none_of_rejected_before_cap
    (shape : BatchShape) (attempt : ℕ) (control : Control shape)
    (blocks : Fin 7 → OracleBlock)
    (hstatus : control.status = .live)
    (hnone : control.equalityPoint = none)
    (hrejected : ¬accepted
      (sliceFromBlocks (m shape - kSkip - 7) (List.ofFn blocks)))
    (hbefore : attempt + 1 < rejectionTrials) :
    let result := iterateFrom (equalityStep shape)
      (equalityOffset + attempt * equalityAttemptBlocks) 7 control blocks
    result.status = .live ∧ result.equalityPoint = none := by
  have hoff (counter : ℕ) :
      equalityOffset + attempt * 7 + counter - equalityOffset =
        attempt * 7 + counter := by omega
  have hoff2 : equalityOffset + attempt * 7 + 1 + 1 - equalityOffset =
      attempt * 7 + 2 := by omega
  have hoff3 : equalityOffset + attempt * 7 + 1 + 1 + 1 - equalityOffset =
      attempt * 7 + 3 := by omega
  have hoff4 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 - equalityOffset =
      attempt * 7 + 4 := by omega
  have hoff5 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 + 1 -
      equalityOffset = attempt * 7 + 5 := by omega
  have hoff6 : equalityOffset + attempt * 7 + 1 + 1 + 1 + 1 + 1 + 1 -
      equalityOffset = attempt * 7 + 6 := by omega
  have hdiv4 : (attempt * 7 + 4) / 7 = attempt := by omega
  have hdiv5 : (attempt * 7 + 5) / 7 = attempt := by omega
  have hdiv6 : (attempt * 7 + 6) / 7 = attempt := by omega
  have hne4 : (attempt * 7 + 4) / 7 + 1 ≠ rejectionTrials := by
    rw [hdiv4]
    omega
  have hne5 : (attempt * 7 + 5) / 7 + 1 ≠ rejectionTrials := by
    rw [hdiv5]
    omega
  have hne6 : (attempt * 7 + 6) / 7 + 1 ≠ rejectionTrials := by
    rw [hdiv6]
    omega
  have hlast4 : (attempt * 7 + 4) / 7 ≠ 4095 := by
    rw [hdiv4]
    norm_num [rejectionTrials] at hbefore ⊢
    omega
  have hlast5 : (attempt * 7 + 5) / 7 ≠ 4095 := by
    rw [hdiv5]
    norm_num [rejectionTrials] at hbefore ⊢
    omega
  have hlast6 : (attempt * 7 + 6) / 7 ≠ 4095 := by
    rw [hdiv6]
    norm_num [rejectionTrials] at hbefore ⊢
    omega
  have hslice := sliceFrom_equalityLiveBlocks shape blocks
  cases shape <;>
    simp [iterateFrom, iterateList, equalityStep, equalityBlockCount,
      equalityAttemptBlocks, m, kSkip, rejectionTrials,
      hoff, hoff2, hoff3, hoff4, hoff5, hoff6, equalityLiveBlocks,
      hdiv4, hdiv5, hdiv6,
      hnone, hstatus] at hrejected hslice ⊢ <;>
    simp_all

theorem equalityStep_skip (shape : BatchShape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (equalityStep shape round control answer).skip = control.skip := by
  classical
  simp [equalityStep]
  repeat' (first | rfl | split)

theorem iterateEquality_skip (shape : BatchShape) (start rounds : ℕ)
    (control : Control shape) (blocks : Fin rounds → OracleBlock) :
    (iterateFrom (equalityStep shape) start rounds control blocks).skip =
      control.skip := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last, equalityStep_skip]
      exact ih (blocks := fun index ↦ blocks index.castSucc)

theorem equalityAttempt_eq_of_some (shape : BatchShape) (attempt : ℕ)
    (control : Control shape) (blocks : Fin 7 → OracleBlock)
    (hsome : control.equalityPoint.isSome = true) :
    iterateFrom (equalityStep shape)
      (equalityOffset + attempt * equalityAttemptBlocks) 7 control blocks =
        control := by
  cases hpoint : control.equalityPoint with
  | none => simp [hpoint] at hsome
  | some point =>
      simp [iterateFrom, iterateList, equalityStep, hpoint]

noncomputable def equalityAttemptsRun (shape : BatchShape) :
    (attempts : ℕ) → Control shape →
      (Fin attempts → Fin 7 → OracleBlock) → Control shape
  | 0, control, _ => control
  | attempts + 1, control, blocks =>
      iterateFrom (equalityStep shape)
        (equalityOffset + attempts * equalityAttemptBlocks) 7
        (equalityAttemptsRun shape attempts control
          (fun index ↦ blocks index.castSucc))
        (blocks (Fin.last attempts))

noncomputable def flatAttemptsEquiv (attempts : ℕ) :
    (Fin (attempts * 7) → OracleBlock) ≃
      (Fin attempts → Fin 7 → OracleBlock) :=
  (Equiv.arrowCongr
      (finProdFinEquiv (m := attempts) (n := 7))
      (Equiv.refl OracleBlock)).symm.trans
    (Equiv.curry (Fin attempts) (Fin 7) OracleBlock)

@[simp]
theorem flatAttemptsEquiv_apply (attempts : ℕ)
    (flat : Fin (attempts * 7) → OracleBlock)
    (attempt : Fin attempts) (counter : Fin 7) :
    flatAttemptsEquiv attempts flat attempt counter =
      flat ⟨counter.val + 7 * attempt.val, by
        have ha := attempt.isLt
        have hc := counter.isLt
        nlinarith⟩ := by
  rfl

theorem equalityAttemptsRun_eq_flat (shape : BatchShape) (attempts : ℕ)
    (control : Control shape) (flat : Fin (attempts * 7) → OracleBlock) :
    equalityAttemptsRun shape attempts control
        (flatAttemptsEquiv attempts flat) =
      iterateFrom (equalityStep shape) equalityOffset (attempts * 7)
        control flat := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      have hsize : (attempts + 1) * 7 = attempts * 7 + 7 := by omega
      let flat' : Fin (attempts * 7 + 7) → OracleBlock :=
        fun index ↦ flat (Fin.cast hsize.symm index)
      let prefixFlat : Fin (attempts * 7) → OracleBlock :=
        fun index ↦ flat' (Fin.castAdd 7 index)
      have hprefix :
          (fun index : Fin attempts ↦
            flatAttemptsEquiv (attempts + 1) flat index.castSucc) =
            flatAttemptsEquiv attempts prefixFlat := by
        funext attempt counter
        simp only [flatAttemptsEquiv_apply]
        apply congrArg flat
        apply Fin.ext
        simp
      have hlast : flatAttemptsEquiv (attempts + 1) flat
            (Fin.last attempts) =
          (fun counter : Fin 7 ↦ flat' (Fin.natAdd (attempts * 7) counter)) := by
        funext counter
        simp only [flatAttemptsEquiv_apply]
        apply congrArg flat
        apply Fin.ext
        simp
        omega
      rw [equalityAttemptsRun, hprefix, hlast,
        ih (flat := prefixFlat)]
      have hadd := iterateFrom_add (equalityStep shape) equalityOffset
        (attempts * 7) 7 control flat'
      rw [show equalityOffset + attempts * 7 =
          equalityOffset + attempts * equalityAttemptBlocks by
        simp [equalityAttemptBlocks]] at hadd
      rw [iterateFrom_cast (equalityStep shape) equalityOffset
        ((attempts + 1) * 7) (attempts * 7 + 7) control flat hsize]
      exact hadd.symm

theorem equalityFlatEquiv_eq_flatAttemptsEquiv :
    equalityFlatEquiv = flatAttemptsEquiv rejectionTrials := by
  rfl

theorem equalityStep_live_implies (shape : BatchShape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock)
    (hlive : (equalityStep shape round control answer).status = .live) :
    control.status = .live := by
  classical
  grind [equalityStep]

theorem iterateEquality_live_implies_initial
    (shape : BatchShape) (start rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hlive : (iterateFrom (equalityStep shape) start rounds control answers).status =
      .live) :
    control.status = .live := by
  induction rounds with
  | zero => simpa [iterateFrom, iterateList] using hlive
  | succ rounds ih =>
      rw [iterateFrom_succ_last] at hlive
      exact ih (answers := fun index ↦ answers index.castSucc)
        (equalityStep_live_implies shape _ _ _ hlive)

set_option maxRecDepth 10000 in
theorem rawStep_equality
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (trial : ℕ) (htrial : trial < equalityWidth)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins
        (equalityOffset + trial) control answer =
      equalityStep shape (equalityOffset + trial) control answer := by
  have hskip : ¬equalityOffset + trial < equalitySkipBlocks := by
    norm_num [equalitySkipBlocks, equalityOffset]
  have hequality : equalityOffset + trial < zerocheckOffset := by
    norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
      equalityAttemptBlocks, zerocheckOffset, rejectionTrials] at htrial ⊢
    omega
  simp [rawStep, hstatus, hskip, hequality]

theorem rawEquality_eq_of_final_live
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hrounds : rounds ≤ equalityWidth)
    (hfinal : (iterateFrom (equalityStep shape) equalityOffset rounds control
      answers).status = .live) :
    iterateFrom (rawStep shape causalSecret completion witness coins)
        equalityOffset rounds control answers =
      iterateFrom (equalityStep shape) equalityOffset rounds control answers := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last, iterateFrom_succ_last]
      have hprefix : (iterateFrom (equalityStep shape) equalityOffset rounds
          control (fun index ↦ answers index.castSucc)).status = .live := by
        rw [iterateFrom_succ_last] at hfinal
        exact equalityStep_live_implies shape _ _ _ hfinal
      rw [ih (hrounds := by omega) (hfinal := hprefix),
        rawStep_equality shape causalSecret completion witness coins rounds
          (by omega)]
      exact hprefix

theorem equalityAttemptsRun_skip (shape : BatchShape) (attempts : ℕ)
    (control : Control shape) (blocks : Fin attempts → Fin 7 → OracleBlock) :
    (equalityAttemptsRun shape attempts control blocks).skip = control.skip := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      rw [equalityAttemptsRun, iterateEquality_skip,
        ih (blocks := fun index ↦ blocks index.castSucc)]

theorem equalityAttemptsRun_status_live_of_lt
    (shape : BatchShape) (attempts : ℕ) (control : Control shape)
    (blocks : Fin attempts → Fin 7 → OracleBlock)
    (hattempts : attempts < rejectionTrials)
    (hstatus : control.status = .live)
    (hskip : control.skip.isSome = true) :
    (equalityAttemptsRun shape attempts control blocks).status = .live := by
  induction attempts with
  | zero => exact hstatus
  | succ attempts ih =>
      let priorControl := equalityAttemptsRun shape attempts control
        (fun index ↦ blocks index.castSucc)
      have hpriorStatus : priorControl.status = .live :=
        ih (blocks := fun index ↦ blocks index.castSucc)
          (hattempts := by omega)
      have hpriorSkip : priorControl.skip.isSome = true := by
        have hskipEq := equalityAttemptsRun_skip shape attempts control
          (fun index ↦ blocks index.castSucc)
        rw [hskipEq]
        exact hskip
      change (iterateFrom (equalityStep shape)
        (equalityOffset + attempts * equalityAttemptBlocks) 7 priorControl
        (blocks (Fin.last attempts))).status = .live
      cases hpoint : priorControl.equalityPoint with
      | some point =>
          rw [equalityAttempt_eq_of_some shape attempts priorControl
            (blocks (Fin.last attempts)) (by simp [hpoint])]
          exact hpriorStatus
      | none =>
          by_cases haccepted : accepted (sliceFromBlocks
            (m shape - kSkip - 7) (List.ofFn (blocks (Fin.last attempts))))
          · exact (equalityAttempt_live_some_of_accepted shape attempts
              priorControl (blocks (Fin.last attempts)) hpriorStatus hpoint
              hpriorSkip haccepted).1
          · exact (equalityAttempt_live_none_of_rejected_before_cap shape attempts
              priorControl (blocks (Fin.last attempts)) hpriorStatus hpoint
              haccepted (by omega)).1

theorem equalityAttemptsRun_live_some_of_exists
    (shape : BatchShape) (attempts : ℕ) (control : Control shape)
    (blocks : Fin attempts → Fin 7 → OracleBlock)
    (hattempts : attempts ≤ rejectionTrials)
    (hstatus : control.status = .live)
    (hskip : control.skip.isSome = true)
    (hexists : ∃ attempt : Fin attempts,
      accepted (sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (blocks attempt)))) :
    let result := equalityAttemptsRun shape attempts control blocks
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  induction attempts with
  | zero => simp at hexists
  | succ attempts ih =>
      let priorControl := equalityAttemptsRun shape attempts control
        (fun index ↦ blocks index.castSucc)
      change (iterateFrom (equalityStep shape)
          (equalityOffset + attempts * equalityAttemptBlocks) 7 priorControl
          (blocks (Fin.last attempts))).status = .live ∧
        (iterateFrom (equalityStep shape)
          (equalityOffset + attempts * equalityAttemptBlocks) 7 priorControl
          (blocks (Fin.last attempts))).equalityPoint.isSome = true
      by_cases hlast : accepted (sliceFromBlocks (m shape - kSkip - 7)
          (List.ofFn (blocks (Fin.last attempts))))
      · have hpriorStatus := equalityAttemptsRun_status_live_of_lt shape attempts
          control (fun index ↦ blocks index.castSucc) (by omega) hstatus hskip
        have hpriorSkip : priorControl.skip.isSome = true := by
          have hskipEq := equalityAttemptsRun_skip shape attempts control
            (fun index ↦ blocks index.castSucc)
          rw [hskipEq]
          exact hskip
        cases hpoint : priorControl.equalityPoint with
        | some point =>
            rw [equalityAttempt_eq_of_some shape attempts priorControl
              (blocks (Fin.last attempts)) (by simp [hpoint])]
            exact ⟨hpriorStatus, by simp [hpoint]⟩
        | none =>
            exact equalityAttempt_live_some_of_accepted shape attempts
              priorControl (blocks (Fin.last attempts)) hpriorStatus hpoint
              hpriorSkip hlast
      · have hearlier : ∃ attempt : Fin attempts,
            accepted (sliceFromBlocks (m shape - kSkip - 7)
              (List.ofFn (blocks attempt.castSucc))) := by
          rcases hexists with ⟨attempt, hattempt⟩
          refine ⟨Fin.castLT attempt (by
            by_contra heq
            have : attempt = Fin.last attempts := Fin.eq_last_of_not_lt heq
            subst attempt
            exact hlast hattempt), hattempt⟩
        have hprior := ih (blocks := fun index ↦ blocks index.castSucc)
          (hattempts := by omega) (hexists := hearlier)
        rw [equalityAttempt_eq_of_some shape attempts priorControl
          (blocks (Fin.last attempts)) hprior.2]
        exact hprior

theorem equalityFlat_live_some
    (shape : BatchShape) (control : Control shape)
    (flat : Fin equalityWidth → OracleBlock)
    (hstatus : control.status = .live)
    (hskip : control.skip.isSome = true)
    (hexists : ∃ attempt : Fin rejectionTrials,
      accepted (sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (equalityFlatEquiv flat attempt)))) :
    let result := iterateFrom (equalityStep shape) equalityOffset equalityWidth
      control flat
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  have hrun := equalityAttemptsRun_live_some_of_exists shape rejectionTrials
    control (equalityFlatEquiv flat) (by rfl) hstatus hskip hexists
  change
    (equalityAttemptsRun shape rejectionTrials control
      (flatAttemptsEquiv rejectionTrials flat)).status = .live ∧
    (equalityAttemptsRun shape rejectionTrials control
      (flatAttemptsEquiv rejectionTrials flat)).equalityPoint.isSome = true at hrun
  rw [equalityAttemptsRun_eq_flat] at hrun
  simpa [equalityWidth, equalityAttemptBlocks] using hrun

theorem rawEquality_live_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (control : Control shape) (answers : Fin equalityWidth → OracleBlock)
    (hstatus : control.status = .live)
    (hskip : control.skip.isSome = true)
    (hexists : ∃ attempt : Fin rejectionTrials,
      accepted (sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (equalityFlatEquiv answers attempt)))) :
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      equalityOffset equalityWidth control answers
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  have hlocal := equalityFlat_live_some shape control answers hstatus hskip
    hexists
  rw [rawEquality_eq_of_final_live shape causalSecret completion witness coins
    equalityWidth control answers (by rfl) hlocal.1]
  exact hlocal

noncomputable def afterSkipControl (shape : BatchShape) (prelude : List Byte)
    (blocks : Fin equalitySkipBlocks → OracleBlock) : Control shape :=
  let blockList := List.ofFn blocks
  let skip := sliceFromBlocks 6 blockList
  { initialControl shape prelude with
    skipBlocks := blockList
    skip := some skip
    transcript := VeiledFlock.ProductionTranscriptFraming.afterSlice prelude skip }

set_option maxRecDepth 10000 in
theorem rawSkipPhase_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (blocks : Fin equalitySkipBlocks → OracleBlock) :
    iterateFrom (rawStep shape causalSecret completion witness coins) 0
        equalitySkipBlocks (initialControl shape prelude) blocks =
      afterSkipControl shape prelude blocks := by
  simp [iterateFrom, iterateList, rawStep, afterSkipControl, initialControl,
    equalitySkipBlocks]

@[simp]
theorem afterSkipControl_status (shape : BatchShape) (prelude : List Byte)
    (blocks : Fin equalitySkipBlocks → OracleBlock) :
    (afterSkipControl shape prelude blocks).status = .live := by
  simp [afterSkipControl, initialControl]

@[simp]
theorem afterSkipControl_skip_isSome (shape : BatchShape) (prelude : List Byte)
    (blocks : Fin equalitySkipBlocks → OracleBlock) :
    (afterSkipControl shape prelude blocks).skip.isSome = true := by
  simp [afterSkipControl]

@[simp]
theorem afterSkipControl_equality_none (shape : BatchShape) (prelude : List Byte)
    (blocks : Fin equalitySkipBlocks → OracleBlock) :
    (afterSkipControl shape prelude blocks).equalityPoint = none := by
  simp [afterSkipControl, initialControl]

theorem zerocheckStep_preserves_live_and_equality
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hequality : control.equalityPoint.isSome = true) :
    let result := zerocheckStep shape causalSecret completion witness coins
      round control answer
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  cases hpoint : control.equalityPoint with
  | none => simp [hpoint] at hequality
  | some point =>
      simp [zerocheckStep, hpoint, hstatus]
      split <;> simp_all ; split <;> simp_all

set_option maxRecDepth 10000 in
theorem rawStep_zerocheck
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (trial : ℕ) (htrial : trial < maxProgrammedPoints)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins
        (zerocheckOffset + trial) control answer =
      zerocheckStep shape causalSecret completion witness coins
        (zerocheckOffset + trial) control answer := by
  have hskip : ¬zerocheckOffset + trial < equalitySkipBlocks := by
    norm_num [equalitySkipBlocks, equalityOffset, equalityWidth,
      equalityAttemptBlocks, zerocheckOffset, rejectionTrials]
    omega
  have hequality : ¬zerocheckOffset + trial < zerocheckOffset := by omega
  have hzero : zerocheckOffset + trial < blindStateOffset := by
    norm_num [zerocheckWidth, blindStateOffset, maxProgrammedPoints] at htrial ⊢
    omega
  simp [rawStep, hstatus, hskip, hequality, hzero]

theorem rawZerocheck_live_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (rounds : ℕ) (control : Control shape)
    (answers : Fin rounds → OracleBlock)
    (hrounds : rounds ≤ maxProgrammedPoints)
    (hstatus : control.status = .live)
    (hequality : control.equalityPoint.isSome = true) :
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      zerocheckOffset rounds control answers
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  induction rounds with
  | zero => simpa [iterateFrom, iterateList] using And.intro hstatus hequality
  | succ rounds ih =>
      have hprior := ih (answers := fun index ↦ answers index.castSucc)
        (hrounds := by omega)
      rw [iterateFrom_succ_last,
        rawStep_zerocheck shape causalSecret completion witness coins rounds
          (by omega) _ _ hprior.1]
      exact zerocheckStep_preserves_live_and_equality shape causalSecret
        completion witness coins _ _ _ hprior.1 hprior.2

/-! ## Ligerito grinding-site operational semantics -/

def ligeritoSiteStart (site : Fin maxLigeritoSites) : ℕ :=
  ligeritoOffset + site.val * ligeritoSiteWidth

def ligeritoSiteTerminalStatus (site : Fin maxLigeritoSites) : Status :=
  if site.val + 1 = maxLigeritoSites then .success else .live

theorem ligerito_trial_offset (site : Fin maxLigeritoSites)
    (trial : ℕ) (htrial : trial < maxLigeritoTrials) :
    (ligeritoSiteStart site + 1 + trial - ligeritoOffset) %
        ligeritoSiteWidth = 1 + trial ∧
      (ligeritoSiteStart site + 1 + trial - ligeritoOffset) /
        ligeritoSiteWidth = site.val := by
  unfold ligeritoSiteStart
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
  have hrem : 1 + trial < ligeritoSiteWidth := by
    norm_num [ligeritoSiteWidth, maxLigeritoTrials] at htrial ⊢
    omega
  constructor
  · exact Nat.mul_add_mod_of_lt hrem
  · have hwidth : 0 < ligeritoSiteWidth := by
      norm_num [ligeritoSiteWidth, maxLigeritoTrials]
    rw [Nat.mul_comm site.val ligeritoSiteWidth,
      Nat.mul_add_div hwidth, Nat.div_eq_of_lt hrem, Nat.add_zero]

theorem ligerito_start_offset (site : Fin maxLigeritoSites) :
    (ligeritoSiteStart site - ligeritoOffset) % ligeritoSiteWidth = 0 ∧
      (ligeritoSiteStart site - ligeritoOffset) / ligeritoSiteWidth = site.val := by
  unfold ligeritoSiteStart
  rw [Nat.add_sub_cancel_left, Nat.mul_comm site.val ligeritoSiteWidth]
  have hwidth : 0 < ligeritoSiteWidth := by
    norm_num [ligeritoSiteWidth, maxLigeritoTrials]
  exact ⟨Nat.mul_mod_right _ _, Nat.mul_div_right _ hwidth⟩

theorem ligeritoStep_at_start {shape : BatchShape}
    (site : Fin maxLigeritoSites) (control : Control shape)
    (answer : OracleBlock) :
    ligeritoStep (ligeritoSiteStart site) control answer =
      { control with
        powState := some answer
        stageDone := false
        stageBlocks := [] } := by
  have hoff := (ligerito_start_offset site).1
  simp [ligeritoStep, hoff]

theorem ligeritoStep_trial_good {shape : BatchShape}
    (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hdone : control.stageDone = false)
    (hgood : rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide) answer) :
    let result := ligeritoStep (ligeritoSiteStart site + 1 + trial)
      control answer
    result.status = ligeritoSiteTerminalStatus site ∧
      result.stageDone = true := by
  have hoff := ligerito_trial_offset site trial htrial
  unfold ligeritoStep
  dsimp only
  rw [hoff.1, hoff.2]
  have hpositive : 1 + trial ≠ 0 := by omega
  by_cases hlast : site.val + 1 = maxLigeritoSites <;>
    simp [ hstatus, hdone, hgood, hlast,
      ligeritoSiteTerminalStatus]

theorem ligeritoStep_trial_bad_before_cap {shape : BatchShape}
    (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial + 1 < maxLigeritoTrials)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live)
    (hdone : control.stageDone = false)
    (hbad : ¬rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide) answer) :
    let result := ligeritoStep (ligeritoSiteStart site + 1 + trial)
      control answer
    result.status = .live ∧ result.stageDone = false := by
  have hoff := ligerito_trial_offset site trial (by omega)
  unfold ligeritoStep
  dsimp only
  rw [hoff.1, hoff.2]
  have hpositive : 1 + trial ≠ 0 := by omega
  have hcap : 1 + trial ≠ maxLigeritoTrials := by omega
  simp [ hstatus, hdone, hbad, hcap]

theorem not_before_ligerito {round bound : ℕ}
    (hbound : bound ≤ ligeritoOffset) (hround : ligeritoOffset ≤ round) :
    ¬round < bound := by
  omega

set_option maxRecDepth 10000 in
theorem rawStep_ligeritoStart
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (control : Control shape)
    (answer : OracleBlock) (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins
        (ligeritoSiteStart site) control answer =
      ligeritoStep (ligeritoSiteStart site) control answer := by
  have hlig : ligeritoSiteStart site < productionSamplingSlots := by
    unfold ligeritoSiteStart productionSamplingSlots ligeritoWidth
    have hwidth : 0 < ligeritoSiteWidth := by
      unfold ligeritoSiteWidth
      omega
    nlinarith [site.isLt]
  have hbefore : ligeritoOffset ≤ ligeritoSiteStart site := by
    unfold ligeritoSiteStart
    omega
  unfold rawStep
  rw [if_neg (by simp [hstatus])]
  simp only [
    dif_neg (not_before_ligerito (by decide : equalitySkipBlocks ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : zerocheckOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindStateOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindGrindingOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : multiplicationAlphaOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : productCoefficientOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_lt_of_ge hbefore), dif_pos hlig]

set_option maxRecDepth 10000 in
theorem rawStep_ligeritoTrial
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = .live) :
    rawStep shape causalSecret completion witness coins
        (ligeritoSiteStart site + 1 + trial) control answer =
      ligeritoStep (ligeritoSiteStart site + 1 + trial) control answer := by
  have hlig : ligeritoSiteStart site + 1 + trial <
      productionSamplingSlots := by
    unfold ligeritoSiteStart productionSamplingSlots ligeritoWidth
    unfold ligeritoSiteWidth
    nlinarith [site.isLt]
  have hbefore : ligeritoOffset ≤ ligeritoSiteStart site + 1 + trial := by
    unfold ligeritoSiteStart
    omega
  unfold rawStep
  rw [if_neg (by simp [hstatus])]
  simp only [
    dif_neg (not_before_ligerito (by decide : equalitySkipBlocks ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : zerocheckOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindStateOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindGrindingOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : multiplicationAlphaOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : productCoefficientOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_lt_of_ge hbefore), dif_pos hlig]

theorem ligeritoStep_trial_eq_of_done {shape : BatchShape}
    (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials)
    (control : Control shape) (answer : OracleBlock)
    (hdone : control.stageDone = true) :
    ligeritoStep (ligeritoSiteStart site + 1 + trial) control answer = control := by
  have hoff := ligerito_trial_offset site trial htrial
  unfold ligeritoStep
  dsimp only
  rw [hoff.1, hoff.2]
  have hpositive : 1 + trial ≠ 0 := by omega
  simp [ hdone]

theorem rawStep_ligeritoTrial_preserves_terminal {W : Type*}
    (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials)
    (control : Control shape) (answer : OracleBlock)
    (hstatus : control.status = ligeritoSiteTerminalStatus site)
    (hdone : control.stageDone = true) :
    rawStep shape causalSecret completion witness coins
        (ligeritoSiteStart site + 1 + trial) control answer = control := by
  by_cases hlast : site.val + 1 = maxLigeritoSites
  · have hsuccess : control.status = .success := by
      simpa [ligeritoSiteTerminalStatus, hlast] using hstatus
    unfold rawStep
    rw [if_pos]
    simp [hsuccess]
  · have hlive : control.status = .live := by
      simpa [ligeritoSiteTerminalStatus, hlast] using hstatus
    rw [rawStep_ligeritoTrial shape causalSecret completion witness coins site
      trial htrial control answer hlive,
      ligeritoStep_trial_eq_of_done site trial htrial control answer hdone]

theorem rawLigeritoFailures_live
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hrounds : rounds < maxLigeritoTrials)
    (hstatus : control.status = .live)
    (hdone : control.stageDone = false)
    (hallbad : ∀ trial : Fin rounds,
      ¬rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (answers trial)) :
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      (ligeritoSiteStart site + 1) rounds control answers
    result.status = .live ∧ result.stageDone = false := by
  induction rounds with
  | zero => simpa [iterateFrom, iterateList] using And.intro hstatus hdone
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      have hprefix := ih (answers := fun index ↦ answers index.castSucc)
        (hrounds := by omega)
        (hallbad := fun trial ↦ hallbad trial.castSucc)
      rw [rawStep_ligeritoTrial shape causalSecret completion witness coins
        site rounds (by omega) _ _ hprefix.1]
      exact ligeritoStep_trial_bad_before_cap site rounds (by omega) _ _
        hprefix.1 hprefix.2 (hallbad (Fin.last rounds))

theorem rawLigeritoGrinding_terminal_of_exists
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hrounds : rounds ≤ maxLigeritoTrials)
    (hstatus : control.status = .live)
    (hdone : control.stageDone = false)
    (hexists : ∃ trial : Fin rounds,
      rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (answers trial)) :
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      (ligeritoSiteStart site + 1) rounds control answers
    result.status = ligeritoSiteTerminalStatus site ∧
      result.stageDone = true := by
  induction rounds with
  | zero => simp at hexists
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      let prefixAnswers : Fin rounds → OracleBlock :=
        fun index ↦ answers index.castSucc
      let prior := iterateFrom
        (rawStep shape causalSecret completion witness coins)
        (ligeritoSiteStart site + 1) rounds control prefixAnswers
      by_cases hearlier : ∃ trial : Fin rounds,
          rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
            (prefixAnswers trial)
      · have hprefix := ih (answers := prefixAnswers) (hrounds := by omega)
          (hexists := hearlier)
        change (rawStep shape causalSecret completion witness coins
          (ligeritoSiteStart site + 1 + rounds) prior
          (answers (Fin.last rounds))).status = ligeritoSiteTerminalStatus site ∧
          (rawStep shape causalSecret completion witness coins
          (ligeritoSiteStart site + 1 + rounds) prior
          (answers (Fin.last rounds))).stageDone = true
        rw [rawStep_ligeritoTrial_preserves_terminal shape causalSecret
          completion witness coins site rounds (by omega) prior
          (answers (Fin.last rounds)) hprefix.1 hprefix.2]
        exact hprefix
      · have hallbad : ∀ trial : Fin rounds,
            ¬rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
              (prefixAnswers trial) := by
          simpa only [not_exists] using hearlier
        have hprefix := rawLigeritoFailures_live shape causalSecret completion
          witness coins site rounds control prefixAnswers (by omega) hstatus
          hdone hallbad
        have hlast : rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
            (answers (Fin.last rounds)) := by
          rcases hexists with ⟨trial, htrial⟩
          rcases Fin.eq_castSucc_or_eq_last trial with ⟨priorTrial, rfl⟩ | rfl
          · exact False.elim ((hallbad priorTrial) htrial)
          · exact htrial
        change (rawStep shape causalSecret completion witness coins
          (ligeritoSiteStart site + 1 + rounds) prior
          (answers (Fin.last rounds))).status = ligeritoSiteTerminalStatus site ∧
          (rawStep shape causalSecret completion witness coins
          (ligeritoSiteStart site + 1 + rounds) prior
          (answers (Fin.last rounds))).stageDone = true
        rw [rawStep_ligeritoTrial shape causalSecret completion witness coins
          site rounds (by omega) prior (answers (Fin.last rounds)) hprefix.1]
        exact ligeritoStep_trial_good site rounds (by omega) prior
          (answers (Fin.last rounds)) hprefix.1 hprefix.2 hlast

theorem rawLigeritoSite_terminal
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (control : Control shape)
    (stateAnswer : OracleBlock)
    (answers : Fin maxLigeritoTrials → OracleBlock)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin maxLigeritoTrials,
      rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (answers trial)) :
    let withState := rawStep shape causalSecret completion witness coins
      (ligeritoSiteStart site) control stateAnswer
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      (ligeritoSiteStart site + 1) maxLigeritoTrials withState answers
    result.status = ligeritoSiteTerminalStatus site ∧
      result.stageDone = true := by
  rw [rawStep_ligeritoStart shape causalSecret completion witness coins site
    control stateAnswer hstatus, ligeritoStep_at_start]
  exact rawLigeritoGrinding_terminal_of_exists shape causalSecret completion
    witness coins site maxLigeritoTrials _ answers (by rfl) hstatus rfl hexists

theorem rawLigeritoSite_window_terminal
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (control : Control shape)
    (answers : SamplingAnswerTape)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin maxLigeritoTrials,
      rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (window (ligeritoSiteStart site + 1) maxLigeritoTrials
          (ligeritoGrinding_window_fits site) answers trial)) :
    let result := iterateFrom
      (rawStep shape causalSecret completion witness coins)
      (ligeritoSiteStart site) ligeritoSiteWidth control
      (window (ligeritoSiteStart site) ligeritoSiteWidth (by
        simpa only [ligeritoSiteStart, ligeritoSiteWidth, Nat.add_assoc] using
          ligeritoGrinding_window_fits site)
        answers)
    result.status = ligeritoSiteTerminalStatus site ∧
      result.stageDone = true := by
  let step := rawStep shape causalSecret completion witness coins
  have hsiteFit : ligeritoSiteStart site + ligeritoSiteWidth ≤
      productionSamplingSlots := by
    simpa only [ligeritoSiteStart, ligeritoSiteWidth, Nat.add_assoc] using
      ligeritoGrinding_window_fits site
  have hsitePos : 0 < ligeritoSiteWidth := by
    unfold ligeritoSiteWidth
    omega
  let siteAnswers := window (ligeritoSiteStart site) (1 + maxLigeritoTrials)
    hsiteFit answers
  change
    (iterateFrom step (ligeritoSiteStart site) (1 + maxLigeritoTrials)
      control siteAnswers).status = ligeritoSiteTerminalStatus site ∧
    (iterateFrom step (ligeritoSiteStart site) (1 + maxLigeritoTrials)
      control siteAnswers).stageDone = true
  rw [iterateFrom_add]
  have hstate : siteAnswers (Fin.castAdd maxLigeritoTrials ⟨0, by omega⟩) =
      answers ⟨ligeritoSiteStart site, by omega⟩ := rfl
  have htail : (fun index : Fin maxLigeritoTrials ↦
      siteAnswers (Fin.natAdd 1 index)) =
      window (ligeritoSiteStart site + 1) maxLigeritoTrials
        (ligeritoGrinding_window_fits site) answers := by
    funext index
    apply congrArg answers
    apply Fin.ext
    simp
    omega
  have hone : iterateFrom step (ligeritoSiteStart site) 1 control
      (fun index ↦ siteAnswers (Fin.castAdd maxLigeritoTrials index)) =
      step (ligeritoSiteStart site) control
        (answers ⟨ligeritoSiteStart site, by omega⟩) := by
    rw [show (fun index : Fin 1 ↦
        siteAnswers (Fin.castAdd maxLigeritoTrials index)) =
        fun _ ↦ answers ⟨ligeritoSiteStart site, by omega⟩ by
      funext index
      fin_cases index
      exact hstate]
    simp [iterateFrom, iterateList]
  rw [hone, htail]
  exact rawLigeritoSite_terminal shape causalSecret completion witness coins
    site control (answers ⟨ligeritoSiteStart site, by omega⟩)
    (window (ligeritoSiteStart site + 1) maxLigeritoTrials
      (ligeritoGrinding_window_fits site) answers) hstatus hexists

/-! ## Prefix controls for whole-schedule composition -/

noncomputable def rawControlUntil
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (rounds : ℕ)
    (hrounds : rounds ≤ productionSamplingSlots) : Control shape :=
  iterateFrom (rawStep shape causalSecret completion witness coins) 0 rounds
    (initialControl shape prelude)
    (fun index ↦ answers ⟨index.val, index.isLt.trans_le hrounds⟩)

theorem rawControlUntil_add
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (start width : ℕ)
    (hfit : start + width ≤ productionSamplingSlots) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (start + width) hfit =
      iterateFrom (rawStep shape causalSecret completion witness coins)
        start width
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers start (Nat.le_trans (Nat.le_add_right start width) hfit))
        (window start width hfit answers) := by
  unfold rawControlUntil
  rw [iterateFrom_add, Nat.zero_add]
  congr 1

theorem controlAfter_eq_rawControlUntil
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) :
    controlAfter shape causalSecret completion witness coins prelude answers =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        productionSamplingSlots (by rfl) := by
  rw [controlAfter_eq_iterateFrom]
  rfl

theorem rawControlUntil_ligerito_prefix_status
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hstart : (rawControlUntil shape causalSecret completion witness coins
      prelude answers ligeritoOffset (by decide)).status = .live)
    (hgrind : ∀ site : Fin maxLigeritoSites,
      ∃ trial : Fin maxLigeritoTrials,
        rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
          (window (ligeritoSiteStart site + 1) maxLigeritoTrials
            (ligeritoGrinding_window_fits site) answers trial))
    (sites : ℕ) (hsites : sites ≤ maxLigeritoSites) :
    let fit : ligeritoOffset + sites * ligeritoSiteWidth ≤
        productionSamplingSlots := by
      unfold productionSamplingSlots ligeritoWidth
      have _hwidth : 0 < ligeritoSiteWidth := by
        unfold ligeritoSiteWidth
        omega
      nlinarith
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (ligeritoOffset + sites * ligeritoSiteWidth) fit).status =
        if sites = maxLigeritoSites then .success else .live := by
  induction sites with
  | zero => simpa [maxLigeritoSites] using hstart
  | succ sites ih =>
      have hsitesLt : sites < maxLigeritoSites := by omega
      have hprefix := ih (hsites := by omega)
      have hprefixLive : (rawControlUntil shape causalSecret completion witness
          coins prelude answers (ligeritoOffset + sites * ligeritoSiteWidth)
          (by
            unfold productionSamplingSlots ligeritoWidth
            have hwidth : 0 < ligeritoSiteWidth := by
              unfold ligeritoSiteWidth
              omega
            nlinarith)).status = .live := by
        simpa [show sites ≠ maxLigeritoSites by omega] using hprefix
      let site : Fin maxLigeritoSites := ⟨sites, hsitesLt⟩
      have hfit : (ligeritoOffset + sites * ligeritoSiteWidth) +
          ligeritoSiteWidth ≤ productionSamplingSlots := by
        unfold productionSamplingSlots ligeritoWidth
        have hwidth : 0 < ligeritoSiteWidth := by
          unfold ligeritoSiteWidth
          omega
        nlinarith
      have hadd := rawControlUntil_add shape causalSecret completion witness
        coins prelude answers (ligeritoOffset + sites * ligeritoSiteWidth)
        ligeritoSiteWidth hfit
      have hsite := rawLigeritoSite_window_terminal shape causalSecret
        completion witness coins site
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (ligeritoOffset + sites * ligeritoSiteWidth) (by
            exact Nat.le_trans (Nat.le_add_right _ _) hfit))
        answers hprefixLive (hgrind site)
      have hsite' :
          let result := iterateFrom
            (rawStep shape causalSecret completion witness coins)
            (ligeritoOffset + sites * ligeritoSiteWidth) ligeritoSiteWidth
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers (ligeritoOffset + sites * ligeritoSiteWidth) (by
                exact Nat.le_trans (Nat.le_add_right _ _) hfit))
            (window (ligeritoOffset + sites * ligeritoSiteWidth)
              ligeritoSiteWidth hfit answers)
          result.status = ligeritoSiteTerminalStatus site ∧
            result.stageDone = true := by
        simpa only [ligeritoSiteStart, site] using hsite
      have hcontrolEq :
          rawControlUntil shape causalSecret completion witness coins prelude
              answers (ligeritoOffset + (sites + 1) * ligeritoSiteWidth) (by
                simpa [Nat.add_mul, Nat.add_assoc] using hfit) =
            iterateFrom (rawStep shape causalSecret completion witness coins)
              (ligeritoOffset + sites * ligeritoSiteWidth) ligeritoSiteWidth
              (rawControlUntil shape causalSecret completion witness coins
                prelude answers (ligeritoOffset + sites * ligeritoSiteWidth)
                (by exact Nat.le_trans (Nat.le_add_right _ _) hfit))
              (window (ligeritoOffset + sites * ligeritoSiteWidth)
                ligeritoSiteWidth hfit answers) := by
        simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hadd
      change
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (ligeritoOffset + (sites + 1) * ligeritoSiteWidth) _).status =
          if sites + 1 = maxLigeritoSites then .success else .live
      rw [hcontrolEq]
      simpa [ligeritoSiteTerminalStatus, site] using hsite'.1

theorem rawControlUntil_ligerito_success
    {W : Type*} (shape : BatchShape)
    (causalSecret : VeiledFlock.ProductionCausalOperational.ProductionCausalSecret
      (W := W) shape)
    (completion : VeiledFlock.OracleCausalOneTimePad.Completion OracleBlock
      (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hstart : (rawControlUntil shape causalSecret completion witness coins
      prelude answers ligeritoOffset (by decide)).status = .live)
    (hgrind : ∀ site : Fin maxLigeritoSites,
      ∃ trial : Fin maxLigeritoTrials,
        rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
          (window (ligeritoSiteStart site + 1) maxLigeritoTrials
            (ligeritoGrinding_window_fits site) answers trial)) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      productionSamplingSlots (by rfl)).status = .success := by
  have hprefix := rawControlUntil_ligerito_prefix_status shape causalSecret
    completion witness coins prelude answers hstart hgrind maxLigeritoSites
    (by rfl)
  simpa [productionSamplingSlots, ligeritoWidth] using hprefix

/-! ## Ledger witnesses in the exact state-machine formats -/

theorem equality_accepted_of_not_globalBad (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    ∃ attempt : Fin rejectionTrials,
      accepted (sliceFromBlocks (m shape - kSkip - 7)
        (List.ofFn (equalityFlatEquiv
          (window equalityOffset equalityWidth (by
            rw [productionSamplingSlots_eq]
            decide) answers) attempt))) := by
  rcases exists_equality_attempt_of_not_globalBad shape answers hgood with
    ⟨attempt, hattempt⟩
  refine ⟨attempt, equality_attempt_prefix_accepted (by
    cases shape <;> decide) _ ?_⟩
  exact hattempt

theorem scalarStage_good_of_not_globalBad (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (stage : ScalarStage) :
    ∃ trial : Fin rejectionTrials,
      scalarFromBlock
          (window (scalarStageStart stage) rejectionTrials (by
            cases stage <;> rw [productionSamplingSlots_eq] <;> decide)
            answers trial) ∉ scalarStageFailure stage := by
  cases stage with
  | multiplicationAlpha =>
      simpa [scalarStageStart, scalarStageFailure] using
        exists_multiplicationAlpha_answer_of_not_globalBad shape answers hgood
  | blindChallenge =>
      simpa [scalarStageStart, scalarStageFailure, nonzeroOffset] using
        exists_nonzero_answer_of_not_globalBad shape answers hgood ⟨0, by decide⟩
  | outerChallenge =>
      simpa [scalarStageStart, scalarStageFailure, nonzeroOffset] using
        exists_nonzero_answer_of_not_globalBad shape answers hgood ⟨1, by decide⟩
  | linearRho =>
      simpa [scalarStageStart, scalarStageFailure, nonzeroOffset] using
        exists_nonzero_answer_of_not_globalBad shape answers hgood ⟨2, by decide⟩
  | hadamardRho =>
      simpa [scalarStageStart, scalarStageFailure, nonzeroOffset] using
        exists_nonzero_answer_of_not_globalBad shape answers hgood ⟨3, by decide⟩
  | productCoefficient =>
      simpa [scalarStageStart, scalarStageFailure, nonzeroOffset] using
        exists_nonzero_answer_of_not_globalBad shape answers hgood ⟨4, by decide⟩

theorem positionStage_card_of_not_globalBad (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (stage : PositionStage) :
    positionStageTarget shape stage ≤
      (observedNatPositions
        (fun block ↦ positionStageProject shape stage (scalarFromBlock block))
        (window (positionStageStart stage) samplingTrials (by
          cases stage <;> rw [productionSamplingSlots_eq] <;> decide)
          answers)).card := by
  cases stage with
  | outer =>
      have h := outerPositions_card_ge_of_not_globalBad shape answers hgood
      rw [← observedNatPositions_card_eq] at h
      simpa [positionStageTarget, positionStageProject, positionStageStart,
        observedNatPositions] using h
  | linear =>
      have h := linearPositions_card_ge_of_not_globalBad shape answers hgood
      rw [← observedNatPositions_card_eq] at h
      simpa [positionStageTarget, positionStageProject, positionStageStart,
        observedNatPositions, veilQueryCount, queryCount] using h
  | hadamard =>
      have h := hadamardPositions_card_ge_of_not_globalBad shape answers hgood
      rw [← observedNatPositions_card_eq] at h
      simpa [positionStageTarget, positionStageProject, positionStageStart,
        observedNatPositions, veilQueryCount, queryCount] using h

end VeiledFlock.ProductionSamplingScheduleSemantics

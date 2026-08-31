import VeiledFlock.Oracle.OptionalAdaptiveOracle
import VeiledFlock.Production.Nizk.NizkCoupling
import VeiledFlock.Production.Sampling.SamplingBadTape

/-!
# One causal schedule for all production sampling loops

The schedule reserves the fixed layout from `ProductionSamplingLayout`.
After an early success, the remaining coordinates of that stage are inactive
and consume only the private dummy tape supplied by `OptionalAdaptiveOracle`.
-/

namespace VeiledFlock.ProductionSamplingSchedule

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OptionalAdaptiveOracle
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.UniquePositionSampling

inductive Status
  | live
  | abort
  | success
  | collision
  deriving DecidableEq

/-- Minimal live state needed to determine the next literal production query.
Proof data not used by later scheduling is intentionally absent. -/
structure Control (shape : BatchShape) where
  status : Status
  transcript : List Byte
  skipBlocks : List OracleBlock
  equalityBlocks : List OracleBlock
  skip : Option (Fin 6 → GhashField)
  equalityPoint : Option (EqualitySample (m shape - kSkip - 7))
  zerocheckAnswers : List OracleBlock
  powState : Option Nonce256
  stageDone : Bool
  stageBlocks : List OracleBlock
  positions : Finset ℕ

def initialControl (shape : BatchShape) (prelude : List Byte) : Control shape :=
  { status := .live
    transcript := prelude
    skipBlocks := []
    equalityBlocks := []
    skip := none
    equalityPoint := none
    zerocheckAnswers := []
    powState := none
    stageDone := false
    stageBlocks := []
    positions := ∅ }

/-- Parse the two 16-byte fields of each consecutive 32-byte counter block. -/
noncomputable def sliceFromBlocks (length : ℕ) (blocks : List OracleBlock) :
    Fin length → GhashField := fun index ↦
  blockFieldsEquiv (blocks.getD (index.val / 2) default)
    ⟨index.val % 2, Nat.mod_lt _ (by decide)⟩

def equalityBlockCount (shape : BatchShape) : ℕ :=
  ((m shape - kSkip - 7) + 1) / 2

theorem equalityBlockCount_le_seven (shape : BatchShape) :
    equalityBlockCount shape ≤ equalityAttemptBlocks := by
  cases shape <;> decide

def historyFromList (blocks : List OracleBlock) (count : ℕ) :
    History (Outcome := OracleBlock) count :=
  fun index ↦ blocks.getD index.val default

def inRange (start width round : ℕ) : Prop :=
  start ≤ round ∧ round < start + width

noncomputable def nonzeroStageQuery {shape : BatchShape} (start round : ℕ)
    (control : Control shape) : Option (List Byte) :=
  if _hrange : start ≤ round ∧ round < start + rejectionTrials then
    let offset := round - start
    if offset = 0 ∨ !control.stageDone then
      some (scalarPoint control.transcript)
    else none
  else none

/-- Literal next query before duplicate-point suppression. -/
noncomputable def rawQuery
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (control : Control shape) : Option (List Byte) :=
  if control.status != .live then none
  else if _hskip : round < equalitySkipBlocks then
    some (slicePoint control.transcript 6 (BitVec.ofNat 64 round))
  else if _hequality : round < zerocheckOffset then
    let offset := round - equalityOffset
    let counter := offset % equalityAttemptBlocks
    if control.equalityPoint.isSome then none
    else if counter < equalityBlockCount shape then
      some (slicePoint control.transcript (m shape - kSkip - 7)
        (BitVec.ofNat 64 counter))
    else none
  else if _hzero : round < blindStateOffset then
    let offset := round - zerocheckOffset
    match control.equalityPoint with
    | none => none
    | some _equalityPoint =>
        if _hsite : offset < programmedPoints shape then
          some ((zerocheckRealByteSchedule shape causalSecret completion
            control.transcript witness coins) offset
              (historyFromList control.zerocheckAnswers offset))
        else none
  else if _hblindState : round < blindGrindingOffset then
    some (scalarPoint control.transcript)
  else if _hblindGrind : round < blindChallengeOffset then
    let offset := round - blindGrindingOffset
    if control.stageDone then none
    else control.powState.map fun state ↦
      encodePowPoint state (BitVec.ofNat 64 offset)
  else if _hblind : round < multiplicationAlphaOffset then
    nonzeroStageQuery blindChallengeOffset round control
  else if _halpha : round < outerChallengeOffset then
    if _hrange : multiplicationAlphaOffset ≤ round ∧
        round < multiplicationAlphaOffset + rejectionTrials then
      let offset := round - multiplicationAlphaOffset
      if offset = 0 ∨ !control.stageDone then
        some (scalarPoint control.transcript)
      else none
    else none
  else if _houterChallenge : round < outerPositionsOffset then
    nonzeroStageQuery outerChallengeOffset round control
  else if _houterPositions : round < linearPositionsOffset then
    let offset := round - outerPositionsOffset
    if offset = 0 ∨ !control.stageDone then
      some (scalarPoint control.transcript)
    else none
  else if _hlinearPositions : round < linearRhoOffset then
    let offset := round - linearPositionsOffset
    if offset = 0 ∨ !control.stageDone then
      some (scalarPoint control.transcript)
    else none
  else if _hlinearRho : round < hadamardPositionsOffset then
    nonzeroStageQuery linearRhoOffset round control
  else if _hhadamardPositions : round < hadamardRhoOffset then
    let offset := round - hadamardPositionsOffset
    if offset = 0 ∨ !control.stageDone then
      some (scalarPoint control.transcript)
    else none
  else if _hhadamardRho : round < productCoefficientOffset then
    nonzeroStageQuery hadamardRhoOffset round control
  else if _hproduct : round < ligeritoOffset then
    nonzeroStageQuery productCoefficientOffset round control
  else if _hligerito : round < productionSamplingSlots then
    let offset := round - ligeritoOffset
    let within := offset % ligeritoSiteWidth
    if within = 0 then some (scalarPoint control.transcript)
    else if control.stageDone then none
    else control.powState.map fun state ↦
      encodePowPoint state (BitVec.ofNat 64 (within - 1))
  else none

noncomputable def acceptScalar {shape : BatchShape} (failed : Finset GhashField)
    (round start : ℕ) (control : Control shape) (answer : OracleBlock) :
    Control shape :=
  let offset := round - start
  let base := if offset = 0 then
      { control with
        stageDone := false
        stageBlocks := [] }
    else control
  if base.stageDone then base
  else
    let nextTranscript := afterScalar base.transcript answer
    if scalarFromBlock answer ∈ failed then
      if offset + 1 = rejectionTrials then
        { base with
          status := .abort
          transcript := nextTranscript
          stageBlocks := base.stageBlocks ++ [answer] }
      else
        { base with
          transcript := nextTranscript
          stageBlocks := base.stageBlocks ++ [answer] }
    else
      { base with
        transcript := nextTranscript
        stageDone := true
        stageBlocks := base.stageBlocks ++ [answer] }

noncomputable def acceptPositions {shape : BatchShape}
    (project : GhashField → ℕ)
    (target start round : ℕ) (control : Control shape)
    (answer : OracleBlock) : Control shape :=
  let offset := round - start
  let base := if offset = 0 then
      { control with
        stageDone := false
        stageBlocks := []
        positions := ∅ }
    else control
  if base.stageDone then base
  else
    let nextTranscript := afterScalar base.transcript answer
    let nextPositions := insert (project (scalarFromBlock answer)) base.positions
    if target ≤ nextPositions.card then
      { base with
        transcript := nextTranscript
        positions := nextPositions
        stageDone := true
        stageBlocks := base.stageBlocks ++ [answer] }
    else if offset + 1 = samplingTrials then
      { base with
        status := .abort
        transcript := nextTranscript
        positions := nextPositions
        stageBlocks := base.stageBlocks ++ [answer] }
    else
      { base with
        transcript := nextTranscript
        positions := nextPositions
        stageBlocks := base.stageBlocks ++ [answer] }

noncomputable def equalityStep (shape : BatchShape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) : Control shape :=
  if control.equalityPoint.isSome then control
  else
    let offset := round - equalityOffset
    let attempt := offset / equalityAttemptBlocks
    let counter := offset % equalityAttemptBlocks
    if _hcounter : counter < equalityBlockCount shape then
      let base := if counter = 0 then
          { control with equalityBlocks := [] }
        else control
      let blocks := base.equalityBlocks ++ [answer]
      if counter + 1 = equalityBlockCount shape then
        let outer := sliceFromBlocks (m shape - kSkip - 7) blocks
        let nextTranscript := afterSlice base.transcript outer
        if accepted outer then
          match base.skip with
          | none => { base with status := .abort }
          | some skip =>
              { base with
                equalityBlocks := blocks
                equalityPoint := some (skip, outer, nextTranscript)
                transcript := nextTranscript }
        else if attempt + 1 = rejectionTrials then
          { base with
            status := .abort
            equalityBlocks := blocks
            transcript := nextTranscript }
        else
          { base with
            equalityBlocks := blocks
            transcript := nextTranscript }
      else { base with equalityBlocks := blocks }
    else control

noncomputable def zerocheckStep
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (control : Control shape) (answer : OracleBlock) :
    Control shape :=
  let offset := round - zerocheckOffset
  match control.equalityPoint with
  | none => { control with status := .abort }
  | some _ =>
      if _hsite : offset < programmedPoints shape then
        let blocks := control.zerocheckAnswers ++ [answer]
        if offset + 1 = programmedPoints shape then
          let answers := historyFromList blocks (programmedPoints shape)
          { control with
            zerocheckAnswers := blocks
            transcript := afterZerocheck shape causalSecret completion
              control.transcript witness coins answers }
        else { control with zerocheckAnswers := blocks }
      else control

noncomputable def blindGrindingStep {shape : BatchShape} (round : ℕ)
    (control : Control shape)
    (answer : OracleBlock) : Control shape :=
  if control.stageDone then control
  else
    let offset := round - blindGrindingOffset
    let blocks := control.stageBlocks ++ [answer]
    if blindGrindingGood answer then
        { control with
          stageDone := true
          stageBlocks := blocks
          transcript := afterGrind control.transcript
            (BitVec.ofNat 64 offset) }
    else if offset + 1 = maxBlindTrials then
      { control with
        status := .abort
        stageBlocks := blocks }
    else { control with stageBlocks := blocks }

noncomputable def ligeritoStep {shape : BatchShape} (round : ℕ)
    (control : Control shape)
    (answer : OracleBlock) : Control shape :=
  let offset := round - ligeritoOffset
  let within := offset % ligeritoSiteWidth
  let site := offset / ligeritoSiteWidth
  if within = 0 then
    { control with
      powState := some answer
      stageDone := false
      stageBlocks := [] }
  else if control.stageDone then control
  else
    let blocks := control.stageBlocks ++ [answer]
    if rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide) answer then
      let next := { control with
        stageDone := true
        stageBlocks := blocks
        transcript := afterGrind control.transcript
            (BitVec.ofNat 64 (within - 1)) }
      if site + 1 = maxLigeritoSites then
        { next with status := .success }
      else next
    else if within = maxLigeritoTrials then
      { control with
        status := .abort
        stageBlocks := blocks }
    else { control with stageBlocks := blocks }

/-- Deterministic transition for one reserved answer coordinate. -/
noncomputable def rawStep
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (control : Control shape) (answer : OracleBlock) :
    Control shape :=
  if control.status != .live then control
  else if _hskip : round < equalitySkipBlocks then
    let blocks := control.skipBlocks ++ [answer]
    if round + 1 = equalitySkipBlocks then
      let skip := sliceFromBlocks 6 blocks
      { control with
        skipBlocks := blocks
        skip := some skip
        transcript := afterSlice control.transcript skip }
    else { control with skipBlocks := blocks }
  else if _hequality : round < zerocheckOffset then
    equalityStep shape round control answer
  else if _hzero : round < blindStateOffset then
    zerocheckStep shape causalSecret completion witness coins round control answer
  else if _hblindState : round < blindGrindingOffset then
    { control with
      powState := some answer
      stageDone := false
      stageBlocks := [] }
  else if _hblindGrind : round < blindChallengeOffset then
    blindGrindingStep round control answer
  else if _hblind : round < multiplicationAlphaOffset then
    acceptScalar zeroFailure round blindChallengeOffset control answer
  else if _halpha : round < outerChallengeOffset then
    acceptScalar zeroOrOneFailure round multiplicationAlphaOffset control answer
  else if _houterChallenge : round < outerPositionsOffset then
    acceptScalar zeroFailure round outerChallengeOffset control answer
  else if _houterPositions : round < linearPositionsOffset then
    acceptPositions (fun value ↦ (rustLowPosition (m shape - 11) value).val)
      (outerL0QueryCount shape) outerPositionsOffset round control answer
  else if _hlinearPositions : round < linearRhoOffset then
    acceptPositions (fun value ↦ (rustLowPosition 13 value).val)
      veilQueryCount linearPositionsOffset round control answer
  else if _hlinearRho : round < hadamardPositionsOffset then
    acceptScalar zeroFailure round linearRhoOffset control answer
  else if _hhadamardPositions : round < hadamardRhoOffset then
    acceptPositions (fun value ↦ (rustLowPosition 11 value).val)
      veilQueryCount hadamardPositionsOffset round control answer
  else if _hhadamardRho : round < productCoefficientOffset then
    acceptScalar zeroFailure round hadamardRhoOffset control answer
  else if _hproduct : round < ligeritoOffset then
    acceptScalar zeroFailure round productCoefficientOffset control answer
  else if _hligerito : round < productionSamplingSlots then
    ligeritoStep round control answer
  else control

noncomputable def controlAfter
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte) :
    {rounds : ℕ} → History (Outcome := OracleBlock) rounds → Control shape
  | 0, _ => initialControl shape prelude
  | rounds + 1, answers =>
      rawStep shape causalSecret completion witness coins rounds
        (controlAfter shape causalSecret completion witness coins prelude
          (fun index : Fin rounds ↦ answers index.castSucc))
        (answers (Fin.last rounds))

noncomputable def schedule
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte) :
    OptionalSchedule (Point := List Byte) (Outcome := OracleBlock)
      productionSamplingSlots :=
  fun round answers ↦ rawQuery shape causalSecret completion witness coins
    round (controlAfter shape causalSecret completion witness coins prelude
      answers)

/-! ## Duplicate-suppressing operational schedule -/

structure ScheduledControl (shape : BatchShape) where
  raw : Control shape
  seen : Finset (List Byte)

def initialScheduledControl (shape : BatchShape) (prelude : List Byte) :
    ScheduledControl shape :=
  { raw := initialControl shape prelude
    seen := ∅ }

noncomputable def scheduledStep
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (control : ScheduledControl shape) (answer : OracleBlock) :
    ScheduledControl shape :=
  match rawQuery shape causalSecret completion witness coins round control.raw with
  | none =>
      { raw := rawStep shape causalSecret completion witness coins round
          control.raw answer
        seen := control.seen }
  | some point =>
      if point ∈ control.seen then
        { raw := { control.raw with status := .collision }
          seen := control.seen }
      else
        { raw := rawStep shape causalSecret completion witness coins round
            control.raw answer
          seen := insert point control.seen }

noncomputable def scheduledControlAfter
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte) :
    {rounds : ℕ} →
      History (Outcome := OracleBlock) rounds → ScheduledControl shape
  | 0, _ => initialScheduledControl shape prelude
  | rounds + 1, answers =>
      scheduledStep shape causalSecret completion witness coins rounds
        (scheduledControlAfter shape causalSecret completion witness coins
          prelude (fun index : Fin rounds ↦ answers index.castSucc))
        (answers (Fin.last rounds))

/-- The concrete optional schedule queries a point only on its first causal
occurrence.  A repeated production point is recorded as `.collision` and the
corresponding coordinate is inactive. -/
noncomputable def freshSchedule
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte) :
    OptionalSchedule (Point := List Byte) (Outcome := OracleBlock)
      productionSamplingSlots :=
  fun round answers ↦
    let control := scheduledControlAfter shape causalSecret completion witness
      coins prelude answers
    match rawQuery shape causalSecret completion witness coins round control.raw with
    | none => none
    | some point => if point ∈ control.seen then none else some point

theorem scheduledStep_seen_mono
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : ScheduledControl shape) (answer : OracleBlock) :
    control.seen ⊆
      (scheduledStep shape causalSecret completion witness coins round control
        answer).seen := by
  classical
  unfold scheduledStep
  split
  · exact Finset.Subset.rfl
  · split
    · exact Finset.Subset.rfl
    · exact Finset.subset_insert _ _

theorem freshSchedule_point_inserted
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    {rounds : ℕ} (answers : History (Outcome := OracleBlock) (rounds + 1))
    (hround : rounds < productionSamplingSlots)
    (point : List Byte)
    (hquery : freshSchedule shape causalSecret completion witness coins prelude
      ⟨rounds, hround⟩
      (fun index : Fin rounds ↦ answers index.castSucc) = some point) :
    point ∈
      (scheduledControlAfter shape causalSecret completion witness coins prelude
        answers).seen := by
  classical
  simp only [freshSchedule] at hquery
  let before := scheduledControlAfter shape causalSecret completion witness
    coins prelude (fun index : Fin rounds ↦ answers index.castSucc)
  change (match rawQuery shape causalSecret completion witness coins rounds
      before.raw with
    | none => none
    | some candidate => if candidate ∈ before.seen then none
      else some candidate) = some point at hquery
  simp only [scheduledControlAfter]
  unfold scheduledStep
  generalize hraw : rawQuery shape causalSecret completion witness coins rounds
      before.raw = result at hquery ⊢
  cases result with
  | none => simp at hquery
  | some candidate =>
      simp only
      by_cases hseen : candidate ∈ before.seen
      · simp [hseen] at hquery
      · simp [hseen] at hquery
        subst point
        simp [before, hseen]

theorem scheduledControlAfter_seen_mono
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    {small large : ℕ} (hle : small ≤ large)
    (answers : History (Outcome := OracleBlock) large) :
    (scheduledControlAfter shape causalSecret completion witness coins prelude
      (fun index : Fin small ↦ answers (Fin.castLE hle index))).seen ⊆
    (scheduledControlAfter shape causalSecret completion witness coins prelude
      answers).seen := by
  induction large with
  | zero =>
      have hsmall : small = 0 := by omega
      subst small
      exact Finset.Subset.rfl
  | succ large ih =>
      by_cases heq : small = large + 1
      · subst small
        exact Finset.Subset.rfl
      · have hsmall : small ≤ large := Nat.le_of_lt_succ
          (lt_of_le_of_ne hle heq)
        refine (ih hsmall
          (fun index : Fin large ↦ answers index.castSucc)).trans ?_
        exact scheduledStep_seen_mono shape causalSecret completion witness
          coins large
          (scheduledControlAfter shape causalSecret completion witness coins
            prelude (fun index : Fin large ↦ answers index.castSucc))
          (answers (Fin.last large))

theorem freshSchedule_activeInjective
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : History (Outcome := OracleBlock) productionSamplingSlots) :
    ActiveInjective
      (freshSchedule shape causalSecret completion witness coins prelude)
      answers := by
  classical
  intro left right leftPoint rightPoint hleft hright heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinsert := freshSchedule_point_inserted shape causalSecret completion
      witness coins prelude
      (fun index : Fin (left.val + 1) ↦ answers
        ⟨index.val, index.isLt.trans_le (Nat.succ_le_of_lt left.isLt)⟩)
      left.isLt leftPoint (by
        change freshSchedule shape causalSecret completion witness coins prelude
          left
          (fun index : Fin left.val ↦ answers
            ⟨index.val, by omega⟩) = some leftPoint
        rw [show (fun index : Fin left.val ↦ answers
            ⟨index.val, by omega⟩) = priorAnswers answers left by
          funext index
          apply congrArg answers
          apply Fin.ext
          rfl]
        exact hleft)
    have hmono := scheduledControlAfter_seen_mono shape causalSecret completion
      witness coins prelude (Nat.succ_le_of_lt hlt)
      (priorAnswers answers right)
    have hleftSeen : leftPoint ∈
        (scheduledControlAfter shape causalSecret completion witness coins
          prelude (priorAnswers answers right)).seen := hmono hinsert
    simp only [freshSchedule] at hright
    let before := scheduledControlAfter shape causalSecret completion witness
      coins prelude (priorAnswers answers right)
    change (match rawQuery shape causalSecret completion witness coins right
        before.raw with
      | none => none
      | some candidate => if candidate ∈ before.seen then none
        else some candidate) = some rightPoint at hright
    generalize hraw : rawQuery shape causalSecret completion witness coins right
      before.raw = result at hright
    cases result with
    | none => simp at hright
    | some candidate =>
        by_cases hseen : candidate ∈ before.seen
        · simp [hseen] at hright
        · have hcand : candidate = rightPoint := by
            simpa [hseen] using hright
          exact hseen (hcand ▸ heq ▸ hleftSeen)
  · have hsymmetric := hgt
    have := freshSchedule_point_inserted shape causalSecret completion witness
      coins prelude
      (fun index : Fin (right.val + 1) ↦ answers
        ⟨index.val, index.isLt.trans_le (Nat.succ_le_of_lt right.isLt)⟩)
      right.isLt rightPoint (by
        change freshSchedule shape causalSecret completion witness coins prelude
          right
          (fun index : Fin right.val ↦ answers
            ⟨index.val, by omega⟩) = some rightPoint
        rw [show (fun index : Fin right.val ↦ answers
            ⟨index.val, by omega⟩) = priorAnswers answers right by
          funext index
          apply congrArg answers
          apply Fin.ext
          rfl]
        exact hright)
    have hmono := scheduledControlAfter_seen_mono shape causalSecret completion
      witness coins prelude (Nat.succ_le_of_lt hsymmetric)
      (priorAnswers answers left)
    have hrightSeen : rightPoint ∈
        (scheduledControlAfter shape causalSecret completion witness coins
          prelude (priorAnswers answers left)).seen := hmono this
    simp only [freshSchedule] at hleft
    let before := scheduledControlAfter shape causalSecret completion witness
      coins prelude (priorAnswers answers left)
    change (match rawQuery shape causalSecret completion witness coins left
        before.raw with
      | none => none
      | some candidate => if candidate ∈ before.seen then none
        else some candidate) = some leftPoint at hleft
    generalize hraw : rawQuery shape causalSecret completion witness coins left
      before.raw = result at hleft
    cases result with
    | none => simp at hleft
    | some candidate =>
        by_cases hseen : candidate ∈ before.seen
        · simp [hseen] at hleft
        · have hcand : candidate = leftPoint := by
            simpa [hseen] using hleft
          exact hseen (hcand ▸ heq.symm ▸ hrightSeen)

/-! ## Public byte-length audit for the complete schedule -/

@[simp]
theorem afterZerocheck_length
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (absorbedPrefix : List Byte) (witness : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (afterZerocheck shape causalSecret completion absorbedPrefix witness coins
      answers).length =
      absorbedPrefix.length +
        2 * (10 + 16 * VeiledFlock.ProductionMaskLayout.ell) + 2 +
        programmedPoints shape * 54 := by
  unfold afterZerocheck
  rw [VeiledFlock.TranscriptSchedule.appendState_length _ _ 54
    (VeiledFlock.TranscriptSchedule.scalarRoundStep_length consumeScalar
      consumeScalar_length
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ConcreteOracle.encodeField_length
        VeiledFlock.Field128Serialization.encodeGhashField)
      _ _)]
  rw [VeiledFlock.ProductionZerocheckSchedule.start_length]

/- The tighter public byte-budget invariant is proved in the bounded-oracle
bridge, where the production maximum length is available. -/
/-
theorem acceptScalar_transcript_length_le (failed : Finset GhashField)
    (round start : ℕ) (control : Control shape) (answer : OracleBlock) :
    (acceptScalar failed round start control answer).transcript.length ≤
      control.transcript.length + 18 := by
  classical
  unfold acceptScalar
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp_all only [afterScalar_length] <;> omega

theorem acceptPositions_transcript_length_le
    (project : GhashField → ℕ) (target start round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (acceptPositions project target start round control answer).transcript.length ≤
      control.transcript.length + 18 := by
  classical
  unfold acceptPositions
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp_all only [afterScalar_length] <;> omega

theorem equalityStep_transcript_length_le (shape : BatchShape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (equalityStep shape round control answer).transcript.length ≤
      control.transcript.length + 4096 := by
  classical
  unfold equalityStep
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp_all only [afterSlice_length] <;>
    (cases shape <;> simp_all [m, kSkip] <;> omega)

theorem zerocheckStep_transcript_length_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (zerocheckStep shape causalSecret completion witness coins round control
      answer).transcript.length ≤ control.transcript.length + 4096 := by
  classical
  unfold zerocheckStep
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp_all only [afterZerocheck_length] <;>
    (cases shape <;> simp_all [programmedPoints] <;> omega)

theorem blindGrindingStep_transcript_length_le (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (blindGrindingStep round control answer).transcript.length ≤
      control.transcript.length + 17 := by
  classical
  unfold blindGrindingStep
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp_all only [afterGrind_length] <;> omega

theorem ligeritoStep_transcript_length_le (round : ℕ)
    (control : Control shape) (answer : OracleBlock) :
    (ligeritoStep round control answer).transcript.length ≤
      control.transcript.length + 17 := by
  classical
  unfold ligeritoStep
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp_all only [afterGrind_length] <;> omega

/-- A deliberately simple reachable-state invariant.  The constant 4096 is
larger than every possible one-coordinate transcript increment, including
the single transition that installs the complete zerocheck transcript.  It
is used only to prove that every serialized query lies in the one finite
production oracle universe; probability bounds continue to use the exact
fixed layout. -/
def ControlLengthBound (prelude : List Byte) (round : ℕ)
    (control : Control shape) : Prop :=
  control.transcript.length ≤ prelude.length + round * 4096

theorem initialControl_lengthBound (shape : BatchShape) (prelude : List Byte) :
    ControlLengthBound prelude 0 (initialControl shape prelude) := by
  simp [ControlLengthBound, initialControl]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 10000 in
theorem rawStep_lengthBound
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (prelude : List Byte) (round : ℕ) (control : Control shape)
    (answer : OracleBlock)
    (hbound : ControlLengthBound prelude round control) :
    ControlLengthBound prelude (round + 1)
      (rawStep shape causalSecret completion witness coins round control
        answer) := by
  classical
  by_cases hstatus : control.status != .live
  · simp [rawStep, hstatus, ControlLengthBound] at hbound ⊢
    omega
  simp only [rawStep, hstatus, ↓reduceIte]
  by_cases hskip : round < equalitySkipBlocks
  · simp [hskip, ControlLengthBound] at hbound ⊢
    split <;> simp_all [afterSlice_length] <;> omega
  simp only [hskip, ↓reduceDIte]
  by_cases hequality : round < zerocheckOffset
  · simp only [hequality, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (equalityStep_transcript_length_le shape round control answer).trans
      (by omega)
  simp only [hequality, ↓reduceDIte]
  by_cases hzero : round < blindStateOffset
  · simp only [hzero, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (zerocheckStep_transcript_length_le shape causalSecret completion
      witness coins round control answer).trans (by omega)
  simp only [hzero, ↓reduceDIte]
  by_cases hblindState : round < blindGrindingOffset
  · simp [hblindState, ControlLengthBound] at hbound ⊢
    omega
  simp only [hblindState, ↓reduceDIte]
  by_cases hblindGrind : round < blindChallengeOffset
  · simp only [hblindGrind, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (blindGrindingStep_transcript_length_le round control answer).trans
      (by omega)
  simp only [hblindGrind, ↓reduceDIte]
  by_cases hblind : round < multiplicationAlphaOffset
  · simp only [hblind, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptScalar_transcript_length_le zeroFailure round
      blindChallengeOffset control answer).trans (by omega)
  simp only [hblind, ↓reduceDIte]
  by_cases halpha : round < outerChallengeOffset
  · simp only [halpha, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptScalar_transcript_length_le zeroOrOneFailure round
      multiplicationAlphaOffset control answer).trans (by omega)
  simp only [halpha, ↓reduceDIte]
  by_cases houterChallenge : round < outerPositionsOffset
  · simp only [houterChallenge, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptScalar_transcript_length_le zeroFailure round
      outerChallengeOffset control answer).trans (by omega)
  simp only [houterChallenge, ↓reduceDIte]
  by_cases houterPositions : round < linearPositionsOffset
  · simp only [houterPositions, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptPositions_transcript_length_le
      (fun value ↦ (rustLowPosition (m shape - 11) value).val)
      (outerL0QueryCount shape) outerPositionsOffset round control answer).trans
        (by omega)
  simp only [houterPositions, ↓reduceDIte]
  by_cases hlinearPositions : round < linearRhoOffset
  · simp only [hlinearPositions, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptPositions_transcript_length_le
      (fun value ↦ (rustLowPosition 13 value).val) veilQueryCount
      linearPositionsOffset round control answer).trans (by omega)
  simp only [hlinearPositions, ↓reduceDIte]
  by_cases hlinearRho : round < hadamardPositionsOffset
  · simp only [hlinearRho, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptScalar_transcript_length_le zeroFailure round
      linearRhoOffset control answer).trans (by omega)
  simp only [hlinearRho, ↓reduceDIte]
  by_cases hhadamardPositions : round < hadamardRhoOffset
  · simp only [hhadamardPositions, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptPositions_transcript_length_le
      (fun value ↦ (rustLowPosition 11 value).val) veilQueryCount
      hadamardPositionsOffset round control answer).trans (by omega)
  simp only [hhadamardPositions, ↓reduceDIte]
  by_cases hhadamardRho : round < productCoefficientOffset
  · simp only [hhadamardRho, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptScalar_transcript_length_le zeroFailure round
      hadamardRhoOffset control answer).trans (by omega)
  simp only [hhadamardRho, ↓reduceDIte]
  by_cases hproduct : round < ligeritoOffset
  · simp only [hproduct, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (acceptScalar_transcript_length_le zeroFailure round
      productCoefficientOffset control answer).trans (by omega)
  simp only [hproduct, ↓reduceDIte]
  by_cases hligerito : round < productionSamplingSlots
  · simp only [hligerito, ↓reduceDIte]
    unfold ControlLengthBound at hbound ⊢
    exact (ligeritoStep_transcript_length_le round control answer).trans
      (by omega)
  · simp [hligerito, ControlLengthBound] at hbound ⊢
    omega

def SamplingLengthFits (prelude : List Byte) (maxPointLength : ℕ) : Prop :=
  prelude.length + productionSamplingSlots * 4096 + 18 ≤ maxPointLength

set_option maxRecDepth 10000 in
theorem scheduledStep_lengthBound
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (prelude : List Byte) (round : ℕ) (control : ScheduledControl shape)
    (answer : OracleBlock)
    (hbound : ControlLengthBound prelude round control.raw) :
    ControlLengthBound prelude (round + 1)
      (scheduledStep shape causalSecret completion witness coins round control
        answer).raw := by
  classical
  unfold scheduledStep
  split
  · exact rawStep_lengthBound shape causalSecret completion witness coins
      prelude round control.raw answer hbound
  · split
    · unfold ControlLengthBound at hbound ⊢
      dsimp
      omega
    · exact rawStep_lengthBound shape causalSecret completion witness coins
        prelude round control.raw answer hbound

theorem scheduledControlAfter_lengthBound
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    {rounds : ℕ} (answers : History (Outcome := OracleBlock) rounds) :
    ControlLengthBound prelude rounds
      (scheduledControlAfter shape causalSecret completion witness coins
        prelude answers).raw := by
  induction rounds with
  | zero => exact initialControl_lengthBound shape prelude
  | succ rounds ih =>
      exact scheduledStep_lengthBound shape causalSecret completion witness
        coins prelude rounds _ _ (ih _)
-/

end VeiledFlock.ProductionSamplingSchedule

import VeiledFlock.Production.Sampling.SamplingScheduleEqualityActive

/-! # Classification and freshness data for equality-stage queries -/

namespace VeiledFlock.ProductionSamplingScheduleEqualityQuery

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleEqualityAcceptedBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityActive
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionTranscriptFraming

theorem iterateEquality_eq_of_some (shape : BatchShape) (start rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hsome : control.equalityPoint.isSome = true) :
    iterateFrom (equalityStep shape) start rounds control answers = control := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last, ih (fun index ↦ answers index.castSucc)]
      simp [equalityStep, hsome]

set_option maxRecDepth 10000 in
theorem rawControlUntil_equality_after_first_isSome
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (attempt counter : ℕ)
    (hafter : firstEqualityAccepted shape answers hgood < attempt)
    (hattempt : attempt < rejectionTrials) (hcounter : counter < 7) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (equalityOffset + attempt * 7 + counter) (by
        have hnext := equalityBoundary_fits (attempt + 1) hattempt
        omega)).equalityPoint.isSome = true := by
  let first := firstEqualityAccepted shape answers hgood
  let extra := attempt - (first + 1)
  have hdecomp : first + 1 + extra = attempt := by
    dsimp only [extra, first]
    omega
  have hextraCap : firstEqualityAccepted shape answers hgood + 1 + extra ≤
      rejectionTrials := by
    rw [hdecomp]
    exact hattempt.le
  have hboundaryEq :=
    rawControlUntil_equality_boundary_after_first_eq shape causalSecret
      completion witness coins prelude answers hgood extra hextraCap
  let boundary := rawControlUntil shape causalSecret completion witness coins
    prelude answers (equalityOffset + attempt * 7)
      (equalityBoundary_fits attempt hattempt.le)
  have hboundarySome : boundary.equalityPoint.isSome = true := by
    rw [show boundary = rawControlUntil shape causalSecret completion witness
      coins prelude answers
        (equalityOffset +
          (firstEqualityAccepted shape answers hgood + 1 + extra) * 7)
        (equalityBoundary_fits
          (firstEqualityAccepted shape answers hgood + 1 + extra)
            hextraCap) by
          dsimp only [boundary]
          congr 2
          omega]
    rw [hboundaryEq]
    exact (rawControlUntil_after_first_equality_live_some shape causalSecret
      completion witness coins prelude answers hgood).2
  have hboundaryStatus : boundary.status = .live := by
    rw [show boundary = rawControlUntil shape causalSecret completion witness
      coins prelude answers
        (equalityOffset +
          (firstEqualityAccepted shape answers hgood + 1 + extra) * 7)
        (equalityBoundary_fits
          (firstEqualityAccepted shape answers hgood + 1 + extra)
            hextraCap) by
          dsimp only [boundary]
          congr 2
          omega]
    rw [hboundaryEq]
    exact (rawControlUntil_after_first_equality_live_some shape causalSecret
      completion witness coins prelude answers hgood).1
  have hfit : equalityOffset + attempt * 7 + counter ≤
      productionSamplingSlots := by
    have hnext := equalityBoundary_fits (attempt + 1) hattempt
    omega
  let localAnswers :=
    window (equalityOffset + attempt * 7) counter hfit answers
  have hlocalEq : iterateFrom (equalityStep shape)
      (equalityOffset + attempt * 7) counter boundary localAnswers = boundary :=
    iterateEquality_eq_of_some shape _ _ boundary localAnswers hboundarySome
  have hraw := rawEqualityAttempt_eq_of_final_live shape causalSecret completion
    witness coins attempt hattempt counter hcounter.le boundary localAnswers (by
      rw [hlocalEq]
      exact hboundaryStatus)
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers (equalityOffset + attempt * 7) counter hfit
  rw [hadd, hraw, hlocalEq]
  exact hboundarySome

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_active_equality_metadata
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (round : Fin productionSamplingSlots) (point : List Byte)
    (hlower : equalityOffset ≤ round.val)
    (hupper : round.val < zerocheckOffset)
    (hquery : rawQuery shape causalSecret completion witness coins round
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers round round.isLt.le) = some point) :
    let offset := round.val - equalityOffset
    let attempt := offset / equalityAttemptBlocks
    let counter := offset % equalityAttemptBlocks
    round.val = equalityOffset + attempt * 7 + counter ∧
      attempt ≤ firstEqualityAccepted shape answers hgood ∧
      counter < equalityBlockCount shape ∧
      point = slicePoint
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers round round.isLt.le).transcript
        (m shape - kSkip - 7) (BitVec.ofNat 64 counter) := by
  dsimp only
  let offset := round.val - equalityOffset
  let attempt := offset / equalityAttemptBlocks
  let counter := offset % equalityAttemptBlocks
  have hoffset : round.val = equalityOffset + offset := by
    dsimp only [offset]
    omega
  have hdecomp : offset = attempt * 7 + counter := by
    dsimp only [attempt, counter]
    have := (Nat.div_add_mod offset equalityAttemptBlocks).symm
    norm_num [equalityAttemptBlocks] at this ⊢
    omega
  have hround : round.val = equalityOffset + attempt * 7 + counter := by
    omega
  have hoffsetUpper : offset < equalityWidth := by
    norm_num [zerocheckOffset] at hupper
    omega
  have hattempt : attempt < rejectionTrials := by
    dsimp only [attempt]
    unfold equalityWidth at hoffsetUpper
    exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by
      simpa [equalityAttemptBlocks, Nat.mul_comm] using hoffsetUpper)
  have hcounterSix : counter < 7 := by
    dsimp only [counter]
    exact Nat.mod_lt _ (by decide)
  let control := rawControlUntil shape causalSecret completion witness coins
    prelude answers round round.isLt.le
  change rawQuery shape causalSecret completion witness coins round control =
    some point at hquery
  have hskip : ¬ round.val < equalitySkipBlocks := by
    norm_num [equalityOffset, equalitySkipBlocks] at hlower ⊢
    omega
  have hequality : round.val < zerocheckOffset := hupper
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hsome : control.equalityPoint.isSome
  · simp [rawQuery, hstatus, hskip, hequality, hsome] at hquery
  by_cases hcounter : counter < equalityBlockCount shape
  · have hattemptFirst :
        attempt ≤ firstEqualityAccepted shape answers hgood := by
      by_contra hnot
      have hafter : firstEqualityAccepted shape answers hgood < attempt := by
        omega
      have hsomeTrue := rawControlUntil_equality_after_first_isSome shape
        causalSecret completion witness coins prelude answers hgood attempt
        counter hafter hattempt hcounterSix
      have hcontrolEq : control = rawControlUntil shape causalSecret completion
          witness coins prelude answers (equalityOffset + attempt * 7 + counter)
            (by simpa [hround] using round.isLt.le) := by
        dsimp only [control]
        congr 2
      rw [hcontrolEq] at hsome
      simp [hsomeTrue] at hsome
    refine ⟨hround, hattemptFirst, hcounter, ?_⟩
    simp [rawQuery, hstatus, hskip, hequality, offset,  counter,
      hsome, hcounter] at hquery
    exact hquery.symm
  · simp [rawQuery, hstatus, hskip, hequality, offset,  counter,
      hsome, hcounter] at hquery

end VeiledFlock.ProductionSamplingScheduleEqualityQuery

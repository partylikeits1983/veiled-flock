import VeiledFlock.Production.Sampling.SamplingScheduleZerocheckPostFreshness

/-! # Exact transcript growth of a production equality attempt -/

namespace VeiledFlock.ProductionSamplingScheduleEqualityGrowth

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionTranscriptFraming

set_option maxRecDepth 10000 in
theorem equalityAttempt_transcript_length_eq
    (shape : BatchShape) (attempt : ℕ) (control : Control shape)
    (blocks : Fin 7 → OracleBlock)
    (hstatus : control.status = .live)
    (hnone : control.equalityPoint = none)
    (hskip : control.skip.isSome = true) :
    (iterateFrom (equalityStep shape)
      (equalityOffset + attempt * equalityAttemptBlocks) 7 control
      blocks).transcript.length =
        control.transcript.length + (10 + 16 * (m shape - kSkip - 7)) := by
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
        split <;> simp_all [afterSlice_length] <;>
        split <;> simp_all [afterSlice_length]

theorem equalityAttempt_transcript_length_strict
    (shape : BatchShape) (attempt : ℕ) (control : Control shape)
    (blocks : Fin 7 → OracleBlock)
    (hstatus : control.status = .live)
    (hnone : control.equalityPoint = none)
    (hskip : control.skip.isSome = true) :
    control.transcript.length <
      (iterateFrom (equalityStep shape)
        (equalityOffset + attempt * equalityAttemptBlocks) 7 control
        blocks).transcript.length := by
  rw [equalityAttempt_transcript_length_eq shape attempt control blocks hstatus
    hnone hskip]
  cases shape <;> norm_num [m, kSkip]

noncomputable def equalityAttemptAnswers (answers : SamplingAnswerTape)
    (attempt : Fin rejectionTrials) : Fin 7 → OracleBlock :=
  fun counter ↦ answers ⟨equalityOffset + attempt.val * 7 + counter.val, by
    have ha := attempt.isLt
    have hc := counter.isLt
    rw [productionSamplingSlots_eq]
    norm_num [equalityOffset, equalitySkipBlocks, rejectionTrials] at ha ⊢
    omega⟩

theorem equalityAttemptAnswers_eq_flat
    (answers : SamplingAnswerTape) (attempt : Fin rejectionTrials) :
    equalityAttemptAnswers answers attempt =
      equalityFlatEquiv
        (window equalityOffset equalityWidth (by
          rw [productionSamplingSlots_eq]
          decide) answers) attempt := by
  funext counter
  apply congrArg answers
  apply Fin.ext
  simp
  omega

set_option maxRecDepth 10000 in
theorem rawEqualityAttempt_eq_of_final_live
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (attempt : ℕ) (hattempt : attempt < rejectionTrials)
    (rounds : ℕ) (hrounds : rounds ≤ 7)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hfinal : (iterateFrom (equalityStep shape)
      (equalityOffset + attempt * 7) rounds control answers).status = .live) :
    iterateFrom (rawStep shape causalSecret completion witness coins)
        (equalityOffset + attempt * 7) rounds control answers =
      iterateFrom (equalityStep shape)
        (equalityOffset + attempt * 7) rounds control answers := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [iterateFrom_succ_last, iterateFrom_succ_last]
      have hprefix :
          (iterateFrom (equalityStep shape)
            (equalityOffset + attempt * 7) rounds control
              (fun index ↦ answers index.castSucc)).status = .live := by
        rw [iterateFrom_succ_last] at hfinal
        exact equalityStep_live_implies shape _ _ _ hfinal
      rw [ih (hrounds := by omega) (hfinal := hprefix)]
      have htrial : attempt * 7 + rounds < equalityWidth := by
        unfold equalityWidth equalityAttemptBlocks
        nlinarith
      have hround :
          equalityOffset + attempt * 7 + rounds =
            equalityOffset + (attempt * 7 + rounds) := by omega
      rw [hround]
      exact rawStep_equality shape causalSecret completion witness coins
        (attempt * 7 + rounds) htrial _ _ hprefix

theorem equalityBoundary_fits (attempt : ℕ)
    (hattempt : attempt ≤ rejectionTrials) :
    equalityOffset + attempt * 7 ≤ productionSamplingSlots := by
  rw [productionSamplingSlots_eq]
  norm_num [equalityOffset, equalitySkipBlocks, rejectionTrials] at hattempt ⊢
  omega

set_option maxRecDepth 10000 in
theorem rawControlUntil_equality_boundary_step
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (attempt : ℕ)
    (hattempt : attempt < rejectionTrials)
    (hfinal :
      (iterateFrom (equalityStep shape)
        (equalityOffset + attempt * 7) 7
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + attempt * 7)
            (equalityBoundary_fits attempt hattempt.le))
        (equalityAttemptAnswers answers ⟨attempt, hattempt⟩)).status = .live) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (equalityOffset + (attempt + 1) * 7)
          (equalityBoundary_fits (attempt + 1) (by omega)) =
      iterateFrom (equalityStep shape)
        (equalityOffset + attempt * 7) 7
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (equalityOffset + attempt * 7)
            (equalityBoundary_fits attempt hattempt.le))
        (equalityAttemptAnswers answers ⟨attempt, hattempt⟩) := by
  have hfit := equalityBoundary_fits (attempt + 1) (by omega)
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers (equalityOffset + attempt * 7) 7 (by
      simpa only [Nat.add_assoc, Nat.add_mul, Nat.one_mul] using hfit)
  have hraw := rawEqualityAttempt_eq_of_final_live shape causalSecret completion
    witness coins attempt hattempt 7 (by rfl)
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (equalityOffset + attempt * 7)
        (equalityBoundary_fits attempt hattempt.le))
    (equalityAttemptAnswers answers ⟨attempt, hattempt⟩) hfinal
  simpa only [Nat.add_assoc, Nat.add_mul, Nat.one_mul] using hadd.trans hraw

end VeiledFlock.ProductionSamplingScheduleEqualityGrowth

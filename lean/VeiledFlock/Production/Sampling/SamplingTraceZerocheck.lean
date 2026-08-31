import VeiledFlock.Production.Sampling.SamplingTraceEquality

/-! # Zerocheck adaptive-run refinement for the operational schedule -/

namespace VeiledFlock.ProductionSamplingTraceZerocheck

open VeiledFlock.AdaptiveOracleProgramming
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
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole
open VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness
open VeiledFlock.ProductionSamplingTraceEquality

theorem equalityStep_zerocheckAnswers
    (shape : BatchShape) (round : ℕ) (control : Control shape)
    (answer : OracleBlock) :
    (equalityStep shape round control answer).zerocheckAnswers =
      control.zerocheckAnswers := by
  classical
  simp [equalityStep]
  repeat' (first | rfl | split)

theorem rawStep_zerocheckAnswers_eq_of_before
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (round : ℕ) (control : Control shape) (answer : OracleBlock)
    (hround : round < zerocheckOffset) :
    (rawStep shape causalSecret completion witness coins round control
      answer).zerocheckAnswers = control.zerocheckAnswers := by
  classical
  by_cases hstatus : control.status != .live
  · simp [rawStep, hstatus]
  by_cases hskip : round < equalitySkipBlocks
  · simp [rawStep, hstatus, hskip]
    split <;> rfl
  · have hequality : round < zerocheckOffset := hround
    simp [rawStep, hstatus, hskip, hequality,
      equalityStep_zerocheckAnswers]

theorem rawControlUntil_zerocheckAnswers_nil_before
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (rounds : ℕ)
    (hrounds : rounds ≤ zerocheckOffset) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      rounds (hrounds.trans (by decide))).zerocheckAnswers = [] := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      have hround : rounds < zerocheckOffset := by omega
      have hsucc := rawControlUntil_succ shape causalSecret completion witness
        coins prelude answers ⟨rounds, hround.trans (by decide)⟩
      rw [hsucc, rawStep_zerocheckAnswers_eq_of_before shape causalSecret
        completion witness coins rounds _ _ hround]
      exact ih (by omega)

set_option maxRecDepth 10000 in
theorem rawControlUntil_zerocheck_prefix_fields
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (rounds : ℕ) (hrounds : rounds ≤ programmedPoints shape) :
    let start := rawControlUntil shape causalSecret completion witness coins
      prelude answers zerocheckOffset (by decide)
    let current := rawControlUntil shape causalSecret completion witness coins
      prelude answers (zerocheckOffset + rounds) (by
        exact (Nat.add_le_add_left hrounds zerocheckOffset).trans
          (zerocheckActiveEnd_le_slots shape))
    current.status = .live ∧ current.equalityPoint.isSome = true ∧
      current.zerocheckAnswers =
        List.ofFn (window zerocheckOffset rounds (by
          exact (Nat.add_le_add_left hrounds zerocheckOffset).trans
            (zerocheckActiveEnd_le_slots shape)) answers) ∧
      (rounds < programmedPoints shape →
        current.transcript = start.transcript) := by
  induction rounds with
  | zero =>
      have hstart := rawControlUntil_equality_live_some shape causalSecret
        completion witness coins prelude answers
          (equality_accepted_of_not_globalBad shape answers hgood)
      have hnil := rawControlUntil_zerocheckAnswers_nil_before shape
        causalSecret completion witness coins prelude answers zerocheckOffset
        (by rfl)
      constructor
      · exact hstart.1
      constructor
      · exact hstart.2
      constructor
      · exact hnil
      · intro _
        rfl
  | succ rounds ih =>
      have hround : rounds < programmedPoints shape := by omega
      have hp := VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness.programmedPoints_le_max shape
      let site : Fin productionSamplingSlots :=
        ⟨zerocheckOffset + rounds, by
          exact (Nat.add_lt_add_left hround zerocheckOffset).trans_le
            (zerocheckActiveEnd_le_slots shape)⟩
      have hprev := ih hround.le
      have hsucc := rawControlUntil_succ shape causalSecret completion witness
        coins prelude answers site
      have hraw := rawStep_zerocheck shape causalSecret completion witness coins
        rounds (hround.trans_le hp) _ (answers site) hprev.1
      rw [hraw] at hsucc
      let previous := rawControlUntil shape causalSecret completion witness coins
        prelude answers (zerocheckOffset + rounds) site.isLt.le
      have hsucc' : rawControlUntil shape causalSecret completion witness coins
          prelude answers (zerocheckOffset + (rounds + 1)) (by
            exact (Nat.add_le_add_left hrounds zerocheckOffset).trans
              (zerocheckActiveEnd_le_slots shape)) =
          zerocheckStep shape causalSecret completion witness coins
            (zerocheckOffset + rounds) previous (answers site) := by
        simpa only [site, Nat.add_assoc] using hsucc
      have hequality : previous.equalityPoint.isSome = true := hprev.2.1
      cases hpoint : previous.equalityPoint with
      | none => simp [hpoint] at hequality
      | some equalityPoint =>
          have hsite : zerocheckOffset + rounds - zerocheckOffset <
              programmedPoints shape := by omega
          have hnextStatus :
              (zerocheckStep shape causalSecret completion witness coins
                (zerocheckOffset + rounds) previous (answers site)).status =
                .live :=
            (zerocheckStep_preserves_live_and_equality shape causalSecret
              completion witness coins _ previous (answers site) hprev.1
              hequality).1
          have hnextEquality :
              (zerocheckStep shape causalSecret completion witness coins
                (zerocheckOffset + rounds) previous
                (answers site)).equalityPoint.isSome = true :=
            (zerocheckStep_preserves_live_and_equality shape causalSecret
              completion witness coins _ previous (answers site) hprev.1
              hequality).2
          have hanswers :
              (zerocheckStep shape causalSecret completion witness coins
                (zerocheckOffset + rounds) previous
                (answers site)).zerocheckAnswers =
                previous.zerocheckAnswers ++ [answers site] := by
            simp [zerocheckStep, hpoint,  hround]
            split <;> rfl
          constructor
          · exact (congrArg Control.status hsucc').trans hnextStatus
          constructor
          · exact (congrArg (fun c ↦ c.equalityPoint.isSome) hsucc').trans
              hnextEquality
          constructor
          · rw [congrArg Control.zerocheckAnswers hsucc', hanswers,
              hprev.2.2.1]
            rw [List.ofFn_succ', List.concat_eq_append]
            congr 1
          · intro hnotLast
            have hnotFinal : rounds + 1 ≠ programmedPoints shape := by omega
            rw [congrArg Control.transcript hsucc']
            simp [zerocheckStep, hpoint, hround, hnotFinal]
            exact hprev.2.2.2 hround

set_option maxRecDepth 10000 in
theorem zerocheck_run_eq_answer_window
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle) :
    let absorbedPrefix :=
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers zerocheckOffset (by decide)).transcript
    AdaptiveOracleProgramming.run
        (zerocheckRealByteSchedule shape causalSecret completion absorbedPrefix
          witness coins) oracle (programmedPoints shape) =
      window zerocheckOffset (programmedPoints shape) (by
        exact zerocheckActiveEnd_le_slots shape) answers := by
  dsimp only
  let schedule := zerocheckRealByteSchedule shape causalSecret completion
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      zerocheckOffset (by decide)).transcript witness coins
  have hprefix : ∀ rounds (hrounds : rounds ≤ programmedPoints shape),
      AdaptiveOracleProgramming.run schedule oracle rounds =
        window zerocheckOffset rounds (by
          exact (Nat.add_le_add_left hrounds zerocheckOffset).trans
            (zerocheckActiveEnd_le_slots shape)) answers := by
    intro rounds hrounds
    induction rounds with
    | zero =>
        funext index
        exact Fin.elim0 index
    | succ rounds ih =>
        have hround : rounds < programmedPoints shape := by omega
        have ih' := ih hround.le
        funext index
        refine Fin.lastCases ?_ (fun prior ↦ ?_) index
        · rw [AdaptiveOracleProgramming.run_succ_last, ih']
          let site : Fin productionSamplingSlots :=
            ⟨zerocheckOffset + rounds, by
              exact (Nat.add_lt_add_left hround zerocheckOffset).trans_le
                (zerocheckActiveEnd_le_slots shape)⟩
          have hfields := rawControlUntil_zerocheck_prefix_fields shape
            causalSecret completion witness coins prelude answers hgood rounds
            hround.le
          let current := rawControlUntil shape causalSecret completion witness
            coins prelude answers (zerocheckOffset + rounds) (by
              exact (Nat.add_le_add_left hround.le zerocheckOffset).trans
                (zerocheckActiveEnd_le_slots shape))
          have hcontrolEq : rawControlUntil shape causalSecret completion witness
              coins prelude answers site site.isLt.le = current := by
            rfl
          have hquery : rawQuery shape causalSecret completion witness coins site
              (rawControlUntil shape causalSecret completion witness coins prelude
                answers site site.isLt.le) =
                some (schedule rounds
                  (window zerocheckOffset rounds (by
                    exact (Nat.add_le_add_left hround.le zerocheckOffset).trans
                      (zerocheckActiveEnd_le_slots shape)) answers)) := by
            have hstatus : current.status = .live := hfields.1
            have hequality : current.equalityPoint.isSome = true := hfields.2.1
            rw [hcontrolEq]
            cases hpoint : current.equalityPoint with
            | none => simp [hpoint] at hequality
            | some equalityPoint =>
                have hsite : site.val - zerocheckOffset <
                    programmedPoints shape := by simp [site]; omega
                have hskip : ¬ site.val < equalitySkipBlocks := by
                  simp [site, zerocheckOffset, equalityOffset,
                    equalitySkipBlocks, equalityWidth]
                  omega
                have hequalityRange : ¬ site.val < zerocheckOffset := by
                  simp [site]
                have hzero : site.val < blindStateOffset := by
                  have hp := VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness.programmedPoints_le_max shape
                  simp only [site]
                  rw [← show zerocheckOffset + maxProgrammedPoints =
                    blindStateOffset by rfl]
                  omega
                have hhistory : historyFromList
                    current.zerocheckAnswers rounds =
                      window zerocheckOffset rounds (by
                        exact (Nat.add_le_add_left hround.le
                          zerocheckOffset).trans
                            (zerocheckActiveEnd_le_slots shape)) answers := by
                  rw [hfields.2.2.1]
                  funext prior
                  simp [historyFromList]
                simp [rawQuery, site, hstatus, hskip, hequalityRange, hzero,
                  hpoint,  schedule]
                constructor
                · exact hround
                · have hoffset : site.val - zerocheckOffset = rounds := by
                    simp [site]
                  rw [hoffset, hhistory]
                  have ht := hfields.2.2.2 hround
                  change current.transcript = _ at ht
                  rw [ht]
          rw [← hagrees site _ hquery]
          rfl
        · rw [AdaptiveOracleProgramming.run_succ_castSucc]
          rw [congrFun ih' prior]
          apply congrArg answers
          apply Fin.ext
          rfl
  exact hprefix (programmedPoints shape) (by rfl)

end VeiledFlock.ProductionSamplingTraceZerocheck

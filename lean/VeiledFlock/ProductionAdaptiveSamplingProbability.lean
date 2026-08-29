import VeiledFlock.AdaptiveOracleProgramming
import VeiledFlock.ProductionBoundedOracle
import VeiledFlock.ProductionGrindingProjection
import VeiledFlock.ProductionScalarProjection

/-!
# Adaptive production sampling probabilities

The production Fiat--Shamir transcript grows after every answer, so later
random-oracle inputs depend on earlier random answers.  This module connects
those literal byte queries to `AdaptiveOracleProgramming` and proves that the
complete block vector seen by a bounded scalar sampler is exactly uniform.
It is the operational probability bridge used for rejection and distinct-
position failure events; no independence premise is assumed.
-/

namespace VeiledFlock.ProductionAdaptiveSamplingProbability

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.ProductionTranscriptFraming

/-- Transcript obtained after reabsorbing a proposed vector of scalar-squeeze
blocks in chronological order. -/
noncomputable def scalarTranscriptAfter (initial : List Byte) {rounds : ℕ}
    (answers : History (Outcome := OracleBlock) rounds) : List Byte :=
  (List.ofFn answers).foldl afterScalar initial

@[simp]
theorem scalarTranscriptAfter_zero (initial : List Byte)
    (answers : History (Outcome := OracleBlock) 0) :
    scalarTranscriptAfter initial answers = initial := by
  simp [scalarTranscriptAfter]

@[simp]
theorem scalarTranscriptAfter_length (initial : List Byte) {rounds : ℕ}
    (answers : History (Outcome := OracleBlock) rounds) :
    (scalarTranscriptAfter initial answers).length =
      initial.length + rounds * 18 := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [scalarTranscriptAfter, List.ofFn_succ', List.concat_eq_append,
        List.foldl_concat]
      change
        (afterScalar
          ((List.ofFn fun index => answers index.castSucc).foldl
            afterScalar initial)
          (answers (Fin.last rounds))).length = _
      rw [afterScalar_length]
      have hprefix := ih (fun index => answers index.castSucc)
      rw [scalarTranscriptAfter] at hprefix
      rw [hprefix]
      omega

/-- Literal causal scalar-squeeze point after the proposed preceding blocks. -/
noncomputable def scalarByteSchedule (initial : List Byte) :
    Schedule (Point := List Byte) (Outcome := OracleBlock) :=
  fun _rounds answers => scalarPoint (scalarTranscriptAfter initial answers)

/-- Embed the first `trials` scalar-squeeze queries into the actual finite
production oracle universe.  Natural rounds beyond the audited public cap
are sent to the empty byte string and are never reached by the run below. -/
noncomputable def boundedScalarSchedule (initial : List Byte) (trials maxLength : ℕ)
    (hbudget : initial.length + trials * 18 ≤ maxLength) :
    Schedule (Point := BoundedBytes maxLength) (Outcome := OracleBlock) :=
  fun rounds answers =>
    if hround : rounds < trials then
      boundBytes (scalarPoint (scalarTranscriptAfter initial answers)) (by
        rw [scalarPoint_length, scalarTranscriptAfter_length]
        omega)
    else
      boundBytes [] (by simp)

@[simp]
theorem unbound_tracePoint_boundedScalarSchedule
    (initial : List Byte) (trials maxLength : ℕ)
    (hbudget : initial.length + trials * 18 ≤ maxLength)
    (answers : History (Outcome := OracleBlock) trials) (site : Fin trials) :
    unboundBytes
        (tracePoint (boundedScalarSchedule initial trials maxLength hbudget)
          answers site) =
      scalarPoint
        (scalarTranscriptAfter initial (priorAnswers answers site)) := by
  simp [tracePoint, boundedScalarSchedule, site.isLt]

/-- Transcript length makes the actual scalar-squeeze inputs pairwise
distinct, even though their byte contents depend on all prior answers. -/
theorem boundedScalarSchedule_tracePoints_injective
    (initial : List Byte) (trials maxLength : ℕ)
    (hbudget : initial.length + trials * 18 ≤ maxLength)
    (answers : History (Outcome := OracleBlock) trials) :
    Injective
      (tracePoints (boundedScalarSchedule initial trials maxLength hbudget)
        answers) := by
  intro left right heq
  have hunbound := congrArg unboundBytes heq
  change
    unboundBytes
        (tracePoint (boundedScalarSchedule initial trials maxLength hbudget)
          answers left) =
      unboundBytes
        (tracePoint (boundedScalarSchedule initial trials maxLength hbudget)
          answers right) at hunbound
  rw [unbound_tracePoint_boundedScalarSchedule,
    unbound_tracePoint_boundedScalarSchedule] at hunbound
  have hlength := congrArg List.length hunbound
  simp only [scalarPoint_length, scalarTranscriptAfter_length] at hlength
  apply Fin.ext
  omega

/-- Operational oracle tables for which every one of the fresh adaptive
scalar-squeeze answers lies in `failed`. -/
noncomputable def adaptiveScalarAbortOracles (initial : List Byte)
    (trials maxLength : ℕ)
    (hbudget : initial.length + trials * 18 ≤ maxLength)
    (failed : Finset VeiledFlock.Field128Ghash.GhashField) :
    Finset (BoundedBytes maxLength → OracleBlock) :=
  adaptiveBadOracles
    (boundedScalarSchedule initial trials maxLength hbudget)
    (scalarBlockAbortRuns failed trials)

theorem mem_adaptiveScalarAbortOracles_iff
    (initial : List Byte) (trials maxLength : ℕ)
    (hbudget : initial.length + trials * 18 ≤ maxLength)
    (failed : Finset VeiledFlock.Field128Ghash.GhashField)
    (table : BoundedBytes maxLength → OracleBlock) :
    table ∈ adaptiveScalarAbortOracles initial trials maxLength hbudget failed ↔
      ∀ site,
        scalarFromBlock
            (run (boundedScalarSchedule initial trials maxLength hbudget)
              table trials site) ∈ failed := by
  rw [adaptiveScalarAbortOracles, mem_adaptiveBadOracles_iff,
    mem_scalarBlockAbortRuns_iff]

/-- Exact failure probability for a bounded scalar sampler at a fixed live
transcript, evaluated on the actual finite production oracle table. -/
theorem adaptiveScalarAbortOracles_probability_eq
    (initial : List Byte) (trials maxLength : ℕ)
    (hbudget : initial.length + trials * 18 ≤ maxLength)
    (failed : Finset VeiledFlock.Field128Ghash.GhashField) :
    ((adaptiveScalarAbortOracles initial trials maxLength hbudget failed).card : ℚ) /
        Fintype.card (BoundedBytes maxLength → OracleBlock) =
      ((scalarBlockAbortRuns failed trials).card : ℚ) /
        Fintype.card (Fin trials → OracleBlock) := by
  exact adaptiveBadOracles_probability_eq
    (boundedScalarSchedule initial trials maxLength hbudget)
    (boundedScalarSchedule_tracePoints_injective initial trials maxLength
      hbudget)
    (scalarBlockAbortRuns failed trials)

end VeiledFlock.ProductionAdaptiveSamplingProbability

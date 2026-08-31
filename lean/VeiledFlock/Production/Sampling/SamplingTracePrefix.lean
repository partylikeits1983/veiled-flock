import VeiledFlock.Production.Sampling.SamplingTraceLigerito

/-! # Exact production prefix refinement -/

namespace VeiledFlock.ProductionSamplingTracePrefix

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleEqualityAcceptedBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionSamplingTraceScalar
open VeiledFlock.ProductionSamplingTraceZerocheck
open VeiledFlock.ProductionTranscriptFraming

set_option maxRecDepth 10000 in
theorem raw_zerocheck_start_transcript_eq_equality_sample
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
    let _firstBoundary := rawControlUntil shape causalSecret completion witness
      coins prelude answers (equalityOffset + first * 7)
        (equalityBoundary_fits first
          (firstEqualityAccepted_lt shape answers hgood).le)
    let outer := sliceFromBlocks (m shape - kSkip - 7)
      (List.ofFn (equalityAttemptAnswers answers
        ⟨first, firstEqualityAccepted_lt shape answers hgood⟩))
    sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
        rejectionTrials prelude =
      some (skip, outer,
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers zerocheckOffset (by decide)).transcript) := by
  dsimp only
  have hsample := sampleEqualityPointPrefix_eq_some_raw shape causalSecret
    completion witness coins prelude answers hgood oracle hagrees
  dsimp only at hsample
  let first := firstEqualityAccepted shape answers hgood
  let firstBoundary := rawControlUntil shape causalSecret completion witness coins
    prelude answers (equalityOffset + first * 7)
      (equalityBoundary_fits first
        (firstEqualityAccepted_lt shape answers hgood).le)
  have hstep := production_equality_boundary_succ_transcript shape causalSecret
    completion witness coins prelude answers hgood first (by rfl)
  have hextra : first + 1 + (rejectionTrials - (first + 1)) =
      rejectionTrials := by
    have hlt := firstEqualityAccepted_lt shape answers hgood
    omega
  have hstable := rawControlUntil_equality_boundary_after_first_eq shape
    causalSecret completion witness coins prelude answers hgood
    (rejectionTrials - (first + 1)) (by omega)
  have hstableTranscript := congrArg Control.transcript hstable
  have hleft : equalityOffset +
      (firstEqualityAccepted shape answers hgood + 1 +
        (rejectionTrials -
          (firstEqualityAccepted shape answers hgood + 1))) * 7 =
      zerocheckOffset := by
    rw [hextra]
    rfl
  have htransport := rawControlUntil_round_eq shape causalSecret completion
    witness coins prelude answers (left := zerocheckOffset)
    (right := equalityOffset +
      (firstEqualityAccepted shape answers hgood + 1 +
        (rejectionTrials -
          (firstEqualityAccepted shape answers hgood + 1))) * 7)
    (by decide) (by rw [hleft]; decide) hleft.symm
  have hfinal :
      afterSlice firstBoundary.transcript
          (sliceFromBlocks (m shape - kSkip - 7)
            (List.ofFn (equalityAttemptAnswers answers
              ⟨first, firstEqualityAccepted_lt shape answers hgood⟩))) =
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers zerocheckOffset (by decide)).transcript := by
    calc
      afterSlice firstBoundary.transcript
          (sliceFromBlocks (m shape - kSkip - 7)
            (List.ofFn (equalityAttemptAnswers answers
              ⟨first, firstEqualityAccepted_lt shape answers hgood⟩))) =
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (equalityOffset + (first + 1) * 7)
              (equalityBoundary_fits (first + 1)
                (firstEqualityAccepted_lt shape answers hgood))).transcript :=
        hstep.symm
      _ = (rawControlUntil shape causalSecret completion witness coins prelude
            answers (equalityOffset +
              (firstEqualityAccepted shape answers hgood + 1 +
                (rejectionTrials -
                  (firstEqualityAccepted shape answers hgood + 1))) * 7) _).transcript :=
        hstableTranscript.symm
      _ = (rawControlUntil shape causalSecret completion witness coins prelude
            answers zerocheckOffset (by decide)).transcript :=
        (congrArg Control.transcript htransport).symm
  rw [hfinal] at hsample
  exact hsample

set_option maxRecDepth 10000 in
theorem raw_active_zerocheck_transcript_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    let start := rawControlUntil shape causalSecret completion witness coins
      prelude answers zerocheckOffset (by decide)
    let activeEnd := rawControlUntil shape causalSecret completion witness coins
      prelude answers (zerocheckOffset + programmedPoints shape)
        (zerocheckActiveEnd_le_slots shape)
    activeEnd.transcript = afterZerocheck shape causalSecret completion
      start.transcript witness coins
        (window zerocheckOffset (programmedPoints shape)
          (zerocheckActiveEnd_le_slots shape) answers) := by
  dsimp only
  have hpp : 0 < programmedPoints shape := by cases shape <;> decide
  let rounds := programmedPoints shape - 1
  have hrounds : rounds < programmedPoints shape := by
    dsimp only [rounds]
    omega
  let site : Fin productionSamplingSlots :=
    ⟨zerocheckOffset + rounds,
      (Nat.add_lt_add_left hrounds zerocheckOffset).trans_le
        (zerocheckActiveEnd_le_slots shape)⟩
  let previous := rawControlUntil shape causalSecret completion witness coins
    prelude answers (zerocheckOffset + rounds)
      ((Nat.add_le_add_left hrounds.le zerocheckOffset).trans
        (zerocheckActiveEnd_le_slots shape))
  have hfields := rawControlUntil_zerocheck_prefix_fields shape causalSecret
    completion witness coins prelude answers hgood rounds hrounds.le
  have hstatus : previous.status = .live := hfields.1
  have hequality : previous.equalityPoint.isSome = true := hfields.2.1
  have hsucc := rawControlUntil_succ shape causalSecret completion witness
    coins prelude answers site
  have hraw := rawStep_zerocheck shape causalSecret completion witness coins
    rounds (hrounds.trans_le
      (VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness.programmedPoints_le_max shape))
    previous (answers site) hstatus
  have hpreviousEq : rawControlUntil shape causalSecret completion witness coins
      prelude answers site site.isLt.le = previous := by rfl
  rw [hpreviousEq, hraw] at hsucc
  cases hpoint : previous.equalityPoint with
  | none => simp [hpoint] at hequality
  | some equalityPoint =>
      have hsite : zerocheckOffset + rounds - zerocheckOffset <
          programmedPoints shape := by omega
      have hlast : zerocheckOffset + rounds - zerocheckOffset + 1 =
          programmedPoints shape := by
        dsimp only [rounds]
        omega
      have hblocks : previous.zerocheckAnswers ++ [answers site] =
          List.ofFn (window zerocheckOffset (programmedPoints shape)
            (zerocheckActiveEnd_le_slots shape) answers) := by
        rw [hfields.2.2.1]
        apply List.ext_get
        · simp [rounds]
          omega
        · intro index hleft hright
          by_cases hindex : index < rounds
          · simp [hindex, FixedWindowProbability.window]
          · have hindexEq : index = rounds := by
              simp at hleft hright
              dsimp only [rounds] at *
              omega
            subst index
            simp [FixedWindowProbability.window, site]
      have hhistory : historyFromList
          (previous.zerocheckAnswers ++ [answers site])
            (programmedPoints shape) =
          window zerocheckOffset (programmedPoints shape)
            (zerocheckActiveEnd_le_slots shape) answers := by
        rw [hblocks]
        funext index
        simp [historyFromList]
      have hstepTranscript :
          (zerocheckStep shape causalSecret completion witness coins
            (zerocheckOffset + rounds) previous (answers site)).transcript =
          afterZerocheck shape causalSecret completion previous.transcript
            witness coins
              (window zerocheckOffset (programmedPoints shape)
                (zerocheckActiveEnd_le_slots shape) answers) := by
        have hroundLast : rounds + 1 = programmedPoints shape := by
          dsimp only [rounds]
          omega
        simp [zerocheckStep, hpoint, hrounds, hroundLast, hhistory]
      have hstartTranscript : previous.transcript =
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers zerocheckOffset (by decide)).transcript :=
        hfields.2.2.2 hrounds
      have hendRound : zerocheckOffset + rounds + 1 =
          zerocheckOffset + programmedPoints shape := by
        dsimp only [rounds]
        omega
      have htransport := rawControlUntil_round_eq shape causalSecret completion
        witness coins prelude answers
        (left := zerocheckOffset + programmedPoints shape)
        (right := site.val + 1) (zerocheckActiveEnd_le_slots shape)
        (by simpa [site, hendRound] using zerocheckActiveEnd_le_slots shape)
        (by simp [site, hendRound])
      rw [congrArg Control.transcript htransport]
      rw [congrArg Control.transcript hsucc, hstepTranscript, hstartTranscript]

set_option maxRecDepth 10000 in
theorem raw_zerocheck_padding_stable
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hstatus : (rawControlUntil shape causalSecret completion witness coins
      prelude answers (zerocheckOffset + programmedPoints shape)
        (zerocheckActiveEnd_le_slots shape)).status = .live)
    (hequality : (rawControlUntil shape causalSecret completion witness coins
      prelude answers (zerocheckOffset + programmedPoints shape)
        (zerocheckActiveEnd_le_slots shape)).equalityPoint.isSome = true) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        blindStateOffset (by decide) =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        (zerocheckOffset + programmedPoints shape)
          (zerocheckActiveEnd_le_slots shape) := by
  let remaining := maxProgrammedPoints - programmedPoints shape
  have hsum : programmedPoints shape + remaining = maxProgrammedPoints := by
    dsimp only [remaining]
    have hp := VeiledFlock.ProductionSamplingScheduleZerocheckPostFreshness.programmedPoints_le_max shape
    omega
  have hstable : ∀ (extra : ℕ)
      (hcap : programmedPoints shape + extra ≤ maxProgrammedPoints),
      rawControlUntil shape causalSecret completion witness coins prelude answers
          (zerocheckOffset + (programmedPoints shape + extra)) (by
            have : zerocheckOffset + maxProgrammedPoints ≤
                productionSamplingSlots := by decide
            omega) =
        rawControlUntil shape causalSecret completion witness coins prelude answers
          (zerocheckOffset + programmedPoints shape)
            (zerocheckActiveEnd_le_slots shape) := by
    intro extra hcap
    induction extra with
    | zero =>
        have htransport := rawControlUntil_round_eq shape causalSecret completion
          witness coins prelude answers
          (left := zerocheckOffset + (programmedPoints shape + 0))
          (right := zerocheckOffset + programmedPoints shape)
          (by
            have : zerocheckOffset + maxProgrammedPoints ≤
                productionSamplingSlots := by decide
            omega)
          (zerocheckActiveEnd_le_slots shape) (by omega)
        exact htransport
    | succ extra ih =>
        have hbefore : programmedPoints shape + extra < maxProgrammedPoints := by
          omega
        let round := programmedPoints shape + extra
        let site : Fin productionSamplingSlots :=
          ⟨zerocheckOffset + round, by
            have : zerocheckOffset + maxProgrammedPoints ≤
                productionSamplingSlots := by decide
            omega⟩
        let current := rawControlUntil shape causalSecret completion witness coins
          prelude answers (zerocheckOffset + round) site.isLt.le
        have ih' := ih (by omega)
        have hcurrentEq : current =
            rawControlUntil shape causalSecret completion witness coins prelude
              answers (zerocheckOffset + programmedPoints shape)
                (zerocheckActiveEnd_le_slots shape) := by
          simpa only [current, round, Nat.add_assoc] using ih'
        have hcurrentStatus : current.status = .live := by
          rw [hcurrentEq]
          exact hstatus
        have hcurrentEquality : current.equalityPoint.isSome = true := by
          rw [hcurrentEq]
          exact hequality
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers site
        have hraw := rawStep_zerocheck shape causalSecret completion witness coins
          round (by omega) current (answers site) hcurrentStatus
        rw [hraw] at hsucc
        have hstepEq : zerocheckStep shape causalSecret completion witness coins
            (zerocheckOffset + round) current (answers site) = current := by
          cases hpoint : current.equalityPoint with
          | none => simp [hpoint] at hcurrentEquality
          | some equalityPoint =>
              have hroundNot : ¬round < programmedPoints shape := by
                dsimp only [round]
                omega
              simp [zerocheckStep, hpoint, hroundNot]
        rw [hstepEq] at hsucc
        have hnext : rawControlUntil shape causalSecret completion witness coins
            prelude answers (zerocheckOffset +
              (programmedPoints shape + (extra + 1))) (by
                have : zerocheckOffset + maxProgrammedPoints ≤
                    productionSamplingSlots := by decide
                omega) = current := by
          simpa only [site, round, Nat.add_assoc] using hsucc
        exact hnext.trans hcurrentEq
  have hremaining := hstable remaining (by omega)
  have hround : zerocheckOffset + (programmedPoints shape + remaining) =
      blindStateOffset := by
    rw [hsum]
    rfl
  have htransport := rawControlUntil_round_eq shape causalSecret completion
    witness coins prelude answers (left := blindStateOffset)
    (right := zerocheckOffset + (programmedPoints shape + remaining))
    (by decide)
    (by
      have : zerocheckOffset + maxProgrammedPoints ≤
          productionSamplingSlots := by decide
      omega) hround.symm
  exact htransport.trans hremaining

end VeiledFlock.ProductionSamplingTracePrefix

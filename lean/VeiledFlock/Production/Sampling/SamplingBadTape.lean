import VeiledFlock.Algebra.EndToEnd
import VeiledFlock.Core.Birthday
import VeiledFlock.Core.FixedWindowProbability
import VeiledFlock.Production.Core.GrindingProjection
import VeiledFlock.Production.Sampling.SamplingLayout
import VeiledFlock.Production.Core.ScalarProjection

/-!
# Explicit bounded-sampling bad set

This is the operational rejection/grinding ledger on one fixed answer tape.
It does not yet identify that tape with the answers reached in a random-oracle
execution; that causal bridge is kept separate.
-/

namespace VeiledFlock.ProductionSamplingBadTape

open VeiledFlock.ChallengeSampling
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.Birthday
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.EndToEnd
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Grinding
open VeiledFlock.Probability
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionScalarProjection
open VeiledFlock.UniquePositionSampling

abbrev SamplingAnswerTape := Fin productionSamplingSlots → OracleBlock

/-- The blind PoW state followed by the state for each production Ligerito
grinding site. -/
def powStateCount : ℕ := 1 + maxLigeritoSites

/-- Fixed locations at which the production schedule samples a fresh PoW
state.  State zero is the blind-grinding state; the remaining states begin
the Ligerito grinding sites. -/
def powStateIndex (site : Fin powStateCount) : Fin productionSamplingSlots :=
  if hzero : site.val = 0 then
    ⟨blindStateOffset, by
      rw [productionSamplingSlots_eq]
      decide⟩
  else
    ⟨ligeritoOffset + (site.val - 1) * ligeritoSiteWidth, by
      have hsite : site.val - 1 < maxLigeritoSites := by
        have := site.isLt
        unfold powStateCount at this
        omega
      unfold productionSamplingSlots ligeritoWidth
      have hwidth : 0 < ligeritoSiteWidth := by
        unfold ligeritoSiteWidth
        omega
      nlinarith⟩

theorem powStateIndex_injective : Function.Injective powStateIndex := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp only [powStateIndex] at hval
  by_cases hleft : left.val = 0
  · by_cases hright : right.val = 0
    · omega
    · simp [hleft, hright] at hval
      have hsep : blindStateOffset < ligeritoOffset := by decide
      omega
  · by_cases hright : right.val = 0
    · simp [hleft, hright] at hval
      have hsep : blindStateOffset < ligeritoOffset := by decide
      omega
    · simp [hleft, hright] at hval
      norm_num [ligeritoSiteWidth, maxLigeritoTrials] at hval
      omega

/-- A fixed injective schedule exposing exactly the sampled PoW states. -/
def powStateSchedule :
    Schedule (Point := Fin productionSamplingSlots) (Outcome := OracleBlock) :=
  fun round _history ↦
    if hround : round < powStateCount then powStateIndex ⟨round, hround⟩
    else ⟨0, by
      rw [productionSamplingSlots_eq]
      decide⟩

@[simp]
theorem tracePoint_powStateSchedule
    (answers : History (Outcome := OracleBlock) powStateCount)
    (site : Fin powStateCount) :
    tracePoint powStateSchedule answers site = powStateIndex site := by
  simp [tracePoint, powStateSchedule, site.isLt]

theorem powStateSchedule_tracePoints_injective
    (answers : History (Outcome := OracleBlock) powStateCount) :
    Function.Injective (tracePoints powStateSchedule answers) := by
  intro left right heq
  rw [tracePoints, tracePoint_powStateSchedule,
    tracePoint_powStateSchedule] at heq
  exact powStateIndex_injective heq

@[simp]
theorem run_powStateSchedule (answers : SamplingAnswerTape) :
    run powStateSchedule answers powStateCount =
      fun site ↦ answers (powStateIndex site) := by
  funext site
  rw [← oracle_tracePoint_run powStateSchedule answers site,
    tracePoint_powStateSchedule]

/-- Reindex the flat equality reservation into attempts, then counter blocks. -/
noncomputable def equalityFlatEquiv :
    (Fin equalityWidth → OracleBlock) ≃
      (Fin rejectionTrials → Fin 7 → OracleBlock) :=
  (Equiv.arrowCongr
      (finProdFinEquiv (m := rejectionTrials)
        (n := 7))
      (Equiv.refl OracleBlock)).symm.trans
    (Equiv.curry (Fin rejectionTrials) (Fin 7)
      OracleBlock)

theorem equalityWidth_eq :
    equalityWidth = rejectionTrials * equalityAttemptBlocks := rfl

/-- The maximum-coordinate equality abort event on the flat reserved range. -/
noncomputable def equalityFlatAbort :
    Finset (Fin equalityWidth → OracleBlock) :=
  transportBad equalityFlatEquiv
    (equalityBlockAbortRuns rejectionTrials)

/-- Five production challenges use the nonzero sampler. -/
def nonzeroOffset : Fin maxNonzeroChallengeSites → ℕ
  | ⟨0, _⟩ => blindChallengeOffset
  | ⟨1, _⟩ => outerChallengeOffset
  | ⟨2, _⟩ => linearRhoOffset
  | ⟨3, _⟩ => hadamardRhoOffset
  | ⟨4, _⟩ => productCoefficientOffset

/-- Primitive causes of a bounded production sampling abort. -/
inductive SamplingBadKind (shape : BatchShape)
  | powStateCollision
  | equality
  | blindGrinding
  | nonzero (site : Fin maxNonzeroChallengeSites)
  | multiplicationAlpha
  | outerPositions
  | linearPositions
  | hadamardPositions
  | ligeritoGrinding (site : Fin maxLigeritoSites)
  deriving DecidableEq, Fintype

noncomputable def badAt (shape : BatchShape) : SamplingBadKind shape →
    Finset SamplingAnswerTape
  | .powStateCollision =>
      adaptiveBadOracles powStateSchedule
        (collisionRuns (Outcome := OracleBlock) powStateCount)
  | .equality =>
      windowBad equalityOffset equalityWidth (by
        rw [productionSamplingSlots_eq]
        decide) equalityFlatAbort
  | .blindGrinding =>
      windowBad blindGrindingOffset maxBlindTrials (by
        rw [productionSamplingSlots_eq]
        decide) (blockAbortRuns maxBlindBits (by decide) maxBlindTrials)
  | .nonzero site =>
      windowBad (nonzeroOffset site) rejectionTrials (by
        fin_cases site <;> rw [productionSamplingSlots_eq] <;> decide)
        (scalarBlockAbortRuns zeroFailure rejectionTrials)
  | .multiplicationAlpha =>
      windowBad multiplicationAlphaOffset rejectionTrials (by
        rw [productionSamplingSlots_eq]
        decide) (scalarBlockAbortRuns zeroOrOneFailure rejectionTrials)
  | .outerPositions =>
      windowBad outerPositionsOffset samplingTrials (by
        rw [productionSamplingSlots_eq]
        decide)
        (positionBlockAbortRuns (m shape - 11)
          (Nat.le_trans (Nat.le_of_lt (outerCodeLog_lt_128 shape))
            (by decide))
          (outerL0QueryCount shape) samplingTrials)
  | .linearPositions =>
      windowBad linearPositionsOffset samplingTrials (by
        rw [productionSamplingSlots_eq]
        decide)
        (positionBlockAbortRuns 13 (by decide) queryCount samplingTrials)
  | .hadamardPositions =>
      windowBad hadamardPositionsOffset samplingTrials (by
        rw [productionSamplingSlots_eq]
        decide)
        (positionBlockAbortRuns 11 (by decide) queryCount samplingTrials)
  | .ligeritoGrinding site =>
      windowBad
        (ligeritoOffset + site.val * ligeritoSiteWidth + 1)
        maxLigeritoTrials (by
          fin_cases site <;> rw [productionSamplingSlots_eq] <;> decide)
        (blockAbortRuns maxLigeritoBits (by decide) maxLigeritoTrials)

def badBound (shape : BatchShape) : SamplingBadKind shape → ℚ
  | .powStateCollision =>
      (powStateCount.choose 2 : ℚ) / Fintype.card OracleBlock
  | .equality => equalityPointAbortBound
  | .blindGrinding => blindAbortProbability
  | .nonzero _ => nonzeroAbortBound
  | .multiplicationAlpha => notZeroOrOneAbortBound
  | .outerPositions => outerAbortBound shape
  | .linearPositions => linearAbortBound
  | .hadamardPositions => hadamardAbortBound
  | .ligeritoGrinding _ => ligeritoAbortProbability

theorem badAt_probability_le (shape : BatchShape)
    (kind : SamplingBadKind shape) :
    ((badAt shape kind).card : ℚ) /
        Fintype.card SamplingAnswerTape ≤ badBound shape kind := by
  cases kind with
  | powStateCollision =>
      rw [badAt, adaptiveBadOracles_probability_eq powStateSchedule
        powStateSchedule_tracePoints_injective]
      exact collisionProbability_le (Outcome := OracleBlock) powStateCount
  | equality =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide)]
      unfold equalityFlatAbort
      rw [card_transportBad]
      rw [Fintype.card_congr equalityFlatEquiv]
      exact equalityBlockAbortProbability_le
  | blindGrinding =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide), blindBlockAbortProbability_eq]
      exact le_rfl
  | nonzero site =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide), nonzeroBlockAbortProbability_eq]
      exact le_rfl
  | multiplicationAlpha =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide), notZeroOrOneBlockAbortProbability_eq]
      exact le_rfl
  | outerPositions =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide), positionBlockAbortProbability_eq]
      exact outerAbortProbability_le shape
  | linearPositions =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide)]
      exact linearPositionBlockAbortProbability_le
  | hadamardPositions =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide)]
      exact hadamardPositionBlockAbortProbability_le
  | ligeritoGrinding site =>
      rw [badAt, windowBad_probability_eq _ _ _ (by
        rw [productionSamplingSlots_eq]
        decide), ligeritoBlockAbortProbability_eq]
      exact le_rfl

noncomputable def globalBad (shape : BatchShape) :
    Finset SamplingAnswerTape := by
  classical
  exact badUnion (badAt shape)

theorem not_badAt_of_not_globalBad (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (kind : SamplingBadKind shape) : answers ∉ badAt shape kind := by
  classical
  intro hbad
  apply hgood
  rw [globalBad, mem_badUnion_iff]
  exact ⟨kind, hbad⟩

theorem powStateAnswers_injective_of_not_globalBad (shape : BatchShape)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    Function.Injective (fun site ↦ answers (powStateIndex site)) := by
  have hnot := not_badAt_of_not_globalBad shape answers hgood
    (.powStateCollision)
  rw [badAt, mem_adaptiveBadOracles_iff, run_powStateSchedule,
    mem_collisionRuns_iff] at hnot
  exact not_not.mp hnot

def samplingAbortBound (shape : BatchShape) : ℚ :=
  ∑ kind, badBound shape kind

theorem sum_badBound_eq (shape : BatchShape) :
    ∑ kind, badBound shape kind = samplingAbortBound shape := rfl

theorem globalBad_probability_le (shape : BatchShape) :
    ((globalBad shape).card : ℚ) /
        Fintype.card SamplingAnswerTape ≤ samplingAbortBound shape := by
  rw [← sum_badBound_eq shape]
  exact badUnionProbability_le_bounds (badAt shape) (badBound shape)
    (badAt_probability_le shape)

end VeiledFlock.ProductionSamplingBadTape

import VeiledFlock.Concrete.ConcreteRandomTape
import VeiledFlock.Concrete.KernelFailureBounds

/-!
# Audited concrete statistical distance

The Rust diagnostic tests a conservative deployment envelope of at most
1,024 proofs, at most `2^64` adversarial oracle queries, at most one million
protocol oracle queries per proof, and 32 programmable points per proof.
The registered shapes actually program at most 20 points.  This file evaluates
the complete exact-rational Lean ledger under that larger envelope.
-/

namespace VeiledFlock.ConcreteSecurityBound

set_option maxRecDepth 1000000

open VeiledFlock.ConcreteParameters
open VeiledFlock.Grinding
open VeiledFlock.ChallengeSampling
open VeiledFlock.KernelFailureBounds
open VeiledFlock.SecurityLedger
open VeiledFlock.UniquePositionSampling

def reviewedParameters : Parameters where
  proofs := 1024
  programmedPoints := 32
  adversaryQueries := 2 ^ 64
  protocolQueriesPerProof := maxProtocolOracleQueriesPerProof

theorem registeredProgrammedPoints_le_reviewed (shape : BatchShape) :
    programmedPoints shape ≤ reviewedParameters.programmedPoints := by
  cases shape <;> decide

theorem reviewedParameters_fields :
    reviewedParameters.proofs = 1024 ∧
      reviewedParameters.programmedPoints = 32 ∧
      reviewedParameters.adversaryQueries = 2 ^ 64 ∧
      reviewedParameters.protocolQueriesPerProof = 1_000_000 := by
  decide

/-- Even the 1,024-proof conservative envelope has statistical distance
strictly below `2^-126` in the classical programmable random-oracle model. -/
theorem reviewed_zkBound_lt_two_pow_neg_126 :
    zkBound reviewedParameters < 1 / (2 : ℚ) ^ 126 := by
  let eps : ℚ := 1 / (2 : ℚ) ^ 180
  have houter : (∑ shape : BatchShape, outerAbortBound shape) ≤ 5 * eps := by
    calc
      ∑ shape : BatchShape, outerAbortBound shape ≤
          ∑ _shape : BatchShape, eps := by
        apply Finset.sum_le_sum
        intro shape _
        exact outer_abort_le_180 shape
      _ = Fintype.card BatchShape * eps := by simp
      _ = 5 * eps := by
        rw [show Fintype.card BatchShape = 5 by decide]
        norm_num
  have hblind : blindAbortProbability ≤ eps := blind_abort_le_180
  have hligerito : ligeritoAbortProbability ≤ eps :=
    ligerito_abort_le_180
  have hnonzero : nonzeroAbortBound ≤ eps := nonzero_abort_le_180
  have hnotZeroOrOne : notZeroOrOneAbortBound ≤ eps :=
    notZeroOrOne_abort_le_180
  have hequality : equalityPointAbortBound ≤ eps := equality_abort_le_180
  have hhadamard : hadamardAbortBound ≤ eps := hadamard_abort_le_180
  have hlinear : linearAbortBound ≤ eps := linear_abort_le_180
  have hgrinding :
      1024 * (blindAbortProbability + 16 * ligeritoAbortProbability) ≤
        1024 * (eps + 16 * eps) := by
    exact mul_le_mul_of_nonneg_left
      (add_le_add hblind (mul_le_mul_of_nonneg_left hligerito (by norm_num)))
      (by norm_num)
  have hnonzeroScaled : 1024 * 5 * nonzeroAbortBound ≤
      1024 * 5 * eps := by
    exact mul_le_mul_of_nonneg_left hnonzero (by norm_num)
  have hnotZeroOrOneScaled : 1024 * notZeroOrOneAbortBound ≤
      1024 * eps := by
    exact mul_le_mul_of_nonneg_left hnotZeroOrOne (by norm_num)
  have hequalityScaled : 1024 * equalityPointAbortBound ≤
      1024 * eps := by
    exact mul_le_mul_of_nonneg_left hequality (by norm_num)
  have houterScaled : 1024 * (∑ shape : BatchShape, outerAbortBound shape) ≤
      1024 * (5 * eps) := by
    exact mul_le_mul_of_nonneg_left houter (by norm_num)
  have hpositionScaled :
      1024 * (hadamardAbortBound + linearAbortBound) ≤
        1024 * (eps + eps) := by
    exact mul_le_mul_of_nonneg_left (add_le_add hhadamard hlinear)
      (by norm_num)
  calc
    zkBound reviewedParameters ≤
        (1024 * 32 * 2 ^ 64 : ℚ) / (2 : ℚ) ^ 256 +
        (1024 * 1_000_000 * 2 ^ 64 : ℚ) / (2 : ℚ) ^ 256 +
        ((2 ^ 64 + 1024 * 1_000_000).choose 2 : ℚ) /
          (2 : ℚ) ^ 256 +
        (4 * (1024 : ℕ).choose 2 : ℚ) / (2 : ℚ) ^ 256 +
        1024 * (eps + 16 * eps) +
        1024 * 5 * eps +
        1024 * eps +
        1024 * eps +
        1024 * (5 * eps) +
        1024 * (eps + eps) := by
      unfold zkBound reviewedParameters nonceSpace
      norm_num only [maxLigeritoSites, maxNonzeroChallengeSites,
        maxNotZeroOrOneChallengeSites]
      gcongr
      · norm_num [maxProtocolOracleQueriesPerProof]
      · norm_num [maxProtocolOracleQueriesPerProof]
      · norm_num
      · exact hgrinding.trans_eq (by norm_num [eps])
      · calc
          5120 * nonzeroAbortBound = 1024 * 5 * nonzeroAbortBound := by ring
          _ ≤ 1024 * 5 * eps := hnonzeroScaled
          _ = _ := by norm_num [eps]
      · calc
          1024 * notZeroOrOneAbortBound ≤ 1024 * eps :=
            hnotZeroOrOneScaled
          _ = _ := by norm_num [eps]
      · calc
          1024 * equalityPointAbortBound ≤ 1024 * eps := hequalityScaled
          _ = _ := by norm_num [eps]
      · calc
          1024 * (∑ shape : BatchShape, outerAbortBound shape) ≤
              1024 * (5 * eps) := houterScaled
          _ = _ := by norm_num [eps]
      · calc
          1024 * (hadamardAbortBound + linearAbortBound) ≤
              1024 * (eps + eps) := hpositionScaled
          _ = _ := by norm_num [eps]
    _ < 1 / (2 : ℚ) ^ 126 := by
      dsimp only [eps]
      norm_num [Nat.choose_two_right]

theorem reviewed_zkBound_negligible :
    zkBound reviewedParameters < 1 / (2 : ℚ) ^ 126 :=
  reviewed_zkBound_lt_two_pow_neg_126

end VeiledFlock.ConcreteSecurityBound

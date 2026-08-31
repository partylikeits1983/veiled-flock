import VeiledFlock.Concrete.KernelFailureBounds
import VeiledFlock.Production.Security.StatisticalDistance

/-! # Kernel-checked concrete production failure bound

All exponent arithmetic in this file is proved by ordinary Lean theorems and
`norm_num`; no native evaluator or custom axiom is used.
-/

namespace VeiledFlock.ProductionConcreteFailureBound

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteParameters
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.KernelFailureBounds
open VeiledFlock.NonceSerialization
open VeiledFlock.ProductionOperationalGlobalProbability
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionSamplingBadTape

private theorem pow_collision_le_180 :
    (powStateCount.choose 2 : ℚ) / Fintype.card OracleBlock ≤
      1 / (2 : ℚ) ^ 180 := by
  norm_num [powStateCount, VeiledFlock.Grinding.maxLigeritoSites, OracleBlock,
    Nat.choose,
    VeiledFlock.Framing.Byte]

theorem badBound_le_two_pow_neg_180 (shape : BatchShape)
    (kind : SamplingBadKind shape) :
    badBound shape kind ≤ 1 / (2 : ℚ) ^ 180 := by
  cases kind with
  | powStateCollision => exact pow_collision_le_180
  | equality => exact equality_abort_le_180
  | blindGrinding => exact blind_abort_le_180
  | nonzero site => exact nonzero_abort_le_180
  | multiplicationAlpha => exact notZeroOrOne_abort_le_180
  | outerPositions => exact outer_abort_le_180 shape
  | linearPositions => exact linear_abort_le_180
  | hadamardPositions => exact hadamard_abort_le_180
  | ligeritoGrinding site => exact ligerito_abort_le_180

theorem samplingAbortBound_le_two_pow_neg_170 (shape : BatchShape) :
    samplingAbortBound shape ≤ 1 / (2 : ℚ) ^ 170 := by
  unfold samplingAbortBound
  calc
    ∑ kind, badBound shape kind ≤
        ∑ _kind : SamplingBadKind shape, 1 / (2 : ℚ) ^ 180 := by
      apply Finset.sum_le_sum
      intro kind _
      exact badBound_le_two_pow_neg_180 shape kind
    _ = Fintype.card (SamplingBadKind shape) * (1 / (2 : ℚ) ^ 180) := by
      simp
    _ ≤ 1 / (2 : ℚ) ^ 170 := by
      have hcard : Fintype.card (SamplingBadKind shape) = 28 := by
        cases shape <;> decide
      rw [hcard]
      norm_num

theorem hiddenLeafCount_le_two_pow_16 (shape : BatchShape) :
    Fintype.card (ProductionHiddenLeafIndex shape) ≤ 2 ^ 16 := by
  cases shape <;> norm_num [ProductionHiddenLeafIndex, m]

theorem operationalFailureBound_lt_two_pow_neg_126
    (shape : BatchShape) (preQueries postQueries : ℕ)
    (hqueries : preQueries + postQueries ≤ 2 ^ 64) :
    operationalFailureBound shape preQueries postQueries <
      1 / (2 : ℚ) ^ 126 := by
  have hpre : preQueries ≤ 2 ^ 64 :=
    le_trans (Nat.le_add_right preQueries postQueries) hqueries
  have hhidden := hiddenLeafCount_le_two_pow_16 shape
  have hpoints := programmedPoints_le_max shape
  have hpoints32 : programmedPoints shape ≤ 2 ^ 5 :=
    hpoints.trans (by norm_num [maxProgrammedPoints])
  have hnonce : Fintype.card NumericNonce = 2 ^ 256 := by simp
  have hnonce256 : Fintype.card VeiledFlock.Framing.Nonce256 = 2 ^ 256 :=
    card_nonceBytes
  let eps : ℚ := 1 / (2 : ℚ) ^ 170
  have htermPreMerkle : operationalPreMerkleBound shape preQueries ≤ eps := by
    dsimp only [operationalPreMerkleBound, eps]
    rw [hnonce]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    apply (div_le_iff₀ (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Nat.mul_le_mul hhidden hpre).trans (by norm_num)
  have htermPrequery : operationalPrequeryBound shape preQueries ≤ eps := by
    dsimp only [operationalPrequeryBound, eps]
    rw [hnonce256]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    apply (div_le_iff₀ (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Nat.mul_le_mul hpoints32 hpre).trans (by norm_num)
  have htermPost :
      operationalPostMerkleBound shape preQueries postQueries ≤ eps := by
    dsimp only [operationalPostMerkleBound, eps]
    rw [hnonce]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    apply (div_le_iff₀ (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Nat.mul_le_mul_left 2
      (Nat.mul_le_mul hhidden hqueries)).trans (by norm_num)
  unfold operationalFailureBound
  have hsum :
      samplingAbortBound shape + operationalPreMerkleBound shape preQueries +
          operationalPrequeryBound shape preQueries +
          operationalPostMerkleBound shape preQueries postQueries ≤
        eps + eps + eps + eps :=
    add_le_add
      (add_le_add
        (add_le_add (samplingAbortBound_le_two_pow_neg_170 shape)
          htermPreMerkle)
        htermPrequery)
      htermPost
  have hfinal : eps + eps + eps + eps < 1 / (2 : ℚ) ^ 126 := by
    dsimp only [eps]
    norm_num
  exact hsum.trans_lt hfinal

end VeiledFlock.ProductionConcreteFailureBound

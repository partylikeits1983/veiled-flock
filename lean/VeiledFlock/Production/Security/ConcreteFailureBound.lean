import VeiledFlock.Production.Security.StatisticalDistance

/-! # Kernel-checked concrete production failure bound

All exponent arithmetic in this file is proved by ordinary Lean theorems and
`norm_num`; no native evaluator or custom axiom is used.
-/

namespace VeiledFlock.ProductionConcreteFailureBound

set_option maxRecDepth 10000

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteParameters
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.NonceSerialization
open VeiledFlock.ProductionOperationalGlobalProbability
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.UniquePositionSampling

private theorem geometric_tail_le
    (x : ℚ) (trials rate remainder : ℕ)
    (hx : 0 ≤ x) (hrate : x ≤ 1 / (2 : ℚ) ^ rate)
    (hsplit : rate * trials = remainder) :
    x ^ trials ≤ 1 / (2 : ℚ) ^ remainder := by
  calc
    x ^ trials ≤ (1 / (2 : ℚ) ^ rate) ^ trials :=
      pow_le_pow_left₀ hx hrate trials
    _ = 1 / (2 : ℚ) ^ remainder := by
      rw [div_pow]
      norm_num only [one_pow]
      rw [← pow_mul, hsplit]

private theorem binomial_tail_le
    (domain target trials rate remainder : ℕ)
    (hrate : ((target : ℕ) : ℚ) / domain ≤
      1 / (2 : ℚ) ^ rate)
    (hsplit : rate * trials = domain + remainder) :
    (domain.choose target : ℚ) *
        (((target : ℕ) : ℚ) / domain) ^ trials ≤
      1 / (2 : ℚ) ^ remainder := by
  have hchoose : (domain.choose target : ℚ) ≤ (2 : ℚ) ^ domain := by
    exact_mod_cast Nat.choose_le_two_pow domain target
  have hpow : ((((target : ℕ) : ℚ) / domain) ^ trials) ≤
      (1 / (2 : ℚ) ^ rate) ^ trials :=
    pow_le_pow_left₀ (by positivity) hrate trials
  calc
    (domain.choose target : ℚ) *
        (((target : ℕ) : ℚ) / domain) ^ trials ≤
      (2 : ℚ) ^ domain * (1 / (2 : ℚ) ^ rate) ^ trials :=
        mul_le_mul hchoose hpow (by positivity) (by positivity)
    _ = 1 / (2 : ℚ) ^ remainder := by
      rw [div_pow]
      norm_num only [one_pow]
      rw [← pow_mul, hsplit, pow_add]
      field_simp

/-- A sharper binomial tail bound for large domains, using
`domain.choose target ≤ domain ^ target` and a power-of-two domain bound. -/
private theorem binomial_tail_le_pow
    (domain target trials rate logDomain remainder : ℕ)
    (hdomain : domain ≤ 2 ^ logDomain)
    (hrate : ((target : ℕ) : ℚ) / domain ≤
      1 / (2 : ℚ) ^ rate)
    (hsplit : rate * trials = logDomain * target + remainder) :
    (domain.choose target : ℚ) *
        (((target : ℕ) : ℚ) / domain) ^ trials ≤
      1 / (2 : ℚ) ^ remainder := by
  have hchooseNat : domain.choose target ≤ (2 ^ logDomain) ^ target :=
    (Nat.choose_le_pow domain target).trans
      (Nat.pow_le_pow_left hdomain target)
  have hchoose : (domain.choose target : ℚ) ≤
      (2 : ℚ) ^ (logDomain * target) := by
    rw [← pow_mul] at hchooseNat
    exact_mod_cast hchooseNat
  have hpow : ((((target : ℕ) : ℚ) / domain) ^ trials) ≤
      (1 / (2 : ℚ) ^ rate) ^ trials :=
    pow_le_pow_left₀ (by positivity) hrate trials
  calc
    (domain.choose target : ℚ) *
        (((target : ℕ) : ℚ) / domain) ^ trials ≤
      (2 : ℚ) ^ (logDomain * target) *
        (1 / (2 : ℚ) ^ rate) ^ trials :=
          mul_le_mul hchoose hpow (by positivity) (by positivity)
    _ = 1 / (2 : ℚ) ^ remainder := by
      rw [div_pow]
      norm_num only [one_pow]
      rw [← pow_mul, hsplit, pow_add]
      field_simp

theorem blindAbort_lt_two_pow_neg_180_kernel :
    blindAbortProbability < 1 / (2 : ℚ) ^ 180 := by
  have hblock : (63 / 64 : ℚ) ^ 45 < 1 / 2 := by norm_num
  have hpow : (((63 / 64 : ℚ) ^ 45) ^ 182) < (1 / 2 : ℚ) ^ 182 :=
    pow_lt_pow_left₀ hblock (by positivity) (by norm_num)
  have htail : (63 / 64 : ℚ) ^ 2 ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  unfold blindAbortProbability maxBlindTrials
  rw [show 8192 = 45 * 182 + 2 by norm_num, pow_add, pow_mul]
  calc
    ((63 / 64 : ℚ) ^ 45) ^ 182 * (63 / 64 : ℚ) ^ 2 ≤
        (1 / 2 : ℚ) ^ 182 * 1 :=
      mul_le_mul (le_of_lt hpow) htail (by positivity) (by positivity)
    _ < 1 / (2 : ℚ) ^ 180 := by norm_num [div_pow]

theorem ligeritoAbort_lt_two_pow_neg_180_kernel :
    ligeritoAbortProbability < 1 / (2 : ℚ) ^ 180 := by
  have hblock : (31 / 32 : ℚ) ^ 22 < 1 / 2 := by norm_num
  have hpow : (((31 / 32 : ℚ) ^ 22) ^ 186) < (1 / 2 : ℚ) ^ 186 :=
    pow_lt_pow_left₀ hblock (by positivity) (by norm_num)
  have htail : (31 / 32 : ℚ) ^ 4 ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  unfold ligeritoAbortProbability maxLigeritoTrials
  rw [show 4096 = 22 * 186 + 4 by norm_num, pow_add, pow_mul]
  calc
    ((31 / 32 : ℚ) ^ 22) ^ 186 * (31 / 32 : ℚ) ^ 4 ≤
        (1 / 2 : ℚ) ^ 186 * 1 :=
      mul_le_mul (le_of_lt hpow) htail (by positivity) (by positivity)
    _ < 1 / (2 : ℚ) ^ 180 := by
      rw [div_pow]
      norm_num only [one_pow, one_div]

private theorem two_pow_inverse_mono
    {large small : ℕ} (h : small < large) :
    1 / (2 : ℚ) ^ large < 1 / (2 : ℚ) ^ small := by
  exact one_div_lt_one_div_of_lt (by positivity)
    (pow_lt_pow_right₀ (a := (2 : ℚ)) (m := small) (n := large)
      (by norm_num) h)

private theorem equality_abort_le_180 :
    equalityPointAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold equalityPointAbortBound
    VeiledFlock.ChallengeSampling.maxEqualityPointOuterCoordinates
    rejectionTrials
  apply le_trans (geometric_tail_le (13 / (2 : ℚ) ^ 128) 4096 124
    (124 * 4096) (by positivity) (by norm_num) rfl)
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 124 * 4096))

private theorem nonzero_abort_le_180 :
    nonzeroAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold nonzeroAbortBound rejectionTrials
  apply le_trans (geometric_tail_le (1 / (2 : ℚ) ^ 128) 4096 128
    (128 * 4096) (by positivity) le_rfl rfl)
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 128 * 4096))

private theorem notZeroOrOne_abort_le_180 :
    notZeroOrOneAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold notZeroOrOneAbortBound rejectionTrials
  apply le_trans (geometric_tail_le (2 / (2 : ℚ) ^ 128) 4096 127
    (127 * 4096) (by positivity) (by norm_num) rfl)
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 127 * 4096))

private theorem hadamard_abort_le_180 :
    hadamardAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold hadamardAbortBound positionAbortBound hadamardDomain queryCount
    samplingTrials
  apply le_trans (binomial_tail_le 2048 159 4096 3 10240
    (by norm_num) (by norm_num))
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 10240))

private theorem linear_abort_le_180 :
    linearAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold linearAbortBound positionAbortBound linearDomain queryCount
    samplingTrials
  apply le_trans (binomial_tail_le 8192 159 4096 5 12288
    (by norm_num) (by norm_num))
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 12288))

private theorem outer_abort_le_180 (shape : BatchShape) :
    outerAbortBound shape ≤ 1 / (2 : ℚ) ^ 180 := by
  cases shape with
  | slots256 =>
      change (Nat.choose 2048 297 : ℚ) * (297 / 2048 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 2048 297 4096 2 6144
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 6144)))
  | slots512 =>
      change (Nat.choose 4096 293 : ℚ) * (293 / 4096 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 4096 293 4096 3 8192
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 8192)))
  | slots1024 =>
      change (Nat.choose 8192 291 : ℚ) * (291 / 8192 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 8192 291 4096 4 8192
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 8192)))
  | slots2048 =>
      change (Nat.choose 16384 290 : ℚ) * (290 / 16384 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 16384 290 4096 5 4096
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 4096)))
  | slots4096 =>
      change (Nat.choose 32768 289 : ℚ) * (289 / 32768 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le_pow 32768 289 4096 6 15 20241
        (by norm_num) (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 20241)))

private theorem pow_collision_le_180 :
    (powStateCount.choose 2 : ℚ) / Fintype.card OracleBlock ≤
      1 / (2 : ℚ) ^ 180 := by
  norm_num [powStateCount, maxLigeritoSites, OracleBlock,
    Nat.choose,
    VeiledFlock.Framing.Byte]

theorem badBound_le_two_pow_neg_180 (shape : BatchShape)
    (kind : SamplingBadKind shape) :
    badBound shape kind ≤ 1 / (2 : ℚ) ^ 180 := by
  cases kind with
  | powStateCollision => exact pow_collision_le_180
  | equality => exact equality_abort_le_180
  | blindGrinding => exact le_of_lt blindAbort_lt_two_pow_neg_180_kernel
  | nonzero site => exact nonzero_abort_le_180
  | multiplicationAlpha => exact notZeroOrOne_abort_le_180
  | outerPositions => exact outer_abort_le_180 shape
  | linearPositions => exact linear_abort_le_180
  | hadamardPositions => exact hadamard_abort_le_180
  | ligeritoGrinding site =>
      exact le_of_lt ligeritoAbort_lt_two_pow_neg_180_kernel

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

set_option maxRecDepth 1000000 in
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

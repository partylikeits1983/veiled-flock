import VeiledFlock.Concrete.ChallengeSampling
import VeiledFlock.Concrete.Grinding
import VeiledFlock.Concrete.UniquePositionSampling

/-! # Kernel-checked bounds for the concrete sampling tails

These bounds are shared by both concrete security ledgers.  Their arithmetic
is checked by the Lean kernel; this module deliberately avoids `native_decide`.
-/

namespace VeiledFlock.KernelFailureBounds

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteParameters
open VeiledFlock.Grinding
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

private theorem two_pow_inverse_mono
    {large small : ℕ} (h : small < large) :
    1 / (2 : ℚ) ^ large < 1 / (2 : ℚ) ^ small := by
  exact one_div_lt_one_div_of_lt (by positivity)
    (pow_lt_pow_right₀ (a := (2 : ℚ)) (m := small) (n := large)
      (by norm_num) h)

theorem blind_abort_le_180 :
    blindAbortProbability ≤ 1 / (2 : ℚ) ^ 180 := by
  exact (le_of_lt blindAbort_lt_two_pow_neg_186).trans
    (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 186)))

theorem ligerito_abort_le_180 :
    ligeritoAbortProbability ≤ 1 / (2 : ℚ) ^ 180 := by
  exact (le_of_lt ligeritoAbort_lt_two_pow_neg_187).trans
    (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 187)))

theorem equality_abort_le_180 :
    equalityPointAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold equalityPointAbortBound
    VeiledFlock.ChallengeSampling.maxEqualityPointOuterCoordinates
    rejectionTrials
  apply le_trans (geometric_tail_le (13 / (2 : ℚ) ^ 128) 4096 124
    (124 * 4096) (by positivity) (by norm_num) rfl)
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 124 * 4096))

theorem nonzero_abort_le_180 :
    nonzeroAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold nonzeroAbortBound rejectionTrials
  apply le_trans (geometric_tail_le (1 / (2 : ℚ) ^ 128) 4096 128
    (128 * 4096) (by positivity) le_rfl rfl)
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 128 * 4096))

theorem notZeroOrOne_abort_le_180 :
    notZeroOrOneAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold notZeroOrOneAbortBound rejectionTrials
  apply le_trans (geometric_tail_le (2 / (2 : ℚ) ^ 128) 4096 127
    (127 * 4096) (by positivity) (by norm_num) rfl)
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 127 * 4096))

theorem hadamard_abort_le_180 :
    hadamardAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold hadamardAbortBound positionAbortBound hadamardDomain queryCount
    samplingTrials
  apply le_trans (binomial_tail_le 2048 159 4096 3 10240
    (by norm_num) (by norm_num))
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 10240))

theorem linear_abort_le_180 :
    linearAbortBound ≤ 1 / (2 : ℚ) ^ 180 := by
  unfold linearAbortBound positionAbortBound linearDomain queryCount
    samplingTrials
  apply le_trans (binomial_tail_le 8192 159 4096 5 12288
    (by norm_num) (by norm_num))
  exact le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 12288))

theorem outer_abort_le_180 (shape : BatchShape) :
    outerAbortBound shape ≤ 1 / (2 : ℚ) ^ 180 := by
  cases shape with
  | slots256 =>
      change (Nat.choose 2048 293 : ℚ) * (293 / 2048 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 2048 293 4096 2 6144
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 6144)))
  | slots512 =>
      change (Nat.choose 4096 291 : ℚ) * (291 / 4096 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 4096 291 4096 3 8192
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 8192)))
  | slots1024 =>
      change (Nat.choose 8192 290 : ℚ) * (290 / 8192 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 8192 290 4096 4 8192
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 8192)))
  | slots2048 =>
      change (Nat.choose 16384 289 : ℚ) * (289 / 16384 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le 16384 289 4096 5 4096
        (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 4096)))
  | slots4096 =>
      change (Nat.choose 32768 289 : ℚ) * (289 / 32768 : ℚ) ^ 4096 ≤ _
      exact (binomial_tail_le_pow 32768 289 4096 6 15 20241
        (by norm_num) (by norm_num) (by norm_num)).trans
        (le_of_lt (two_pow_inverse_mono (by norm_num : 180 < 20241)))

end VeiledFlock.KernelFailureBounds

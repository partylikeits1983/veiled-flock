import Mathlib
import VeiledFlock.Concrete.ChallengeSampling

/-!
# Registered VEIL--FLOCK parameters

These are the five BLAKE3-preimage batch geometries accepted by the full-ZK
entry point.  The
formulas mirror `MaskLayout::{piop_count, observed_count}` and the simulator's
`1 + m - K_SKIP` programmed-challenge count.  The small closed datatype lets
Lean exhaustively prove the bounds for every accepted shape.
-/

namespace VeiledFlock.ConcreteParameters

/-- The only batch sizes accepted by the full-ZK entry point. -/
inductive BatchShape
  | slots256
  | slots512
  | slots1024
  | slots2048
  | slots4096
  deriving DecidableEq, Fintype

def m : BatchShape → ℕ
  | .slots256 => 22
  | .slots512 => 23
  | .slots1024 => 24
  | .slots2048 => 25
  | .slots4096 => 26

def expectedMasks : BatchShape → ℕ
  | .slots256 => 754
  | .slots512 => 756
  | .slots1024 => 758
  | .slots2048 => 760
  | .slots4096 => 762

def kSkip : ℕ := 6
def kLog : ℕ := 14
def ringWidth : ℕ := 2 ^ 7
def ringClaimCount : ℕ := 2

/-- Rust's `MaskLayout::piop_count`. -/
def piopCount (shape : BatchShape) : ℕ :=
  2 * 2 ^ kSkip + 2 * (m shape - kSkip) + 2 +
    2 * (kLog - kSkip) + 2 ^ kSkip

/-- Rust's `MaskLayout::observed_count`. -/
def observedCount (shape : BatchShape) : ℕ :=
  piopCount shape + 2 * ringClaimCount * ringWidth

/-- Every registered shape has exactly one independent field mask for every
coordinate consumed by the shifted verifier circuit. -/
theorem observedCount_eq_expectedMasks (shape : BatchShape) :
    observedCount shape = expectedMasks shape := by
  cases shape <;> decide

/-- Number of Fiat--Shamir sites programmed by the zerocheck simulator. -/
def programmedPoints (shape : BatchShape) : ℕ := 1 + m shape - kSkip

def maxProgrammedPoints : ℕ := 21
def maxProtocolOracleQueriesPerProof : ℕ := 1_000_000
/-- `sampleProductionTailRaw` samples the blind, outer, linear, Hadamard,
and product challenges independently with the bounded nonzero sampler. -/
def maxNonzeroChallengeSites : ℕ := 5
def maxNotZeroOrOneChallengeSites : ℕ := 1
def maxEqualityPointOuterCoordinates : ℕ := 13
def veilQueryCount : ℕ := 160
def veilSamplingTrials : ℕ := 4096
def veilInverseRate : ℕ := 8
def paddedMultiplications : ℕ := 3
def hadamardCodeLength : ℕ := 2048
def linearCodeLength : ℕ := 8192

/-! ## Outer shielded-PCS geometry -/

/-- `PcsParams.log_batch_size = 6`: every initial additive NTT has 64
interleaved message lanes (and another 64 blinder lanes). -/
def outerLaneCount : ℕ := 2 ^ 6

/-- Number of low-half random mask symbols in each message lane. -/
def outerMaskSymbolsPerLane (shape : BatchShape) : ℕ :=
  2 ^ (m shape - 13)

/-- Exact L0 query count in the registered Secure Ligerito profiles.
ZK adds one committed-message dimension, so R1CS shapes `m22` through `m26`
load `m23_secure.toml` through `m27_secure.toml`. -/
def outerL0QueryCount : BatchShape → ℕ
  | .slots256 => 294
  | .slots512 => 292
  | .slots1024 => 291
  | .slots2048 => 290
  | .slots4096 => 290

/-- Per-lane committed message dimension after adjoining the low random half. -/
def outerMessagePositions (shape : BatchShape) : ℕ :=
  2 * outerMaskSymbolsPerLane shape

/-- Per-lane rate-1/2 additive-RS codeword dimension. -/
def outerCodePositions (shape : BatchShape) : ℕ :=
  2 * outerMessagePositions shape

theorem outerL0QueryCount_positive (shape : BatchShape) :
    0 < outerL0QueryCount shape := by
  cases shape <;> decide

/-- There are strictly more independent low-half mask symbols per lane than
raw L0 rows opened by every registered Secure profile. -/
theorem outerL0QueryCount_le_maskSymbols (shape : BatchShape) :
    outerL0QueryCount shape ≤ outerMaskSymbolsPerLane shape := by
  cases shape <;> decide

theorem outerMessagePositions_eq_pow (shape : BatchShape) :
    outerMessagePositions shape = 2 ^ (m shape - 12) := by
  cases shape <;> decide

theorem outerCodePositions_eq_pow (shape : BatchShape) :
    outerCodePositions shape = 2 ^ (m shape - 11) := by
  cases shape <;> decide

theorem outerCodeLog_lt_128 (shape : BatchShape) : m shape - 11 < 128 := by
  cases shape <;> decide

/-- The original shifted circuit has one product and VEIL adds two masking
products before constructing its Hadamard code. -/
theorem paddedMultiplications_eq : paddedMultiplications = 1 + 2 := by decide

/-- The Hadamard message length is `3 + 160 = 163`, so its next power-of-two
capacity is 256 and inverse rate 8 gives 2,048 code coordinates. -/
theorem hadamard_message_geometry :
    128 < paddedMultiplications + veilQueryCount ∧
      paddedMultiplications + veilQueryCount ≤ 256 ∧
      256 * veilInverseRate = hadamardCodeLength := by
  decide

/-- For all registered shapes, the linear message length lies strictly above
512 and at most 1,024.  Rust's `next_power_of_two` therefore returns 1,024,
and inverse rate 8 gives 8,192 code coordinates. -/
theorem linear_message_geometry (shape : BatchShape) :
    512 < expectedMasks shape + 6 + veilQueryCount ∧
      expectedMasks shape + 6 + veilQueryCount ≤ 1024 ∧
      1024 * veilInverseRate = linearCodeLength := by
  cases shape <;> decide

theorem programmedPoints_le_max (shape : BatchShape) :
    programmedPoints shape ≤ maxProgrammedPoints := by
  cases shape <;> decide

theorem programmedPoints_positive (shape : BatchShape) :
    0 < programmedPoints shape := by
  cases shape <;> decide

/-- The largest rejection-sampled equality-point suffix is
`26 - K_SKIP(6) - N_INNER(7) = 13`. -/
theorem equalityPointOuterCoordinates_le_max (shape : BatchShape) :
    m shape - kSkip - 7 ≤ maxEqualityPointOuterCoordinates := by
  cases shape <;> decide

theorem maxEqualityPointOuterCoordinates_matches_sampler :
    maxEqualityPointOuterCoordinates =
      ChallengeSampling.maxEqualityPointOuterCoordinates := by
  rfl

/-- All registered shapes satisfy the geometry preconditions checked by
`MaskLayout::new`. -/
theorem registered_geometry (shape : BatchShape) :
    kSkip + 7 ≤ m shape ∧ kSkip ≤ kLog := by
  cases shape <;> decide

end VeiledFlock.ConcreteParameters

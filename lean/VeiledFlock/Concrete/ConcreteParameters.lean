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

/-- One level of the exact embedded Rust Secure-profile ladder.  The Rust
`k_recursive` and `log_num_interleaved` fields agree at every registered
level, so `foldWidth` records both values. -/
structure RegisteredLigeritoLevel where
  logInvRate : ℕ
  logMessageColumns : ℕ
  foldWidth : ℕ
  queryCount : ℕ
  queryGrindingBits : ℕ
  foldGrindingBits : ℕ
  foldGrindingTaper : Bool
  outOfDomainSamples : ℕ
  deriving DecidableEq

/-- Constructor for the unique-decoding levels used by all five production
Secure profiles.  Query-phase grinding, tapering, and OOD sampling are all
disabled in these profiles. -/
def secureUdrLevel (logInvRate logMessageColumns foldWidth queryCount
    foldGrindingBits : ℕ) : RegisteredLigeritoLevel where
  logInvRate := logInvRate
  logMessageColumns := logMessageColumns
  foldWidth := foldWidth
  queryCount := queryCount
  queryGrindingBits := 0
  foldGrindingBits := foldGrindingBits
  foldGrindingTaper := false
  outOfDomainSamples := 0

/-- Complete per-level tables loaded by Rust from `m23_secure.toml` through
`m27_secure.toml`.  Recording the entire ladder makes changes below L0 visible
to the Lean review even though only L0 openings require fresh hiding entropy. -/
def registeredLigeritoLevels : BatchShape → List RegisteredLigeritoLevel
  | .slots256 =>
      [secureUdrLevel 1 10 6 294 1,
        secureUdrLevel 2 7 3 182 0,
        secureUdrLevel 4 4 3 137 0]
  | .slots512 =>
      [secureUdrLevel 1 11 6 292 2,
        secureUdrLevel 2 8 3 180 1,
        secureUdrLevel 3 5 3 151 0]
  | .slots1024 =>
      [secureUdrLevel 1 12 6 291 3,
        secureUdrLevel 2 9 3 179 2,
        secureUdrLevel 3 6 3 148 0,
        secureUdrLevel 5 3 3 131 0]
  | .slots2048 =>
      [secureUdrLevel 1 13 6 290 4,
        secureUdrLevel 2 10 3 178 3,
        secureUdrLevel 3 7 3 147 1,
        secureUdrLevel 4 4 3 137 0]
  | .slots4096 =>
      [secureUdrLevel 1 14 6 290 5,
        secureUdrLevel 2 11 3 178 4,
        secureUdrLevel 3 8 3 146 2,
        secureUdrLevel 4 5 3 134 0]

/-- Exact clear final-block dimension (`final_block.yr_log_n`) of the
registered Secure profile. -/
def ligeritoFinalLogSize : BatchShape → ℕ
  | .slots256 => 4
  | .slots512 => 5
  | .slots1024 => 3
  | .slots2048 => 4
  | .slots4096 => 5

/-- Flatten the live per-fold grinds directly from the registered Rust level
table.  Zero-width levels emit no nonce. -/
def registeredLigeritoProfileFoldSchedule (shape : BatchShape) : List ℕ :=
  (registeredLigeritoLevels shape).flatMap fun level ↦
    if level.foldGrindingBits = 0 then []
    else List.replicate level.foldWidth level.foldGrindingBits

/-- `recursive_steps` in the Secure Ligerito profile selected by the
corresponding ZK-wide commitment (`m23_secure` through `m27_secure`). -/
def ligeritoRecursiveSteps : BatchShape → ℕ
  | .slots256 => 2
  | .slots512 => 2
  | .slots1024 => 3
  | .slots2048 => 3
  | .slots4096 => 3

theorem ligeritoRecursiveSteps_positive (shape : BatchShape) :
    0 < ligeritoRecursiveSteps shape := by
  cases shape <;> decide

/-- Closed cross-check of the complete Rust Secure-profile table: there is one
L0 level plus `recursive_steps` recursive levels, the first query count is the
hiding budget used by Lean, L0 has six folds and every recursive level has
three, the final message size agrees with the last level, and all registered
levels use the non-tapered UDR mode with no query grinding or OOD samples. -/
theorem registered_ligeritoLevels_consistent (shape : BatchShape) :
    (registeredLigeritoLevels shape).length =
        ligeritoRecursiveSteps shape + 1 ∧
      ((registeredLigeritoLevels shape).map
          RegisteredLigeritoLevel.queryCount).head? =
        some (outerL0QueryCount shape) ∧
      (registeredLigeritoLevels shape).map
          RegisteredLigeritoLevel.foldWidth =
        6 :: List.replicate (ligeritoRecursiveSteps shape) 3 ∧
      ((registeredLigeritoLevels shape).map
          RegisteredLigeritoLevel.logMessageColumns).getLast? =
        some (ligeritoFinalLogSize shape) ∧
      (∀ level ∈ registeredLigeritoLevels shape,
        level.queryGrindingBits = 0 ∧
          level.foldGrindingTaper = false ∧
          level.outOfDomainSamples = 0) := by
  cases shape <;> decide

/-- Largest per-fold grind in the selected Secure profile.  These are the
first-level `fold_grinding_bits` values in `m23_secure` through `m27_secure`;
all registered levels use the non-tapered UDR regime. -/
def ligeritoLiveFoldGrindingBits : BatchShape → ℕ
  | .slots256 => 1
  | .slots512 => 2
  | .slots1024 => 3
  | .slots2048 => 4
  | .slots4096 => 5

/-- The preblinded L0 challenge charges one bit beyond the first-level fold
grind, exactly as Rust's `l0_derived_grind_bits`. -/
def blindGrindingBits (shape : BatchShape) : ℕ :=
  ligeritoLiveFoldGrindingBits shape + 1

/-- Number of positive-width fold-grind nonces emitted by the complete Secure
profile: six initial lane folds, plus each live three-fold recursive level. -/
def ligeritoPositiveFoldGrindingSites : BatchShape → ℕ
  | .slots256 => 6
  | .slots512 => 9
  | .slots1024 => 9
  | .slots2048 => 12
  | .slots4096 => 12

/-- Exact flattened fold-grinding width at a reserved production site.  The
first six entries are the initial L0-to-L6 folds; each following group of
three is one recursive Secure-profile level.  A zero denotes an inactive
reserved site and is never executed. -/
def ligeritoFoldGrindingBitsAt : BatchShape → ℕ → ℕ
  | .slots256, site => if site < 6 then 1 else 0
  | .slots512, site => if site < 6 then 2 else if site < 9 then 1 else 0
  | .slots1024, site => if site < 6 then 3 else if site < 9 then 2 else 0
  | .slots2048, site =>
      if site < 6 then 4 else if site < 9 then 3 else if site < 12 then 1 else 0
  | .slots4096, site =>
      if site < 6 then 5 else if site < 9 then 4 else if site < 12 then 2 else 0

/-- The exact Rust fold-grinding schedule, with inactive reservation slots
excluded. -/
def ligeritoFoldGrindingSchedule (shape : BatchShape) : List ℕ :=
  List.ofFn fun site : Fin (ligeritoPositiveFoldGrindingSites shape) ↦
    ligeritoFoldGrindingBitsAt shape site.val

@[simp]
theorem ligeritoFoldGrindingSchedule_length (shape : BatchShape) :
    (ligeritoFoldGrindingSchedule shape).length =
      ligeritoPositiveFoldGrindingSites shape := by
  simp [ligeritoFoldGrindingSchedule]

/-- Closed audit of the five Rust Secure-profile schedules. -/
theorem registered_ligeritoFoldGrindingSchedules :
    ligeritoFoldGrindingSchedule .slots256 = [1, 1, 1, 1, 1, 1] ∧
    ligeritoFoldGrindingSchedule .slots512 = [2, 2, 2, 2, 2, 2, 1, 1, 1] ∧
    ligeritoFoldGrindingSchedule .slots1024 = [3, 3, 3, 3, 3, 3, 2, 2, 2] ∧
    ligeritoFoldGrindingSchedule .slots2048 =
      [4, 4, 4, 4, 4, 4, 3, 3, 3, 1, 1, 1] ∧
    ligeritoFoldGrindingSchedule .slots4096 =
      [5, 5, 5, 5, 5, 5, 4, 4, 4, 2, 2, 2] := by
  decide

/-- The independently reviewable per-level Rust table produces exactly the
flattened schedule executed by the formal production sampler. -/
theorem registered_ligeritoLevels_fold_schedule (shape : BatchShape) :
    registeredLigeritoProfileFoldSchedule shape =
      ligeritoFoldGrindingSchedule shape := by
  cases shape <;> decide

theorem ligeritoPositiveFoldGrindingSites_positive (shape : BatchShape) :
    0 < ligeritoPositiveFoldGrindingSites shape := by
  cases shape <;> decide

theorem ligeritoFoldGrindingBitsAt_positive (shape : BatchShape) (site : ℕ)
    (hsite : site < ligeritoPositiveFoldGrindingSites shape) :
    0 < ligeritoFoldGrindingBitsAt shape site := by
  cases shape with
  | slots256 => simp_all [ligeritoPositiveFoldGrindingSites,
      ligeritoFoldGrindingBitsAt]
  | slots512 | slots1024 =>
      simp only [ligeritoPositiveFoldGrindingSites] at hsite
      simp only [ligeritoFoldGrindingBitsAt]
      split <;> simp_all
  | slots2048 | slots4096 =>
      simp only [ligeritoPositiveFoldGrindingSites] at hsite
      simp only [ligeritoFoldGrindingBitsAt]
      split <;> simp_all
      split <;> simp_all

theorem ligeritoFoldGrindingBitsAt_le_max (shape : BatchShape) (site : ℕ) :
    ligeritoFoldGrindingBitsAt shape site ≤
      VeiledFlock.Grinding.maxLigeritoBits := by
  cases shape <;> simp [ligeritoFoldGrindingBitsAt,
    VeiledFlock.Grinding.maxLigeritoBits] <;> split <;> simp_all <;>
    split <;> simp_all <;> split <;> simp_all

theorem ligeritoFoldGrindingBitsAt_le_eight (shape : BatchShape) (site : ℕ) :
    ligeritoFoldGrindingBitsAt shape site ≤ 8 :=
  (ligeritoFoldGrindingBitsAt_le_max shape site).trans (by decide)

theorem registered_grinding_bounds (shape : BatchShape) :
    ligeritoLiveFoldGrindingBits shape ≤
        VeiledFlock.Grinding.maxLigeritoBits ∧
      blindGrindingBits shape ≤ VeiledFlock.Grinding.maxBlindBits ∧
      ligeritoPositiveFoldGrindingSites shape ≤
        VeiledFlock.Grinding.maxLigeritoSites := by
  cases shape <;> decide

theorem blindGrindingBits_le_eight (shape : BatchShape) :
    blindGrindingBits shape ≤ 8 :=
  (registered_grinding_bounds shape).2.1.trans (by decide)

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

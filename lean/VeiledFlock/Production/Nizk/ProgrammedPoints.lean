import VeiledFlock.Production.Core.ZerocheckSchedule

/-!
# Complete production programming ledger

The deployed simulator programs only the zerocheck scalar challenges: the
interpolation challenge `z`, followed by one recursive challenge `rho_i` per
zerocheck round. Equality-point vector sampling, nonzero rejection sampling,
and PoW grinding query the same global oracle honestly and are not programmed.

For each entry below:

* `input` is the exact byte string queried by `OracleChallenger`, including
  the scalar-squeeze tag and little-endian counter zero;
* `knownPrefix` is precisely the already-realized oracle history when the
  point becomes determined;
* `target` is the full 32-byte block installed there (the production runtime
  constrains its first 16 bytes and retains a uniform unused suffix);
* the fresh proof nonce has already been absorbed into `absorbedPrefix`;
* a prior adversarial query is `BadPrequery`, while coincidence with another
  programmed point is ruled out by append-only schedule injectivity.

Thus this table enumerates every programmed location without pretending that
honest rejection or grinding queries are simulator programming sites.
-/

namespace VeiledFlock.ProductionProgrammedPoints

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.ProductionMaskLayout
open VeiledFlock.ProductionZerocheckSchedule

inductive ProgrammedPhase
  | interpolationChallenge
  | recursiveChallenge (round : ℕ)
  deriving DecidableEq

def phase {shape : BatchShape} (site : Fin (programmedPoints shape)) :
    ProgrammedPhase :=
  if site.val = 0 then .interpolationChallenge
  else .recursiveChallenge (site.val - 1)

/-- One complete entry in the simulator's production programming table. -/
structure Entry (shape : BatchShape) (maxStartLength : ℕ) where
  site : Fin (programmedPoints shape)
  phase : ProgrammedPhase
  input : BoundedBytes
    (VeiledFlock.TranscriptSchedule.maxPointLengthFromBound
      (programmedPoints shape) maxStartLength 54)
  knownPrefix : History (Outcome := OracleBlock) site
  target : OracleBlock

noncomputable def table (shape : BatchShape) (maxStartLength : ℕ)
    (absorbedPrefix : List Byte) (transcript : MaskedTranscript shape)
    (hstart : (start shape absorbedPrefix transcript).length ≤ maxStartLength)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (site : Fin (programmedPoints shape)) : Entry shape maxStartLength where
  site := site
  phase := phase site
  input := tracePoint
    (schedule shape maxStartLength absorbedPrefix transcript hstart) answers site
  knownPrefix := priorAnswers answers site
  target := answers site

@[simp]
theorem table_site (shape : BatchShape) (maxStartLength : ℕ)
    (absorbedPrefix : List Byte) (transcript : MaskedTranscript shape)
    (hstart : (start shape absorbedPrefix transcript).length ≤ maxStartLength)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (site : Fin (programmedPoints shape)) :
    (table shape maxStartLength absorbedPrefix transcript hstart answers site).site =
      site := rfl

@[simp]
theorem table_input (shape : BatchShape) (maxStartLength : ℕ)
    (absorbedPrefix : List Byte) (transcript : MaskedTranscript shape)
    (hstart : (start shape absorbedPrefix transcript).length ≤ maxStartLength)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (site : Fin (programmedPoints shape)) :
    (table shape maxStartLength absorbedPrefix transcript hstart answers site).input =
      tracePoint (schedule shape maxStartLength absorbedPrefix transcript hstart)
        answers site := rfl

@[simp]
theorem table_target (shape : BatchShape) (maxStartLength : ℕ)
    (absorbedPrefix : List Byte) (transcript : MaskedTranscript shape)
    (hstart : (start shape absorbedPrefix transcript).length ≤ maxStartLength)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (site : Fin (programmedPoints shape)) :
    (table shape maxStartLength absorbedPrefix transcript hstart answers site).target =
      answers site := rfl

/-- The ledger is complete and duplicate-free: its cardinality is exactly the
Rust programmed-point count and its exact encoded inputs are pairwise distinct
for every possible adaptive answer history. -/
theorem table_inputs_injective (shape : BatchShape) (maxStartLength : ℕ)
    (absorbedPrefix : List Byte) (transcript : MaskedTranscript shape)
    (hstart : (start shape absorbedPrefix transcript).length ≤ maxStartLength)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    Injective fun site =>
      (table shape maxStartLength absorbedPrefix transcript hstart answers site).input := by
  change Injective
    (tracePoints (schedule shape maxStartLength absorbedPrefix transcript hstart)
      answers)
  exact schedule_injective shape maxStartLength absorbedPrefix transcript hstart
    answers

theorem programmed_point_count (shape : BatchShape) :
    programmedPoints shape = 1 + zerocheckRounds shape :=
  programmedPoints_eq shape

end VeiledFlock.ProductionProgrammedPoints

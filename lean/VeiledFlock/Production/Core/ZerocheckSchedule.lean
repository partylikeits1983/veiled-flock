import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Production.Algebra.MaskLayout
import VeiledFlock.Production.Core.TranscriptFraming

/-!
# Exact programmed zerocheck schedule

The full-ZK Rust path programs exactly the scalar following the two masked
round-one slices and then one scalar after each masked recursive pair.  This
module selects those values from the literal flat mask-cursor order and
serializes them with the exact `FsChallenger` framing.
-/

namespace VeiledFlock.ProductionZerocheckSchedule

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.Framing
open VeiledFlock.ProductionMaskLayout
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.TranscriptSchedule

abbrev MaskedTranscript (shape : BatchShape) :=
  Fin (expectedMasks shape) → GhashField

def round1Ab (shape : BatchShape) (transcript : MaskedTranscript shape) :
    Fin ell → GhashField :=
  fun index ↦ transcript (round1AbIndex shape index)

def round1C (shape : BatchShape) (transcript : MaskedTranscript shape) :
    Fin ell → GhashField :=
  fun index ↦ transcript (round1CIndex shape index)

/-- The absorbed transcript immediately before the counter-zero query for
the programmed `z`.  `prefix` is the exact challenger state after the
zerocheck label and bounded equality-point sampling. -/
noncomputable def start (shape : BatchShape) (absorbedPrefix : List Byte)
    (transcript : MaskedTranscript shape) : List Byte :=
  absorbedPrefix ++ observeScalarSlice (round1Ab shape transcript) ++
    observeScalarSlice (round1C shape transcript) ++ squeezeScalarTag

noncomputable def recursiveMessage (shape : BatchShape) (entry : PairIndex)
    (transcript : MaskedTranscript shape) (round : ℕ) : GhashField :=
  if hround : round < zerocheckRounds shape then
    transcript (zerocheckRoundIndex shape ⟨round, hround⟩ entry)
  else
    0

noncomputable def first (shape : BatchShape) (transcript : MaskedTranscript shape)
    (round : ℕ)
    (_history : History (Outcome := OracleBlock) (round + 1)) : GhashField :=
  recursiveMessage shape ⟨0, by decide⟩ transcript round

noncomputable def second (shape : BatchShape) (transcript : MaskedTranscript shape)
    (round : ℕ)
    (_history : History (Outcome := OracleBlock) (round + 1)) : GhashField :=
  recursiveMessage shape ⟨1, by decide⟩ transcript round

theorem programmedPoints_eq (shape : BatchShape) :
    programmedPoints shape = 1 + zerocheckRounds shape := by
  cases shape <;> decide

@[simp]
theorem start_length (shape : BatchShape) (absorbedPrefix : List Byte)
    (transcript : MaskedTranscript shape) :
    (start shape absorbedPrefix transcript).length =
      absorbedPrefix.length + 2 * (10 + 16 * ell) + 2 := by
  simp [start]
  omega

theorem recursiveMessage_of_lt (shape : BatchShape) (entry : PairIndex)
    (transcript : MaskedTranscript shape) (round : ℕ)
    (hround : round < zerocheckRounds shape) :
    recursiveMessage shape entry transcript round =
      transcript
        (zerocheckRoundIndex shape ⟨round, hround⟩ entry) := by
  simp [recursiveMessage, hround]

theorem first_of_reached (shape : BatchShape)
    (transcript : MaskedTranscript shape) (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1))
    (hreached : round + 1 < programmedPoints shape) :
    first shape transcript round history =
      transcript (zerocheckRoundIndex shape
        ⟨round, by rw [programmedPoints_eq] at hreached; omega⟩
        ⟨0, by decide⟩) := by
  apply recursiveMessage_of_lt

theorem second_of_reached (shape : BatchShape)
    (transcript : MaskedTranscript shape) (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1))
    (hreached : round + 1 < programmedPoints shape) :
    second shape transcript round history =
      transcript (zerocheckRoundIndex shape
        ⟨round, by rw [programmedPoints_eq] at hreached; omega⟩
        ⟨1, by decide⟩) := by
  apply recursiveMessage_of_lt

/-- A complete schedule using the exact flat transcript.  This form is used
for the lookahead simulator; the honest causal refinement proves that each
reached coordinate agrees with its prefix-computed counterpart. -/
noncomputable def schedule (shape : BatchShape) (maxStartLength : ℕ)
    (absorbedPrefix : List Byte) (transcript : MaskedTranscript shape)
    (hstart : (start shape absorbedPrefix transcript).length ≤ maxStartLength) :
    Schedule
      (Point := BoundedBytes
        (maxPointLengthFromBound (programmedPoints shape)
          maxStartLength 54))
      (Outcome := OracleBlock) :=
  scalarSchedule (programmedPoints shape) maxStartLength
    (fun _ : Unit ↦ start shape absorbedPrefix transcript) (fun _ ↦ hstart)
    encodeGhashField
    (fun _ ↦ first shape transcript)
    (fun _ ↦ second shape transcript) ()

theorem schedule_injective (shape : BatchShape) (maxStartLength : ℕ)
    (absorbedPrefix : List Byte) (transcript : MaskedTranscript shape)
    (hstart : (start shape absorbedPrefix transcript).length ≤ maxStartLength)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    Function.Injective (tracePoints
      (schedule shape maxStartLength absorbedPrefix transcript hstart) answers) := by
  exact scalarSchedule_injective (programmedPoints shape) maxStartLength
    (fun _ : Unit ↦ start shape absorbedPrefix transcript) (fun _ ↦ hstart)
    encodeGhashField
    (fun _ ↦ first shape transcript)
    (fun _ ↦ second shape transcript) () answers

theorem start_transport (shape : BatchShape)
    {leftPrefix rightPrefix : List Byte}
    {leftTranscript rightTranscript : MaskedTranscript shape}
    (hprefix : rightPrefix = leftPrefix)
    (htranscript : rightTranscript = leftTranscript) :
    start shape rightPrefix rightTranscript =
      start shape leftPrefix leftTranscript := by
  simp [hprefix, htranscript]

theorem first_transport (shape : BatchShape)
    {leftTranscript rightTranscript : MaskedTranscript shape}
    (htranscript : rightTranscript = leftTranscript)
    (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1)) :
    first shape rightTranscript round history =
      first shape leftTranscript round history := by
  simp [htranscript]

theorem second_transport (shape : BatchShape)
    {leftTranscript rightTranscript : MaskedTranscript shape}
    (htranscript : rightTranscript = leftTranscript)
    (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1)) :
    second shape rightTranscript round history =
      second shape leftTranscript round history := by
  simp [htranscript]

end VeiledFlock.ProductionZerocheckSchedule

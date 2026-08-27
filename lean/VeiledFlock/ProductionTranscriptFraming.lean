import VeiledFlock.ConcreteOracle
import VeiledFlock.Field128Serialization
import VeiledFlock.ProductionFraming

/-!
# Exact `FsChallenger` transcript framing

This module mirrors the byte strings absorbed by
`flock-core/src/challenger.rs`.  In particular, a scalar programming point is
the complete absorbed transcript after the scalar-squeeze tag, followed by
the little-endian counter zero.  The first sixteen bytes of the resulting
32-byte oracle block are then reabsorbed before the next operation.
-/

namespace VeiledFlock.ProductionTranscriptFraming

open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.Framing
open VeiledFlock.ProductionFraming
open VeiledFlock.TranscriptSchedule

def opDomain : Byte := 0x01
def opLabel : Byte := 0x02
def opObserve : Byte := 0x03
def opSqueeze : Byte := 0x04
def opBytes : Byte := 0x05
def kindScalar : Byte := 0x01
def kindSlice : Byte := 0x02

/-- Rust's `(length as u64).to_le_bytes()`, under the protocol-size
precondition that the mathematical length fits in `u64`. -/
def encodeLength (length : ℕ) : List Byte :=
  encodeLEList (byteCount := 8) (BitVec.ofNat 64 length)

@[simp]
theorem encodeLength_length (length : ℕ) :
    (encodeLength length).length = 8 := by
  simp [encodeLength]

noncomputable def fieldBytes (value : GhashField) : List Byte :=
  encodeField encodeGhashField value

@[simp]
theorem fieldBytes_length (value : GhashField) :
    (fieldBytes value).length = 16 := by
  simp [fieldBytes]

/-- Exact bytes absorbed by `FsChallenger::new(domain)`. -/
def initTranscript (domain : List Byte) : List Byte :=
  [opDomain] ++ encodeLength domain.length ++ domain

/-- Exact bytes absorbed by `observe_label`. -/
def observeLabel (label : List Byte) : List Byte :=
  [opLabel] ++ encodeLength label.length ++ label

/-- Exact bytes absorbed by `observe_f128`. -/
noncomputable def observeScalar (value : GhashField) : List Byte :=
  [opObserve, kindScalar] ++ fieldBytes value

/-- Exact bytes absorbed by one `observe_f128_slice`. -/
noncomputable def observeScalarSlice {length : ℕ}
    (values : Fin length → GhashField) : List Byte :=
  [opObserve, kindSlice] ++ encodeLength length ++
    (List.ofFn values).flatMap fieldBytes

/-- Exact bytes absorbed by `observe_bytes`. -/
def observeBytes (bytes : List Byte) : List Byte :=
  [opBytes] ++ encodeLength bytes.length ++ bytes

def squeezeScalarTag : List Byte := [opSqueeze, kindScalar]

def squeezeSliceTag (length : ℕ) : List Byte :=
  [opSqueeze, kindSlice] ++ encodeLength length

@[simp]
theorem initTranscript_length (domain : List Byte) :
    (initTranscript domain).length = 9 + domain.length := by
  simp [initTranscript]
  omega

@[simp]
theorem observeLabel_length (label : List Byte) :
    (observeLabel label).length = 9 + label.length := by
  simp [observeLabel]
  omega

@[simp]
theorem observeScalar_length (value : GhashField) :
    (observeScalar value).length = 18 := by
  simp [observeScalar]

@[simp]
theorem observeScalarSlice_length {length : ℕ}
    (values : Fin length → GhashField) :
    (observeScalarSlice values).length = 10 + 16 * length := by
  simp [observeScalarSlice, fieldBytes, List.length_flatMap,
    List.sum_ofFn, Fin.sum_const]
  omega

@[simp]
theorem observeBytes_length (bytes : List Byte) :
    (observeBytes bytes).length = 9 + bytes.length := by
  simp [observeBytes]
  omega

@[simp]
theorem squeezeScalarTag_length : squeezeScalarTag.length = 2 := by
  decide

@[simp]
theorem squeezeSliceTag_length (length : ℕ) :
    (squeezeSliceTag length).length = 10 := by
  simp [squeezeSliceTag]

/-- Exact query point used by the first 32-byte block of a scalar squeeze. -/
def scalarPoint (absorbedBeforeSqueeze : List Byte) : List Byte :=
  absorbedBeforeSqueeze ++ squeezeScalarTag ++ counterZero

/-- Exact live transcript after the scalar challenge has been returned and
reabsorbed. -/
def afterScalar (absorbedBeforeSqueeze : List Byte)
    (answer : OracleBlock) : List Byte :=
  absorbedBeforeSqueeze ++ squeezeScalarTag ++ consumeScalar answer

@[simp]
theorem scalarPoint_length (absorbedBeforeSqueeze : List Byte) :
  (scalarPoint absorbedBeforeSqueeze).length =
      absorbedBeforeSqueeze.length + 10 := by
  simp [scalarPoint, counterZero]

@[simp]
theorem afterScalar_length (absorbedBeforeSqueeze : List Byte)
    (answer : OracleBlock) :
    (afterScalar absorbedBeforeSqueeze answer).length =
      absorbedBeforeSqueeze.length + 18 := by
  simp [afterScalar]

/-- Exact point for counter `counter` of a vector squeeze.  Rust clones the
live SHA-256 state after absorbing the slice tag and hashes that state with
the little-endian `u64` counter. -/
def slicePoint (absorbedBeforeSqueeze : List Byte) (length : ℕ)
    (counter : ProductionFraming.Word64) : List Byte :=
  absorbedBeforeSqueeze ++ squeezeSliceTag length ++
    encodeLEList (byteCount := 8) counter

/-- Exact bytes returned and reabsorbed by a successful vector squeeze,
expressed after parsing each consecutive 16-byte chunk as an `F128`. -/
noncomputable def sliceAnswerBytes {length : ℕ}
    (answer : Fin length → GhashField) : List Byte :=
  (List.ofFn answer).flatMap fieldBytes

/-- Exact live transcript after `sample_f128_vec(length)`. -/
noncomputable def afterSlice (absorbedBeforeSqueeze : List Byte)
    {length : ℕ} (answer : Fin length → GhashField) : List Byte :=
  absorbedBeforeSqueeze ++ squeezeSliceTag length ++ sliceAnswerBytes answer

@[simp]
theorem slicePoint_length (absorbedBeforeSqueeze : List Byte) (length : ℕ)
    (counter : ProductionFraming.Word64) :
    (slicePoint absorbedBeforeSqueeze length counter).length =
      absorbedBeforeSqueeze.length + 18 := by
  simp [slicePoint]

@[simp]
theorem sliceAnswerBytes_length {length : ℕ}
    (answer : Fin length → GhashField) :
    (sliceAnswerBytes answer).length = 16 * length := by
  simp [sliceAnswerBytes, fieldBytes, List.length_flatMap,
    List.sum_ofFn]
  omega

@[simp]
theorem afterSlice_length (absorbedBeforeSqueeze : List Byte)
    {length : ℕ} (answer : Fin length → GhashField) :
    (afterSlice absorbedBeforeSqueeze answer).length =
      absorbedBeforeSqueeze.length + 10 + 16 * length := by
  simp [afterSlice]
  omega

/-- Vector-squeeze transcript transport is purely functional: equal live
prefixes and equal returned field vectors produce equal next prefixes. -/
theorem afterSlice_congr {leftPrefix rightPrefix : List Byte} {length : ℕ}
    {leftAnswer rightAnswer : Fin length → GhashField}
    (hprefix : rightPrefix = leftPrefix)
    (hanswer : rightAnswer = leftAnswer) :
    afterSlice rightPrefix rightAnswer = afterSlice leftPrefix leftAnswer := by
  rw [hprefix, hanswer]

/-- The generic schedule's scalar observation is byte-for-byte the production
`observe_f128` framing. -/
theorem transcriptObserveScalar_eq (value : GhashField) :
    VeiledFlock.TranscriptSchedule.observeScalar
        (encodeField encodeGhashField) value =
      observeScalar value := by
  rfl

/-- Bytes between consecutive programmed zerocheck sites are exactly the
Rust operations `reabsorb answer; observe_f128(g1); observe_f128(gInf);
sample_f128 tag`. -/
theorem scalarRoundStep_eq
    (first second : ∀ rounds,
      VeiledFlock.AdaptiveOracleProgramming.History
        (Outcome := OracleBlock) (rounds + 1) → GhashField)
    (rounds : ℕ)
    (history : VeiledFlock.AdaptiveOracleProgramming.History
      (Outcome := OracleBlock) (rounds + 1)) :
    scalarRoundStep consumeScalar (encodeField encodeGhashField)
        first second rounds history =
      consumeScalar (history (Fin.last rounds)) ++
        observeScalar (first rounds history) ++
        observeScalar (second rounds history) ++ squeezeScalarTag := by
  rfl

end VeiledFlock.ProductionTranscriptFraming

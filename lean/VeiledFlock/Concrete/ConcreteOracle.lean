import VeiledFlock.Concrete.TranscriptSchedule

/-!
# Concrete finite oracle blocks and scalar transcript schedule

The implementation's SHA-256/random-oracle answer is 32 bytes.  A scalar
Fiat--Shamir challenge consumes and reabsorbs its first 16 bytes; the remaining
16 bytes stay uniform when the simulator programs the scalar prefix.  This
file instantiates the byte-growth theorem with those exact widths.
-/

namespace VeiledFlock.ConcreteOracle

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.Framing
open VeiledFlock.TranscriptSchedule

abbrev OracleBlock := Fin 32 → Byte
abbrev OracleHalf := Fin 16 → Byte

/-- A 32-byte random-oracle answer is exactly its low and high 16-byte
halves.  This is the factorization used when the simulator overwrites the
scalar prefix and preserves the still-uniform suffix. -/
def oracleBlockSplit : OracleBlock ≃ OracleHalf × OracleHalf :=
  (Equiv.arrowCongr (finSumFinEquiv (m := 16) (n := 16))
    (Equiv.refl Byte)).symm.trans
      (Equiv.sumArrowEquivProdArrow (Fin 16) (Fin 16) Byte)

def consumeScalar (block : OracleBlock) : List Byte :=
  List.ofFn fun index : Fin 16 => block (Fin.castLE (by decide) index)

theorem consumeScalar_eq_firstHalf (block : OracleBlock) :
    consumeScalar block = List.ofFn (oracleBlockSplit block).1 := by
  rfl

/-- Replace only the first 16 bytes of an oracle block. -/
def programScalarPrefix (scalarPrefix : OracleHalf) (block : OracleBlock) : OracleBlock :=
  oracleBlockSplit.symm (scalarPrefix, (oracleBlockSplit block).2)

@[simp]
theorem oracleBlockSplit_programScalarPrefix (scalarPrefix : OracleHalf)
    (block : OracleBlock) :
    oracleBlockSplit (programScalarPrefix scalarPrefix block) =
      (scalarPrefix, (oracleBlockSplit block).2) := by
  simp [programScalarPrefix]

@[simp]
theorem consumeScalar_length (block : OracleBlock) :
    (consumeScalar block).length = 16 := by
  simp [consumeScalar]

def encodeField {F : Type*} (encode : F → Fin 16 → Byte) (value : F) :
    List Byte :=
  List.ofFn (encode value)

@[simp]
theorem encodeField_length {F : Type*} (encode : F → Fin 16 → Byte)
    (value : F) : (encodeField encode value).length = 16 := by
  simp [encodeField]

/-- Exact finite point universe and causal schedule for all scalar points
programmed by one simulated proof. -/
def scalarSchedule {AlgView F : Type*}
    (sites maxStartLength : ℕ)
    (start : AlgView → List Byte)
    (hstart : ∀ algebraic, (start algebraic).length ≤ maxStartLength)
    (encode : F → Fin 16 → Byte)
    (first second : AlgView → ∀ rounds,
      History (Outcome := OracleBlock) (rounds + 1) → F)
    (algebraic : AlgView) :
    Schedule
      (Point := BoundedBytes
        (maxPointLengthFromBound sites maxStartLength 54))
      (Outcome := OracleBlock) :=
  boundedAppendScheduleFromBound sites maxStartLength (start algebraic)
    (hstart algebraic)
    (scalarRoundStep consumeScalar (encodeField encode)
      (first algebraic) (second algebraic))
    54
    (scalarRoundStep_length consumeScalar consumeScalar_length
      (encodeField encode) (encodeField_length encode)
      (first algebraic) (second algebraic))

/-- All concrete scalar programming points are pairwise distinct, uniformly
over algebraic transcripts and oracle-answer histories. -/
theorem scalarSchedule_injective {AlgView F : Type*}
    (sites maxStartLength : ℕ)
    (start : AlgView → List Byte)
    (hstart : ∀ algebraic, (start algebraic).length ≤ maxStartLength)
    (encode : F → Fin 16 → Byte)
    (first second : AlgView → ∀ rounds,
      History (Outcome := OracleBlock) (rounds + 1) → F)
    (algebraic : AlgView)
    (answers : History (Outcome := OracleBlock) sites) :
    Injective (tracePoints
      (scalarSchedule sites maxStartLength start hstart encode first second
        algebraic) answers) :=
  tracePoints_boundedAppendScheduleFromBound_injective
    (start algebraic) (hstart algebraic)
    (scalarRoundStep consumeScalar (encodeField encode)
      (first algebraic) (second algebraic))
    54 (by decide)
    (scalarRoundStep_length consumeScalar consumeScalar_length
      (encodeField encode) (encodeField_length encode)
      (first algebraic) (second algebraic)) answers

/-- Exact causal correspondence for two production scalar schedules.  It is
enough to preserve the initial serialized transcript and the two field
messages emitted on each prefix of the proposed answer vector. -/
theorem scalarSchedule_tracePoint_eq {AlgView F : Type*}
    (sites maxStartLength : ℕ)
    (leftStart rightStart : AlgView → List Byte)
    (hleftStart : ∀ algebraic,
      (leftStart algebraic).length ≤ maxStartLength)
    (hrightStart : ∀ algebraic,
      (rightStart algebraic).length ≤ maxStartLength)
    (encode : F → Fin 16 → Byte)
    (leftFirst leftSecond rightFirst rightSecond : AlgView → ∀ rounds,
      History (Outcome := OracleBlock) (rounds + 1) → F)
    (leftAlg rightAlg : AlgView)
    (answers : History (Outcome := OracleBlock) sites)
    (hstart : rightStart rightAlg = leftStart leftAlg)
    (hfirst : ∀ rounds (hle : rounds + 1 ≤ sites),
      rightFirst rightAlg rounds
          (fun site ↦ answers (Fin.castLE hle site)) =
        leftFirst leftAlg rounds
          (fun site ↦ answers (Fin.castLE hle site)))
    (hsecond : ∀ rounds (hle : rounds + 1 ≤ sites),
      rightSecond rightAlg rounds
          (fun site ↦ answers (Fin.castLE hle site)) =
        leftSecond leftAlg rounds
          (fun site ↦ answers (Fin.castLE hle site)))
    (site : Fin sites) :
    tracePoint
        (scalarSchedule sites maxStartLength rightStart hrightStart encode
          rightFirst rightSecond rightAlg) answers site =
      tracePoint
        (scalarSchedule sites maxStartLength leftStart hleftStart encode
          leftFirst leftSecond leftAlg) answers site := by
  apply unboundBytes_injective
  simp only [scalarSchedule]
  rw [unbound_tracePoint_boundedAppendScheduleFromBound,
    unbound_tracePoint_boundedAppendScheduleFromBound]
  apply tracePoint_appendSchedule_eq_of_traceSteps
    (leftStart leftAlg) (rightStart rightAlg)
    (scalarRoundStep consumeScalar (encodeField encode)
      (leftFirst leftAlg) (leftSecond leftAlg))
    (scalarRoundStep consumeScalar (encodeField encode)
      (rightFirst rightAlg) (rightSecond rightAlg)) answers hstart
  intro rounds hle
  simp only [scalarRoundStep, hfirst rounds hle, hsecond rounds hle]

end VeiledFlock.ConcreteOracle

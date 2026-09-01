import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Concrete.ConcreteFraming
import VeiledFlock.Oracle.UniversalFreshness

/-!
# Uniform freshness of the concrete scalar programming schedule

All scalar-programming points extend the same initial transcript state.  If
that state contains the tagged 256-bit proof nonce at its production-fixed
offset, equality of any two points at a fixed site recovers equality of the
nonces, even when the algebraic view and every prior oracle answer differ.
-/

namespace VeiledFlock.ConcreteScalarScheduleFreshness

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.NonceSerialization
open VeiledFlock.TranscriptSchedule

/-- The complete bounded scalar schedule is cross-history injective in the
proof nonce.  This discharges the load-bearing premise of
`UniversalFreshness.card_badNonces_le`. -/
theorem scalarSchedule_cross_nonce
    {AlgView F : Type*} (sites maxStartLength : ℕ)
    (head : List Byte)
    (startSuffix : AlgView → NumericNonce → List Byte)
    (hstart : ∀ algebraic nonce,
      (VeiledFlock.ConcreteFraming.transcriptPoint head
        (startSuffix algebraic) nonce).length ≤ maxStartLength)
    (encode : F → Fin 16 → Byte)
    (first second : AlgView → ∀ rounds,
      History (Outcome := OracleBlock) (rounds + 1) → F)
    (site : Fin sites)
    (leftAlg rightAlg : AlgView)
    (leftNonce rightNonce : NumericNonce)
    (leftAnswers rightAnswers : History (Outcome := OracleBlock) sites)
    (heq :
      tracePoint
          (scalarSchedule sites maxStartLength
            (fun algebraic ↦ VeiledFlock.ConcreteFraming.transcriptPoint head
              (startSuffix algebraic) leftNonce)
            (fun algebraic ↦ hstart algebraic leftNonce)
            encode first second leftAlg)
          leftAnswers site =
        tracePoint
          (scalarSchedule sites maxStartLength
            (fun algebraic ↦ VeiledFlock.ConcreteFraming.transcriptPoint head
              (startSuffix algebraic) rightNonce)
            (fun algebraic ↦ hstart algebraic rightNonce)
            encode first second rightAlg)
          rightAnswers site) :
    leftNonce = rightNonce := by
  have hunbound := congrArg unboundBytes heq
  let leftStart := VeiledFlock.ConcreteFraming.transcriptPoint head
    (startSuffix leftAlg) leftNonce
  let rightStart := VeiledFlock.ConcreteFraming.transcriptPoint head
    (startSuffix rightAlg) rightNonce
  let leftStep := scalarRoundStep consumeScalar (encodeField encode)
    (first leftAlg) (second leftAlg)
  let rightStep := scalarRoundStep consumeScalar (encodeField encode)
    (first rightAlg) (second rightAlg)
  have hleftUnbound :
      unboundBytes
          (tracePoint
            (scalarSchedule sites maxStartLength
              (fun algebraic ↦ VeiledFlock.ConcreteFraming.transcriptPoint head
                (startSuffix algebraic) leftNonce)
              (fun algebraic ↦ hstart algebraic leftNonce)
              encode first second leftAlg)
            leftAnswers site) =
        tracePoint (appendSchedule leftStart leftStep) leftAnswers site := by
    exact unbound_tracePoint_boundedAppendScheduleFromBound leftStart
      (hstart leftAlg leftNonce) leftStep 54
      (scalarRoundStep_length consumeScalar consumeScalar_length
        (encodeField encode) (encodeField_length encode)
        (first leftAlg) (second leftAlg)) leftAnswers site
  have hrightUnbound :
      unboundBytes
          (tracePoint
            (scalarSchedule sites maxStartLength
              (fun algebraic ↦ VeiledFlock.ConcreteFraming.transcriptPoint head
                (startSuffix algebraic) rightNonce)
              (fun algebraic ↦ hstart algebraic rightNonce)
              encode first second rightAlg)
            rightAnswers site) =
        tracePoint (appendSchedule rightStart rightStep) rightAnswers site := by
    exact unbound_tracePoint_boundedAppendScheduleFromBound rightStart
      (hstart rightAlg rightNonce) rightStep 54
      (scalarRoundStep_length consumeScalar consumeScalar_length
        (encodeField encode) (encodeField_length encode)
        (first rightAlg) (second rightAlg)) rightAnswers site
  rw [hleftUnbound, hrightUnbound] at hunbound
  obtain ⟨leftTail, hleftPrefix⟩ :=
    tracePoint_appendSchedule_hasPrefix leftStart leftStep leftAnswers site
  obtain ⟨rightTail, hrightPrefix⟩ :=
    tracePoint_appendSchedule_hasPrefix rightStart rightStep rightAnswers site
  rw [hleftPrefix, hrightPrefix] at hunbound
  apply VeiledFlock.UniversalFreshness.transcriptPoint_cross_injective head
    (fun _ nonce ↦ startSuffix leftAlg nonce ++ leftTail)
    (fun _ nonce ↦ startSuffix rightAlg nonce ++ rightTail)
    (leftContext := ()) (rightContext := ())
  simpa only [leftStart, rightStart,
    VeiledFlock.ConcreteFraming.transcriptPoint,
    fixedOffsetFrame, List.append_assoc] using hunbound

end VeiledFlock.ConcreteScalarScheduleFreshness

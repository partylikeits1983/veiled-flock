import VeiledFlock.Production.Operational.CausalMaskTranscript

/-!
# Field-to-byte transport for the causal production schedule

Given equality of the complete algebraic masked transcript, this module
derives all three byte-transport facts required by the operational simulator.
The honest side completes only the oracle prefix reached at the relevant
point; the causality lemmas prove that arbitrary future completion is inert.
-/

namespace VeiledFlock.ProductionCausalScheduleTransport

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalMaskTranscript
open VeiledFlock.ProductionMaskLayout
open VeiledFlock.ProductionZerocheckSchedule

variable {W : Type*}

def completedAnswers (shape : BatchShape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1)) :
    OracleHistory (Outcome := OracleBlock) (programmedPoints shape) :=
  if hle : round + 1 ≤ programmedPoints shape then
    completion.complete (round + 1) hle history
  else
    emptyCompletion shape completion

noncomputable def honestStartTranscript (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (masks : Masks shape) : MaskedTranscript shape :=
  transcript shape secret (emptyCompletion shape completion) witness masks

noncomputable def honestRoundTranscript (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (masks : Masks shape) (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1)) :
    MaskedTranscript shape :=
  transcript shape secret (completedAnswers shape completion round history)
    witness masks

noncomputable def honestFirst (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (masks : Masks shape) (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1)) : GhashField :=
  first shape
    (honestRoundTranscript shape secret completion witness masks round history)
    round history

noncomputable def honestSecond (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (masks : Masks shape) (round : ℕ)
    (history : History (Outcome := OracleBlock) (round + 1)) : GhashField :=
  second shape
    (honestRoundTranscript shape secret completion witness masks round history)
    round history

theorem start_transport (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (witness : W) (masks : Masks shape)
    (simulatedTranscript : MaskedTranscript shape)
    (htranscript : simulatedTranscript =
      transcript shape secret answers witness masks)
    {honestPrefix simulatedPrefix : List Byte}
    (hprefix : simulatedPrefix = honestPrefix) :
    start shape simulatedPrefix simulatedTranscript =
      start shape honestPrefix
        (honestStartTranscript shape secret completion witness masks) := by
  rw [hprefix, htranscript]
  unfold start honestStartTranscript
  rw [round1Ab_completion_eq shape secret completion answers witness masks,
    round1C_completion_eq shape secret completion answers witness masks]

theorem recursive_transport (shape : BatchShape) (entry : PairIndex)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (witness : W) (masks : Masks shape)
    (simulatedTranscript : MaskedTranscript shape)
    (htranscript : simulatedTranscript =
      transcript shape secret answers witness masks)
    (round : ℕ) (hle : round + 1 ≤ programmedPoints shape) :
    recursiveMessage shape entry simulatedTranscript round =
      recursiveMessage shape entry
        (honestRoundTranscript shape secret completion witness masks round
          (fun site ↦ answers (Fin.castLE hle site))) round := by
  by_cases hround : round < zerocheckRounds shape
  · let roundIndex : Fin (zerocheckRounds shape) := ⟨round, hround⟩
    rw [recursiveMessage_of_lt shape entry simulatedTranscript round hround]
    rw [recursiveMessage_of_lt shape entry
      (honestRoundTranscript shape secret completion witness masks round
        (fun site ↦ answers (Fin.castLE hle site))) round hround]
    have hcausal := recursive_completion_eq shape secret completion
      roundIndex entry
      (fun site ↦ answers (Fin.castLE hle site)) answers
      (fun _ ↦ rfl) witness masks
    change
      simulatedTranscript (zerocheckRoundIndex shape roundIndex entry) =
        honestRoundTranscript shape secret completion witness masks round
          (fun site ↦ answers (Fin.castLE hle site))
          (zerocheckRoundIndex shape roundIndex entry)
    rw [htranscript]
    symm
    simpa [honestRoundTranscript, completedAnswers, hle] using hcausal
  · simp [recursiveMessage, hround]

theorem first_transport (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (witness : W) (masks : Masks shape)
    (simulatedTranscript : MaskedTranscript shape)
    (htranscript : simulatedTranscript =
      transcript shape secret answers witness masks)
    (round : ℕ) (hle : round + 1 ≤ programmedPoints shape) :
    first shape simulatedTranscript round
        (fun site ↦ answers (Fin.castLE hle site)) =
      honestFirst shape secret completion witness masks round
        (fun site ↦ answers (Fin.castLE hle site)) := by
  exact recursive_transport shape ⟨0, by decide⟩ secret completion answers
    witness masks simulatedTranscript htranscript round hle

theorem second_transport (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (witness : W) (masks : Masks shape)
    (simulatedTranscript : MaskedTranscript shape)
    (htranscript : simulatedTranscript =
      transcript shape secret answers witness masks)
    (round : ℕ) (hle : round + 1 ≤ programmedPoints shape) :
    second shape simulatedTranscript round
        (fun site ↦ answers (Fin.castLE hle site)) =
      honestSecond shape secret completion witness masks round
        (fun site ↦ answers (Fin.castLE hle site)) := by
  exact recursive_transport shape ⟨1, by decide⟩ secret completion answers
    witness masks simulatedTranscript htranscript round hle

end VeiledFlock.ProductionCausalScheduleTransport

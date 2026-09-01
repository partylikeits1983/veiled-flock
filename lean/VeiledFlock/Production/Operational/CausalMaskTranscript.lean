import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Production.Operational.MaskCausality
import VeiledFlock.Production.Core.ZerocheckSchedule

/-!
# Causal extraction of the production masked transcript

This module connects the generic external-oracle causality theorem to the
literal flat VEIL mask cursor.  It proves that completing the empty oracle
history cannot change either round-one slice, and completing a reached
`z,rho...` prefix cannot change the recursive pair emitted at that point.
-/

namespace VeiledFlock.ProductionCausalMaskTranscript

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionMaskCausality
open VeiledFlock.ProductionMaskLayout
open VeiledFlock.ProductionZerocheckSchedule

variable {W : Type*}

abbrev CausalSecret (shape : BatchShape) :=
  VeiledFlock.OracleCausalOneTimePad.CausalSecret
    (F := GhashField) (I := Unit) (W := W)
    (Outcome := OracleBlock) (available shape)

abbrev Masks (shape : BatchShape) :=
  VeiledFlock.AdaptiveOneTimePad.Masks
    (F := GhashField) (I := Unit) (expectedMasks shape)

noncomputable def transcript (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (answers : OracleHistory (Outcome := OracleBlock)
      (programmedPoints shape))
    (witness : W) (masks : Masks shape) : MaskedTranscript shape :=
  fun site ↦
    run
      (closeSecret (available shape) (available_le_sites shape) secret answers)
      witness (expectedMasks shape) masks site ()

def emptyHistory : OracleHistory (Outcome := OracleBlock) 0 := Fin.elim0

def emptyCompletion (shape : BatchShape)
    (completion : Completion OracleBlock (programmedPoints shape)) :
    OracleHistory (Outcome := OracleBlock) (programmedPoints shape) :=
  completion.complete 0 (Nat.zero_le _) emptyHistory

theorem round1Ab_completion_eq (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (answers : OracleHistory (Outcome := OracleBlock)
      (programmedPoints shape))
    (witness : W) (masks : Masks shape) :
    round1Ab shape
        (transcript shape secret (emptyCompletion shape completion)
          witness masks) =
      round1Ab shape (transcript shape secret answers witness masks) := by
  funext index
  simp only [round1Ab, transcript, emptyCompletion]
  apply congrFun
  apply run_at_completion_eq
    (available shape) (available_le_sites shape) (available_monotone shape)
    secret completion (Nat.zero_le _) emptyHistory answers
  · intro site
    exact Fin.elim0 site
  · apply le_of_eq
    apply prefixAvailable_initial shape
    have hindex := index.isLt
    simp only [round1AbIndex_val]
    omega

theorem round1C_completion_eq (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (answers : OracleHistory (Outcome := OracleBlock)
      (programmedPoints shape))
    (witness : W) (masks : Masks shape) :
    round1C shape
        (transcript shape secret (emptyCompletion shape completion)
          witness masks) =
      round1C shape (transcript shape secret answers witness masks) := by
  funext index
  simp only [round1C, transcript, emptyCompletion]
  apply congrFun
  apply run_at_completion_eq
    (available shape) (available_le_sites shape) (available_monotone shape)
    secret completion (Nat.zero_le _) emptyHistory answers
  · intro site
    exact Fin.elim0 site
  · apply le_of_eq
    apply prefixAvailable_initial shape
    have hindex := index.isLt
    simp only [round1CIndex_val]
    omega

theorem recursive_completion_eq (shape : BatchShape)
    (secret : CausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (round : Fin (zerocheckRounds shape)) (entry : PairIndex)
    (history : OracleHistory (Outcome := OracleBlock) (round.val + 1))
    (answers : OracleHistory (Outcome := OracleBlock)
      (programmedPoints shape))
    (hanswers : ∀ site : Fin (round.val + 1),
      answers
          (Fin.castLE (by
            cases shape <;>
              simp [programmedPoints, zerocheckRounds, m, kSkip] at * <;>
              omega) site) =
        history site)
    (witness : W) (masks : Masks shape) :
    transcript shape secret
        (completion.complete (round.val + 1) (by
          cases shape <;>
            simp [programmedPoints, zerocheckRounds, m, kSkip] at * <;>
            omega) history)
        witness masks (zerocheckRoundIndex shape round entry) =
      transcript shape secret answers witness masks
        (zerocheckRoundIndex shape round entry) := by
  simp only [transcript]
  apply congrFun
  apply run_at_completion_eq
    (available shape) (available_le_sites shape) (available_monotone shape)
    secret completion
    (by
      cases shape <;>
        simp [programmedPoints, zerocheckRounds, m, kSkip] at * <;>
        omega)
    history answers hanswers witness masks
    (zerocheckRoundIndex shape round entry)
  exact recursive_available_le_reached shape round entry

end VeiledFlock.ProductionCausalMaskTranscript

import VeiledFlock.ProductionCorrelatedConstraintCompiler
import VeiledFlock.ShiftedLinearCircuit

/-!
# Exact shifted-circuit to VEIL compiler bridge

The Rust compiler preserves the 259 shifted affine rows, appends
`r + (r+1) + 1 = 0`, and finally appends three Hadamard-link rows.  This file
constructs that exact 263-row sequence and proves the four appended rows from
the dummy definitions and the original multiplication-gate evaluation.
-/

namespace VeiledFlock.ProductionShiftedCompiler

set_option maxHeartbeats 400000

open Function
open VeiledFlock.BinaryPolynomial
open VeiledFlock.ConcreteParameters
open VeiledFlock.ConcreteTranscript
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionCorrelatedConstraintCompiler
open VeiledFlock.ProductionLinearBatch
open VeiledFlock.ProductionMultiplicationPadding

abbrev MaskIndex (shape : BatchShape) := Fin (expectedMasks shape)
abbrev FullIndex (shape : BatchShape) := Fin (linearLogicalLength shape)
abbrev OriginalRow := Fin shiftedLinearConstraints
abbrev Side := Fin 3

noncomputable def dummyValues
    (dummy : GhashField × GhashField × GhashField) :
    Fin 6 → GhashField := ![
  dummy.1, dummy.2.1, dummy.1 * dummy.2.1,
  dummy.1 + 1, dummy.2.2, (dummy.1 + 1) * dummy.2.2]

noncomputable def paddedMessage (shape : BatchShape)
    (masks : MaskIndex shape → GhashField)
    (dummy : GhashField × GhashField × GhashField) :
    FullIndex shape → GhashField :=
  Fin.append masks (dummyValues dummy)

noncomputable def maskRestriction (shape : BatchShape) :
    (FullIndex shape → GhashField) →ₗ[GhashField]
      (MaskIndex shape → GhashField) where
  toFun values index := values (Fin.castAdd 6 index)
  map_add' left right := rfl
  map_smul' scalar values := rfl

@[simp]
theorem maskRestriction_paddedMessage (shape : BatchShape)
    (masks : MaskIndex shape → GhashField)
    (dummy : GhashField × GhashField × GhashField) :
    maskRestriction shape (paddedMessage shape masks dummy) = masks := by
  funext index
  exact Fin.append_left masks (dummyValues dummy) index

noncomputable def extendFunctional (shape : BatchShape)
    (functional :
      (MaskIndex shape → GhashField) →ₗ[GhashField] GhashField) :
    (FullIndex shape → GhashField) →ₗ[GhashField] GhashField :=
  functional.comp (maskRestriction shape)

@[simp]
theorem extendFunctional_paddedMessage (shape : BatchShape)
    (functional :
      (MaskIndex shape → GhashField) →ₗ[GhashField] GhashField)
    (masks : MaskIndex shape → GhashField)
    (dummy : GhashField × GhashField × GhashField) :
    extendFunctional shape functional (paddedMessage shape masks dummy) =
      functional masks := by
  simp [extendFunctional]

noncomputable def dummyCoordinate (shape : BatchShape) (index : Fin 6) :
    (FullIndex shape → GhashField) →ₗ[GhashField] GhashField where
  toFun values := values (Fin.natAdd (expectedMasks shape) index)
  map_add' left right := rfl
  map_smul' scalar values := rfl

@[simp]
theorem dummyCoordinate_paddedMessage (shape : BatchShape) (index : Fin 6)
    (masks : MaskIndex shape → GhashField)
    (dummy : GhashField × GhashField × GhashField) :
    dummyCoordinate shape index (paddedMessage shape masks dummy) =
      dummyValues dummy index := by
  exact Fin.append_right masks (dummyValues dummy) index

def component (values : GhashField × GhashField × GhashField) :
    Side → GhashField
  | ⟨0, _⟩ => values.1
  | ⟨1, _⟩ => values.2.1
  | ⟨2, _⟩ => values.2.2

def dummyGateIndex (side : Side) (row : Fin 2) : Fin 6 :=
  ⟨side.val + 3 * row.val, by omega⟩

@[simp]
theorem component_visibleClaims (alpha : GhashField)
    (secret dummy : GhashField × GhashField × GhashField)
    (side : Side) :
    component (productionDummyView alpha dummy + secret) side =
      component secret side +
        alpha * dummyValues dummy (dummyGateIndex side 0) +
        alpha ^ 2 * dummyValues dummy (dummyGateIndex side 1) := by
  rcases secret with ⟨a, b, c⟩
  rcases dummy with ⟨r, s, t⟩
  fin_cases side <;>
    simp [component, productionDummyView, dummyValues, dummyGateIndex] <;>
    ring

/-- Exact semantic certificate exported by `shifted_verifier_circuit` before
VEIL appends its four rows. -/
structure ShiftedExecution (shape : BatchShape) (W : Type*) where
  maskMessage : W → MaskIndex shape → GhashField
  multiplicationSecret : W →
    GhashField × GhashField × GhashField
  multiplicationValid : ∀ witness,
    (multiplicationSecret witness).1 *
        (multiplicationSecret witness).2.1 =
      (multiplicationSecret witness).2.2
  multiplicationFunctional : Side →
    (MaskIndex shape → GhashField) →ₗ[GhashField] GhashField
  multiplicationConstant : Side → GhashField
  multiplication_evaluation : ∀ witness side,
    multiplicationFunctional side (maskMessage witness) +
        multiplicationConstant side =
      component (multiplicationSecret witness) side
  originalRows : OriginalRow →
    (MaskIndex shape → GhashField) →ₗ[GhashField] GhashField
  originalConstants : OriginalRow → GhashField
  original_satisfied : ∀ witness row,
    originalRows row (maskMessage witness) + originalConstants row = 0
  constraintRlc : GhashField
  gammaFunctional :
    (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField

noncomputable def paddingRow (shape : BatchShape) :
    (FullIndex shape → GhashField) →ₗ[GhashField] GhashField :=
  dummyCoordinate shape 0 + dummyCoordinate shape 3

noncomputable def linkRow (shape : BatchShape) (alpha : GhashField)
    (execution : ShiftedExecution shape W) (side : Side) :
    (FullIndex shape → GhashField) →ₗ[GhashField] GhashField :=
  extendFunctional shape (execution.multiplicationFunctional side) +
    alpha • dummyCoordinate shape (dummyGateIndex side 0) +
    alpha ^ 2 • dummyCoordinate shape (dummyGateIndex side 1)

noncomputable def compiledRows (shape : BatchShape) (alpha : GhashField)
    (execution : ShiftedExecution shape W) :
    Fin combinedLinearConstraints →
      (FullIndex shape → GhashField) →ₗ[GhashField] GhashField :=
  Fin.append
    (Fin.append (fun row => extendFunctional shape (execution.originalRows row))
      (fun _ : Fin 1 => paddingRow shape))
    (linkRow shape alpha execution)

noncomputable def compiledConstants {shape : BatchShape} {Public : Type*}
    (alpha : GhashField)
    (execution : ShiftedExecution shape W)
    (_ : Public) (claims : GhashField × GhashField × GhashField) :
    Fin combinedLinearConstraints → GhashField :=
  Fin.append
    (Fin.append execution.originalConstants (fun _ : Fin 1 => 1))
    (fun side => component claims side + execution.multiplicationConstant side)

theorem paddingRow_satisfied (shape : BatchShape)
    (masks : MaskIndex shape → GhashField)
    (dummy : GhashField × GhashField × GhashField) :
    paddingRow shape (paddedMessage shape masks dummy) + 1 = 0 := by
  rcases dummy with ⟨r, s, t⟩
  simp only [paddingRow, LinearMap.add_apply,
    dummyCoordinate_paddedMessage, dummyValues]
  change r + (r + 1) + 1 = 0
  linear_combination add_self_eq_zero_charTwo r +
    add_self_eq_zero_charTwo (1 : GhashField)

theorem linkRow_satisfied (shape : BatchShape) (alpha : GhashField)
    (execution : ShiftedExecution shape W) (witness : W)
    (dummy : GhashField × GhashField × GhashField) (side : Side) :
    linkRow shape alpha execution side
          (paddedMessage shape (execution.maskMessage witness) dummy) +
        (component
            (visibleClaims alpha execution.multiplicationSecret witness dummy)
            side + execution.multiplicationConstant side) =
      0 := by
  rw [visibleClaims]
  simp only [linkRow, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    extendFunctional_paddedMessage, dummyCoordinate_paddedMessage]
  rw [component_visibleClaims]
  have heval := execution.multiplication_evaluation witness side
  have hself := add_self_eq_zero_charTwo
    (component (execution.multiplicationSecret witness) side)
  have hdummy0 := add_self_eq_zero_charTwo
    (alpha * dummyValues dummy (dummyGateIndex side 0))
  have hdummy1 := add_self_eq_zero_charTwo
    (alpha ^ 2 * dummyValues dummy (dummyGateIndex side 1))
  linear_combination heval + hself + hdummy0 + hdummy1

theorem compiledRows_satisfied {Public : Type*}
    (shape : BatchShape) (alpha : GhashField)
    (execution : ShiftedExecution shape W) (statement : W → Public)
    (witness : W) (dummy : GhashField × GhashField × GhashField)
    (row : Fin combinedLinearConstraints) :
    compiledRows shape alpha execution row
          (paddedMessage shape (execution.maskMessage witness) dummy) +
        compiledConstants alpha execution (statement witness)
          (visibleClaims alpha execution.multiplicationSecret witness dummy)
          row = 0 := by
  obtain ⟨row | side, rfl⟩ := finSumFinEquiv.surjective row
  · obtain ⟨original | padding, rfl⟩ := finSumFinEquiv.surjective row
    · simpa [compiledRows, compiledConstants] using
        execution.original_satisfied witness original
    · rw [Subsingleton.elim padding 0]
      simpa [compiledRows, compiledConstants] using
        paddingRow_satisfied shape (execution.maskMessage witness) dummy
  · simpa [compiledRows, compiledConstants] using
      linkRow_satisfied shape alpha execution witness dummy side

/-- The exact 263-row compiler execution, with all four appended-row proofs
discharged. -/
noncomputable def toExecution {Public : Type*}
    (shape : BatchShape) (alpha : GhashField)
    (execution : ShiftedExecution shape W) (statement : W → Public) :
    ProductionCorrelatedConstraintCompiler.Execution
      shape W Public statement alpha where
  multiplicationSecret := execution.multiplicationSecret
  multiplicationValid := execution.multiplicationValid
  linearRows := compiledRows shape alpha execution
  rowConstants := compiledConstants alpha execution
  linearMessage := fun witness dummy =>
    paddedMessage shape (execution.maskMessage witness) dummy
  rows_satisfied := compiledRows_satisfied shape alpha execution statement
  constraintRlc := execution.constraintRlc
  gammaFunctional := execution.gammaFunctional

end VeiledFlock.ProductionShiftedCompiler

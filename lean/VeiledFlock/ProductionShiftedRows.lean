import VeiledFlock.ProductionMaskLayout
import VeiledFlock.ProductionShiftedCompiler

/-!
# The 259 production shifted-verifier rows

This module expands the previously abstract `original_satisfied` premise into
the exact row inventory emitted by `shifted_verifier_circuit`: one lincheck
row, then two blocks of 128 ring-scale rows, then two terminal ring-claim
rows.  It also binds every ring variable to the literal suffix of the flat
754--760-element mask cursor.

The remaining semantic premises are the ordinary completeness identities of
the underlying honest FLOCK transcript: its lincheck equation, the definition
of each blinded ring slice, and evaluation of the two terminal claims.
-/

namespace VeiledFlock.ProductionShiftedRows

set_option maxHeartbeats 500000

open VeiledFlock.BinaryPolynomial
open VeiledFlock.ConcreteParameters
open VeiledFlock.ConcreteTranscript
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionMaskLayout
open VeiledFlock.ProductionShiftedCompiler
open VeiledFlock.RingScale
open VeiledFlock.ShiftedLinearCircuit

abbrev Masks (shape : BatchShape) :=
  ProductionMaskLayout.MaskIndex shape → GhashField
abbrev PiopVector (shape : BatchShape) :=
  ProductionMaskLayout.PiopIndex shape → GhashField
abbrev Slice := SliceIndex → GhashField
abbrev Claim := ProductionMaskLayout.ClaimIndex
abbrev Channel := ProductionMaskLayout.ChannelIndex
abbrev Side := Fin 3
abbrev OriginalRow := Fin shiftedLinearConstraints

noncomputable def ringSliceRestriction (shape : BatchShape)
    (claim : Claim) (channel : Channel) :
    Masks shape →ₗ[GhashField] Slice where
  toFun values coordinate :=
    values (ProductionMaskLayout.ringIndex shape claim channel coordinate)
  map_add' left right := rfl
  map_smul' scalar values := rfl

@[simp] theorem ringSliceRestriction_apply (shape : BatchShape)
    (claim : Claim) (channel : Channel) (values : Masks shape)
    (coordinate : SliceIndex) :
    ringSliceRestriction shape claim channel values coordinate =
      values (ProductionMaskLayout.ringIndex shape claim channel coordinate) :=
  rfl

/-- Completeness data selected by one already-visible Fiat--Shamir prefix.
The published masked values and row constants are fixed; changing the witness
changes the private mask vector so that each recovered value is unchanged. -/
structure Execution (shape : BatchShape) (W : Type*) where
  maskMessage : W → Masks shape

  multiplicationSecret : W →
    GhashField × GhashField × GhashField
  multiplicationValid : ∀ witness,
    (multiplicationSecret witness).1 *
        (multiplicationSecret witness).2.1 =
      (multiplicationSecret witness).2.2
  multiplicationFunctional : Side →
    Masks shape →ₗ[GhashField] GhashField
  multiplicationConstant : Side → GhashField
  multiplication_evaluation : ∀ witness side,
    multiplicationFunctional side (maskMessage witness) +
        multiplicationConstant side =
      ProductionShiftedCompiler.component
        (multiplicationSecret witness) side

  underlyingPiop : W → PiopVector shape
  maskedPiop : PiopVector shape
  piop_masking : ∀ witness,
    maskedPiop = publishVector (underlyingPiop witness)
      (piopRestriction shape (maskMessage witness))
  lincheckFunctional :
    PiopVector shape →ₗ[GhashField] GhashField
  lincheckConstant : GhashField
  lincheck_complete : ∀ witness,
    lincheckFunctional (underlyingPiop witness) + lincheckConstant = 0

  blindChallenge : GhashField
  witnessSlice : W → Claim → Slice
  blindSlice : W → Claim → Slice
  maskedWitnessSlice : Claim → Slice
  maskedBlindSlice : Claim → Slice
  witness_masking : ∀ witness claim,
    maskedWitnessSlice claim =
      publishVector (witnessSlice witness claim)
        (ringSliceRestriction shape claim 0 (maskMessage witness))
  blind_masking : ∀ witness claim,
    maskedBlindSlice claim =
      publishVector (blindSlice witness claim)
        (ringSliceRestriction shape claim 1 (maskMessage witness))
  qSlice : Claim → Slice
  qSlice_definition : ∀ witness claim,
    qSlice claim = witnessSlice witness claim +
      scaleSlices blindChallenge (blindSlice witness claim)

  claimFunctional : Claim → Slice →ₗ[GhashField] GhashField
  piopClaim : Claim → GhashField
  claim_evaluation : ∀ witness claim,
    piopClaim claim = claimFunctional claim (witnessSlice witness claim)

  constraintRlc : GhashField
  gammaFunctional :
    (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField

noncomputable def lincheckRow (shape : BatchShape)
    (execution : Execution shape W) :
    Masks shape →ₗ[GhashField] GhashField :=
  execution.lincheckFunctional.comp (piopRestriction shape)

noncomputable def lincheckRowConstant (shape : BatchShape)
    (execution : Execution shape W) : GhashField :=
  execution.lincheckFunctional execution.maskedPiop +
    execution.lincheckConstant

theorem lincheckRow_satisfied (shape : BatchShape)
    (execution : Execution shape W) (witness : W) :
    lincheckRow shape execution (execution.maskMessage witness) +
        lincheckRowConstant shape execution = 0 := by
  have h := affineConstraint_of_underlying execution.lincheckFunctional
    execution.lincheckConstant (execution.underlyingPiop witness)
    (piopRestriction shape (execution.maskMessage witness))
    (execution.lincheck_complete witness)
  rw [← execution.piop_masking witness] at h
  simp only [affineConstraint, recoverVector] at h
  simp only [lincheckRow, lincheckRowConstant, LinearMap.comp_apply]
  rw [map_add] at h
  linear_combination h

noncomputable def ringScaleRow (shape : BatchShape)
    (execution : Execution shape W) (claim : Claim)
    (coordinate : SliceIndex) :
    Masks shape →ₗ[GhashField] GhashField :=
  (LinearMap.proj coordinate).comp
      (ringSliceRestriction shape claim 0) +
    (LinearMap.proj coordinate).comp
      ((scaleSlices execution.blindChallenge).comp
        (ringSliceRestriction shape claim 1))

noncomputable def ringScaleRowConstant {shape : BatchShape}
    (execution : Execution shape W)
    (claim : Claim) (coordinate : SliceIndex) : GhashField :=
  execution.qSlice claim coordinate +
    execution.maskedWitnessSlice claim coordinate +
    scaleSlices execution.blindChallenge
      (execution.maskedBlindSlice claim) coordinate

theorem ringScaleRow_satisfied (shape : BatchShape)
    (execution : Execution shape W) (witness : W) (claim : Claim)
    (coordinate : SliceIndex) :
    ringScaleRow shape execution claim coordinate
          (execution.maskMessage witness) +
        ringScaleRowConstant execution claim coordinate = 0 := by
  have h := ringScaleConstraint_of_definition
    (scaleSlices execution.blindChallenge)
    (execution.witnessSlice witness claim)
    (execution.blindSlice witness claim)
    (ringSliceRestriction shape claim 0 (execution.maskMessage witness))
    (ringSliceRestriction shape claim 1 (execution.maskMessage witness))
    coordinate
  rw [← execution.qSlice_definition witness claim] at h
  rw [← execution.witness_masking witness claim,
    ← execution.blind_masking witness claim] at h
  simp only [ringScaleConstraint, recoverVector, Pi.add_apply] at h
  simp only [ringScaleRow, ringScaleRowConstant, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_add] at h
  simp only [Pi.add_apply] at h
  linear_combination h

noncomputable def ringClaimRow (shape : BatchShape)
    (execution : Execution shape W) (claim : Claim) :
    Masks shape →ₗ[GhashField] GhashField :=
  (execution.claimFunctional claim).comp
    (ringSliceRestriction shape claim 0)

noncomputable def ringClaimRowConstant {shape : BatchShape}
    (execution : Execution shape W)
    (claim : Claim) : GhashField :=
  execution.piopClaim claim +
    execution.claimFunctional claim (execution.maskedWitnessSlice claim)

theorem ringClaimRow_satisfied (shape : BatchShape)
    (execution : Execution shape W) (witness : W) (claim : Claim) :
    ringClaimRow shape execution claim (execution.maskMessage witness) +
        ringClaimRowConstant execution claim = 0 := by
  have h := ringClaimConstraint_of_evaluation
    (execution.claimFunctional claim)
    (execution.witnessSlice witness claim)
    (ringSliceRestriction shape claim 0 (execution.maskMessage witness))
  rw [← execution.claim_evaluation witness claim] at h
  rw [← execution.witness_masking witness claim] at h
  simp only [ringClaimConstraint, recoverVector] at h
  simp only [ringClaimRow, ringClaimRowConstant, LinearMap.comp_apply]
  rw [map_add] at h
  linear_combination h

abbrev RingScaleRow := Fin (ringClaimCount * ringWidth)

def ringScaleCoordinates (row : RingScaleRow) : Claim × SliceIndex :=
  finProdFinEquiv.symm row

abbrev StructuredRow := (Fin 1 ⊕ RingScaleRow) ⊕ Claim

theorem structuredRowCount :
    (1 + ringClaimCount * ringWidth) + ringClaimCount =
      shiftedLinearConstraints := by
  decide

/-- Order-preserving equivalence from the three literal builder blocks to
the flat `Fin 259` row number used by Rust's power batching. -/
def structuredRowEquiv : StructuredRow ≃ OriginalRow :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl Claim)).trans
    finSumFinEquiv).trans (finCongr structuredRowCount)

noncomputable def structuredRowFunctional (shape : BatchShape)
    (execution : Execution shape W) :
    StructuredRow → Masks shape →ₗ[GhashField] GhashField
  | Sum.inl (Sum.inl _) => lincheckRow shape execution
  | Sum.inl (Sum.inr row) =>
      ringScaleRow shape execution (ringScaleCoordinates row).1
        (ringScaleCoordinates row).2
  | Sum.inr claim => ringClaimRow shape execution claim

noncomputable def structuredRowConstant (shape : BatchShape)
    (execution : Execution shape W) : StructuredRow → GhashField
  | Sum.inl (Sum.inl _) => lincheckRowConstant shape execution
  | Sum.inl (Sum.inr row) =>
      ringScaleRowConstant execution (ringScaleCoordinates row).1
        (ringScaleCoordinates row).2
  | Sum.inr claim => ringClaimRowConstant execution claim

/-- Literal builder order: lincheck; claim-0 scale coordinates 0--127;
claim-1 scale coordinates 0--127; then the two terminal claim rows. -/
noncomputable def originalRows (shape : BatchShape)
    (execution : Execution shape W) :
    OriginalRow → Masks shape →ₗ[GhashField] GhashField :=
  fun row => structuredRowFunctional shape execution
    (structuredRowEquiv.symm row)

noncomputable def originalConstants (shape : BatchShape)
    (execution : Execution shape W) : OriginalRow → GhashField :=
  fun row => structuredRowConstant shape execution
    (structuredRowEquiv.symm row)

theorem originalRows_satisfied (shape : BatchShape)
    (execution : Execution shape W) (witness : W) (row : OriginalRow) :
    originalRows shape execution row (execution.maskMessage witness) +
        originalConstants shape execution row = 0 := by
  generalize hslot : structuredRowEquiv.symm row = slot
  rcases slot with (lincheck | scale) | claim
  · simpa [originalRows, originalConstants, structuredRowFunctional,
      structuredRowConstant, hslot] using
      lincheckRow_satisfied shape execution witness
  · simpa [originalRows, originalConstants, structuredRowFunctional,
      structuredRowConstant, hslot] using
      ringScaleRow_satisfied shape execution witness
        (ringScaleCoordinates scale).1 (ringScaleCoordinates scale).2
  · simpa [originalRows, originalConstants, structuredRowFunctional,
      structuredRowConstant, hslot] using
      ringClaimRow_satisfied shape execution witness claim

/-- The abstract compiler certificate is now derived from the literal
mask-cursor and the three honest FLOCK completeness identities. -/
noncomputable def toShiftedExecution (shape : BatchShape)
    (execution : Execution shape W) :
    ProductionShiftedCompiler.ShiftedExecution shape W where
  maskMessage := execution.maskMessage
  multiplicationSecret := execution.multiplicationSecret
  multiplicationValid := execution.multiplicationValid
  multiplicationFunctional := execution.multiplicationFunctional
  multiplicationConstant := execution.multiplicationConstant
  multiplication_evaluation := execution.multiplication_evaluation
  originalRows := originalRows shape execution
  originalConstants := originalConstants shape execution
  original_satisfied := originalRows_satisfied shape execution
  constraintRlc := execution.constraintRlc
  gammaFunctional := execution.gammaFunctional

end VeiledFlock.ProductionShiftedRows

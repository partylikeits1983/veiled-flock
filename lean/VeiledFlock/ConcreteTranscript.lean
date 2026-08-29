import VeiledFlock.ConcreteParameters
import VeiledFlock.AdaptiveOneTimePad
import VeiledFlock.OneTimePad

/-!
# Registered shifted-verifier transcript

The production `MaskingChallenger`, `mask_proofs`, and `mask_ring_claims`
consume one independent field mask for every private coordinate later supplied
to the shifted verifier circuit.  This module specializes the coordinate-wise
one-time-pad theorem to each registered batch shape and records the exact
circuit inventory checked by `ShiftedCircuitCertificate::validate`.
-/

namespace VeiledFlock.ConcreteTranscript

open VeiledFlock.ConcreteParameters

variable {F W : Type*}
variable [AddCommGroup F] [Fintype F] [DecidableEq F]

abbrev Coordinate (shape : BatchShape) := Fin (expectedMasks shape)
abbrev Masks (shape : BatchShape) := Coordinate shape → F
abbrev Visible (shape : BatchShape) := Coordinate shape → F

/-- The exact vector serialized into the masked PIOP and two ring claims. -/
def maskedTranscript (shape : BatchShape)
    (secret : W → Visible (F := F) shape)
    (witness : W) (masks : Masks (F := F) shape) :
    Visible (F := F) shape :=
  masks + secret witness

/-- Every registered shifted-verifier transcript is perfectly witness
independent before it is committed by VEIL. -/
theorem maskedTranscript_zeroKnowledge (shape : BatchShape)
    (secret : W → Visible (F := F) shape) (left right : W) :
    (PMF.uniformOfFintype (Masks (F := F) shape)).map
        (maskedTranscript shape secret left) =
      (PMF.uniformOfFintype (Masks (F := F) shape)).map
        (maskedTranscript shape secret right) := by
  change
    (PMF.uniformOfFintype (Coordinate shape → F)).map
        (fun masks => masks + secret left) =
      (PMF.uniformOfFintype (Coordinate shape → F)).map
        (fun masks => masks + secret right)
  simpa [VeiledFlock.OneTimePad.identityMask] using
    (VeiledFlock.OneTimePad.maskedVector_witness_independent
      (I := Coordinate shape) secret left right)

/-- Private inputs checked by the production shifted-circuit certificate. -/
def shiftedPrivateInputs (shape : BatchShape) : ℕ := observedCount shape

def shiftedMultiplications : ℕ := 1
def shiftedLincheckConstraints : ℕ := 1
def shiftedRingScaleConstraints : ℕ := ringClaimCount * ringWidth
def shiftedRingClaimConstraints : ℕ := ringClaimCount

def shiftedLinearConstraints : ℕ :=
  shiftedLincheckConstraints + shiftedRingScaleConstraints +
    shiftedRingClaimConstraints

theorem shiftedPrivateInputs_eq_masks (shape : BatchShape) :
    shiftedPrivateInputs shape = expectedMasks shape := by
  exact observedCount_eq_expectedMasks shape

theorem shiftedLinearConstraints_eq : shiftedLinearConstraints = 259 := by
  decide

theorem shiftedMultiplications_eq : shiftedMultiplications = 1 := rfl

/-- Closed, exhaustive inventory for every full-ZK registered shape. -/
theorem registeredShiftedInventory (shape : BatchShape) :
    shiftedPrivateInputs shape = expectedMasks shape ∧
      shiftedMultiplications = 1 ∧ shiftedLinearConstraints = 259 := by
  exact ⟨shiftedPrivateInputs_eq_masks shape,
    shiftedMultiplications_eq, shiftedLinearConstraints_eq⟩

section Adaptive

variable {Rest FullView : Type*}

/-- A scalar-by-scalar causal model of the exact mask cursor consumed by the
Rust `MaskingChallenger`, `mask_proofs`, and `mask_ring_claims` path.  The
unmasked value may depend on the complete visible prefix and on arbitrary
fixed external state (including the random-oracle table). -/
abbrev CausalSecret (shape : BatchShape) :=
  Rest → W → ∀ round : ℕ, (Fin round → F) → F

private def liftCausalSecret (shape : BatchShape)
    (secret : CausalSecret (F := F) (W := W) (Rest := Rest) shape)
    (rest : Rest) :
    AdaptiveOneTimePad.Secret (F := F) (I := Unit) (W := W) :=
  fun witness round history _ =>
    secret rest witness round (fun site => history site ())

/-- A flat scalar tape is exactly a sequence of one-coordinate adaptive
messages.  This is exported for the implementation refinement. -/
def scalarMaskEquiv (count : ℕ) :
    (Fin count → F) ≃
      AdaptiveOneTimePad.Masks (F := F) (I := Unit) count where
  toFun masks := fun site _ => masks site
  invFun masks := fun site => masks site ()
  left_inv _ := rfl
  right_inv masks := by
    funext site unit
    cases unit
    rfl

/-- Visible scalar coordinates in exact mask-cursor order. -/
def adaptiveMaskedTranscript (shape : BatchShape)
    (secret : CausalSecret (F := F) (W := W) (Rest := Rest) shape)
    (rest : Rest) (witness : W) (masks : Fin (expectedMasks shape) → F) :
    Fin (expectedMasks shape) → F :=
  fun site =>
    AdaptiveOneTimePad.run (liftCausalSecret shape secret rest) witness
      (expectedMasks shape) (scalarMaskEquiv (expectedMasks shape) masks) site ()

/-- Explicit translation of the production scalar-mask tape between two
witnesses while preserving the entire adaptive visible transcript. -/
def adaptiveMaskCoinEquiv (shape : BatchShape)
    (secret : CausalSecret (F := F) (W := W) (Rest := Rest) shape)
    (rest : Rest) (left right : W) :
    (Fin (expectedMasks shape) → F) ≃
      (Fin (expectedMasks shape) → F) :=
  (scalarMaskEquiv (F := F) (expectedMasks shape)).trans
    ((AdaptiveOneTimePad.witnessCoinEquiv
      (liftCausalSecret shape secret rest) left right
      (expectedMasks shape)).trans
        (scalarMaskEquiv (F := F) (expectedMasks shape)).symm)

theorem adaptiveMaskedTranscript_transport (shape : BatchShape)
    (secret : CausalSecret (F := F) (W := W) (Rest := Rest) shape)
    (rest : Rest) (left right : W)
    (masks : Fin (expectedMasks shape) → F) :
    adaptiveMaskedTranscript shape secret rest right
        (adaptiveMaskCoinEquiv shape secret rest left right masks) =
      adaptiveMaskedTranscript shape secret rest left masks := by
  funext site
  exact congrFun
    (congrFun
      (AdaptiveOneTimePad.run_witnessCoinEquiv
        (liftCausalSecret shape secret rest) left right
        (expectedMasks shape)
        (scalarMaskEquiv (expectedMasks shape) masks)) site) ()

/-- Registered end-to-end masking theorem for all 754--760 production mask
coordinates.  Challenges may be derived adaptively from the unchanged oracle
in `Rest`, and arbitrary post-processing of the complete visible transcript
is covered. -/
theorem registeredAdaptiveMasking_zeroKnowledge
    [Fintype Rest] [Nonempty Rest]
    (shape : BatchShape)
    (secret : CausalSecret (F := F) (W := W) (Rest := Rest) shape)
    (left right : W)
    (continueWith : Rest → (Fin (expectedMasks shape) → F) → FullView) :
    (PMF.uniformOfFintype
      ((Fin (expectedMasks shape) → F) × Rest)).map
        (fun coins => continueWith coins.2
          (adaptiveMaskedTranscript shape secret coins.2 left coins.1)) =
      (PMF.uniformOfFintype
        ((Fin (expectedMasks shape) → F) × Rest)).map
          (fun coins => continueWith coins.2
            (adaptiveMaskedTranscript shape secret coins.2 right coins.1)) := by
  let split :
      ((Fin (expectedMasks shape) → F) × Rest) ≃
        ((Fin (expectedMasks shape) → F) × Rest) := Equiv.refl _
  let equiv := VeiledFlock.Probability.fiberwiseEquiv split
    (fun rest => adaptiveMaskCoinEquiv shape secret rest left right)
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv equiv
  intro coins
  simp only [equiv, split]
  exact congrArg (continueWith coins.2)
    (adaptiveMaskedTranscript_transport shape secret coins.2 left right coins.1).symm

end Adaptive

end VeiledFlock.ConcreteTranscript

import VeiledFlock.ConcreteTranscript
import VeiledFlock.ShiftedZerocheckCircuit

/-!
# Shifted verifier linear constraints

After the one zerocheck multiplication gate, every remaining constraint
emitted by `shifted_verifier_circuit` is linear in the private VEIL masks.
These lemmas prove the exact mask-cancellation argument for the lincheck
identity, the 256 ring-scale coordinates, and the two ring-claim identities.
-/

namespace VeiledFlock.ShiftedLinearCircuit

open VeiledFlock.BinaryPolynomial
open VeiledFlock.ShiftedZerocheckCircuit

variable {F I : Type*} [Field F] [CharP F 2]

def publishVector (value mask : I → F) : I → F := value + mask

def recoverVector (masked privateMask : I → F) : I → F :=
  masked + privateMask

@[simp]
theorem recoverVector_publish (value mask : I → F) :
    recoverVector (publishVector value mask) mask = value := by
  funext index
  exact recover_publish (value index) (mask index)

/-- One arbitrary affine-linear constraint as evaluated by the shifted
verifier circuit. -/
def affineConstraint (functional : (I → F) →ₗ[F] F) (constant : F)
    (masked privateMask : I → F) : Prop :=
  functional (recoverVector masked privateMask) + constant = 0

theorem affineConstraint_of_underlying
    (functional : (I → F) →ₗ[F] F) (constant : F)
    (value mask : I → F)
    (hsatisfied : functional value + constant = 0) :
    affineConstraint functional constant (publishVector value mask) mask := by
  simpa [affineConstraint]

/-- A ring-scale row has the exact form `q + witness + scale(blind) = 0`.
`scale` abstracts one row of the fixed 128-by-128 binary multiplication
matrix constructed by `scale_ring_expressions`. -/
def ringScaleConstraint (scale : (I → F) →ₗ[F] (I → F))
    (q : I → F)
    (maskedWitness witnessMask maskedBlind blindMask : I → F)
    (coordinate : I) : Prop :=
  q coordinate + recoverVector maskedWitness witnessMask coordinate +
      scale (recoverVector maskedBlind blindMask) coordinate = 0

theorem ringScaleConstraint_of_definition
    (scale : (I → F) →ₗ[F] (I → F))
    (witness blind witnessMask blindMask : I → F) (coordinate : I) :
    ringScaleConstraint scale (witness + scale blind)
      (publishVector witness witnessMask) witnessMask
      (publishVector blind blindMask) blindMask coordinate := by
  simp only [ringScaleConstraint, recoverVector_publish, Pi.add_apply,
    add_assoc]
  have hw := add_self_eq_zero_charTwo (witness coordinate)
  have hb := add_self_eq_zero_charTwo (scale blind coordinate)
  linear_combination hw + hb

/-- The two terminal ring-link rows assert that a public PIOP evaluation and
the corresponding recovered ring-switch slice evaluate to the same value. -/
def ringClaimConstraint (functional : (I → F) →ₗ[F] F)
    (publicValue : F) (maskedWitness witnessMask : I → F) : Prop :=
  publicValue + functional (recoverVector maskedWitness witnessMask) = 0

theorem ringClaimConstraint_of_evaluation
    (functional : (I → F) →ₗ[F] F)
    (witness mask : I → F) :
    ringClaimConstraint functional (functional witness)
      (publishVector witness mask) mask := by
  simp [ringClaimConstraint, add_self_eq_zero_charTwo]

/-- The complete production linear inventory: one lincheck row, two sets of
128 ring-scale rows, and two terminal ring-claim rows. -/
def linearConstraintCount : ℕ := 1 + 2 * 128 + 2

theorem linearConstraintCount_eq_production :
    linearConstraintCount =
      VeiledFlock.ConcreteTranscript.shiftedLinearConstraints := by
  decide

theorem completeShiftedConstraintInventory :
    VeiledFlock.ConcreteTranscript.shiftedMultiplications = 1 ∧
      linearConstraintCount = 259 := by
  decide

end VeiledFlock.ShiftedLinearCircuit

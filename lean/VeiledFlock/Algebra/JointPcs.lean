import Mathlib
import VeiledFlock.Core.Probability

/-!
# Joint shielded-PCS reparameterization

The shielded opening folds a message `message` with a full random blinder
`blind` using a nonzero challenge `c`.  A change `delta` in the witness half
can be cancelled by translating the blinder.  Public linear functionals are
preserved whenever `delta` lies in their kernel.  In characteristic two the
subtraction in the generic formula is the addition used by the Rust code.
-/

namespace VeiledFlock.JointPcs

variable {F I : Type*} [Field F]

def folded (c : F) (message blind : I → F) : I → F := message + c • blind

def translateBlind (c : F) (delta blind : I → F) : I → F :=
  blind - c⁻¹ • delta

/-- The complete folded vector is invariant under the affine mask translation. -/
theorem folded_translate (c : F) (hc : c ≠ 0) (message blind delta : I → F) :
    folded c (message + delta) (translateBlind c delta blind) =
      folded c message blind := by
  ext i
  simp only [folded, translateBlind, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- A public functional's exposed blinder value is invariant under the same
translation when the witness difference is in its kernel. -/
theorem functional_translate (c : F) (blind delta : I → F)
    (functional : (I → F) →ₗ[F] F) (hkernel : functional delta = 0) :
    functional (translateBlind c delta blind) = functional blind := by
  simp [translateBlind, map_sub, map_smul, hkernel]

/-- Over the implementation field, subtraction and addition coincide, so the
generic translation is byte-for-byte the `blind + c⁻¹ * delta` formula used
by VEIL-FLOCK. -/
theorem translateBlind_charTwo [CharP F 2] (c : F) (delta blind : I → F) :
    translateBlind c delta blind = blind + c⁻¹ • delta := by
  ext i
  simp only [translateBlind, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  exact CharTwo.sub_eq_add _ _

theorem folded_translate_charTwo [CharP F 2] (c : F) (hc : c ≠ 0)
    (message blind delta : I → F) :
    folded c (message + delta) (blind + c⁻¹ • delta) =
      folded c message blind := by
  rw [← translateBlind_charTwo c delta blind]
  exact folded_translate c hc message blind delta

/-- Folding with a nonzero blinding challenge is a bijection from the PCS
blinder to the opened combined message. -/
noncomputable def foldedEquiv (c : F) (hc : c ≠ 0) (message : I → F) :
    (I → F) ≃ (I → F) where
  toFun := folded c message
  invFun := fun combined => c⁻¹ • (combined - message)
  left_inv := fun blind => by
    ext index
    simp only [folded, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  right_inv := fun combined => by
    ext index
    simp only [folded, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring

/-- Real PCS-visible pair: the combined message and the exposed public linear
functional of the blinder. -/
def realOpeningView (c : F) (functional : (I → F) →ₗ[F] F)
    (message blind : I → F) : (I → F) × F :=
  (folded c message blind, functional blind)

/-- Public-input-only PCS simulator.  It samples the combined message
uniformly and reconstructs the unique exposed blinder functional from the
public functional of the witness message. -/
def simulatedOpeningView (c : F) (functional : (I → F) →ₗ[F] F)
    (publicMessageValue : F) (combined : I → F) : (I → F) × F :=
  (combined, c⁻¹ * (functional combined - publicMessageValue))

theorem realOpeningView_foldedEquiv (c : F) (hc : c ≠ 0)
    (functional : (I → F) →ₗ[F] F) (message blind : I → F) :
    realOpeningView c functional message blind =
      simulatedOpeningView c functional (functional message)
        (foldedEquiv c hc message blind) := by
  apply Prod.ext
  · rfl
  · change functional blind =
      c⁻¹ * (functional (message + c • blind) - functional message)
    rw [map_add, map_smul]
    field_simp
    ring

/-- Exact explicit PCS simulation. -/
theorem openingSimulator_exact [Fintype F] [DecidableEq F]
    [Fintype I] [Fintype (I → F)]
    (c : F) (hc : c ≠ 0) (functional : (I → F) →ₗ[F] F)
    (message : I → F) :
    (PMF.uniformOfFintype (I → F)).map
        (realOpeningView c functional message) =
      (PMF.uniformOfFintype (I → F)).map
        (simulatedOpeningView c functional (functional message)) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (foldedEquiv c hc message)
  exact realOpeningView_foldedEquiv c hc functional message

end VeiledFlock.JointPcs

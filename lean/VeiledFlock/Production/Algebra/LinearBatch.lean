import VeiledFlock.Production.Algebra.ConstraintCompiler
import VeiledFlock.Algebra.ShiftedLinearCircuit

/-!
# Exact affine batching used by `combine_linear_constraints`

Rust turns every affine constraint `L(x) + c = 0` into one dot-product
functional by weighting row `i` with `rho^i`.  In characteristic two, a
satisfied row has `L(x) = c`, so the batched dot product equals the weighted
sum of the constants.  The last three constants contain the published
Hadamard claims; keeping that dependency explicit is essential for the
dummy-coin transport used by the zero-knowledge proof.
-/

namespace VeiledFlock.ProductionLinearBatch

open VeiledFlock.BinaryPolynomial
open VeiledFlock.ConcreteParameters
open VeiledFlock.ConcreteTranscript
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionConstraintCompiler
open VeiledFlock.ProductionMultiplicationPadding
open VeiledFlock.ProductionProductMask
open VeiledFlock.ProductionVeilLayer

/-- Original 259 shifted constraints plus `r + (r+1) + 1 = 0`. -/
def paddedLinearConstraints : ℕ := shiftedLinearConstraints + 1

/-- The padded rows followed by the three Hadamard-link rows. -/
def combinedLinearConstraints : ℕ := paddedLinearConstraints + 3

theorem paddedLinearConstraints_eq : paddedLinearConstraints = 260 := by
  decide

theorem combinedLinearConstraints_eq : combinedLinearConstraints = 263 := by
  decide

variable {F I : Type*} [Field F] [CharP F 2]

/-- The exact variable-coefficient part emitted for one affine row. -/
abbrev RowFunctional (I F : Type*) [Semiring F] [AddCommMonoid (I → F)]
    [Module F (I → F)] := (I → F) →ₗ[F] F

/-- Rust's Horner/power batching of all variable coefficients. -/
noncomputable def combinedFunctional {rowCount : ℕ}
    (rows : Fin rowCount → RowFunctional I F)
    (rho : F) : RowFunctional I F :=
  ∑ row, (rho ^ row.val) • rows row

/-- Rust's `expected` accumulator: the same powers applied to constants. -/
noncomputable def combinedTarget {rowCount : ℕ}
    (constants : Fin rowCount → F) (rho : F) : F :=
  ∑ row, rho ^ row.val * constants row

theorem value_eq_constant_of_satisfied (functional : RowFunctional I F)
    (constant : F) (message : I → F)
    (hsatisfied : functional message + constant = 0) :
    functional message = constant := by
  have hconstant : constant + constant = 0 :=
    add_self_eq_zero_charTwo constant
  rw [eq_neg_of_add_eq_zero_left hsatisfied]
  exact neg_eq_of_add_eq_zero_left hconstant

/-- Kernel proof of `combine_linear_constraints`: satisfaction of every
input row implies equality of the one combined dot-product claim. -/
theorem combinedFunctional_eq_target
    {rowCount : ℕ} (rows : Fin rowCount → RowFunctional I F)
    (constants : Fin rowCount → F)
    (rho : F) (message : I → F)
    (hsatisfied : ∀ row, rows row message + constants row = 0) :
    combinedFunctional rows rho message = combinedTarget constants rho := by
  classical
  simp only [combinedFunctional, combinedTarget, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  rw [value_eq_constant_of_satisfied (rows row) (constants row) message
    (hsatisfied row)]

/-! ## Production compiler interface -/

/-- A satisfied execution of the exact 263-row production compiler.

The coefficient maps are fixed by the already-visible shifted circuit and
Fiat--Shamir challenges.  Constants may depend on the public statement and
the three published Hadamard claims, exactly as in Rust. -/
structure Execution (shape : BatchShape) (W Public : Type*)
    (statement : W → Public) (multiplicationAlpha : GhashField) where
  multiplicationSecret : W → GhashField × GhashField × GhashField
  triple : W → DummyCoins → ValidTriple
  triple_a_rows : ∀ witness dummy index,
    (triple witness dummy).a.1.eval (multiplicationPoint index) =
      rowA (multiplicationSecret witness) dummy index
  triple_b_rows : ∀ witness dummy index,
    (triple witness dummy).b.1.eval (multiplicationPoint index) =
      rowB (multiplicationSecret witness) dummy index
  triple_c_rows : ∀ witness dummy index,
    (triple witness dummy).c.1.eval (multiplicationPoint index) =
      rowC (multiplicationSecret witness) dummy index
  linearRows : Fin combinedLinearConstraints →
    (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField] GhashField
  rowConstants : Public → (GhashField × GhashField × GhashField) →
    Fin combinedLinearConstraints → GhashField
  linearMessage : W → DummyCoins →
    Fin (linearLogicalLength shape) → GhashField
  rows_satisfied : ∀ witness dummy row,
    linearRows row (linearMessage witness dummy) +
      rowConstants (statement witness)
        (visibleClaims multiplicationAlpha multiplicationSecret witness dummy)
        row = 0
  constraintRlc : GhashField
  gammaFunctional :
    (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField

/-- Derive the higher-level VEIL semantics from literal row satisfaction;
there is no separate batched-linear acceptance assumption. -/
noncomputable def Execution.toSemantics {shape : BatchShape}
    {W Public : Type*} {statement : W → Public}
    {multiplicationAlpha : GhashField}
    (execution : Execution shape W Public statement multiplicationAlpha) :
    Semantics shape W Public statement multiplicationAlpha where
  multiplicationSecret := execution.multiplicationSecret
  triple := execution.triple
  triple_a_rows := execution.triple_a_rows
  triple_b_rows := execution.triple_b_rows
  triple_c_rows := execution.triple_c_rows
  linearFunctional :=
    combinedFunctional execution.linearRows execution.constraintRlc
  linearMessage := fun witness dummy _ =>
    execution.linearMessage witness dummy
  publicLinearTarget := fun publicValue claims =>
    combinedTarget (execution.rowConstants publicValue claims)
      execution.constraintRlc
  linear_accepted witness dummy _ := by
    exact combinedFunctional_eq_target execution.linearRows
      (execution.rowConstants (statement witness)
        (visibleClaims multiplicationAlpha execution.multiplicationSecret
          witness dummy))
      execution.constraintRlc (execution.linearMessage witness dummy)
      (execution.rows_satisfied witness dummy)
  gammaFunctional := execution.gammaFunctional

end VeiledFlock.ProductionLinearBatch

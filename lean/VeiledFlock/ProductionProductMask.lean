import VeiledFlock.AdditiveReedSolomon
import VeiledFlock.BinaryPolynomial
import VeiledFlock.ProductMask
import VeiledFlock.ProductionCodeDomains

/-!
# Production Hadamard square-code mask

The fifth Hadamard commitment column masks the square-code defect polynomial
`A*B+C`.  Its coefficients are uniform, and a nonzero challenge translates
them by the defect difference.  Because both honest shifted-circuit witnesses
satisfy all three multiplication rows, that difference evaluates to zero on
the exact coordinates used by `gamma`; hence the translation preserves both
the revealed product word (`phi`) and `gamma`.
-/

namespace VeiledFlock.ProductionProductMask

open Function
open Polynomial
open VeiledFlock.AdditiveReedSolomon
open VeiledFlock.BinaryPolynomial
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductMask
open VeiledFlock.ProductionCodeDomains

def baseCapacity : ℕ := 256
def squareDimension : ℕ := 2 * baseCapacity - 1

theorem squareDimension_eq : squareDimension = 511 := by decide

noncomputable abbrev BasePolynomial := degreeLT GhashField baseCapacity
abbrev SquarePolynomial := Fin squareDimension → GhashField

/-- Exact first three base-domain points occupied by the one original and two
VEIL padding multiplication rows. -/
noncomputable def multiplicationPoint (index : Fin paddedMultiplications) :
    GhashField :=
  basePoint hadamardLogicalLength veilQueryCount (Sum.inl index)

/-- The 511 independent square-code coordinates.  This evaluation vector is
linearly equivalent to the Rust square-code coefficient/intermediate form. -/
noncomputable def squarePoint (index : Fin squareDimension) : GhashField :=
  basePoint squareDimension 0 (Sum.inl index)

theorem squarePoint_injective : Function.Injective squarePoint := by
  intro left right heq
  have hsum :
      (Sum.inl left : Fin squareDimension ⊕ Fin 0) = Sum.inl right :=
    (basePoint_injective squareDimension 0 9 (by decide) (by decide)) (by
      simpa only [squarePoint] using heq)
  exact Sum.inl_injective hsum

set_option maxRecDepth 8192

/-- Mathematical square-code coefficient/evaluation equivalence at the exact
511-dimensional production bound. -/
noncomputable def squareEvaluationEquiv :
    degreeLT GhashField squareDimension ≃ₗ[GhashField] SquarePolynomial := by
  change degreeLT GhashField (Fintype.card (Fin squareDimension)) ≃ₗ[GhashField]
    (Fin squareDimension → GhashField)
  exact evaluationEquiv squarePoint squarePoint_injective

noncomputable def defectPolynomial (a b c : BasePolynomial) :
    SquarePolynomial :=
  fun index => (a.1 * b.1 + c.1).eval (squarePoint index)

/-- Restriction of a square-code polynomial to the three multiplication data
coordinates read by production's `gamma` computation. -/
noncomputable def multiplicationRestriction :
    SquarePolynomial →ₗ[GhashField]
      (Fin paddedMultiplications → GhashField) where
  toFun polynomial index := polynomial
    ⟨index.val, lt_trans index.isLt (by decide)⟩
  map_add' left right := rfl
  map_smul' scalar polynomial := rfl

/-- A valid multiplication triple has zero defect at all three data rows. -/
theorem multiplicationRestriction_defect_eq_zero
    (a b c : BasePolynomial)
    (hvalid : ∀ index : Fin paddedMultiplications,
      a.1.eval (multiplicationPoint index) *
          b.1.eval (multiplicationPoint index) =
        c.1.eval (multiplicationPoint index)) :
    multiplicationRestriction (defectPolynomial a b c) = 0 := by
  funext index
  change (a.1 * b.1 + c.1).eval
    (squarePoint ⟨index.val, lt_trans index.isLt (by decide)⟩) = 0
  have hpoint :
      squarePoint ⟨index.val, lt_trans index.isLt (by decide)⟩ =
        multiplicationPoint index := rfl
  rw [hpoint]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hvalid index]
  exact add_self_eq_zero_charTwo _

structure ValidTriple where
  a : BasePolynomial
  b : BasePolynomial
  c : BasePolynomial
  valid : ∀ index : Fin paddedMultiplications,
    a.1.eval (multiplicationPoint index) *
        b.1.eval (multiplicationPoint index) =
      c.1.eval (multiplicationPoint index)

noncomputable def ValidTriple.defect (triple : ValidTriple) :
    SquarePolynomial :=
  defectPolynomial triple.a triple.b triple.c

theorem valid_defect_difference_restricts_to_zero
    (left right : ValidTriple) :
    multiplicationRestriction (right.defect - left.defect) = 0 := by
  change multiplicationRestriction
      (defectPolynomial right.a right.b right.c -
        defectPolynomial left.a left.b left.c) = 0
  rw [map_sub, multiplicationRestriction_defect_eq_zero _ _ _ right.valid,
    multiplicationRestriction_defect_eq_zero _ _ _ left.valid, sub_zero]

/-- Exact production product-mask theorem.  The `gammaFunctional` includes the
sampled evaluation-point powers; it may be arbitrary because the translated
defect difference is identically zero on the three coordinates it reads. -/
theorem product_mask_witness_independent
    (coefficient : GhashField) (hcoefficient : coefficient ≠ 0)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (left right : ValidTriple) :
    (PMF.uniformOfFintype SquarePolynomial).map
        (ProductMask.view coefficient multiplicationRestriction
          gammaFunctional ValidTriple.defect left) =
      (PMF.uniformOfFintype SquarePolynomial).map
        (ProductMask.view coefficient multiplicationRestriction
          gammaFunctional ValidTriple.defect right) := by
  exact ProductMask.witness_independent coefficient hcoefficient
    multiplicationRestriction gammaFunctional ValidTriple.defect left right
    (valid_defect_difference_restricts_to_zero left right)

end VeiledFlock.ProductionProductMask

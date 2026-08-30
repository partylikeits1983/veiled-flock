import VeiledFlock.Production.Algebra.PaddedCommitments
import VeiledFlock.Production.Algebra.ProductMask

/-!
# Correlated production Hadamard commitment

The operand polynomials are determined jointly by their three logical values,
their 160 random padding rows, and the 93 fixed zero tail values inserted by
`AdditiveRsCode::encode`.  Consequently the product defect used to construct
`phi` depends on the same padding coins as the operand Merkle columns.  This
file keeps that correlation explicit and translates the square-code mask only
after translating the operand padding.
-/

namespace VeiledFlock.ProductionCorrelatedHadamard

set_option maxHeartbeats 500000
set_option maxRecDepth 8192

open Function
open VeiledFlock.AdditiveReedSolomon
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.PaddedHornerCommitment
open VeiledFlock.ProductMask
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionPaddedCommitments
open VeiledFlock.ProductionProductMask
open VeiledFlock.ReedSolomonDecomposition

abbrev QueryIndex := Fin veilQueryCount
abbrev LogicalIndex := Fin hadamardLogicalLength
abbrev DataColumn := Fin 3
abbrev Padding :=
  PaddedHornerCommitment.Padding
    (F := GhashField) (DataColumn := DataColumn) (Row := QueryIndex)

/-- Padding belonging to one of the three operand columns. -/
def operandPadding (padding : Padding) (column : DataColumn) :
    QueryIndex → GhashField :=
  padding (Sum.inl column)

/-- The exact base-domain polynomial interpolated by Rust from
`[logical || random padding || zero tail]`. -/
noncomputable def operandPolynomial
    (data : LogicalIndex → GhashField)
    (padding : QueryIndex → GhashField) : BasePolynomial := by
  let base := capacityBasePoint hadamardLogicalLength veilQueryCount 8
  have hbase := capacityBasePoint_injective hadamardLogicalLength
    veilQueryCount 8 hadamardMessageFits (by decide)
  let values :
      CapacityData hadamardLogicalLength veilQueryCount (2 ^ 8) ⊕
          QueryIndex → GhashField :=
    ReedSolomonDecomposition.fullValues
      (logicalDataValues hadamardLogicalLength veilQueryCount (2 ^ 8) data,
        padding)
  exact (evaluationEquiv base hbase).symm values

@[simp]
theorem operandPolynomial_eval_logical
    (data : LogicalIndex → GhashField)
    (padding : QueryIndex → GhashField) (index : LogicalIndex) :
    (operandPolynomial data padding).1.eval (multiplicationPoint index) =
      data index := by
  let base := capacityBasePoint hadamardLogicalLength veilQueryCount 8
  have hbase := capacityBasePoint_injective hadamardLogicalLength
    veilQueryCount 8 hadamardMessageFits (by decide)
  let values :
      CapacityData hadamardLogicalLength veilQueryCount (2 ^ 8) ⊕
          QueryIndex → GhashField :=
    ReedSolomonDecomposition.fullValues
      (logicalDataValues hadamardLogicalLength veilQueryCount (2 ^ 8) data,
        padding)
  have happly := congrFun ((evaluationEquiv base hbase).apply_symm_apply values)
    (Sum.inl (Sum.inl index))
  have hpoint : base (Sum.inl (Sum.inl index)) =
      multiplicationPoint index := by
    rfl
  change ((evaluationEquiv base hbase).symm values).1.eval
      (multiplicationPoint index) = data index
  rw [← hpoint]
  exact happly

/-- The three exact operand polynomials sharing the commitment's padding
matrix. -/
noncomputable def operandTriple
    (message : DataColumn → LogicalIndex → GhashField)
    (padding : Padding) : BasePolynomial × BasePolynomial × BasePolynomial :=
  (operandPolynomial (message 0) (operandPadding padding 0),
    operandPolynomial (message 1) (operandPadding padding 1),
    operandPolynomial (message 2) (operandPadding padding 2))

noncomputable def actualDefect
    (message : DataColumn → LogicalIndex → GhashField)
    (padding : Padding) : SquarePolynomial :=
  let triple := operandTriple message padding
  defectPolynomial triple.1 triple.2.1 triple.2.2

/-- Validity is required only at the three logical multiplication rows; the
random interpolation padding is intentionally unconstrained. -/
def RowsValid (message : DataColumn → LogicalIndex → GhashField) : Prop :=
  ∀ index, message 0 index * message 1 index = message 2 index

theorem actualDefect_restricts_to_zero
    (message : DataColumn → LogicalIndex → GhashField)
    (padding : Padding) (hvalid : RowsValid message) :
    multiplicationRestriction (actualDefect message padding) = 0 := by
  apply multiplicationRestriction_defect_eq_zero
  intro index
  simp only [actualDefect, operandTriple]
  rw [operandPolynomial_eval_logical, operandPolynomial_eval_logical,
    operandPolynomial_eval_logical]
  exact hvalid index

theorem actualDefect_difference_restricts_to_zero
    (left right : DataColumn → LogicalIndex → GhashField)
    (leftPadding rightPadding : Padding)
    (hleft : RowsValid left) (hright : RowsValid right) :
    multiplicationRestriction
        (actualDefect right rightPadding -
          actualDefect left leftPadding) = 0 := by
  rw [map_sub, actualDefect_restricts_to_zero right rightPadding hright,
    actualDefect_restricts_to_zero left leftPadding hleft, sub_zero]

abbrev CommitmentCoins :=
  PaddedHornerCommitment.Coins
    (F := GhashField) (Index := LogicalIndex)
    (DataColumn := DataColumn) (Row := QueryIndex)

abbrev Coins := CommitmentCoins × SquarePolynomial

abbrev CommitmentView :=
  PaddedHornerCommitment.CommitmentView
    (F := GhashField) (Index := LogicalIndex)
    (DataColumn := DataColumn) (Row := QueryIndex)

abbrev View := CommitmentView × (SquarePolynomial × GhashField)

/-- Complete correlated view: operand openings and `phi` use the same
padding matrix. -/
noncomputable def view {W : Type*}
    (positions : QueryIndex → Fin hadamardCodeLength)
    (hpositions : Injective positions)
    (rho productCoefficient : GhashField)
    (functional :
      (LogicalIndex → GhashField) →ₗ[GhashField] GhashField)
    (message : W → DataColumn → LogicalIndex → GhashField)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (witness : W) (coins : Coins) : View :=
  (PaddedHornerCommitment.commitmentView
      (hadamardPaddingQueryEquiv positions hpositions)
      (hadamardDataToQueries positions) (hadamardDataWeight rho)
      (hadamardMaskCoefficient rho) functional message witness coins.1,
    ProductMask.view productCoefficient multiplicationRestriction
      gammaFunctional
      (fun state : W × Padding => actualDefect (message state.1) state.2)
      (witness, coins.1.2) coins.2)

/-- First transport the operand commitment, then transport the square-code
mask in the resulting padding fiber. -/
noncomputable def coinEquiv {W : Type*}
    (positions : QueryIndex → Fin hadamardCodeLength)
    (hpositions : Injective positions)
    (rho productCoefficient : GhashField)
    (message : W → DataColumn → LogicalIndex → GhashField)
    (left right : W) : Coins ≃ Coins where
  toFun coins :=
    let rightCommitment := PaddedHornerCommitment.commitmentCoinEquiv
      (hadamardPaddingQueryEquiv positions hpositions)
      (hadamardDataToQueries positions) (hadamardDataWeight rho)
      (hadamardMaskCoefficient rho) message left right coins.1
    let defect := fun side : Bool => if side then
      actualDefect (message right) rightCommitment.2
    else actualDefect (message left) coins.1.2
    (rightCommitment,
      ProductMask.coinEquiv productCoefficient defect false true coins.2)
  invFun coins :=
    let commitmentEquiv := PaddedHornerCommitment.commitmentCoinEquiv
      (hadamardPaddingQueryEquiv positions hpositions)
      (hadamardDataToQueries positions) (hadamardDataWeight rho)
      (hadamardMaskCoefficient rho) message left right
    let leftCommitment := commitmentEquiv.symm coins.1
    let defect := fun side : Bool => if side then
      actualDefect (message right) coins.1.2
    else actualDefect (message left) leftCommitment.2
    (leftCommitment,
      (ProductMask.coinEquiv productCoefficient defect false true).symm
        coins.2)
  left_inv coins := by
    let commitmentEquiv := PaddedHornerCommitment.commitmentCoinEquiv
      (hadamardPaddingQueryEquiv positions hpositions)
      (hadamardDataToQueries positions) (hadamardDataWeight rho)
      (hadamardMaskCoefficient rho) message left right
    let rightCommitment := commitmentEquiv coins.1
    let defect := fun side : Bool => if side then
      actualDefect (message right) rightCommitment.2
    else actualDefect (message left) coins.1.2
    change
      (commitmentEquiv.symm rightCommitment,
        (ProductMask.coinEquiv productCoefficient
          (fun side : Bool => if side then
            actualDefect (message right) rightCommitment.2
          else actualDefect (message left)
            (commitmentEquiv.symm rightCommitment).2)
          false true).symm
          (ProductMask.coinEquiv productCoefficient defect false true
            coins.2)) = coins
    have hcommitment := commitmentEquiv.symm_apply_apply coins.1
    rw [hcommitment]
    exact Prod.ext rfl
      ((ProductMask.coinEquiv productCoefficient defect false true).symm_apply_apply
        coins.2)
  right_inv coins := by
    let commitmentEquiv := PaddedHornerCommitment.commitmentCoinEquiv
      (hadamardPaddingQueryEquiv positions hpositions)
      (hadamardDataToQueries positions) (hadamardDataWeight rho)
      (hadamardMaskCoefficient rho) message left right
    let leftCommitment := commitmentEquiv.symm coins.1
    let defect := fun side : Bool => if side then
      actualDefect (message right) coins.1.2
    else actualDefect (message left) leftCommitment.2
    change
      (commitmentEquiv leftCommitment,
        ProductMask.coinEquiv productCoefficient
          (fun side : Bool => if side then
            actualDefect (message right) (commitmentEquiv leftCommitment).2
          else actualDefect (message left) leftCommitment.2)
          false true
          ((ProductMask.coinEquiv productCoefficient defect false true).symm
            coins.2)) = coins
    have hcommitment := commitmentEquiv.apply_symm_apply coins.1
    rw [hcommitment]
    exact Prod.ext rfl
      ((ProductMask.coinEquiv productCoefficient defect false true).apply_symm_apply
        coins.2)

theorem view_coinEquiv {W : Type*}
    (positions : QueryIndex → Fin hadamardCodeLength)
    (hpositions : Injective positions)
    (rho productCoefficient : GhashField)
    (hrho : rho ≠ 0) (hproductCoefficient : productCoefficient ≠ 0)
    (functional :
      (LogicalIndex → GhashField) →ₗ[GhashField] GhashField)
    (message : W → DataColumn → LogicalIndex → GhashField)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (left right : W)
    (hfunctional : ∀ column,
      functional (message right column - message left column) = 0)
    (hleft : RowsValid (message left))
    (hright : RowsValid (message right))
    (coins : Coins) :
    view positions hpositions rho productCoefficient functional message
        gammaFunctional left coins =
      view positions hpositions rho productCoefficient functional message
        gammaFunctional right
        (coinEquiv positions hpositions rho productCoefficient message
          left right coins) := by
  let commitmentEquiv := PaddedHornerCommitment.commitmentCoinEquiv
    (hadamardPaddingQueryEquiv positions hpositions)
    (hadamardDataToQueries positions) (hadamardDataWeight rho)
    (hadamardMaskCoefficient rho) message left right
  let rightCommitment := commitmentEquiv coins.1
  apply Prod.ext
  · exact PaddedHornerCommitment.commitmentView_commitmentCoinEquiv
      (hadamardPaddingQueryEquiv positions hpositions)
      (hadamardDataToQueries positions) (hadamardDataWeight rho)
      (hadamardMaskCoefficient rho)
      (hadamardMaskCoefficient_ne_zero rho hrho) functional message
      left right hfunctional coins.1
  · exact ProductMask.view_coinEquiv productCoefficient hproductCoefficient
      multiplicationRestriction gammaFunctional
      (fun side : Bool => if side then
        actualDefect (message right) rightCommitment.2
      else actualDefect (message left) coins.1.2)
      false true
      (by
        simpa [rightCommitment] using
          actualDefect_difference_restricts_to_zero
            (message left) (message right) coins.1.2 rightCommitment.2
            hleft hright)
      coins.2

end VeiledFlock.ProductionCorrelatedHadamard

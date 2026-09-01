import VeiledFlock.Production.Algebra.ConstraintCompiler
import VeiledFlock.Production.Algebra.CorrelatedVeilCore

/-!
# Corrected complete production VEIL layer

The dummy multiplication claims are composed with the padding-correlated
Hadamard/product core.  The sole original multiplication row must be valid;
the two dummy rows are valid by construction.
-/

namespace VeiledFlock.ProductionCorrelatedVeilLayer

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionConstraintCompiler
open VeiledFlock.ProductionCorrelatedHadamard
open VeiledFlock.ProductionCorrelatedVeilCore
open VeiledFlock.ProductionMultiplicationPadding

abbrev DummyCoins := GhashField × GhashField × GhashField

/-- Literal `(a,b,c)` columns for the original product and both padding
products. -/
noncomputable def hadamardMessage {W : Type*}
    (multiplicationSecret : W →
      GhashField × GhashField × GhashField)
    (witness : W) (dummy : DummyCoins) :
    Fin 3 → Fin hadamardLogicalLength → GhashField
  | ⟨0, _⟩ => rowA (multiplicationSecret witness) dummy
  | ⟨1, _⟩ => rowB (multiplicationSecret witness) dummy
  | ⟨2, _⟩ => rowC (multiplicationSecret witness) dummy

theorem hadamardMessage_rowsValid {W : Type*}
    (multiplicationSecret : W →
      GhashField × GhashField × GhashField)
    (multiplicationValid : ∀ witness,
      (multiplicationSecret witness).1 *
          (multiplicationSecret witness).2.1 =
        (multiplicationSecret witness).2.2)
    (witness : W) (dummy : DummyCoins) :
    RowsValid (hadamardMessage multiplicationSecret witness dummy) := by
  intro index
  exact rows_valid (multiplicationSecret witness)
    (multiplicationValid witness) dummy index

noncomputable def hadamardClaims
    (functional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (message : Fin 3 → Fin hadamardLogicalLength → GhashField) :
    GhashField × GhashField × GhashField :=
  (functional (message 0), functional (message 1), functional (message 2))

theorem hadamardClaims_message
    (alpha : GhashField) {W : Type*}
    (multiplicationSecret : W →
      GhashField × GhashField × GhashField)
    (witness : W) (dummy : DummyCoins) :
    hadamardClaims (multiplicationFunctional alpha)
        (hadamardMessage multiplicationSecret witness dummy) =
      visibleClaims alpha multiplicationSecret witness dummy := by
  rcases dummy with ⟨r, s, t⟩
  apply Prod.ext
  · change
      (multiplicationSecret witness).1 + alpha * r +
          alpha ^ 2 * (r + 1) =
        alpha * r + alpha ^ 2 * (r + 1) +
          (multiplicationSecret witness).1
    ring
  · apply Prod.ext
    · change
        (multiplicationSecret witness).2.1 + alpha * s +
            alpha ^ 2 * t =
          alpha * s + alpha ^ 2 * t +
            (multiplicationSecret witness).2.1
      ring
    · change
        (multiplicationSecret witness).2.2 + alpha * (r * s) +
            alpha ^ 2 * ((r + 1) * t) =
          alpha * (r * s) + alpha ^ 2 * ((r + 1) * t) +
            (multiplicationSecret witness).2.2
      ring

theorem functional_kernel_of_claims_eq
    (functional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (left right : Fin 3 → Fin hadamardLogicalLength → GhashField)
    (hclaims : hadamardClaims functional left =
      hadamardClaims functional right) :
    ∀ column, functional (right column - left column) = 0 := by
  intro column
  have h0 := congrArg Prod.fst hclaims
  have h1 := congrArg (fun claims => claims.2.1) hclaims
  have h2 := congrArg (fun claims => claims.2.2) hclaims
  rw [map_sub]
  fin_cases column
  · exact sub_eq_zero.mpr h0.symm
  · exact sub_eq_zero.mpr h1.symm
  · exact sub_eq_zero.mpr h2.symm

abbrev LayerCoins (shape : BatchShape) :=
  DummyCoins × ProductionCorrelatedVeilCore.VeilCoins shape

abbrev LayerView (shape : BatchShape) :=
  (GhashField × GhashField × GhashField) ×
    ProductionCorrelatedVeilCore.VeilView shape

noncomputable def view {W : Type*}
    (shape : BatchShape)
    (linearPositions : Fin veilQueryCount → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : Fin veilQueryCount → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (multiplicationAlpha linearRho hadamardRho productCoefficient :
      GhashField)
    (multiplicationSecret : W →
      GhashField × GhashField × GhashField)
    (linearFunctional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (linearMessage : W → DummyCoins → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (witness : W) (coins : LayerCoins shape) : LayerView shape :=
  (visibleClaims multiplicationAlpha multiplicationSecret witness coins.1,
    ProductionCorrelatedVeilCore.view shape linearPositions hlinearPositions
      hadamardPositions hhadamardPositions linearRho hadamardRho
      productCoefficient linearFunctional
      (fun state : W × DummyCoins => linearMessage state.1 state.2)
      (multiplicationFunctional multiplicationAlpha)
      (fun state : W × DummyCoins =>
        hadamardMessage multiplicationSecret state.1 state.2)
      gammaFunctional (witness, coins.1) coins.2)

noncomputable def coinEquiv {W : Type*}
    (shape : BatchShape)
    (linearPositions : Fin veilQueryCount → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : Fin veilQueryCount → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (multiplicationAlpha linearRho hadamardRho productCoefficient :
      GhashField)
    (hmultiplicationAlpha : multiplicationAlpha ≠ 0)
    (hmultiplicationPlus : 1 + multiplicationAlpha ≠ 0)
    (multiplicationSecret : W →
      GhashField × GhashField × GhashField)
    (linearMessage : W → DummyCoins → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (left right : W) : LayerCoins shape ≃ LayerCoins shape where
  toFun coins :=
    let rightDummy := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
      left right coins.1
    (rightDummy,
      ProductionCorrelatedVeilCore.coinEquiv shape linearPositions
        hlinearPositions hadamardPositions hhadamardPositions linearRho
        hadamardRho productCoefficient
        (fun state : W × DummyCoins => linearMessage state.1 state.2)
        (fun state : W × DummyCoins =>
          hadamardMessage multiplicationSecret state.1 state.2)
        (left, coins.1) (right, rightDummy) coins.2)
  invFun coins :=
    let dummyEquiv := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
      left right
    let leftDummy := dummyEquiv.symm coins.1
    (leftDummy,
      (ProductionCorrelatedVeilCore.coinEquiv shape linearPositions
        hlinearPositions hadamardPositions hhadamardPositions linearRho
        hadamardRho productCoefficient
        (fun state : W × DummyCoins => linearMessage state.1 state.2)
        (fun state : W × DummyCoins =>
          hadamardMessage multiplicationSecret state.1 state.2)
        (left, leftDummy) (right, coins.1)).symm coins.2)
  left_inv coins := by
    let dummyEquiv := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
      left right
    let rightDummy := dummyEquiv coins.1
    let coreEquiv := ProductionCorrelatedVeilCore.coinEquiv shape
      linearPositions hlinearPositions hadamardPositions hhadamardPositions
      linearRho hadamardRho productCoefficient
      (fun state : W × DummyCoins => linearMessage state.1 state.2)
      (fun state : W × DummyCoins =>
        hadamardMessage multiplicationSecret state.1 state.2)
      (left, coins.1) (right, rightDummy)
    change
      (dummyEquiv.symm rightDummy,
        (ProductionCorrelatedVeilCore.coinEquiv shape linearPositions
          hlinearPositions hadamardPositions hhadamardPositions linearRho
          hadamardRho productCoefficient
          (fun state : W × DummyCoins => linearMessage state.1 state.2)
          (fun state : W × DummyCoins =>
            hadamardMessage multiplicationSecret state.1 state.2)
          (left, dummyEquiv.symm rightDummy) (right, rightDummy)).symm
          (coreEquiv coins.2)) = coins
    have hdummy := dummyEquiv.symm_apply_apply coins.1
    rw [hdummy]
    exact Prod.ext rfl (coreEquiv.symm_apply_apply coins.2)
  right_inv coins := by
    let dummyEquiv := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
      left right
    let leftDummy := dummyEquiv.symm coins.1
    let coreEquiv := ProductionCorrelatedVeilCore.coinEquiv shape
      linearPositions hlinearPositions hadamardPositions hhadamardPositions
      linearRho hadamardRho productCoefficient
      (fun state : W × DummyCoins => linearMessage state.1 state.2)
      (fun state : W × DummyCoins =>
        hadamardMessage multiplicationSecret state.1 state.2)
      (left, leftDummy) (right, coins.1)
    change
      (dummyEquiv leftDummy,
        ProductionCorrelatedVeilCore.coinEquiv shape linearPositions
          hlinearPositions hadamardPositions hhadamardPositions linearRho
          hadamardRho productCoefficient
          (fun state : W × DummyCoins => linearMessage state.1 state.2)
          (fun state : W × DummyCoins =>
            hadamardMessage multiplicationSecret state.1 state.2)
          (left, leftDummy) (right, dummyEquiv leftDummy)
          (coreEquiv.symm coins.2)) = coins
    have hdummy := dummyEquiv.apply_symm_apply coins.1
    rw [hdummy]
    exact Prod.ext rfl (coreEquiv.apply_symm_apply coins.2)

theorem view_coinEquiv {W : Type*}
    (shape : BatchShape)
    (linearPositions : Fin veilQueryCount → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : Fin veilQueryCount → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (multiplicationAlpha linearRho hadamardRho productCoefficient :
      GhashField)
    (hmultiplicationAlpha : multiplicationAlpha ≠ 0)
    (hmultiplicationPlus : 1 + multiplicationAlpha ≠ 0)
    (hlinearRho : linearRho ≠ 0)
    (hhadamardRho : hadamardRho ≠ 0)
    (hproductCoefficient : productCoefficient ≠ 0)
    (multiplicationSecret : W →
      GhashField × GhashField × GhashField)
    (multiplicationValid : ∀ witness,
      (multiplicationSecret witness).1 *
          (multiplicationSecret witness).2.1 =
        (multiplicationSecret witness).2.2)
    (linearFunctional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (linearMessage : W → DummyCoins → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (left right : W)
    (hlinearPublic : ∀ dummy,
      let rightDummy := claimCoinEquiv multiplicationAlpha
        hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
        left right dummy
      ∀ column, linearFunctional
        (linearMessage right rightDummy column -
          linearMessage left dummy column) = 0)
    (coins : LayerCoins shape) :
    view shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions multiplicationAlpha linearRho hadamardRho
        productCoefficient multiplicationSecret linearFunctional
        linearMessage gammaFunctional left coins =
      view shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions multiplicationAlpha linearRho hadamardRho
        productCoefficient multiplicationSecret linearFunctional
        linearMessage gammaFunctional right
        (coinEquiv shape linearPositions hlinearPositions hadamardPositions
          hhadamardPositions multiplicationAlpha linearRho hadamardRho
          productCoefficient hmultiplicationAlpha hmultiplicationPlus
          multiplicationSecret linearMessage left right coins) := by
  let rightDummy := claimCoinEquiv multiplicationAlpha
    hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
    left right coins.1
  have hvisible := visibleClaims_claimCoinEquiv multiplicationAlpha
    hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
    left right coins.1
  have hhadamardClaims :
      hadamardClaims (multiplicationFunctional multiplicationAlpha)
          (hadamardMessage multiplicationSecret left coins.1) =
        hadamardClaims (multiplicationFunctional multiplicationAlpha)
          (hadamardMessage multiplicationSecret right rightDummy) := by
    rw [hadamardClaims_message, hadamardClaims_message]
    exact hvisible
  apply Prod.ext
  · exact hvisible
  · exact ProductionCorrelatedVeilCore.view_coinEquiv shape linearPositions
      hlinearPositions hadamardPositions hhadamardPositions linearRho
      hadamardRho productCoefficient hlinearRho hhadamardRho
      hproductCoefficient linearFunctional
      (fun state : W × DummyCoins => linearMessage state.1 state.2)
      (multiplicationFunctional multiplicationAlpha)
      (fun state : W × DummyCoins =>
        hadamardMessage multiplicationSecret state.1 state.2)
      gammaFunctional (left, coins.1) (right, rightDummy)
      (hlinearPublic coins.1)
      (functional_kernel_of_claims_eq
        (multiplicationFunctional multiplicationAlpha)
        (hadamardMessage multiplicationSecret left coins.1)
        (hadamardMessage multiplicationSecret right rightDummy)
        hhadamardClaims)
      (hadamardMessage_rowsValid multiplicationSecret multiplicationValid
        left coins.1)
      (hadamardMessage_rowsValid multiplicationSecret multiplicationValid
        right rightDummy)
      coins.2

end VeiledFlock.ProductionCorrelatedVeilLayer

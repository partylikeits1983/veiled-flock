import VeiledFlock.Production.Algebra.MultiplicationPadding
import VeiledFlock.Production.Algebra.VeilCore

/-!
# Complete production VEIL algebraic layer

This composes the two dummy multiplication products with the complete
linear/Hadamard/product-code core.  The second coin translation depends on the
translated dummy coins, matching the actual protocol: those six padded values
are themselves committed in the linear proof and form two of the three
Hadamard rows.
-/

namespace VeiledFlock.ProductionVeilLayer

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionMultiplicationPadding
open VeiledFlock.ProductionProductMask
open VeiledFlock.ProductionVeilCore

abbrev QueryIndex := Fin veilQueryCount
abbrev DummyCoins := GhashField × GhashField × GhashField

abbrev LayerCoins (shape : BatchShape) :=
  DummyCoins × VeilCoins shape

abbrev LayerView (shape : BatchShape) :=
  (GhashField × GhashField × GhashField) × VeilView shape

noncomputable def layerView {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (multiplicationAlpha linearRho hadamardRho productCoefficient :
      GhashField)
    (multiplicationSecret : W → GhashField × GhashField × GhashField)
    (linearFunctional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (linearMessage : W → DummyCoins → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (hadamardFunctional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (triple : W → DummyCoins → ValidTriple)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (witness : W) (coins : LayerCoins shape) : LayerView shape :=
  (visibleClaims multiplicationAlpha multiplicationSecret witness coins.1,
    veilView shape linearPositions hlinearPositions hadamardPositions
      hhadamardPositions linearRho hadamardRho productCoefficient
      linearFunctional
      (fun state => linearMessage state.1 state.2)
      hadamardFunctional (fun state => triple state.1 state.2)
      gammaFunctional (witness, coins.1) coins.2)

noncomputable def layerCoinEquiv {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (multiplicationAlpha linearRho hadamardRho productCoefficient :
      GhashField)
    (hmultiplicationAlpha : multiplicationAlpha ≠ 0)
    (hmultiplicationPlus : 1 + multiplicationAlpha ≠ 0)
    (multiplicationSecret : W → GhashField × GhashField × GhashField)
    (linearMessage : W → DummyCoins → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (triple : W → DummyCoins → ValidTriple)
    (left right : W) : LayerCoins shape ≃ LayerCoins shape where
  toFun coins :=
    let rightDummy := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
      left right coins.1
    (rightDummy,
      veilCoinEquiv shape linearPositions hlinearPositions
        hadamardPositions hhadamardPositions linearRho hadamardRho
        productCoefficient (fun state => linearMessage state.1 state.2)
        (fun state => triple state.1 state.2)
        (left, coins.1) (right, rightDummy) coins.2)
  invFun coins :=
    let dummyEquiv := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret left right
    let leftDummy := dummyEquiv.symm coins.1
    (leftDummy,
      (veilCoinEquiv shape linearPositions hlinearPositions
        hadamardPositions hhadamardPositions linearRho hadamardRho
        productCoefficient (fun state => linearMessage state.1 state.2)
        (fun state => triple state.1 state.2)
        (left, leftDummy) (right, coins.1)).symm coins.2)
  left_inv coins := by
    rcases coins with ⟨dummy, veil⟩
    let dummyEquiv := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret left right
    let rightDummy := dummyEquiv dummy
    let coreEquiv := veilCoinEquiv shape linearPositions hlinearPositions
      hadamardPositions hhadamardPositions linearRho hadamardRho
      productCoefficient (fun state => linearMessage state.1 state.2)
      (fun state => triple state.1 state.2)
      (left, dummy) (right, rightDummy)
    change
      (dummyEquiv.symm rightDummy,
        (veilCoinEquiv shape linearPositions hlinearPositions
          hadamardPositions hhadamardPositions linearRho hadamardRho
          productCoefficient (fun state => linearMessage state.1 state.2)
          (fun state => triple state.1 state.2)
          (left, dummyEquiv.symm rightDummy) (right, rightDummy)).symm
            (coreEquiv veil)) = (dummy, veil)
    have hdummy : dummyEquiv.symm rightDummy = dummy :=
      dummyEquiv.symm_apply_apply dummy
    rw [hdummy]
    exact Prod.ext rfl (coreEquiv.symm_apply_apply veil)
  right_inv coins := by
    rcases coins with ⟨dummy, veil⟩
    let dummyEquiv := claimCoinEquiv multiplicationAlpha
      hmultiplicationAlpha hmultiplicationPlus multiplicationSecret left right
    let leftDummy := dummyEquiv.symm dummy
    let coreEquiv := veilCoinEquiv shape linearPositions hlinearPositions
      hadamardPositions hhadamardPositions linearRho hadamardRho
      productCoefficient (fun state => linearMessage state.1 state.2)
      (fun state => triple state.1 state.2)
      (left, leftDummy) (right, dummy)
    dsimp only
    have hdummy : dummyEquiv leftDummy = dummy :=
      dummyEquiv.apply_symm_apply dummy
    rw [hdummy]
    exact Prod.ext rfl (coreEquiv.apply_symm_apply veil)

theorem layerView_layerCoinEquiv {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (multiplicationAlpha linearRho hadamardRho productCoefficient :
      GhashField)
    (hmultiplicationAlpha : multiplicationAlpha ≠ 0)
    (hmultiplicationPlus : 1 + multiplicationAlpha ≠ 0)
    (hlinearRho : linearRho ≠ 0)
    (hhadamardRho : hadamardRho ≠ 0)
    (hproductCoefficient : productCoefficient ≠ 0)
    (multiplicationSecret : W → GhashField × GhashField × GhashField)
    (linearFunctional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (linearMessage : W → DummyCoins → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (hadamardFunctional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (triple : W → DummyCoins → ValidTriple)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (hclaims : ∀ witness dummy,
      tripleClaims hadamardFunctional (triple witness dummy) =
        visibleClaims multiplicationAlpha multiplicationSecret witness dummy)
    (left right : W)
    (hlinearPublic : ∀ dummy,
      let rightDummy := claimCoinEquiv multiplicationAlpha
        hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
        left right dummy
      ∀ column,
        linearFunctional
          (linearMessage right rightDummy column -
            linearMessage left dummy column) = 0)
    (coins : LayerCoins shape) :
    layerView shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions multiplicationAlpha linearRho hadamardRho
        productCoefficient multiplicationSecret linearFunctional linearMessage
        hadamardFunctional triple gammaFunctional left coins =
      layerView shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions multiplicationAlpha linearRho hadamardRho
        productCoefficient multiplicationSecret linearFunctional linearMessage
        hadamardFunctional triple gammaFunctional right
        (layerCoinEquiv shape linearPositions hlinearPositions
          hadamardPositions hhadamardPositions multiplicationAlpha linearRho
          hadamardRho productCoefficient hmultiplicationAlpha
          hmultiplicationPlus multiplicationSecret linearMessage triple
          left right coins) := by
  let rightDummy := claimCoinEquiv multiplicationAlpha hmultiplicationAlpha
    hmultiplicationPlus multiplicationSecret left right coins.1
  have hdummy := visibleClaims_claimCoinEquiv multiplicationAlpha
    hmultiplicationAlpha hmultiplicationPlus multiplicationSecret left right
    coins.1
  have htripleClaims :
      tripleClaims hadamardFunctional (triple left coins.1) =
        tripleClaims hadamardFunctional (triple right rightDummy) := by
    rw [hclaims left coins.1, hclaims right rightDummy]
    exact hdummy
  apply Prod.ext
  · exact hdummy
  · exact veilView_veilCoinEquiv shape linearPositions hlinearPositions
      hadamardPositions hhadamardPositions linearRho hadamardRho
      productCoefficient hlinearRho hhadamardRho hproductCoefficient
      linearFunctional (fun state => linearMessage state.1 state.2)
      hadamardFunctional (fun state => triple state.1 state.2)
      gammaFunctional (left, coins.1) (right, rightDummy)
      (hlinearPublic coins.1)
      (hadamardPublic_of_claims_eq hadamardFunctional
        (triple left coins.1) (triple right rightDummy) htripleClaims)
      coins.2

/-- Exact witness independence of the complete algebraic VEIL layer,
including both dummy products and every correlated code value. -/
theorem layer_witness_independent {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (multiplicationAlpha linearRho hadamardRho productCoefficient :
      GhashField)
    (hmultiplicationAlpha : multiplicationAlpha ≠ 0)
    (hmultiplicationPlus : 1 + multiplicationAlpha ≠ 0)
    (hlinearRho : linearRho ≠ 0)
    (hhadamardRho : hadamardRho ≠ 0)
    (hproductCoefficient : productCoefficient ≠ 0)
    (multiplicationSecret : W → GhashField × GhashField × GhashField)
    (linearFunctional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (linearMessage : W → DummyCoins → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (hadamardFunctional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (triple : W → DummyCoins → ValidTriple)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (hclaims : ∀ witness dummy,
      tripleClaims hadamardFunctional (triple witness dummy) =
        visibleClaims multiplicationAlpha multiplicationSecret witness dummy)
    (left right : W)
    (hlinearPublic : ∀ dummy,
      let rightDummy := claimCoinEquiv multiplicationAlpha
        hmultiplicationAlpha hmultiplicationPlus multiplicationSecret
        left right dummy
      ∀ column,
        linearFunctional
          (linearMessage right rightDummy column -
            linearMessage left dummy column) = 0) :
    (PMF.uniformOfFintype (LayerCoins shape)).map
        (layerView shape linearPositions hlinearPositions hadamardPositions
          hhadamardPositions multiplicationAlpha linearRho hadamardRho
          productCoefficient multiplicationSecret linearFunctional
          linearMessage hadamardFunctional triple gammaFunctional left) =
      (PMF.uniformOfFintype (LayerCoins shape)).map
        (layerView shape linearPositions hlinearPositions hadamardPositions
          hhadamardPositions multiplicationAlpha linearRho hadamardRho
          productCoefficient multiplicationSecret linearFunctional
          linearMessage hadamardFunctional triple gammaFunctional right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (layerCoinEquiv shape linearPositions hlinearPositions hadamardPositions
      hhadamardPositions multiplicationAlpha linearRho hadamardRho
      productCoefficient hmultiplicationAlpha hmultiplicationPlus
      multiplicationSecret linearMessage triple left right)
  exact layerView_layerCoinEquiv shape linearPositions hlinearPositions
    hadamardPositions hhadamardPositions multiplicationAlpha linearRho
    hadamardRho productCoefficient hmultiplicationAlpha hmultiplicationPlus
    hlinearRho hhadamardRho hproductCoefficient multiplicationSecret
    linearFunctional linearMessage hadamardFunctional triple gammaFunctional
    hclaims left right hlinearPublic

end VeiledFlock.ProductionVeilLayer

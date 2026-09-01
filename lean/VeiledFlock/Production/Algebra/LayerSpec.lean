import VeiledFlock.Production.Algebra.VeilLayer

/-!
# Auditable production VEIL layer specification

This structure collects the relation-specific data consumed by the generic
VEIL coin bijection.  Its proof fields are local semantic facts about the
shifted verifier circuit: the three Hadamard claims agree with the padded
multiplication claims, and equal public statements make the batched linear
claim identical after the dummy-coin translation.  All cryptographic hiding
and all concrete code geometry are proved outside the structure.
-/

namespace VeiledFlock.ProductionLayerSpec

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionMultiplicationPadding
open VeiledFlock.ProductionProductMask
open VeiledFlock.ProductionVeilCore
open VeiledFlock.ProductionVeilLayer

abbrev QueryIndex := Fin veilQueryCount

structure Spec (shape : BatchShape) (W Public : Type*) where
  statement : W → Public
  linearPositions : QueryIndex → Fin linearCodeLength
  linearPositions_injective : Injective linearPositions
  hadamardPositions : QueryIndex → Fin hadamardCodeLength
  hadamardPositions_injective : Injective hadamardPositions
  multiplicationAlpha : GhashField
  linearRho : GhashField
  hadamardRho : GhashField
  productCoefficient : GhashField
  multiplicationAlpha_ne_zero : multiplicationAlpha ≠ 0
  multiplicationAlpha_plus_ne_zero : 1 + multiplicationAlpha ≠ 0
  linearRho_ne_zero : linearRho ≠ 0
  hadamardRho_ne_zero : hadamardRho ≠ 0
  productCoefficient_ne_zero : productCoefficient ≠ 0
  multiplicationSecret : W → GhashField × GhashField × GhashField
  linearFunctional :
    (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField] GhashField
  linearMessage : W → DummyCoins → Fin 1 →
    Fin (linearLogicalLength shape) → GhashField
  hadamardFunctional :
    (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField
  triple : W → DummyCoins → ValidTriple
  gammaFunctional :
    (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField
  triple_claims : ∀ witness dummy,
    tripleClaims hadamardFunctional (triple witness dummy) =
      visibleClaims multiplicationAlpha multiplicationSecret witness dummy
  linear_public : ∀ left right,
    statement left = statement right → ∀ dummy,
      let rightDummy := claimCoinEquiv multiplicationAlpha
        multiplicationAlpha_ne_zero multiplicationAlpha_plus_ne_zero
        multiplicationSecret left right dummy
      ∀ column,
        linearFunctional
          (linearMessage right rightDummy column -
            linearMessage left dummy column) = 0

noncomputable def view {shape : BatchShape} {W Public : Type*}
    (spec : Spec shape W Public) (witness : W)
    (coins : LayerCoins shape) : LayerView shape :=
  layerView shape spec.linearPositions spec.linearPositions_injective
    spec.hadamardPositions spec.hadamardPositions_injective
    spec.multiplicationAlpha spec.linearRho spec.hadamardRho
    spec.productCoefficient spec.multiplicationSecret spec.linearFunctional
    spec.linearMessage spec.hadamardFunctional spec.triple
    spec.gammaFunctional witness coins

noncomputable def coinEquiv {shape : BatchShape} {W Public : Type*}
    (spec : Spec shape W Public) (left right : W) :
    LayerCoins shape ≃ LayerCoins shape :=
  layerCoinEquiv shape spec.linearPositions spec.linearPositions_injective
    spec.hadamardPositions spec.hadamardPositions_injective
    spec.multiplicationAlpha spec.linearRho spec.hadamardRho
    spec.productCoefficient spec.multiplicationAlpha_ne_zero
    spec.multiplicationAlpha_plus_ne_zero spec.multiplicationSecret
    spec.linearMessage spec.triple left right

theorem view_coinEquiv {shape : BatchShape} {W Public : Type*}
    (spec : Spec shape W Public) (left right : W)
    (hpublic : spec.statement left = spec.statement right)
    (coins : LayerCoins shape) :
    view spec left coins = view spec right (coinEquiv spec left right coins) := by
  exact layerView_layerCoinEquiv shape spec.linearPositions
    spec.linearPositions_injective spec.hadamardPositions
    spec.hadamardPositions_injective spec.multiplicationAlpha spec.linearRho
    spec.hadamardRho spec.productCoefficient
    spec.multiplicationAlpha_ne_zero spec.multiplicationAlpha_plus_ne_zero
    spec.linearRho_ne_zero spec.hadamardRho_ne_zero
    spec.productCoefficient_ne_zero spec.multiplicationSecret
    spec.linearFunctional spec.linearMessage spec.hadamardFunctional
    spec.triple spec.gammaFunctional spec.triple_claims left right
    (spec.linear_public left right hpublic) coins

theorem witness_independent {shape : BatchShape} {W Public : Type*}
    (spec : Spec shape W Public) {left right : W}
    (hpublic : spec.statement left = spec.statement right) :
    (PMF.uniformOfFintype (LayerCoins shape)).map (view spec left) =
      (PMF.uniformOfFintype (LayerCoins shape)).map (view spec right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv spec left right)
  exact view_coinEquiv spec left right hpublic

end VeiledFlock.ProductionLayerSpec

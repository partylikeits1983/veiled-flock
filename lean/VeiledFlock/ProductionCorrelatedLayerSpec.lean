import VeiledFlock.ProductionCorrelatedVeilLayer

/-!
# Auditable corrected production VEIL specification

Unlike the earlier interface, this specification does not accept an
independent Hadamard polynomial triple.  The operand polynomials and product
defect are derived internally from the committed logical rows and the same
random padding matrix.
-/

namespace VeiledFlock.ProductionCorrelatedLayerSpec

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionCorrelatedVeilLayer
open VeiledFlock.ProductionMultiplicationPadding

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
  multiplicationSecret : W →
    GhashField × GhashField × GhashField
  multiplicationValid : ∀ witness,
    (multiplicationSecret witness).1 *
        (multiplicationSecret witness).2.1 =
      (multiplicationSecret witness).2.2
  linearFunctional :
    (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField] GhashField
  linearMessage : W → DummyCoins → Fin 1 →
    Fin (linearLogicalLength shape) → GhashField
  gammaFunctional :
    (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField
  linear_public : ∀ left right,
    statement left = statement right → ∀ dummy,
      let rightDummy := claimCoinEquiv multiplicationAlpha
        multiplicationAlpha_ne_zero multiplicationAlpha_plus_ne_zero
        multiplicationSecret left right dummy
      ∀ column, linearFunctional
        (linearMessage right rightDummy column -
          linearMessage left dummy column) = 0

noncomputable def view {shape : BatchShape} {W Public : Type*}
    (spec : Spec shape W Public) (witness : W)
    (coins : LayerCoins shape) : LayerView shape :=
  ProductionCorrelatedVeilLayer.view shape spec.linearPositions
    spec.linearPositions_injective spec.hadamardPositions
    spec.hadamardPositions_injective spec.multiplicationAlpha spec.linearRho
    spec.hadamardRho spec.productCoefficient spec.multiplicationSecret
    spec.linearFunctional spec.linearMessage spec.gammaFunctional witness coins

noncomputable def coinEquiv {shape : BatchShape} {W Public : Type*}
    (spec : Spec shape W Public) (left right : W) :
    LayerCoins shape ≃ LayerCoins shape :=
  ProductionCorrelatedVeilLayer.coinEquiv shape spec.linearPositions
    spec.linearPositions_injective spec.hadamardPositions
    spec.hadamardPositions_injective spec.multiplicationAlpha spec.linearRho
    spec.hadamardRho spec.productCoefficient
    spec.multiplicationAlpha_ne_zero spec.multiplicationAlpha_plus_ne_zero
    spec.multiplicationSecret spec.linearMessage left right

theorem view_coinEquiv {shape : BatchShape} {W Public : Type*}
    (spec : Spec shape W Public) (left right : W)
    (hpublic : spec.statement left = spec.statement right)
    (coins : LayerCoins shape) :
    view spec left coins =
      view spec right (coinEquiv spec left right coins) := by
  exact ProductionCorrelatedVeilLayer.view_coinEquiv shape
    spec.linearPositions spec.linearPositions_injective
    spec.hadamardPositions spec.hadamardPositions_injective
    spec.multiplicationAlpha spec.linearRho spec.hadamardRho
    spec.productCoefficient spec.multiplicationAlpha_ne_zero
    spec.multiplicationAlpha_plus_ne_zero spec.linearRho_ne_zero
    spec.hadamardRho_ne_zero spec.productCoefficient_ne_zero
    spec.multiplicationSecret spec.multiplicationValid spec.linearFunctional
    spec.linearMessage spec.gammaFunctional left right
    (spec.linear_public left right hpublic) coins

end VeiledFlock.ProductionCorrelatedLayerSpec

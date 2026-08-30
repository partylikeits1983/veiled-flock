import VeiledFlock.Production.Algebra.CorrelatedHadamard

/-!
# Corrected joint production VEIL core

This composes the linear padded commitment with the Hadamard commitment and
its padding-correlated product defect.  All translated randomness is carried
by one explicit equivalence.
-/

namespace VeiledFlock.ProductionCorrelatedVeilCore

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.PaddedHornerCommitment
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionCorrelatedHadamard
open VeiledFlock.ProductionPaddedCommitments

abbrev QueryIndex := Fin veilQueryCount

abbrev LinearCoins (shape : BatchShape) :=
  PaddedHornerCommitment.Coins
    (F := GhashField) (Index := Fin (linearLogicalLength shape))
    (DataColumn := Fin 1) (Row := QueryIndex)

abbrev VeilCoins (shape : BatchShape) :=
  LinearCoins shape × ProductionCorrelatedHadamard.Coins

abbrev LinearView (shape : BatchShape) :=
  PaddedHornerCommitment.CommitmentView
    (F := GhashField) (Index := Fin (linearLogicalLength shape))
    (DataColumn := Fin 1) (Row := QueryIndex)

abbrev VeilView (shape : BatchShape) :=
  LinearView shape × ProductionCorrelatedHadamard.View

noncomputable def view {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearRho hadamardRho productCoefficient : GhashField)
    (linearFunctional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (linearMessage : W → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (hadamardFunctional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (hadamardMessage : W → Fin 3 →
      Fin hadamardLogicalLength → GhashField)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (witness : W) (coins : VeilCoins shape) : VeilView shape :=
  (PaddedHornerCommitment.commitmentView
      (linearPaddingQueryEquiv shape linearPositions hlinearPositions)
      (linearDataToQueries shape linearPositions) linearDataWeight linearRho
      linearFunctional linearMessage witness coins.1,
    ProductionCorrelatedHadamard.view hadamardPositions
      hhadamardPositions hadamardRho productCoefficient hadamardFunctional
      hadamardMessage gammaFunctional witness coins.2)

noncomputable def coinEquiv {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearRho hadamardRho productCoefficient : GhashField)
    (linearMessage : W → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (hadamardMessage : W → Fin 3 →
      Fin hadamardLogicalLength → GhashField)
    (left right : W) : VeilCoins shape ≃ VeilCoins shape :=
  Equiv.prodCongr
    (PaddedHornerCommitment.commitmentCoinEquiv
      (linearPaddingQueryEquiv shape linearPositions hlinearPositions)
      (linearDataToQueries shape linearPositions) linearDataWeight linearRho
      linearMessage left right)
    (ProductionCorrelatedHadamard.coinEquiv hadamardPositions
      hhadamardPositions hadamardRho productCoefficient hadamardMessage
      left right)

theorem view_coinEquiv {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearRho hadamardRho productCoefficient : GhashField)
    (hlinearRho : linearRho ≠ 0)
    (hhadamardRho : hadamardRho ≠ 0)
    (hproductCoefficient : productCoefficient ≠ 0)
    (linearFunctional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (linearMessage : W → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (hadamardFunctional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (hadamardMessage : W → Fin 3 →
      Fin hadamardLogicalLength → GhashField)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (left right : W)
    (hlinearPublic : ∀ column,
      linearFunctional
        (linearMessage right column - linearMessage left column) = 0)
    (hhadamardPublic : ∀ column,
      hadamardFunctional
        (hadamardMessage right column - hadamardMessage left column) = 0)
    (hleft : ProductionCorrelatedHadamard.RowsValid
      (hadamardMessage left))
    (hright : ProductionCorrelatedHadamard.RowsValid
      (hadamardMessage right))
    (coins : VeilCoins shape) :
    view shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions linearRho hadamardRho productCoefficient
        linearFunctional linearMessage hadamardFunctional hadamardMessage
        gammaFunctional left coins =
      view shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions linearRho hadamardRho productCoefficient
        linearFunctional linearMessage hadamardFunctional hadamardMessage
        gammaFunctional right
        (coinEquiv shape linearPositions hlinearPositions hadamardPositions
          hhadamardPositions linearRho hadamardRho productCoefficient
          linearMessage hadamardMessage left right coins) := by
  apply Prod.ext
  · exact PaddedHornerCommitment.commitmentView_commitmentCoinEquiv
      (linearPaddingQueryEquiv shape linearPositions hlinearPositions)
      (linearDataToQueries shape linearPositions) linearDataWeight linearRho
      hlinearRho linearFunctional linearMessage left right hlinearPublic
      coins.1
  · exact ProductionCorrelatedHadamard.view_coinEquiv hadamardPositions
      hhadamardPositions hadamardRho productCoefficient hhadamardRho
      hproductCoefficient hadamardFunctional hadamardMessage gammaFunctional
      left right hhadamardPublic hleft hright coins.2

end VeiledFlock.ProductionCorrelatedVeilCore

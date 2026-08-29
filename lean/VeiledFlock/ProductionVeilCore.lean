import VeiledFlock.ProductionPaddedCommitments
import VeiledFlock.ProductionProductMask

/-!
# Joint production VEIL core

This module combines all algebraic randomness in the two production VEIL
commitments: the linear additive mask and padding matrix, the Hadamard
additive mask and padding matrix, and the square-code product mask.  The
result is one explicit equivalence on the complete coin product and a
pointwise identity of the complete visible view.
-/

namespace VeiledFlock.ProductionVeilCore

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.HornerMask
open VeiledFlock.PaddedHornerCommitment
open VeiledFlock.ProductMask
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionPaddedCommitments
open VeiledFlock.ProductionProductMask

abbrev QueryIndex := Fin veilQueryCount

noncomputable def tripleColumnMessage
    (triple : ValidTriple) :
    Fin 3 → Fin hadamardLogicalLength → GhashField
  | ⟨0, _⟩, index => triple.a.1.eval (multiplicationPoint index)
  | ⟨1, _⟩, index => triple.b.1.eval (multiplicationPoint index)
  | ⟨2, _⟩, index => triple.c.1.eval (multiplicationPoint index)

noncomputable def tripleClaims
    (functional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (triple : ValidTriple) : GhashField × GhashField × GhashField :=
  (functional (tripleColumnMessage triple 0),
    functional (tripleColumnMessage triple 1),
    functional (tripleColumnMessage triple 2))

theorem hadamardPublic_of_claims_eq
    (functional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (left right : ValidTriple)
    (hclaims : tripleClaims functional left = tripleClaims functional right) :
    ∀ column,
      functional
        (tripleColumnMessage right column -
          tripleColumnMessage left column) = 0 := by
  intro column
  have h0 := congrArg Prod.fst hclaims
  have h1 := congrArg (fun claims => claims.2.1) hclaims
  have h2 := congrArg (fun claims => claims.2.2) hclaims
  rw [map_sub]
  fin_cases column
  · exact sub_eq_zero.mpr h0.symm
  · exact sub_eq_zero.mpr h1.symm
  · exact sub_eq_zero.mpr h2.symm

abbrev LinearCoins (shape : BatchShape) :=
  PaddedHornerCommitment.Coins
    (F := GhashField) (Index := Fin (linearLogicalLength shape))
    (DataColumn := Fin 1) (Row := QueryIndex)

abbrev HadamardCoins :=
  PaddedHornerCommitment.Coins
    (F := GhashField) (Index := Fin hadamardLogicalLength)
    (DataColumn := Fin 3) (Row := QueryIndex)

abbrev VeilCoins (shape : BatchShape) :=
  LinearCoins shape × HadamardCoins × SquarePolynomial

abbrev LinearView (shape : BatchShape) :=
  PaddedHornerCommitment.CommitmentView
    (F := GhashField) (Index := Fin (linearLogicalLength shape))
    (DataColumn := Fin 1) (Row := QueryIndex)

abbrev HadamardView :=
  PaddedHornerCommitment.CommitmentView
    (F := GhashField) (Index := Fin hadamardLogicalLength)
    (DataColumn := Fin 3) (Row := QueryIndex)

abbrev ProductView := SquarePolynomial × GhashField

abbrev VeilView (shape : BatchShape) :=
  LinearView shape × HadamardView × ProductView

noncomputable def veilView {W : Type*}
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
    (triple : W → ValidTriple)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (witness : W) (coins : VeilCoins shape) : VeilView shape :=
  (PaddedHornerCommitment.commitmentView
      (linearPaddingQueryEquiv shape linearPositions hlinearPositions)
      (linearDataToQueries shape linearPositions) linearDataWeight linearRho
      linearFunctional linearMessage witness coins.1,
    PaddedHornerCommitment.commitmentView
      (hadamardPaddingQueryEquiv hadamardPositions hhadamardPositions)
      (hadamardDataToQueries hadamardPositions)
      (hadamardDataWeight hadamardRho)
      (hadamardMaskCoefficient hadamardRho) hadamardFunctional
      (fun witness => tripleColumnMessage (triple witness)) witness coins.2.1,
    ProductMask.view productCoefficient multiplicationRestriction
      gammaFunctional (fun witness => (triple witness).defect)
      witness coins.2.2)

noncomputable def veilCoinEquiv {W : Type*}
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearRho hadamardRho productCoefficient : GhashField)
    (linearMessage : W → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (triple : W → ValidTriple) (left right : W) :
    VeilCoins shape ≃ VeilCoins shape :=
  Equiv.prodCongr
    (PaddedHornerCommitment.commitmentCoinEquiv
      (linearPaddingQueryEquiv shape linearPositions hlinearPositions)
      (linearDataToQueries shape linearPositions) linearDataWeight linearRho
      linearMessage left right)
    (Equiv.prodCongr
      (PaddedHornerCommitment.commitmentCoinEquiv
        (hadamardPaddingQueryEquiv hadamardPositions hhadamardPositions)
        (hadamardDataToQueries hadamardPositions)
        (hadamardDataWeight hadamardRho)
        (hadamardMaskCoefficient hadamardRho)
        (fun witness => tripleColumnMessage (triple witness)) left right)
      (ProductMask.coinEquiv productCoefficient
        (fun witness => (triple witness).defect) left right))

theorem veilView_veilCoinEquiv {W : Type*}
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
    (triple : W → ValidTriple)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (left right : W)
    (hlinearPublic : ∀ column,
      linearFunctional
        (linearMessage right column - linearMessage left column) = 0)
    (hhadamardPublic : ∀ column,
      hadamardFunctional
        (tripleColumnMessage (triple right) column -
          tripleColumnMessage (triple left) column) = 0)
    (coins : VeilCoins shape) :
    veilView shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions linearRho hadamardRho productCoefficient
        linearFunctional linearMessage hadamardFunctional triple
        gammaFunctional left coins =
      veilView shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions linearRho hadamardRho productCoefficient
        linearFunctional linearMessage hadamardFunctional triple
        gammaFunctional right
        (veilCoinEquiv shape linearPositions hlinearPositions
          hadamardPositions hhadamardPositions linearRho hadamardRho
          productCoefficient linearMessage triple left right coins) := by
  apply Prod.ext
  · exact PaddedHornerCommitment.commitmentView_commitmentCoinEquiv
      (linearPaddingQueryEquiv shape linearPositions hlinearPositions)
      (linearDataToQueries shape linearPositions) linearDataWeight linearRho
      hlinearRho linearFunctional linearMessage left right hlinearPublic coins.1
  · apply Prod.ext
    · exact PaddedHornerCommitment.commitmentView_commitmentCoinEquiv
        (hadamardPaddingQueryEquiv hadamardPositions hhadamardPositions)
        (hadamardDataToQueries hadamardPositions)
        (hadamardDataWeight hadamardRho)
        (hadamardMaskCoefficient hadamardRho)
        (hadamardMaskCoefficient_ne_zero hadamardRho hhadamardRho)
        hadamardFunctional
        (fun witness => tripleColumnMessage (triple witness)) left right
        hhadamardPublic coins.2.1
    · exact ProductMask.view_coinEquiv productCoefficient hproductCoefficient
        multiplicationRestriction gammaFunctional
        (fun witness => (triple witness).defect) left right
        (valid_defect_difference_restricts_to_zero (triple left)
          (triple right)) coins.2.2

/-- The full algebraic view of both production VEIL commitments is exactly
witness independent under one complete coin bijection. -/
theorem veil_core_witness_independent {W : Type*}
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
    (triple : W → ValidTriple)
    (gammaFunctional :
      (Fin paddedMultiplications → GhashField) →ₗ[GhashField] GhashField)
    (left right : W)
    (hlinearPublic : ∀ column,
      linearFunctional
        (linearMessage right column - linearMessage left column) = 0)
    (hhadamardPublic : ∀ column,
      hadamardFunctional
        (tripleColumnMessage (triple right) column -
          tripleColumnMessage (triple left) column) = 0) :
    (PMF.uniformOfFintype (VeilCoins shape)).map
        (veilView shape linearPositions hlinearPositions hadamardPositions
          hhadamardPositions linearRho hadamardRho productCoefficient
          linearFunctional linearMessage hadamardFunctional triple
          gammaFunctional left) =
      (PMF.uniformOfFintype (VeilCoins shape)).map
        (veilView shape linearPositions hlinearPositions hadamardPositions
          hhadamardPositions linearRho hadamardRho productCoefficient
          linearFunctional linearMessage hadamardFunctional triple
          gammaFunctional right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (veilCoinEquiv shape linearPositions hlinearPositions hadamardPositions
      hhadamardPositions linearRho hadamardRho productCoefficient
      linearMessage triple left right)
  exact veilView_veilCoinEquiv shape linearPositions hlinearPositions
    hadamardPositions hhadamardPositions linearRho hadamardRho
    productCoefficient hlinearRho hhadamardRho hproductCoefficient
    linearFunctional linearMessage hadamardFunctional triple gammaFunctional
    left right hlinearPublic hhadamardPublic

end VeiledFlock.ProductionVeilCore

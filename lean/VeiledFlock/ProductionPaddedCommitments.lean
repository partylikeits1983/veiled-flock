import VeiledFlock.PaddedHornerCommitment
import VeiledFlock.ProductionCodeDomains

/-!
# Exact production specializations of the two padded VEIL commitments

The linear commitment contains the padded shifted-circuit witness plus one
additive-mask column.  The Hadamard commitment contains the three
multiplication-side columns plus one additive-mask column.  These theorems
instantiate the joint Horner/padding proof at the exact 8,192- and
2,048-coordinate production domains.
-/

namespace VeiledFlock.ProductionPaddedCommitments

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.HornerMask
open VeiledFlock.PaddedHornerCommitment
open VeiledFlock.ProductionCodeDomains

abbrev QueryIndex := Fin veilQueryCount

/-- The production linear proof has one data column; its Horner weight is
one and the additive-mask coefficient is the sampled nonzero `rho`. -/
noncomputable def linearDataWeight (_ : Fin 1) : GhashField := 1

theorem linear_commitment_witness_independent
    {W : Type*} (shape : BatchShape)
    (positions : QueryIndex → Fin linearCodeLength)
    (hpositions : Injective positions)
    (rho : GhashField) (hrho : rho ≠ 0)
    (functional :
      (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
        GhashField)
    (message : W → Fin 1 →
      Fin (linearLogicalLength shape) → GhashField)
    (left right : W)
    (hpublic : ∀ column,
      functional (message right column - message left column) = 0) :
    (PMF.uniformOfFintype
      (PaddedHornerCommitment.Coins
        (F := GhashField)
        (Index := Fin (linearLogicalLength shape))
        (DataColumn := Fin 1) (Row := QueryIndex))).map
        (PaddedHornerCommitment.commitmentView
          (linearPaddingQueryEquiv shape positions hpositions)
          (linearDataToQueries shape positions)
          linearDataWeight rho functional message left) =
      (PMF.uniformOfFintype
        (PaddedHornerCommitment.Coins
          (F := GhashField)
          (Index := Fin (linearLogicalLength shape))
          (DataColumn := Fin 1) (Row := QueryIndex))).map
        (PaddedHornerCommitment.commitmentView
          (linearPaddingQueryEquiv shape positions hpositions)
          (linearDataToQueries shape positions)
          linearDataWeight rho functional message right) := by
  exact PaddedHornerCommitment.commitment_witness_independent
    (linearPaddingQueryEquiv shape positions hpositions)
    (linearDataToQueries shape positions) linearDataWeight rho hrho functional
    message left right hpublic

/-- Production Hadamard base-column weights.  The Rust Horner fold is
`a + rho*(b + rho*(c + rho*mask))`, hence data weights `1,rho,rho^2` and
mask coefficient `rho^3`. -/
noncomputable def hadamardDataWeight (rho : GhashField) : Fin 3 → GhashField
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => rho
  | ⟨2, _⟩ => rho ^ 2

noncomputable def hadamardMaskCoefficient (rho : GhashField) : GhashField :=
  rho ^ 3

theorem hadamardMaskCoefficient_ne_zero (rho : GhashField) (hrho : rho ≠ 0) :
    hadamardMaskCoefficient rho ≠ 0 := by
  exact pow_ne_zero 3 hrho

theorem hadamard_commitment_witness_independent
    {W : Type*}
    (positions : QueryIndex → Fin hadamardCodeLength)
    (hpositions : Injective positions)
    (rho : GhashField) (hrho : rho ≠ 0)
    (functional :
      (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField] GhashField)
    (message : W → Fin 3 → Fin hadamardLogicalLength → GhashField)
    (left right : W)
    (hpublic : ∀ column,
      functional (message right column - message left column) = 0) :
    (PMF.uniformOfFintype
      (PaddedHornerCommitment.Coins
        (F := GhashField) (Index := Fin hadamardLogicalLength)
        (DataColumn := Fin 3) (Row := QueryIndex))).map
        (PaddedHornerCommitment.commitmentView
          (hadamardPaddingQueryEquiv positions hpositions)
          (hadamardDataToQueries positions)
          (hadamardDataWeight rho) (hadamardMaskCoefficient rho)
          functional message left) =
      (PMF.uniformOfFintype
        (PaddedHornerCommitment.Coins
          (F := GhashField) (Index := Fin hadamardLogicalLength)
          (DataColumn := Fin 3) (Row := QueryIndex))).map
        (PaddedHornerCommitment.commitmentView
          (hadamardPaddingQueryEquiv positions hpositions)
          (hadamardDataToQueries positions)
          (hadamardDataWeight rho) (hadamardMaskCoefficient rho)
          functional message right) := by
  exact PaddedHornerCommitment.commitment_witness_independent
    (hadamardPaddingQueryEquiv positions hpositions)
    (hadamardDataToQueries positions) (hadamardDataWeight rho)
    (hadamardMaskCoefficient rho) (hadamardMaskCoefficient_ne_zero rho hrho)
    functional message left right hpublic

end VeiledFlock.ProductionPaddedCommitments

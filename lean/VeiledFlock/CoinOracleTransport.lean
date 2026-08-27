import VeiledFlock.PairedOracleReplacement
import VeiledFlock.Probability

/-!
# Joint algebraic-coin and oracle transport

An end-to-end simulator changes its algebraic masking coins and its hidden
salted-leaf oracle inputs together.  This file packages that triangular map
as one explicit bijection.  The inverse first recovers the old algebraic
coins and then applies the inverse point permutation in that recovered fiber.
-/

namespace VeiledFlock.CoinOracleTransport

open Function
open VeiledFlock.PairedOracleReplacement

variable {Coins Index Point Outcome : Type*}
variable [Finite Index] [DecidableEq Point]

/-- Joint transport along an arbitrary algebraic coin equivalence. -/
noncomputable def coinOracleEquiv (coinEquiv : Coins ≃ Coins)
    (left right : Coins → Index → Point)
    (hleft : ∀ coins, Injective (left coins))
    (hright : ∀ coins, Injective (right coins))
    (hcross : ∀ coins leftIndex rightIndex,
      left coins leftIndex = right (coinEquiv coins) rightIndex →
        leftIndex = rightIndex) :
    (Coins × (Point → Outcome)) ≃ (Coins × (Point → Outcome)) where
  toFun input :=
    let renamed := PairedOracleReplacement.renameOracle
      (left input.1) (right (coinEquiv input.1))
      (hleft input.1) (hright (coinEquiv input.1)) (hcross input.1)
    (coinEquiv input.1, renamed input.2)
  invFun output :=
    let recovered := coinEquiv.symm output.1
    let renamed := PairedOracleReplacement.renameOracle
      (left recovered) (right output.1)
      (hleft recovered) (hright output.1)
      (by
        intro leftIndex rightIndex equality
        apply hcross recovered leftIndex rightIndex
        rw [coinEquiv.apply_symm_apply]
        exact equality)
    (recovered, renamed.symm output.2)
  left_inv input := by
    apply Prod.ext
    · exact coinEquiv.symm_apply_apply input.1
    · simpa only [coinEquiv.symm_apply_apply] using
        (PairedOracleReplacement.renameOracle
        (left input.1) (right (coinEquiv input.1))
        (hleft input.1) (hright (coinEquiv input.1))
        (hcross input.1)).symm_apply_apply input.2
  right_inv output := by
    apply Prod.ext
    · exact coinEquiv.apply_symm_apply output.1
    · simpa only [coinEquiv.apply_symm_apply] using
        (PairedOracleReplacement.renameOracle
        (left (coinEquiv.symm output.1)) (right output.1)
        (hleft (coinEquiv.symm output.1)) (hright output.1)
        (by
          intro leftIndex rightIndex equality
          exact hcross (coinEquiv.symm output.1) leftIndex rightIndex (by
            simpa using equality))).apply_symm_apply output.2

@[simp]
theorem coinOracleEquiv_coins (coinEquiv : Coins ≃ Coins)
    (left right : Coins → Index → Point)
    (hleft : ∀ coins, Injective (left coins))
    (hright : ∀ coins, Injective (right coins))
    (hcross : ∀ coins leftIndex rightIndex,
      left coins leftIndex = right (coinEquiv coins) rightIndex →
        leftIndex = rightIndex)
    (input : Coins × (Point → Outcome)) :
    (coinOracleEquiv coinEquiv left right hleft hright hcross input).1 =
      coinEquiv input.1 := by
  rfl

/-- A corresponding simulated point receives the honest point's answer after
the joint transport. -/
theorem coinOracleEquiv_at_right (coinEquiv : Coins ≃ Coins)
    (left right : Coins → Index → Point)
    (hleft : ∀ coins, Injective (left coins))
    (hright : ∀ coins, Injective (right coins))
    (hcross : ∀ coins leftIndex rightIndex,
      left coins leftIndex = right (coinEquiv coins) rightIndex →
        leftIndex = rightIndex)
    (input : Coins × (Point → Outcome)) (index : Index) :
    (coinOracleEquiv coinEquiv left right hleft hright hcross input).2
        (right (coinEquiv input.1) index) =
      input.2 (left input.1 index) := by
  exact PairedOracleReplacement.renameOracle_at_right
    (left input.1) (right (coinEquiv input.1))
    (hleft input.1) (hright (coinEquiv input.1)) (hcross input.1)
    input.2 index

/-- Every point outside both moved families retains its exact oracle answer
under the joint transport. -/
theorem coinOracleEquiv_off (coinEquiv : Coins ≃ Coins)
    (left right : Coins → Index → Point)
    (hleft : ∀ coins, Injective (left coins))
    (hright : ∀ coins, Injective (right coins))
    (hcross : ∀ coins leftIndex rightIndex,
      left coins leftIndex = right (coinEquiv coins) rightIndex →
        leftIndex = rightIndex)
    (input : Coins × (Point → Outcome)) (point : Point)
    (hoffLeft : ∀ index, point ≠ left input.1 index)
    (hoffRight : ∀ index, point ≠ right (coinEquiv input.1) index) :
    (coinOracleEquiv coinEquiv left right hleft hright hcross input).2 point =
      input.2 point := by
  exact PairedOracleReplacement.renameOracle_off
    (left input.1) (right (coinEquiv input.1))
    (hleft input.1) (hright (coinEquiv input.1)) (hcross input.1)
    input.2 point hoffLeft hoffRight

/-- The joint reparameterization preserves the uniform coin/oracle
distribution exactly. -/
theorem uniform_coinOracleEquiv
    [Fintype Coins] [DecidableEq Coins]
    [Nonempty Coins]
    [Fintype Point] [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Outcome]
    (coinEquiv : Coins ≃ Coins)
    (left right : Coins → Index → Point)
    (hleft : ∀ coins, Injective (left coins))
    (hright : ∀ coins, Injective (right coins))
    (hcross : ∀ coins leftIndex rightIndex,
      left coins leftIndex = right (coinEquiv coins) rightIndex →
        leftIndex = rightIndex) :
    (PMF.uniformOfFintype (Coins × (Point → Outcome))).map
        (coinOracleEquiv coinEquiv left right hleft hright hcross) =
      PMF.uniformOfFintype (Coins × (Point → Outcome)) := by
  exact VeiledFlock.Probability.uniform_map_equiv
    (coinOracleEquiv coinEquiv left right hleft hright hcross)

end VeiledFlock.CoinOracleTransport

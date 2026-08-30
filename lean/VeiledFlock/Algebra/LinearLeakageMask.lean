import Mathlib
import VeiledFlock.Core.Probability

/-!
# Linear masking with a correlated revealed value

The VEIL dot-product commitments do not merely open padded Reed--Solomon
coordinates.  They also reveal a linear combination of the raw padding rows.
Consequently, uniformity of the opened coordinates by itself is insufficient:
the simulator must preserve the opening and this correlated value jointly.

This file gives the required exact finite-distribution lemma.  It also proves
the column-wise specialization used by the linear and Hadamard commitments.
-/

namespace VeiledFlock.LinearLeakageMask

open Function

variable {F Pad Opened Leaked W : Type*}
variable [Field F]
variable [AddCommGroup Pad] [Module F Pad]
variable [AddCommGroup Opened] [Module F Opened]
variable [AddCommGroup Leaked] [Module F Leaked]

/-- The joint visible value: an invertibly masked opening together with a
possibly correlated linear leakage of the same padding coins. -/
def view (mask : Pad ≃ₗ[F] Opened) (leak : Pad →ₗ[F] Leaked)
    (openedSecret : W → Opened) (leakedSecret : W → Leaked)
    (witness : W) (coins : Pad) : Opened × Leaked :=
  (mask coins + openedSecret witness,
    leak coins + leakedSecret witness)

/-- Translate padding coins so the first, fully masked component is unchanged
when the witness changes. -/
def coinEquiv (mask : Pad ≃ₗ[F] Opened)
    (openedSecret : W → Opened) (left right : W) : Pad ≃ Pad :=
  Equiv.addRight (mask.symm (openedSecret left - openedSecret right))

@[simp]
theorem coinEquiv_apply (mask : Pad ≃ₗ[F] Opened)
    (openedSecret : W → Opened) (left right : W) (coins : Pad) :
    coinEquiv mask openedSecret left right coins =
      coins + mask.symm (openedSecret left - openedSecret right) := rfl

/-- Pointwise preservation of both visible components.  The compatibility
equation is exactly the condition that the padding translation's change in
the leaked value cancels the witness-dependent leaked value. -/
theorem view_coinEquiv
    (mask : Pad ≃ₗ[F] Opened) (leak : Pad →ₗ[F] Leaked)
    (openedSecret : W → Opened) (leakedSecret : W → Leaked)
    (left right : W)
    (hcompatible :
      leak (mask.symm (openedSecret left - openedSecret right)) +
          leakedSecret right = leakedSecret left)
    (coins : Pad) :
    view mask leak openedSecret leakedSecret left coins =
      view mask leak openedSecret leakedSecret right
        (coinEquiv mask openedSecret left right coins) := by
  apply Prod.ext
  · simp only [view, coinEquiv_apply, map_add,
      LinearEquiv.apply_symm_apply]
    abel
  · simp only [view, coinEquiv_apply, map_add]
    rw [add_assoc, hcompatible]

/-- Exact joint witness independence under finite uniform padding coins. -/
theorem witness_independent
    [Fintype Pad] [Nonempty Pad]
    (mask : Pad ≃ₗ[F] Opened) (leak : Pad →ₗ[F] Leaked)
    (openedSecret : W → Opened) (leakedSecret : W → Leaked)
    (left right : W)
    (hcompatible :
      leak (mask.symm (openedSecret left - openedSecret right)) +
          leakedSecret right = leakedSecret left) :
    (PMF.uniformOfFintype Pad).map
        (view mask leak openedSecret leakedSecret left) =
      (PMF.uniformOfFintype Pad).map
        (view mask leak openedSecret leakedSecret right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv mask openedSecret left right)
  exact view_coinEquiv mask leak openedSecret leakedSecret left right
    hcompatible

section Columns

variable {Row Column : Type*}
variable [Fintype Row] [Fintype Column]

/-- Apply the same Reed--Solomon padding-to-query equivalence independently
to every commitment column. -/
def columnwiseEquiv (rowMask : (Row → F) ≃ₗ[F] (Row → F)) :
    (Column → Row → F) ≃ₗ[F] (Column → Row → F) where
  toFun matrix column := rowMask (matrix column)
  invFun matrix column := rowMask.symm (matrix column)
  map_add' left right := by
    funext column row
    exact congrFun (map_add rowMask (left column) (right column)) row
  map_smul' scalar matrix := by
    funext column row
    exact congrFun (map_smul rowMask scalar (matrix column)) row
  left_inv matrix := by
    funext column
    exact rowMask.symm_apply_apply (matrix column)
  right_inv matrix := by
    funext column
    exact rowMask.apply_symm_apply (matrix column)

/-- The raw-padding value revealed by Horner folding the commitment columns.
The theorem is agnostic to how the weights were generated. -/
def columnCombination (weights : Column → F) :
    (Column → Row → F) →ₗ[F] (Row → F) where
  toFun matrix row := ∑ column, weights column * matrix column row
  map_add' left right := by
    funext row
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar matrix := by
    funext row
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro column _
    ring

/-- Column folding commutes with applying the same linear code map to every
column. -/
theorem columnCombination_columnwiseEquiv
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (weights : Column → F) (matrix : Column → Row → F) :
    columnCombination weights (columnwiseEquiv rowMask matrix) =
      rowMask (columnCombination weights matrix) := by
  funext row
  change (∑ column, weights column * rowMask (matrix column) row) =
    rowMask (fun row => ∑ column, weights column * matrix column row) row
  have hsum :
      (fun row => ∑ column, weights column * matrix column row) =
        ∑ column, weights column • matrix column := by
    funext coordinate
    simp
  rw [hsum, map_sum]
  simp

/-- If the witness change has zero weighted combination at the opened
coordinates, translating the per-column padding leaves the revealed raw
padding combination unchanged as well. -/
theorem columnCombination_inverse_eq_zero
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (weights : Column → F) (delta : Column → Row → F)
    (hdelta : columnCombination weights delta = 0) :
    columnCombination weights ((columnwiseEquiv rowMask).symm delta) = 0 := by
  have hcomm := columnCombination_columnwiseEquiv rowMask weights
    ((columnwiseEquiv rowMask).symm delta)
  rw [LinearEquiv.apply_symm_apply, hdelta] at hcomm
  apply rowMask.injective
  simpa using hcomm.symm

/-- Production-shaped corollary: independently padded columns, their opened
coordinates, and the revealed padding RLC are jointly witness independent
whenever the same RLC of the secret opened columns is public/unchanged. -/
theorem column_openings_with_rlc_witness_independent
    [Fintype (Column → Row → F)] [Nonempty (Column → Row → F)]
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (weights : Column → F)
    (openedSecret : W → Column → Row → F)
    (left right : W)
    (hpublicRlc :
      columnCombination weights (openedSecret left - openedSecret right) = 0) :
    (PMF.uniformOfFintype (Column → Row → F)).map
        (view (columnwiseEquiv rowMask) (columnCombination weights)
          openedSecret (fun _ => 0) left) =
      (PMF.uniformOfFintype (Column → Row → F)).map
        (view (columnwiseEquiv rowMask) (columnCombination weights)
          openedSecret (fun _ => 0) right) := by
  apply witness_independent
  have hzero := columnCombination_inverse_eq_zero rowMask weights
    (openedSecret left - openedSecret right) hpublicRlc
  simpa using hzero

end Columns

end VeiledFlock.LinearLeakageMask

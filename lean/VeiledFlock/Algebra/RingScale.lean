import VeiledFlock.Algebra.Field128Serialization

/-!
# Exact ring-slice scaling

`scale_s_hat_v` and `scale_ring_expressions` multiply a packed field element
by scanning the 128 polynomial-basis bits of `scalar * basis[i]`.  This module
defines that exact 128-by-128 binary matrix over the proved GHASH field and
shows that it really represents multiplication by `scalar` after the slices
are recombined.
-/

namespace VeiledFlock.RingScale

open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization

abbrev SliceIndex := Fin 128

/-- Polynomial-basis coefficient selected by the Rust bit scan. -/
noncomputable def scaleCoefficient (scalar : GhashField)
    (input output : SliceIndex) : GhashField :=
  algebraMap (ZMod 2) GhashField
    (ghashBasis128.equivFun (scalar * ghashBasis128 input) output)

/-- Literal coefficient obtained by inspecting the corresponding stored bit,
as `scale_ring_expressions` does. -/
noncomputable def rustBitCoefficient (scalar : GhashField)
    (input output : SliceIndex) : GhashField :=
  if (bitsGhashEquiv.symm
      (scalar * ghashBasis128 input)).getLsb output then 1 else 0

private theorem coordinate_eq_storedBit (value : GhashField)
    (index : SliceIndex) :
    ghashBasis128.equivFun value index =
      boolF2Equiv ((bitsGhashEquiv.symm value).getLsb index) := by
  have h := bitsGhashEquiv.apply_symm_apply value
  change ghashBasis128.equivFun.symm
    (fun i => boolF2Equiv ((bitsGhashEquiv.symm value).getLsb i)) = value at h
  have heq := congrArg ghashBasis128.equivFun h
  rw [LinearEquiv.apply_symm_apply] at heq
  exact (congrFun heq index).symm

theorem scaleCoefficient_eq_rustBitCoefficient (scalar : GhashField)
    (input output : SliceIndex) :
    scaleCoefficient scalar input output =
      rustBitCoefficient scalar input output := by
  rw [scaleCoefficient, coordinate_eq_storedBit]
  change algebraMap (ZMod 2) GhashField
      (boolF2Equiv ((bitsGhashEquiv.symm
        (scalar * ghashBasis128 input)).getLsb output)) =
    if (bitsGhashEquiv.symm
        (scalar * ghashBasis128 input)).getLsb output then 1 else 0
  cases hbit : (bitsGhashEquiv.symm
      (scalar * ghashBasis128 input)).getLsb output <;>
    simp [boolF2Equiv]

/-- The exact matrix implemented by the nested input-bit/output-bit loops. -/
noncomputable def scaleSlices (scalar : GhashField) :
    (SliceIndex → GhashField) →ₗ[GhashField] (SliceIndex → GhashField) where
  toFun slices output :=
    ∑ input, scaleCoefficient scalar input output * slices input
  map_add' left right := by
    funext output
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' coefficient slices := by
    funext output
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro input _
    ring

/-- Recombine the 128 bit slices into one packed field value. -/
noncomputable def reconstruct (slices : SliceIndex → GhashField) : GhashField :=
  ∑ index, ghashBasis128 index * slices index

private theorem basis_reconstruct (value : GhashField) :
    (∑ index : SliceIndex,
      algebraMap (ZMod 2) GhashField (ghashBasis128.equivFun value index) *
        ghashBasis128 index) = value := by
  simpa only [Algebra.smul_def] using ghashBasis128.sum_equivFun value

theorem coefficient_reconstruct (scalar : GhashField) (input : SliceIndex) :
    (∑ output : SliceIndex,
      ghashBasis128 output * scaleCoefficient scalar input output) =
        scalar * ghashBasis128 input := by
  rw [show (∑ output : SliceIndex,
      ghashBasis128 output * scaleCoefficient scalar input output) =
      ∑ output : SliceIndex,
        scaleCoefficient scalar input output * ghashBasis128 output by
          apply Finset.sum_congr rfl
          intro output _
          ring]
  exact basis_reconstruct (scalar * ghashBasis128 input)

/-- Semantic correctness of both Rust scaling routines: after recombination,
the output slices represent the input multiplied by `scalar`. -/
theorem reconstruct_scaleSlices (scalar : GhashField)
    (slices : SliceIndex → GhashField) :
    reconstruct (scaleSlices scalar slices) =
      scalar * reconstruct slices := by
  simp only [reconstruct, scaleSlices, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ output : SliceIndex,
        ghashBasis128 output *
          ∑ input : SliceIndex,
            scaleCoefficient scalar input output * slices input) =
        ∑ output : SliceIndex, ∑ input : SliceIndex,
          ghashBasis128 output *
            (scaleCoefficient scalar input output * slices input) := by
      apply Finset.sum_congr rfl
      intro output _
      rw [Finset.mul_sum]
    _ = ∑ input : SliceIndex, ∑ output : SliceIndex,
          ghashBasis128 output *
            (scaleCoefficient scalar input output * slices input) := by
      rw [Finset.sum_comm]
    _ = ∑ input : SliceIndex,
          (∑ output : SliceIndex,
            ghashBasis128 output * scaleCoefficient scalar input output) *
              slices input := by
      apply Finset.sum_congr rfl
      intro input _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro output _
      ring
    _ = ∑ input : SliceIndex,
          (scalar * ghashBasis128 input) * slices input := by
      apply Finset.sum_congr rfl
      intro input _
      rw [coefficient_reconstruct]
    _ = scalar * ∑ input : SliceIndex,
          ghashBasis128 input * slices input := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _
      ring

end VeiledFlock.RingScale

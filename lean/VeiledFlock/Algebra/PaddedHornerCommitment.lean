import VeiledFlock.Algebra.HornerMask
import VeiledFlock.Algebra.LinearLeakageMask

/-!
# Joint simulation of a padded multi-column commitment

This is the exact algebraic shape shared by VEIL's linear and Hadamard
proximity commitments.  A nonzero-coefficient additive-mask column hides the
revealed Horner combination of base vectors.  Independently padded code
columns hide all opened rows, while the prover also reveals the same Horner
combination of the raw padding rows.  The lemmas below prove that the two
translations are compatible and form one joint coin bijection.
-/

namespace VeiledFlock.PaddedHornerCommitment

open VeiledFlock.HornerMask
open VeiledFlock.JointPcs
open VeiledFlock.LinearLeakageMask

variable {F Index DataColumn Row W : Type*}
variable [Field F] [Fintype DataColumn] [Fintype Row]

abbrev Column := DataColumn ⊕ Unit
abbrev Padding := Column (DataColumn := DataColumn) → Row → F

def columnWeight (weights : DataColumn → F) (maskCoefficient : F) :
    Column (DataColumn := DataColumn) → F
  | .inl column => weights column
  | .inr _ => maskCoefficient

def openedColumns (encode : (Index → F) →ₗ[F] (Row → F))
    (message : W → DataColumn → Index → F)
    (witness : W) (mask : Index → F) :
    Padding (F := F) (DataColumn := DataColumn) (Row := Row) :=
  fun column => match column with
    | .inl data => encode (message witness data)
    | .inr _ => encode mask

omit [Fintype Row] in
/-- Encoding and column folding commute.  Thus the opened-column RLC is the
encoding of the base-vector RLC, including the additive-mask column. -/
theorem columnCombination_openedColumns
    (encode : (Index → F) →ₗ[F] (Row → F))
    (weights : DataColumn → F) (maskCoefficient : F)
    (message : W → DataColumn → Index → F)
    (witness : W) (mask : Index → F) :
    columnCombination (columnWeight weights maskCoefficient)
        (openedColumns encode message witness mask) =
      encode
        (folded maskCoefficient
          (combinedMessage weights message witness) mask) := by
  funext row
  simp only [columnCombination, columnWeight, openedColumns,
    LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_sum_type,
    combinedMessage, folded, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_sum, map_smul]
  simp

omit [Fintype Row] in
/-- Once the Horner-mask translation has preserved the complete base RLC,
the induced change of all encoded columns has zero RLC.  This is the exact
compatibility condition required to preserve the revealed raw-padding RLC. -/
theorem opened_difference_columnCombination_eq_zero
    (encode : (Index → F) →ₗ[F] (Row → F))
    (weights : DataColumn → F) (maskCoefficient : F)
    (message : W → DataColumn → Index → F)
    (left right : W) (leftMask rightMask : Index → F)
    (hfolded :
      folded maskCoefficient (combinedMessage weights message left) leftMask =
        folded maskCoefficient (combinedMessage weights message right)
          rightMask) :
    columnCombination (columnWeight weights maskCoefficient)
      (openedColumns encode message left leftMask -
        openedColumns encode message right rightMask) = 0 := by
  rw [map_sub, columnCombination_openedColumns,
    columnCombination_openedColumns, hfolded, sub_self]

/-- The padding translation selected after the additive-mask translation. -/
def paddingCoinEquiv (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (encode : (Index → F) →ₗ[F] (Row → F))
    (message : W → DataColumn → Index → F)
    (left right : W) (leftMask rightMask : Index → F) :
    Padding (F := F) (DataColumn := DataColumn) (Row := Row) ≃
      Padding (F := F) (DataColumn := DataColumn) (Row := Row) :=
  LinearLeakageMask.coinEquiv (columnwiseEquiv rowMask)
    (fun side : Bool =>
      if side then openedColumns encode message right rightMask
      else openedColumns encode message left leftMask)
    false true

omit [Fintype DataColumn] [Fintype Row] in
@[simp]
theorem paddingCoinEquiv_apply
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (encode : (Index → F) →ₗ[F] (Row → F))
    (message : W → DataColumn → Index → F)
    (left right : W) (leftMask rightMask : Index → F)
    (padding : Padding (F := F) (DataColumn := DataColumn) (Row := Row)) :
    paddingCoinEquiv rowMask encode message left right leftMask rightMask
        padding =
      LinearLeakageMask.coinEquiv (columnwiseEquiv rowMask)
        (fun side : Bool =>
          if side then openedColumns encode message right rightMask
          else openedColumns encode message left leftMask)
        false true padding := rfl

omit [Fintype Row] in
/-- Pointwise preservation of all opened code rows and the correlated raw
padding RLC after the Horner RLC has been preserved. -/
theorem paddingView_transport_after_horner
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (encode : (Index → F) →ₗ[F] (Row → F))
    (weights : DataColumn → F) (maskCoefficient : F)
    (message : W → DataColumn → Index → F)
    (left right : W) (leftMask rightMask : Index → F)
    (hfolded :
      folded maskCoefficient (combinedMessage weights message left) leftMask =
        folded maskCoefficient (combinedMessage weights message right)
          rightMask)
    (padding : Padding (F := F) (DataColumn := DataColumn) (Row := Row)) :
    LinearLeakageMask.view (columnwiseEquiv rowMask)
        (columnCombination (columnWeight weights maskCoefficient))
        (fun side : Bool =>
          if side then openedColumns encode message right rightMask
          else openedColumns encode message left leftMask)
        (fun _ => 0) false padding =
      LinearLeakageMask.view (columnwiseEquiv rowMask)
        (columnCombination (columnWeight weights maskCoefficient))
        (fun side : Bool =>
          if side then openedColumns encode message right rightMask
          else openedColumns encode message left leftMask)
        (fun _ => 0) true
        (paddingCoinEquiv rowMask encode message left right leftMask rightMask
          padding) := by
  apply LinearLeakageMask.view_coinEquiv
  have hzero := opened_difference_columnCombination_eq_zero encode weights
    maskCoefficient message left right leftMask rightMask hfolded
  have hinverse := columnCombination_inverse_eq_zero rowMask
    (columnWeight weights maskCoefficient)
    (openedColumns encode message left leftMask -
      openedColumns encode message right rightMask) hzero
  simpa using hinverse

section CompleteCommitment

variable [Fintype F] [DecidableEq F]
variable [Fintype Index] [Fintype (Index → F)]
variable [Fintype (Padding (F := F) (DataColumn := DataColumn) (Row := Row))]

abbrev Coins :=
  (Index → F) ×
    Padding (F := F) (DataColumn := DataColumn) (Row := Row)

abbrev CommitmentView :=
  ((Index → F) × F) ×
    (Padding (F := F) (DataColumn := DataColumn) (Row := Row) ×
      (Row → F))

/-- All algebraic values exposed by one padded proximity commitment: the
base-vector RLC and mask claim, followed by every opened code column and the
revealed raw-padding RLC. -/
noncomputable def commitmentView
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (encode : (Index → F) →ₗ[F] (Row → F))
    (weights : DataColumn → F) (maskCoefficient : F)
    (functional : (Index → F) →ₗ[F] F)
    (message : W → DataColumn → Index → F)
    (witness : W)
    (coins : Coins (F := F) (Index := Index)
      (DataColumn := DataColumn) (Row := Row)) :
    CommitmentView (F := F) (Index := Index)
      (DataColumn := DataColumn) (Row := Row) :=
  (HornerMask.view weights maskCoefficient functional message witness coins.1,
    (columnwiseEquiv rowMask coins.2 +
        openedColumns encode message witness coins.1,
      columnCombination (columnWeight weights maskCoefficient) coins.2))

/-- The dependent two-stage coin translation.  First translate the additive
mask to preserve the base RLC; then, in that exact mask fiber, translate all
padding columns to preserve the openings and raw-padding RLC. -/
noncomputable def commitmentCoinEquiv
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (encode : (Index → F) →ₗ[F] (Row → F))
    (weights : DataColumn → F) (maskCoefficient : F)
    (message : W → DataColumn → Index → F)
    (left right : W) :
    Coins (F := F) (Index := Index) (DataColumn := DataColumn) (Row := Row) ≃
      Coins (F := F) (Index := Index) (DataColumn := DataColumn) (Row := Row) where
  toFun coins :=
    let rightMask := HornerMask.coinEquiv weights maskCoefficient message
      left right coins.1
    (rightMask,
      paddingCoinEquiv rowMask encode message left right coins.1 rightMask
        coins.2)
  invFun coins :=
    let leftMask := (HornerMask.coinEquiv weights maskCoefficient message
      left right).symm coins.1
    (leftMask,
      (paddingCoinEquiv rowMask encode message left right leftMask coins.1).symm
        coins.2)
  left_inv coins := by
    rcases coins with ⟨mask, padding⟩
    let maskEquiv := HornerMask.coinEquiv weights maskCoefficient message
      left right
    let rightMask := maskEquiv mask
    let paddingEquiv := paddingCoinEquiv rowMask encode message left right
      mask rightMask
    change
      (maskEquiv.symm rightMask,
        (paddingCoinEquiv rowMask encode message left right
          (maskEquiv.symm rightMask) rightMask).symm
          (paddingEquiv padding)) = (mask, padding)
    have hmask : maskEquiv.symm rightMask = mask :=
      maskEquiv.symm_apply_apply mask
    rw [hmask]
    exact Prod.ext rfl (paddingEquiv.symm_apply_apply padding)
  right_inv coins := by
    rcases coins with ⟨mask, padding⟩
    let maskEquiv := HornerMask.coinEquiv weights maskCoefficient message
      left right
    let leftMask := maskEquiv.symm mask
    let paddingEquiv := paddingCoinEquiv rowMask encode message left right
      leftMask mask
    change
      (maskEquiv leftMask,
        paddingCoinEquiv rowMask encode message left right leftMask
          (maskEquiv leftMask) (paddingEquiv.symm padding)) = (mask, padding)
    have hmask : maskEquiv leftMask = mask :=
      maskEquiv.apply_symm_apply mask
    rw [hmask]
    exact Prod.ext rfl (paddingEquiv.apply_symm_apply padding)

omit [Fintype F] [DecidableEq F] [Fintype Index] [Fintype (Index → F)] [Fintype Padding] in
theorem commitmentView_commitmentCoinEquiv
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (encode : (Index → F) →ₗ[F] (Row → F))
    (weights : DataColumn → F) (maskCoefficient : F)
    (hmaskCoefficient : maskCoefficient ≠ 0)
    (functional : (Index → F) →ₗ[F] F)
    (message : W → DataColumn → Index → F)
    (left right : W)
    (hpublic : ∀ column,
      functional (message right column - message left column) = 0)
    (coins : Coins (F := F) (Index := Index)
      (DataColumn := DataColumn) (Row := Row)) :
    commitmentView rowMask encode weights maskCoefficient functional message
        left coins =
      commitmentView rowMask encode weights maskCoefficient functional message
        right
        (commitmentCoinEquiv rowMask encode weights maskCoefficient message
          left right coins) := by
  let rightMask := HornerMask.coinEquiv weights maskCoefficient message
    left right coins.1
  have hhorner := HornerMask.view_coinEquiv weights maskCoefficient
    hmaskCoefficient functional message left right hpublic coins.1
  have hfolded :
      folded maskCoefficient (combinedMessage weights message left) coins.1 =
        folded maskCoefficient (combinedMessage weights message right)
          rightMask := congrArg Prod.fst hhorner
  apply Prod.ext
  · exact hhorner
  · have hpadding := paddingView_transport_after_horner rowMask encode weights
      maskCoefficient message left right coins.1 rightMask hfolded coins.2
    change
      (columnwiseEquiv rowMask coins.2 +
          openedColumns encode message left coins.1,
        columnCombination (columnWeight weights maskCoefficient) coins.2) =
      (columnwiseEquiv rowMask
            (paddingCoinEquiv rowMask encode message left right coins.1
              rightMask coins.2) +
          openedColumns encode message right rightMask,
        columnCombination (columnWeight weights maskCoefficient)
          (paddingCoinEquiv rowMask encode message left right coins.1
            rightMask coins.2))
    simpa [LinearLeakageMask.view] using hpadding

omit [Fintype F] [DecidableEq F] [Fintype Index] in
/-- Exact joint finite-distribution theorem for one complete production-shaped
padded proximity commitment. -/
theorem commitment_witness_independent
    (rowMask : (Row → F) ≃ₗ[F] (Row → F))
    (encode : (Index → F) →ₗ[F] (Row → F))
    (weights : DataColumn → F) (maskCoefficient : F)
    (hmaskCoefficient : maskCoefficient ≠ 0)
    (functional : (Index → F) →ₗ[F] F)
    (message : W → DataColumn → Index → F)
    (left right : W)
    (hpublic : ∀ column,
      functional (message right column - message left column) = 0) :
    (PMF.uniformOfFintype
      (Coins (F := F) (Index := Index)
        (DataColumn := DataColumn) (Row := Row))).map
        (commitmentView rowMask encode weights maskCoefficient functional
          message left) =
      (PMF.uniformOfFintype
        (Coins (F := F) (Index := Index)
          (DataColumn := DataColumn) (Row := Row))).map
        (commitmentView rowMask encode weights maskCoefficient functional
          message right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (commitmentCoinEquiv rowMask encode weights maskCoefficient message
      left right)
  exact commitmentView_commitmentCoinEquiv rowMask encode weights
    maskCoefficient hmaskCoefficient functional message left right hpublic

end CompleteCommitment

end VeiledFlock.PaddedHornerCommitment

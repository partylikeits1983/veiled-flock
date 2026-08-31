import VeiledFlock.Algebra.AdditiveReedSolomon

/-!
# Data/padding decomposition of Reed--Solomon query values

The production encoder interpolates one message containing logical data
followed by random padding.  Linearity splits every queried code coordinate
into a deterministic data contribution and the invertible padding
contribution already proved in `AdditiveReedSolomon`.
-/

namespace VeiledFlock.ReedSolomonDecomposition

open Function
open Polynomial
open VeiledFlock.AdditiveReedSolomon

variable {F Data Padding Query : Type*}
variable [Field F]
variable [Fintype Data] [Fintype Padding]
variable [DecidableEq Data] [DecidableEq Padding]

def dataValues : (Data → F) →ₗ[F] (Data ⊕ Padding → F) where
  toFun data := Sum.elim data (fun _ => 0)
  map_add' left right := by
    funext index
    cases index <;> simp
  map_smul' scalar data := by
    funext index
    cases index <;> simp

def fullValues : ((Data → F) × (Padding → F)) →ₗ[F]
    (Data ⊕ Padding → F) where
  toFun values := Sum.elim values.1 values.2
  map_add' left right := by
    funext index
    cases index <;> rfl
  map_smul' scalar values := by
    funext index
    cases index <;> rfl

omit [Fintype Data] [Fintype Padding] [DecidableEq Data] [DecidableEq Padding] in
theorem fullValues_eq_data_add_padding (data : Data → F)
    (padding : Padding → F) :
    fullValues (data, padding) =
      dataValues data + AdditiveReedSolomon.paddingValues padding := by
  funext index
  cases index <;> simp [fullValues, dataValues,
    AdditiveReedSolomon.paddingValues]

noncomputable def polynomialFromData (base : Data ⊕ Padding → F)
    (hbase : Injective base) :
    (Data → F) →ₗ[F] degreeLT F (Fintype.card (Data ⊕ Padding)) :=
  (evaluationEquiv base hbase).symm.toLinearMap.comp dataValues

noncomputable def polynomialFromValues (base : Data ⊕ Padding → F)
    (hbase : Injective base) :
    ((Data → F) × (Padding → F)) →ₗ[F]
      degreeLT F (Fintype.card (Data ⊕ Padding)) :=
  (evaluationEquiv base hbase).symm.toLinearMap.comp fullValues

def evaluateAt (queries : Query → F) :
    degreeLT F (Fintype.card (Data ⊕ Padding)) →ₗ[F] (Query → F) where
  toFun polynomial query := polynomial.1.eval (queries query)
  map_add' left right := by
    funext query
    exact Polynomial.eval_add.trans rfl
  map_smul' scalar polynomial := by
    funext query
    simp

noncomputable def dataToQueries (base : Data ⊕ Padding → F)
    (hbase : Injective base) (queries : Query → F) :
    (Data → F) →ₗ[F] (Query → F) :=
  (evaluateAt queries).comp (polynomialFromData base hbase)

noncomputable def valuesToQueries (base : Data ⊕ Padding → F)
    (hbase : Injective base) (queries : Query → F) :
    ((Data → F) × (Padding → F)) →ₗ[F] (Query → F) :=
  (evaluateAt queries).comp (polynomialFromValues base hbase)

/-- Exact linear decomposition of every queried encoded coordinate. -/
theorem valuesToQueries_decompose (base : Data ⊕ Padding → F)
    (hbase : Injective base) (queries : Padding → F)
    (data : Data → F) (padding : Padding → F) :
    valuesToQueries base hbase queries (data, padding) =
      dataToQueries base hbase queries data +
        AdditiveReedSolomon.paddingToQueries base hbase queries padding := by
  have hvalues := fullValues_eq_data_add_padding (F := F) data padding
  change (evaluateAt queries)
      ((evaluationEquiv base hbase).symm (fullValues (data, padding))) = _
  rw [hvalues, map_add, map_add]
  rfl

end VeiledFlock.ReedSolomonDecomposition

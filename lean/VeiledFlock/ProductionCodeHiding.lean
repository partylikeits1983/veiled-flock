import VeiledFlock.LinearLeakageMask
import VeiledFlock.ProductionCodeDomains

/-!
# Joint hiding of the two production VEIL code commitments

The linear commitment and the Hadamard commitment each pad every base-code
column with 160 independent field elements.  At exactly 160 distinct output
positions, the production additive Reed--Solomon map is an equivalence.  The
proof also exposes a Horner linear combination of the raw padding rows, so we
use `LinearLeakageMask` to preserve the openings and that correlated value
jointly.
-/

namespace VeiledFlock.ProductionCodeHiding

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.LinearLeakageMask
open VeiledFlock.ProductionCodeDomains

abbrev QueryIndex := Fin veilQueryCount

abbrev LinearPadding (Column : Type*) :=
  Column → QueryIndex → GhashField

abbrev HadamardPadding (Column : Type*) :=
  Column → QueryIndex → GhashField

/-- Exact per-column padding-to-opening map for the 8,192-coordinate linear
commitment. -/
noncomputable def linearOpeningEquiv (shape : BatchShape) (Column : Type*)
    [Fintype Column]
    (positions : QueryIndex → Fin linearCodeLength)
    (hpositions : Injective positions) :
    LinearPadding Column ≃ₗ[GhashField] LinearPadding Column :=
  columnwiseEquiv (linearPaddingQueryEquiv shape positions hpositions)

/-- Exact per-column padding-to-opening map for the 2,048-coordinate
Hadamard commitment. -/
noncomputable def hadamardOpeningEquiv (Column : Type*) [Fintype Column]
    (positions : QueryIndex → Fin hadamardCodeLength)
    (hpositions : Injective positions) :
    HadamardPadding Column ≃ₗ[GhashField] HadamardPadding Column :=
  columnwiseEquiv (hadamardPaddingQueryEquiv positions hpositions)

theorem linear_openings_and_paddingRlc_witness_independent
    {Column W : Type*} [Fintype Column] [Fintype (LinearPadding Column)]
    (shape : BatchShape)
    (positions : QueryIndex → Fin linearCodeLength)
    (hpositions : Injective positions)
    (weights : Column → GhashField)
    (openedSecret : W → LinearPadding Column)
    (left right : W)
    (hpublicRlc : columnCombination weights
      (openedSecret left - openedSecret right) = 0) :
    (PMF.uniformOfFintype (LinearPadding Column)).map
        (view (linearOpeningEquiv shape Column positions hpositions)
          (columnCombination weights) openedSecret (fun _ => 0) left) =
      (PMF.uniformOfFintype (LinearPadding Column)).map
        (view (linearOpeningEquiv shape Column positions hpositions)
          (columnCombination weights) openedSecret (fun _ => 0) right) := by
  exact column_openings_with_rlc_witness_independent
    (linearPaddingQueryEquiv shape positions hpositions) weights openedSecret
    left right hpublicRlc

theorem hadamard_openings_and_paddingRlc_witness_independent
    {Column W : Type*} [Fintype Column] [Fintype (HadamardPadding Column)]
    (positions : QueryIndex → Fin hadamardCodeLength)
    (hpositions : Injective positions)
    (weights : Column → GhashField)
    (openedSecret : W → HadamardPadding Column)
    (left right : W)
    (hpublicRlc : columnCombination weights
      (openedSecret left - openedSecret right) = 0) :
    (PMF.uniformOfFintype (HadamardPadding Column)).map
        (view (hadamardOpeningEquiv Column positions hpositions)
          (columnCombination weights) openedSecret (fun _ => 0) left) =
      (PMF.uniformOfFintype (HadamardPadding Column)).map
        (view (hadamardOpeningEquiv Column positions hpositions)
          (columnCombination weights) openedSecret (fun _ => 0) right) := by
  exact column_openings_with_rlc_witness_independent
    (hadamardPaddingQueryEquiv positions hpositions) weights openedSecret
    left right hpublicRlc

section Joint

variable {LinearColumn HadamardColumn W FullView : Type*}
variable [Fintype LinearColumn] [Fintype HadamardColumn]
variable [Fintype (LinearPadding LinearColumn)]
variable [Fintype (HadamardPadding HadamardColumn)]

abbrev CodeCoins :=
  LinearPadding LinearColumn × HadamardPadding HadamardColumn

abbrev CodeView :=
  (LinearPadding LinearColumn × (QueryIndex → GhashField)) ×
    (HadamardPadding HadamardColumn × (QueryIndex → GhashField))

noncomputable def codeView
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearWeights : LinearColumn → GhashField)
    (hadamardWeights : HadamardColumn → GhashField)
    (linearSecret : W → LinearPadding LinearColumn)
    (hadamardSecret : W → HadamardPadding HadamardColumn)
    (witness : W)
    (coins : CodeCoins (LinearColumn := LinearColumn)
      (HadamardColumn := HadamardColumn)) :
    CodeView (LinearColumn := LinearColumn)
      (HadamardColumn := HadamardColumn) :=
  (view (linearOpeningEquiv shape LinearColumn linearPositions
      hlinearPositions) (columnCombination linearWeights)
      linearSecret (fun _ => 0) witness coins.1,
    view (hadamardOpeningEquiv HadamardColumn hadamardPositions
      hhadamardPositions) (columnCombination hadamardWeights)
      hadamardSecret (fun _ => 0) witness coins.2)

noncomputable def codeCoinEquiv
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearSecret : W → LinearPadding LinearColumn)
    (hadamardSecret : W → HadamardPadding HadamardColumn)
    (left right : W) :
    CodeCoins (LinearColumn := LinearColumn)
        (HadamardColumn := HadamardColumn) ≃
      CodeCoins (LinearColumn := LinearColumn)
        (HadamardColumn := HadamardColumn) :=
  Equiv.prodCongr
    (coinEquiv
      (linearOpeningEquiv shape LinearColumn linearPositions hlinearPositions)
      linearSecret left right)
    (coinEquiv
      (hadamardOpeningEquiv HadamardColumn hadamardPositions
        hhadamardPositions) hadamardSecret left right)

theorem codeView_codeCoinEquiv
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearWeights : LinearColumn → GhashField)
    (hadamardWeights : HadamardColumn → GhashField)
    (linearSecret : W → LinearPadding LinearColumn)
    (hadamardSecret : W → HadamardPadding HadamardColumn)
    (left right : W)
    (hlinear : columnCombination linearWeights
      (linearSecret left - linearSecret right) = 0)
    (hhadamard : columnCombination hadamardWeights
      (hadamardSecret left - hadamardSecret right) = 0)
    (coins : CodeCoins (LinearColumn := LinearColumn)
      (HadamardColumn := HadamardColumn)) :
    codeView shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions linearWeights hadamardWeights linearSecret
        hadamardSecret left coins =
      codeView shape linearPositions hlinearPositions hadamardPositions
        hhadamardPositions linearWeights hadamardWeights linearSecret
        hadamardSecret right
        (codeCoinEquiv shape linearPositions hlinearPositions
          hadamardPositions hhadamardPositions linearSecret hadamardSecret
          left right coins) := by
  apply Prod.ext
  · exact view_coinEquiv
      (linearOpeningEquiv shape LinearColumn linearPositions hlinearPositions)
      (columnCombination linearWeights) linearSecret (fun _ => 0) left right
      (by
        have hzero := columnCombination_inverse_eq_zero
          (linearPaddingQueryEquiv shape linearPositions hlinearPositions)
          linearWeights (linearSecret left - linearSecret right) hlinear
        simpa only [linearOpeningEquiv, add_zero] using hzero)
      coins.1
  · exact view_coinEquiv
      (hadamardOpeningEquiv HadamardColumn hadamardPositions
        hhadamardPositions)
      (columnCombination hadamardWeights) hadamardSecret (fun _ => 0)
      left right
      (by
        have hzero := columnCombination_inverse_eq_zero
          (hadamardPaddingQueryEquiv hadamardPositions hhadamardPositions)
          hadamardWeights (hadamardSecret left - hadamardSecret right)
          hhadamard
        simpa only [hadamardOpeningEquiv, add_zero] using hzero)
      coins.2

/-- Both actual VEIL padding matrices, their opened code rows, and their two
revealed padding RLCs are jointly witness independent. -/
theorem both_code_commitments_witness_independent
    (shape : BatchShape)
    (linearPositions : QueryIndex → Fin linearCodeLength)
    (hlinearPositions : Injective linearPositions)
    (hadamardPositions : QueryIndex → Fin hadamardCodeLength)
    (hhadamardPositions : Injective hadamardPositions)
    (linearWeights : LinearColumn → GhashField)
    (hadamardWeights : HadamardColumn → GhashField)
    (linearSecret : W → LinearPadding LinearColumn)
    (hadamardSecret : W → HadamardPadding HadamardColumn)
    (left right : W)
    (hlinear : columnCombination linearWeights
      (linearSecret left - linearSecret right) = 0)
    (hhadamard : columnCombination hadamardWeights
      (hadamardSecret left - hadamardSecret right) = 0)
    (continueWith : CodeView (LinearColumn := LinearColumn)
      (HadamardColumn := HadamardColumn) → FullView) :
    (PMF.uniformOfFintype
      (CodeCoins (LinearColumn := LinearColumn)
        (HadamardColumn := HadamardColumn))).map
        (fun coins => continueWith
          (codeView shape linearPositions hlinearPositions hadamardPositions
            hhadamardPositions linearWeights hadamardWeights linearSecret
            hadamardSecret left coins)) =
      (PMF.uniformOfFintype
        (CodeCoins (LinearColumn := LinearColumn)
          (HadamardColumn := HadamardColumn))).map
        (fun coins => continueWith
          (codeView shape linearPositions hlinearPositions hadamardPositions
            hhadamardPositions linearWeights hadamardWeights linearSecret
            hadamardSecret right coins)) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (codeCoinEquiv shape linearPositions hlinearPositions hadamardPositions
      hhadamardPositions linearSecret hadamardSecret left right)
  intro coins
  exact congrArg continueWith
    (codeView_codeCoinEquiv shape linearPositions hlinearPositions
      hadamardPositions hhadamardPositions linearWeights hadamardWeights
      linearSecret hadamardSecret left right hlinear hhadamard coins)

end Joint

end VeiledFlock.ProductionCodeHiding

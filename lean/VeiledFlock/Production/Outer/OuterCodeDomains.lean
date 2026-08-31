import VeiledFlock.Production.Outer.OuterPaddedPcs
import VeiledFlock.Production.Algebra.CodeDomains

/-!
# Production outer PCS code domains

The outer shielded PCS commits, lane by lane, to a rate-1/2 additive
Reed--Solomon encoding of `[mask || witness]`.  A Secure-profile L0 opening
reveals fewer rows than there are low-half mask symbols.  We choose exactly
one active mask coordinate per queried row and regard every remaining mask
coordinate as residual randomness.  This file proves that, for the literal
production field domains and every registered batch shape, the active mask
coordinates map bijectively to all opened L0 rows in all 64 lanes.
-/

namespace VeiledFlock.ProductionOuterCodeDomains

open Function
open VeiledFlock.AdditiveReedSolomon
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.ProductionCodeDomains

/-- Coordinate order after splitting the low mask half into residual and
active coordinates.  Residual mask coordinates retain their original low
indices; witness coordinates retain their original high indices; the active
mask coordinates fill the gap between them. -/
def outerBaseIndex (mask queries : ℕ) :
    Fin (2 * mask - queries) ⊕ Fin queries → ℕ
  | .inl data =>
      if data.val < mask - queries then data.val else data.val + queries
  | .inr padding => mask - queries + padding.val

theorem outerBaseIndex_lt (mask queries : ℕ) (hqueries : queries ≤ mask)
    (index : Fin (2 * mask - queries) ⊕ Fin queries) :
    outerBaseIndex mask queries index < 2 * mask := by
  cases index with
  | inl data =>
      by_cases hlow : data.val < mask - queries
      · simp [outerBaseIndex, hlow]
        omega
      · simp [outerBaseIndex, hlow]
        omega
  | inr padding =>
      simp [outerBaseIndex]
      omega

theorem outerBaseIndex_injective (mask queries : ℕ)
    (_hqueries : queries ≤ mask) :
    Injective (outerBaseIndex mask queries) := by
  intro left right heq
  cases left with
  | inl leftData =>
      cases right with
      | inl rightData =>
          by_cases hleft : leftData.val < mask - queries
          · by_cases hright : rightData.val < mask - queries
            · simp [outerBaseIndex, hleft, hright] at heq
              congr 1
              exact Fin.ext heq
            · simp [outerBaseIndex, hleft, hright] at heq
              omega
          · by_cases hright : rightData.val < mask - queries
            · simp [outerBaseIndex, hleft, hright] at heq
              omega
            · simp [outerBaseIndex, hleft, hright] at heq
              congr 1
              exact Fin.ext heq
      | inr rightPadding =>
          by_cases hleft : leftData.val < mask - queries
          · simp [outerBaseIndex, hleft] at heq
            omega
          · simp [outerBaseIndex, hleft] at heq
            omega
  | inr leftPadding =>
      cases right with
      | inl rightData =>
          by_cases hright : rightData.val < mask - queries
          · simp [outerBaseIndex, hright] at heq
            omega
          · simp [outerBaseIndex, hright] at heq
            omega
      | inr rightPadding =>
          simp [outerBaseIndex] at heq
          congr 1
          exact Fin.ext heq

/-- Concrete field point for the reordered complete message domain. -/
noncomputable def outerBasePoint (mask queries : ℕ)
    (index : Fin (2 * mask - queries) ⊕ Fin queries) : GhashField :=
  bitsGhashEquiv (BitVec.ofNat 128 (outerBaseIndex mask queries index))

private theorem bitVecOfNat_eq_of_lt {left right : ℕ}
    (hleft : left < 2 ^ 128) (hright : right < 2 ^ 128)
    (heq : BitVec.ofNat 128 left = BitVec.ofNat 128 right) :
    left = right := by
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hnat
  exact hnat

theorem outerBasePoint_injective (mask queries baseLog : ℕ)
    (hqueries : queries ≤ mask) (htotal : 2 * mask ≤ 2 ^ baseLog)
    (hlog : baseLog ≤ 128) :
    Injective (outerBasePoint mask queries) := by
  intro left right heq
  apply outerBaseIndex_injective mask queries hqueries
  apply bitVecOfNat_eq_of_lt
  · exact lt_of_lt_of_le (outerBaseIndex_lt mask queries hqueries left)
      (htotal.trans (Nat.pow_le_pow_right (by decide) hlog))
  · exact lt_of_lt_of_le (outerBaseIndex_lt mask queries hqueries right)
      (htotal.trans (Nat.pow_le_pow_right (by decide) hlog))
  · exact bitsGhashEquiv.injective heq

theorem outerBasePoint_ne_outputPoint
    (mask queries baseLog codeLog : ℕ)
    (hqueries : queries ≤ mask) (htotal : 2 * mask ≤ 2 ^ baseLog)
    (hlogs : baseLog ≤ codeLog) (hcode : codeLog < 128)
    (data : Fin (2 * mask - queries))
    (query : Fin (2 ^ codeLog)) :
    outerBasePoint mask queries (Sum.inl data) ≠ outputPoint codeLog query := by
  intro heq
  have hbase : outerBaseIndex mask queries (Sum.inl data) < 2 ^ codeLog :=
    lt_of_lt_of_le (outerBaseIndex_lt mask queries hqueries (Sum.inl data))
      (htotal.trans (Nat.pow_le_pow_right (by decide) hlogs))
  have hleft : outerBaseIndex mask queries (Sum.inl data) < 2 ^ 128 :=
    lt_of_lt_of_le hbase
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hcode))
  have hright : 2 ^ codeLog + query.val < 2 ^ 128 := by
    have : 2 ^ codeLog + query.val < 2 ^ (codeLog + 1) := by
      rw [pow_succ]
      omega
    exact lt_of_lt_of_le this
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hnat := bitVecOfNat_eq_of_lt hleft hright
    (bitsGhashEquiv.injective heq)
  omega

abbrev QueryIndex (shape : BatchShape) := Fin (outerL0QueryCount shape)
abbrev LaneIndex := Fin outerLaneCount
abbrev CodeIndex (shape : BatchShape) := Fin (outerCodePositions shape)
abbrev ActivePadding (shape : BatchShape) :=
  QueryIndex shape → LaneIndex → GhashField
abbrev OpenedRows (shape : BatchShape) :=
  QueryIndex shape → LaneIndex → GhashField
abbrev EncodedWord (shape : BatchShape) :=
  CodeIndex shape → LaneIndex → GhashField

private theorem productionBaseFits (shape : BatchShape) :
    2 * outerMaskSymbolsPerLane shape ≤ 2 ^ (m shape - 12) := by
  rw [← outerMessagePositions_eq_pow]
  rfl

private theorem productionBaseLog_le_codeLog (shape : BatchShape) :
    m shape - 12 ≤ m shape - 11 := by
  cases shape <;> decide

private theorem productionBase_injective (shape : BatchShape) :
    Injective (outerBasePoint (outerMaskSymbolsPerLane shape)
      (outerL0QueryCount shape)) :=
  outerBasePoint_injective _ _ _ (outerL0QueryCount_le_maskSymbols shape)
    (productionBaseFits shape) (by cases shape <;> decide)

private theorem productionData_output_disjoint (shape : BatchShape)
    (data : Fin (2 * outerMaskSymbolsPerLane shape - outerL0QueryCount shape))
    (query : Fin (2 ^ (m shape - 11))) :
    outerBasePoint (outerMaskSymbolsPerLane shape)
        (outerL0QueryCount shape) (Sum.inl data) ≠
      outputPoint (m shape - 11) query :=
  outerBasePoint_ne_outputPoint _ _ _ _
    (outerL0QueryCount_le_maskSymbols shape) (productionBaseFits shape)
    (productionBaseLog_le_codeLog shape) (outerCodeLog_lt_128 shape) data query

private noncomputable def castCodeIndex (shape : BatchShape) :
    CodeIndex shape ≃ Fin (2 ^ (m shape - 11)) :=
  finCongr (outerCodePositions_eq_pow shape)

/-- Encode one lane's active low-half mask contribution over the complete
production rate-1/2 output domain. -/
noncomputable def singleLanePaddingEmbed (shape : BatchShape) :
    (QueryIndex shape → GhashField) →ₗ[GhashField]
      (CodeIndex shape → GhashField) where
  toFun padding position :=
    (polynomialFromPadding
      (outerBasePoint (outerMaskSymbolsPerLane shape)
        (outerL0QueryCount shape))
      (productionBase_injective shape) padding).1.eval
        (outputPoint (m shape - 11) (castCodeIndex shape position))
  map_add' left right := by
    funext position
    simp
  map_smul' scalar padding := by
    funext position
    simp

def singleLaneOpening (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape) :
    (CodeIndex shape → GhashField) →ₗ[GhashField]
      (QueryIndex shape → GhashField) where
  toFun word query := word (positions query)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact one-lane active-padding/opened-row equivalence. -/
noncomputable def singleLanePaddingEquiv (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape)
    (hpositions : Injective positions) :
    (QueryIndex shape → GhashField) ≃ₗ[GhashField]
      (QueryIndex shape → GhashField) := by
  letI : Nonempty (QueryIndex shape) :=
    ⟨⟨0, outerL0QueryCount_positive shape⟩⟩
  exact AdditiveReedSolomon.paddingQueryEquiv
    (outerBasePoint (outerMaskSymbolsPerLane shape)
      (outerL0QueryCount shape))
    (productionBase_injective shape)
    (fun query => outputPoint (m shape - 11)
      (castCodeIndex shape (positions query)))
    ((outputPoint_injective (m shape - 11)
      (outerCodeLog_lt_128 shape)).comp
        ((castCodeIndex shape).injective.comp hpositions))
    (fun data query => productionData_output_disjoint shape data
      (castCodeIndex shape (positions query)))

@[simp]
theorem singleLane_opening_paddingEmbed (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape)
    (hpositions : Injective positions)
    (padding : QueryIndex shape → GhashField) :
    singleLaneOpening shape positions (singleLanePaddingEmbed shape padding) =
      singleLanePaddingEquiv shape positions hpositions padding := by
  rfl

/-- Swap row-major and lane-major views without changing any scalar. -/
def transpose (Left Right : Type*) :
    (Left → Right → GhashField) ≃ₗ[GhashField]
      (Right → Left → GhashField) where
  toFun values right left := values left right
  invFun values left right := values right left
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Encode all 64 active-padding lanes exactly as the production wide NTT. -/
noncomputable def outerPaddingEmbed (shape : BatchShape) :
    ActivePadding shape →ₗ[GhashField] EncodedWord shape where
  toFun padding position lane :=
    singleLanePaddingEmbed shape (fun query => padding query lane) position
  map_add' left right := by
    funext position lane
    change
      singleLanePaddingEmbed shape (fun query =>
          left query lane + right query lane) position =
        singleLanePaddingEmbed shape (fun query => left query lane) position +
          singleLanePaddingEmbed shape (fun query => right query lane) position
    have hadd : (fun query => left query lane + right query lane) =
        (fun query => left query lane) + (fun query => right query lane) := by
      funext query
      rfl
    rw [hadd]
    exact congrFun ((singleLanePaddingEmbed shape).map_add
      (fun query => left query lane) (fun query => right query lane)) position
  map_smul' scalar padding := by
    funext position lane
    change
      singleLanePaddingEmbed shape (fun query =>
          scalar * padding query lane) position =
        scalar * singleLanePaddingEmbed shape
          (fun query => padding query lane) position
    have hsmul : (fun query => scalar * padding query lane) =
        scalar • (fun query => padding query lane) := by
      funext query
      rfl
    rw [hsmul]
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun
      ((singleLanePaddingEmbed shape).map_smul scalar
        (fun query => padding query lane)) position

/-- Select all fields in the distinct raw L0 rows. -/
def outerOpening (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape) :
    EncodedWord shape →ₗ[GhashField] OpenedRows shape where
  toFun word query lane := word (positions query) lane
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Product of the 64 independent lane equivalences, in production row-major
layout. -/
noncomputable def outerPaddingQueryEquiv (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape)
    (hpositions : Injective positions) :
    ActivePadding shape ≃ₗ[GhashField] OpenedRows shape :=
  (transpose (QueryIndex shape) LaneIndex).trans
    ((LinearEquiv.piCongrRight fun _ : LaneIndex =>
      singleLanePaddingEquiv shape positions hpositions).trans
        (transpose LaneIndex (QueryIndex shape)))

/-- The exact premise required by `ProductionOuterPaddedPcs`: opening the
active mask's production encoding is the concrete padding equivalence. -/
theorem outerOpening_paddingEmbed (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape)
    (hpositions : Injective positions) (padding : ActivePadding shape) :
    outerOpening shape positions (outerPaddingEmbed shape padding) =
      outerPaddingQueryEquiv shape positions hpositions padding := by
  funext query lane
  rfl

/-! `ProductionOuterPaddedPcs` indexes the whole encoded word by one type.
The following zero-cost reshaping equivalence turns the production row/lane
layout into that flat index without changing any field value. -/

abbrev FlatIndex (shape : BatchShape) := CodeIndex shape × LaneIndex
abbrev FlatEncodedWord (shape : BatchShape) := FlatIndex shape → GhashField

def flattenWord (shape : BatchShape) :
    EncodedWord shape ≃ₗ[GhashField] FlatEncodedWord shape where
  toFun word index := word index.1 index.2
  invFun word position lane := word (position, lane)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def flatPaddingEmbed (shape : BatchShape) :
    ActivePadding shape →ₗ[GhashField] FlatEncodedWord shape :=
  (flattenWord shape).toLinearMap.comp (outerPaddingEmbed shape)

def flatOpening (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape) :
    FlatEncodedWord shape →ₗ[GhashField] OpenedRows shape where
  toFun word query lane := word (positions query, lane)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatOpening_paddingEmbed (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape)
    (hpositions : Injective positions) (padding : ActivePadding shape) :
    flatOpening shape positions (flatPaddingEmbed shape padding) =
      outerPaddingQueryEquiv shape positions hpositions padding := by
  exact outerOpening_paddingEmbed shape positions hpositions padding

/-! ## Faithful base-message representation

Rust samples `[mask || witness]` and `g` before the additive NTT.  The outer
PCS theorem therefore uses the following split base index as its `I`: the
first summand contains residual-mask and witness coordinates, while the second
summand contains the active low-mask coordinates.  `outerBaseIndex` is the
proved permutation back to Rust's flat `[mask || witness]` order. -/

abbrev ResidualDataIndex (shape : BatchShape) :=
  Fin (2 * outerMaskSymbolsPerLane shape - outerL0QueryCount shape)
abbrev SplitBaseIndex (shape : BatchShape) :=
  ResidualDataIndex shape ⊕ QueryIndex shape
abbrev BaseScalarIndex (shape : BatchShape) :=
  SplitBaseIndex shape × LaneIndex
abbrev BaseWord (shape : BatchShape) := BaseScalarIndex shape → GhashField

/-- Insert active low-mask values into the second summand, leaving all
residual-mask and witness coordinates zero. -/
noncomputable def basePaddingEmbed (shape : BatchShape) :
    ActivePadding shape →ₗ[GhashField] BaseWord shape where
  toFun padding index :=
    match index.1 with
    | .inl _ => 0
    | .inr query => padding query index.2
  map_add' left right := by
    funext index
    rcases index with ⟨index, lane⟩
    cases index <;> simp
  map_smul' scalar padding := by
    funext index
    rcases index with ⟨index, lane⟩
    cases index <;> simp

@[simp]
theorem basePaddingEmbed_data (shape : BatchShape)
    (padding : ActivePadding shape) (data : ResidualDataIndex shape)
    (lane : LaneIndex) :
    basePaddingEmbed shape padding (Sum.inl data, lane) = 0 := rfl

@[simp]
theorem basePaddingEmbed_padding (shape : BatchShape)
    (padding : ActivePadding shape) (query : QueryIndex shape)
    (lane : LaneIndex) :
    basePaddingEmbed shape padding (Sum.inr query, lane) =
      padding query lane := rfl

/-- Literal lane-wise production additive-RS encoder from the split base
message to all rate-1/2 output coordinates. -/
noncomputable def encodeBaseWord (shape : BatchShape) :
    BaseWord shape →ₗ[GhashField] EncodedWord shape where
  toFun values position lane :=
    ((evaluationEquiv
      (outerBasePoint (outerMaskSymbolsPerLane shape)
        (outerL0QueryCount shape))
      (productionBase_injective shape)).symm
        (fun index => values (index, lane))).1.eval
      (outputPoint (m shape - 11) (castCodeIndex shape position))
  map_add' left right := by
    funext position lane
    simp only [Pi.add_apply]
    have hinput :
        (fun index => left (index, lane) + right (index, lane)) =
          (fun index => left (index, lane)) +
            (fun index => right (index, lane)) := rfl
    rw [hinput]
    rw [map_add]
    exact Polynomial.eval_add
  map_smul' scalar values := by
    funext position lane
    simp only [Pi.smul_apply, RingHom.id_apply]
    have hinput :
        (fun index => scalar • values (index, lane)) =
          scalar • (fun index => values (index, lane)) := rfl
    rw [hinput]
    rw [map_smul]
    exact Polynomial.eval_smul scalar _ _

/-- Encode the base message and select the complete distinct L0 row set. -/
noncomputable def baseOpening (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape) :
    BaseWord shape →ₗ[GhashField] OpenedRows shape :=
  (outerOpening shape positions).comp (encodeBaseWord shape)

@[simp]
theorem encodeBaseWord_basePaddingEmbed (shape : BatchShape)
    (padding : ActivePadding shape) :
    encodeBaseWord shape (basePaddingEmbed shape padding) =
      outerPaddingEmbed shape padding := by
  funext position lane
  apply congrArg (fun polynomial :
      Polynomial.degreeLT GhashField
        (Fintype.card (SplitBaseIndex shape)) =>
      polynomial.1.eval
        (outputPoint (m shape - 11) (castCodeIndex shape position)))
  change
    (evaluationEquiv
        (outerBasePoint (outerMaskSymbolsPerLane shape)
          (outerL0QueryCount shape))
        (productionBase_injective shape)).symm
      (fun index => basePaddingEmbed shape padding (index, lane)) =
    polynomialFromPadding
      (outerBasePoint (outerMaskSymbolsPerLane shape)
        (outerL0QueryCount shape))
      (productionBase_injective shape) (fun query => padding query lane)
  change
    (evaluationEquiv
        (outerBasePoint (outerMaskSymbolsPerLane shape)
          (outerL0QueryCount shape))
        (productionBase_injective shape)).symm
      (fun index => basePaddingEmbed shape padding (index, lane)) =
    (evaluationEquiv
        (outerBasePoint (outerMaskSymbolsPerLane shape)
          (outerL0QueryCount shape))
        (productionBase_injective shape)).symm
      (paddingValues (fun query => padding query lane))
  apply congrArg (evaluationEquiv
    (outerBasePoint (outerMaskSymbolsPerLane shape)
      (outerL0QueryCount shape))
    (productionBase_injective shape)).symm
  funext index
  cases index <;> rfl

/-- Faithful base-domain form of the active-padding equivalence used by the
corrected outer PCS theorem. -/
theorem baseOpening_paddingEmbed (shape : BatchShape)
    (positions : QueryIndex shape → CodeIndex shape)
    (hpositions : Injective positions) (padding : ActivePadding shape) :
    baseOpening shape positions (basePaddingEmbed shape padding) =
      outerPaddingQueryEquiv shape positions hpositions padding := by
  rw [baseOpening, LinearMap.comp_apply, encodeBaseWord_basePaddingEmbed]
  exact outerOpening_paddingEmbed shape positions hpositions padding

end VeiledFlock.ProductionOuterCodeDomains

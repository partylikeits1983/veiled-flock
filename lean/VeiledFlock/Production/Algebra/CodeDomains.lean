import VeiledFlock.Algebra.AdditiveReedSolomon
import VeiledFlock.Concrete.ConcreteParameters
import VeiledFlock.Algebra.Field128Serialization
import VeiledFlock.Algebra.ReedSolomonDecomposition

/-!
# Production additive-RS domains

`veil-f128/src/ntt.rs` evaluates messages on the binary span of basis elements
`0 .. baseLog-1` and codewords on the affine coset obtained by adding basis
element `codeLog`.  In the concrete polynomial-basis field representation,
these are respectively the integers below `2^baseLog` and the integers in
`[2^codeLog, 2^(codeLog+1))`.  This file proves exact injectivity and
disjointness, then instantiates the Reed--Solomon padding equivalence for both
production VEIL commitments.
-/

namespace VeiledFlock.ProductionCodeDomains

set_option maxHeartbeats 600000

open Function
open VeiledFlock.AdditiveReedSolomon
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization

/-- Logical coordinates precede random padding coordinates in the Rust
message vector. -/
def baseIndex (logical padding : ℕ) : Fin logical ⊕ Fin padding → ℕ
  | .inl index => index.val
  | .inr index => logical + index.val

theorem baseIndex_lt (logical padding : ℕ)
    (index : Fin logical ⊕ Fin padding) :
    baseIndex logical padding index < logical + padding := by
  cases index <;> simp [baseIndex] ; omega

theorem baseIndex_injective (logical padding : ℕ) :
    Function.Injective (baseIndex logical padding) := by
  intro left right heq
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          congr 1
          exact Fin.ext heq
      | inr right =>
          simp [baseIndex] at heq
          omega
  | inr left =>
      cases right with
      | inl right =>
          simp [baseIndex] at heq
          omega
      | inr right =>
          congr 1
          apply Fin.ext
          simp [baseIndex] at heq
          omega

/-- Exact base-domain point represented by the first standard polynomial
basis elements. -/
noncomputable def basePoint (logical padding : ℕ)
    (index : Fin logical ⊕ Fin padding) : GhashField :=
  bitsGhashEquiv (BitVec.ofNat 128 (baseIndex logical padding index))

/-- Exact output-coset point `basis[codeLog] + span(basis[..codeLog])`.
Because the span index is smaller than `2^codeLog`, integer addition and
bitwise XOR coincide here. -/
noncomputable def outputPoint (codeLog : ℕ) (index : Fin (2 ^ codeLog)) :
    GhashField :=
  bitsGhashEquiv (BitVec.ofNat 128 (2 ^ codeLog + index.val))

private theorem bitVecOfNat_eq_of_lt {left right : ℕ}
    (hleft : left < 2 ^ 128) (hright : right < 2 ^ 128)
    (heq : BitVec.ofNat 128 left = BitVec.ofNat 128 right) :
    left = right := by
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hnat
  exact hnat

theorem basePoint_injective (logical padding baseLog : ℕ)
    (htotal : logical + padding ≤ 2 ^ baseLog) (hlog : baseLog ≤ 128) :
    Function.Injective (basePoint logical padding) := by
  intro left right heq
  apply baseIndex_injective logical padding
  apply bitVecOfNat_eq_of_lt
  · exact lt_of_lt_of_le (baseIndex_lt logical padding left)
      (htotal.trans (Nat.pow_le_pow_right (by decide) hlog))
  · exact lt_of_lt_of_le (baseIndex_lt logical padding right)
      (htotal.trans (Nat.pow_le_pow_right (by decide) hlog))
  · exact bitsGhashEquiv.injective heq

theorem outputPoint_injective (codeLog : ℕ) (hlog : codeLog < 128) :
    Function.Injective (outputPoint codeLog) := by
  intro left right heq
  apply Fin.ext
  have hsum := bitVecOfNat_eq_of_lt
    (left := 2 ^ codeLog + left.val)
    (right := 2 ^ codeLog + right.val) (by
      have : 2 ^ codeLog + left.val < 2 ^ (codeLog + 1) := by
        rw [pow_succ]
        omega
      exact lt_of_lt_of_le this
        (Nat.pow_le_pow_right (by decide) (by omega))) (by
      have : 2 ^ codeLog + right.val < 2 ^ (codeLog + 1) := by
        rw [pow_succ]
        omega
      exact lt_of_lt_of_le this
        (Nat.pow_le_pow_right (by decide) (by omega)))
    (bitsGhashEquiv.injective heq)
  omega

/-- The production interpolation domain and output coset cannot intersect:
the former is below `2^codeLog`, while the latter has bit `codeLog` set. -/
theorem basePoint_ne_outputPoint (logical padding baseLog codeLog : ℕ)
    (htotal : logical + padding ≤ 2 ^ baseLog)
    (hlogs : baseLog ≤ codeLog) (hcode : codeLog < 128)
    (data : Fin logical) (query : Fin (2 ^ codeLog)) :
    basePoint logical padding (Sum.inl data) ≠ outputPoint codeLog query := by
  intro heq
  have hbase : baseIndex logical padding (Sum.inl data) < 2 ^ codeLog :=
    lt_of_lt_of_le (baseIndex_lt logical padding (Sum.inl data))
      (htotal.trans (Nat.pow_le_pow_right (by decide) hlogs))
  have hleft : baseIndex logical padding (Sum.inl data) < 2 ^ 128 :=
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

/-- Exact production specialization of the abstract RS hiding theorem. -/
noncomputable def paddingQueryEquiv (logical padding baseLog codeLog : ℕ)
    (hpadding : 0 < padding)
    (htotal : logical + padding ≤ 2 ^ baseLog)
    (hlogs : baseLog ≤ codeLog) (hcode : codeLog < 128)
    (positions : Fin padding → Fin (2 ^ codeLog))
    (hpositions : Injective positions) :
    (Fin padding → GhashField) ≃ₗ[GhashField]
      (Fin padding → GhashField) := by
  letI : Nonempty (Fin padding) := ⟨⟨0, hpadding⟩⟩
  exact AdditiveReedSolomon.paddingQueryEquiv
    (basePoint logical padding)
    (basePoint_injective logical padding baseLog htotal
      (hlogs.trans (Nat.le_of_lt hcode)))
    (fun index => outputPoint codeLog (positions index))
    ((outputPoint_injective codeLog hcode).comp hpositions)
    (fun data query => basePoint_ne_outputPoint logical padding baseLog codeLog
      htotal hlogs hcode data (positions query))

/-! ## Exact next-power-of-two interpolation domain

`AdditiveRsCode::encode` appends fixed zero evaluations after the logical and
random-padding coordinates until the base-domain length is a power of two.
The following domain keeps those tail coordinates explicit.  Their order is
exactly Rust's `[logical || random padding || zero tail]`. -/

abbrev CapacityData (logical padding capacity : ℕ) :=
  Fin logical ⊕ Fin (capacity - logical - padding)

def capacityBaseIndex (logical padding capacity : ℕ) :
    CapacityData logical padding capacity ⊕ Fin padding → ℕ
  | .inl (.inl index) => index.val
  | .inr index => logical + index.val
  | .inl (.inr index) => logical + padding + index.val

theorem capacityBaseIndex_lt (logical padding capacity : ℕ)
    (htotal : logical + padding ≤ capacity)
    (index : CapacityData logical padding capacity ⊕ Fin padding) :
    capacityBaseIndex logical padding capacity index < capacity := by
  rcases index with (⟨index | index⟩ | index)
  · simp only [capacityBaseIndex]
    omega
  · simp only [capacityBaseIndex]
    omega
  · simp only [capacityBaseIndex]
    omega

theorem capacityBaseIndex_injective (logical padding capacity : ℕ)
    (_htotal : logical + padding ≤ capacity) :
    Function.Injective (capacityBaseIndex logical padding capacity) := by
  intro left right heq
  rcases left with (⟨left | left⟩ | left) <;>
    rcases right with (⟨right | right⟩ | right) <;>
    simp only [capacityBaseIndex] at heq
  · congr 2
    exact Fin.ext heq
  · omega
  · omega
  · omega
  · congr 2
    apply Fin.ext
    omega
  · omega
  · omega
  · omega
  · congr 1
    apply Fin.ext
    omega

noncomputable def capacityBasePoint (logical padding baseLog : ℕ)
    (index : CapacityData logical padding (2 ^ baseLog) ⊕ Fin padding) :
    GhashField :=
  bitsGhashEquiv
    (BitVec.ofNat 128 (capacityBaseIndex logical padding (2 ^ baseLog) index))

theorem capacityBasePoint_injective (logical padding baseLog : ℕ)
    (htotal : logical + padding ≤ 2 ^ baseLog) (hlog : baseLog ≤ 128) :
    Function.Injective (capacityBasePoint logical padding baseLog) := by
  intro left right heq
  apply capacityBaseIndex_injective logical padding (2 ^ baseLog) htotal
  apply bitVecOfNat_eq_of_lt
  · exact lt_of_lt_of_le (capacityBaseIndex_lt _ _ _ htotal left)
      (Nat.pow_le_pow_right (by decide) hlog)
  · exact lt_of_lt_of_le (capacityBaseIndex_lt _ _ _ htotal right)
      (Nat.pow_le_pow_right (by decide) hlog)
  · exact bitsGhashEquiv.injective heq

theorem capacityBasePoint_ne_outputPoint
    (logical padding baseLog codeLog : ℕ)
    (htotal : logical + padding ≤ 2 ^ baseLog)
    (hlogs : baseLog ≤ codeLog) (hcode : codeLog < 128)
    (data : CapacityData logical padding (2 ^ baseLog))
    (query : Fin (2 ^ codeLog)) :
    capacityBasePoint logical padding baseLog (Sum.inl data) ≠
      outputPoint codeLog query := by
  intro heq
  have hbase :
      capacityBaseIndex logical padding (2 ^ baseLog) (Sum.inl data) <
        2 ^ codeLog :=
    lt_of_lt_of_le (capacityBaseIndex_lt _ _ _ htotal (Sum.inl data))
      (Nat.pow_le_pow_right (by decide) hlogs)
  have hleft :
      capacityBaseIndex logical padding (2 ^ baseLog) (Sum.inl data) <
        2 ^ 128 :=
    lt_of_lt_of_le hbase
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hcode))
  have hright : 2 ^ codeLog + query.val < 2 ^ 128 := by
    have hnext : 2 ^ codeLog + query.val < 2 ^ (codeLog + 1) := by
      rw [pow_succ]
      omega
    exact lt_of_lt_of_le hnext
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hnat := bitVecOfNat_eq_of_lt hleft hright
    (bitsGhashEquiv.injective heq)
  omega

/-- Exact padding-to-query equivalence for the power-of-two base domain used
by Rust, including its fixed zero tail. -/
noncomputable def capacityPaddingQueryEquiv
    (logical padding baseLog codeLog : ℕ)
    (hpadding : 0 < padding)
    (htotal : logical + padding ≤ 2 ^ baseLog)
    (hlogs : baseLog ≤ codeLog) (hcode : codeLog < 128)
    (positions : Fin padding → Fin (2 ^ codeLog))
    (hpositions : Injective positions) :
    (Fin padding → GhashField) ≃ₗ[GhashField]
      (Fin padding → GhashField) := by
  letI : Nonempty (Fin padding) := ⟨⟨0, hpadding⟩⟩
  exact AdditiveReedSolomon.paddingQueryEquiv
    (capacityBasePoint logical padding baseLog)
    (capacityBasePoint_injective logical padding baseLog htotal
      (hlogs.trans (Nat.le_of_lt hcode)))
    (fun index => outputPoint codeLog (positions index))
    ((outputPoint_injective codeLog hcode).comp hpositions)
    (fun data query => capacityBasePoint_ne_outputPoint logical padding
      baseLog codeLog htotal hlogs hcode data (positions query))

/-- Embed the committed logical vector into the data coordinates of the
power-of-two interpolation domain; every tail coordinate is fixed to zero. -/
noncomputable def logicalDataValues (logical padding capacity : ℕ) :
    (Fin logical → GhashField) →ₗ[GhashField]
      (CapacityData logical padding capacity → GhashField) where
  toFun values := Sum.elim values (fun _ => 0)
  map_add' left right := by
    funext index
    cases index <;> simp
  map_smul' scalar values := by
    funext index
    cases index <;> simp

/-- Full additive-Reed--Solomon codeword produced from the literal Rust base
layout `[logical || random padding || zero tail]`.  Existing hiding lemmas
only needed projections at queried positions; the production experiment also
needs the complete rows consumed by the Merkle constructor. -/
noncomputable def capacityCodeword
    (logical padding baseLog codeLog : ℕ)
    (htotal : logical + padding ≤ 2 ^ baseLog)
    (hlogs : baseLog ≤ codeLog) (hcode : codeLog < 128)
    (logicalValues : Fin logical → GhashField)
    (paddingValues : Fin padding → GhashField) :
    Fin (2 ^ codeLog) → GhashField :=
  let data := logicalDataValues logical padding (2 ^ baseLog) logicalValues
  let values :
      CapacityData logical padding (2 ^ baseLog) ⊕ Fin padding →
        GhashField :=
    Sum.elim data paddingValues
  let polynomial :=
    (VeiledFlock.AdditiveReedSolomon.evaluationEquiv
      (capacityBasePoint logical padding baseLog)
      (capacityBasePoint_injective logical padding baseLog htotal
        (hlogs.trans (Nat.le_of_lt hcode)))).symm values
  fun index ↦ polynomial.1.eval (outputPoint codeLog index)

/-! ## Registered production geometries -/

def linearLogicalLength (shape : BatchShape) : ℕ :=
  expectedMasks shape + 6

def hadamardLogicalLength : ℕ := paddedMultiplications

theorem linearMessageFits (shape : BatchShape) :
    linearLogicalLength shape + veilQueryCount ≤ 2 ^ 10 := by
  cases shape <;> decide

theorem hadamardMessageFits :
    hadamardLogicalLength + veilQueryCount ≤ 2 ^ 8 := by
  decide

/-- Complete 8,192-coordinate linear VEIL codeword. -/
noncomputable def linearCodeword (shape : BatchShape)
    (logicalValues : Fin (linearLogicalLength shape) → GhashField)
    (paddingValues : Fin veilQueryCount → GhashField) :
    Fin linearCodeLength → GhashField :=
  let castPosition : Fin linearCodeLength ≃ Fin (2 ^ 13) :=
    finCongr (by decide)
  fun index ↦ capacityCodeword (linearLogicalLength shape) veilQueryCount
    10 13 (linearMessageFits shape) (by decide) (by decide)
    logicalValues paddingValues (castPosition index)

/-- Complete 2,048-coordinate Hadamard VEIL codeword. -/
noncomputable def hadamardCodeword
    (logicalValues : Fin hadamardLogicalLength → GhashField)
    (paddingValues : Fin veilQueryCount → GhashField) :
    Fin hadamardCodeLength → GhashField :=
  let castPosition : Fin hadamardCodeLength ≃ Fin (2 ^ 11) :=
    finCongr (by decide)
  fun index ↦ capacityCodeword hadamardLogicalLength veilQueryCount 8 11
    hadamardMessageFits (by decide) (by decide) logicalValues paddingValues
    (castPosition index)

/-- The exact 160-dimensional padding-to-opening map for the 8,192-coordinate
linear commitment is a linear equivalence for every registered batch. -/
noncomputable def linearPaddingQueryEquiv (shape : BatchShape)
    (positions : Fin veilQueryCount → Fin linearCodeLength)
    (hpositions : Injective positions) :
    (Fin veilQueryCount → GhashField) ≃ₗ[GhashField]
      (Fin veilQueryCount → GhashField) := by
  change (Fin veilQueryCount → GhashField) ≃ₗ[GhashField]
    (Fin veilQueryCount → GhashField)
  have hcode : linearCodeLength = 2 ^ 13 := by decide
  let castPosition : Fin linearCodeLength ≃ Fin (2 ^ 13) := finCongr hcode
  let concretePositions := fun index => castPosition (positions index)
  exact capacityPaddingQueryEquiv (linearLogicalLength shape)
    veilQueryCount 10 13
    (by decide) (linearMessageFits shape) (by decide) (by decide)
    concretePositions (castPosition.injective.comp hpositions)

/-- The exact 160-dimensional padding-to-opening map for the 2,048-coordinate
Hadamard commitment is a linear equivalence. -/
noncomputable def hadamardPaddingQueryEquiv
    (positions : Fin veilQueryCount → Fin hadamardCodeLength)
    (hpositions : Injective positions) :
    (Fin veilQueryCount → GhashField) ≃ₗ[GhashField]
      (Fin veilQueryCount → GhashField) := by
  change (Fin veilQueryCount → GhashField) ≃ₗ[GhashField]
    (Fin veilQueryCount → GhashField)
  have hcode : hadamardCodeLength = 2 ^ 11 := by decide
  let castPosition : Fin hadamardCodeLength ≃ Fin (2 ^ 11) := finCongr hcode
  let concretePositions := fun index => castPosition (positions index)
  exact capacityPaddingQueryEquiv hadamardLogicalLength veilQueryCount 8 11
    (by decide) hadamardMessageFits (by decide) (by decide)
    concretePositions (castPosition.injective.comp hpositions)

/-- Deterministic contribution of the shifted-circuit witness to the 160
opened coordinates of the production linear code. -/
noncomputable def linearDataToQueries (shape : BatchShape)
    (positions : Fin veilQueryCount → Fin linearCodeLength) :
    (Fin (linearLogicalLength shape) → GhashField) →ₗ[GhashField]
      (Fin veilQueryCount → GhashField) := by
  have hbase := capacityBasePoint_injective (linearLogicalLength shape)
    veilQueryCount 10 (linearMessageFits shape) (by decide)
  exact (VeiledFlock.ReedSolomonDecomposition.dataToQueries
    (capacityBasePoint (linearLogicalLength shape) veilQueryCount 10) hbase
    (fun index => outputPoint 13
      (finCongr (by decide : linearCodeLength = 2 ^ 13)
        (positions index)))).comp
      (logicalDataValues (linearLogicalLength shape) veilQueryCount (2 ^ 10))

/-- Deterministic contribution of the three padded multiplication rows to the
160 opened coordinates of the production Hadamard base code. -/
noncomputable def hadamardDataToQueries
    (positions : Fin veilQueryCount → Fin hadamardCodeLength) :
    (Fin hadamardLogicalLength → GhashField) →ₗ[GhashField]
      (Fin veilQueryCount → GhashField) := by
  have hbase := capacityBasePoint_injective hadamardLogicalLength
    veilQueryCount 8 hadamardMessageFits (by decide)
  exact (VeiledFlock.ReedSolomonDecomposition.dataToQueries
    (capacityBasePoint hadamardLogicalLength veilQueryCount 8) hbase
    (fun index => outputPoint 11
      (finCongr (by decide : hadamardCodeLength = 2 ^ 11)
        (positions index)))).comp
      (logicalDataValues hadamardLogicalLength veilQueryCount (2 ^ 8))

/-- Full linear-code query values split exactly into data and padding
contributions. -/
theorem linearValuesToQueries_decompose (shape : BatchShape)
    (positions : Fin veilQueryCount → Fin linearCodeLength)
    (data : Fin (linearLogicalLength shape) → GhashField)
    (padding : Fin veilQueryCount → GhashField) :
    let hbase := capacityBasePoint_injective (linearLogicalLength shape)
      veilQueryCount 10 (linearMessageFits shape) (by decide)
    let queries := fun index => outputPoint 13
      (finCongr (by decide : linearCodeLength = 2 ^ 13) (positions index))
    VeiledFlock.ReedSolomonDecomposition.valuesToQueries
        (capacityBasePoint (linearLogicalLength shape) veilQueryCount 10)
        hbase queries
        (logicalDataValues (linearLogicalLength shape) veilQueryCount
          (2 ^ 10) data, padding) =
      linearDataToQueries shape positions data +
        AdditiveReedSolomon.paddingToQueries
          (capacityBasePoint (linearLogicalLength shape) veilQueryCount 10)
          hbase queries
          padding := by
  dsimp only
  exact VeiledFlock.ReedSolomonDecomposition.valuesToQueries_decompose
    _ _ _
    (logicalDataValues (linearLogicalLength shape) veilQueryCount (2 ^ 10)
      data)
    padding

/-- Full Hadamard-code query values split exactly into data and padding
contributions. -/
theorem hadamardValuesToQueries_decompose
    (positions : Fin veilQueryCount → Fin hadamardCodeLength)
    (data : Fin hadamardLogicalLength → GhashField)
    (padding : Fin veilQueryCount → GhashField) :
    let hbase := capacityBasePoint_injective hadamardLogicalLength
      veilQueryCount 8 hadamardMessageFits (by decide)
    let queries := fun index => outputPoint 11
      (finCongr (by decide : hadamardCodeLength = 2 ^ 11) (positions index))
    VeiledFlock.ReedSolomonDecomposition.valuesToQueries
        (capacityBasePoint hadamardLogicalLength veilQueryCount 8) hbase
        queries
        (logicalDataValues hadamardLogicalLength veilQueryCount (2 ^ 8) data,
          padding) =
      hadamardDataToQueries positions data +
        AdditiveReedSolomon.paddingToQueries
          (capacityBasePoint hadamardLogicalLength veilQueryCount 8) hbase
          queries
          padding := by
  dsimp only
  exact VeiledFlock.ReedSolomonDecomposition.valuesToQueries_decompose
    _ _ _
    (logicalDataValues hadamardLogicalLength veilQueryCount (2 ^ 8) data)
    padding

end VeiledFlock.ProductionCodeDomains

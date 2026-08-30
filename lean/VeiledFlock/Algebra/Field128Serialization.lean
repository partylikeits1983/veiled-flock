import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Algebra.Field128Ghash
import VeiledFlock.Core.Probability
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Concrete 128-bit field representation and little-endian serialization

This module connects three finite representations used at different layers:

* the 128 coefficient bits stored by Rust as two little-endian `u64` limbs;
* the 16 little-endian transcript bytes consumed by Fiat--Shamir;
* the power-basis coordinates of the proved GHASH quotient field.

The byte encoder below is the direct `to_le_bytes` layout: byte `i` contains
bits `8*i .. 8*i+7`, least-significant bit first.
-/

namespace VeiledFlock.Field128Serialization

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open Polynomial
open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing

abbrev Bits128 := BitVec 128
abbrev Word64 := BitVec 64

noncomputable instance : Fintype GhashField := Fintype.ofFinite GhashField

/-- Rust's two-limb in-memory value, with `lo` representing coefficients
`0..63` and `hi` representing coefficients `64..127`. -/
structure Words where
  lo : Word64
  hi : Word64
  deriving DecidableEq, Fintype

/-- `BitVec.append` places its left argument in the more-significant part, so
`hi ++ lo` is the exact little-endian coefficient layout. -/
def wordsBits (value : Words) : Bits128 :=
  value.hi ++ value.lo

/-- The byte at index `i` is the eight-bit slice beginning at bit `8*i`. -/
def encodeLE (value : Bits128) (index : Fin 16) : Byte :=
  (value.extractLsb' (index.val * 8) 8).toFin

private theorem bit_eq_of_encoded_byte_eq
    (left right : Bits128) (byte : Fin 16)
    (hbyte : encodeLE left byte = encodeLE right byte)
    (bit : Fin 8) :
    left.getLsbD (byte.val * 8 + bit.val) =
      right.getLsbD (byte.val * 8 + bit.val) := by
  have hvector :
      left.extractLsb' (byte.val * 8) 8 =
        right.extractLsb' (byte.val * 8) 8 := by
    apply BitVec.toFin_injective
    exact hbyte
  have hbit := congrArg (fun value : BitVec 8 => value.getLsbD bit.val) hvector
  simpa only [BitVec.getLsbD_extractLsb', bit.isLt, decide_true,
    Bool.true_and] using hbit

theorem encodeLE_injective : Function.Injective encodeLE := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  let byte : Fin 16 :=
    ⟨index / 8, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
  let bit : Fin 8 := ⟨index % 8, Nat.mod_lt index (by omega)⟩
  have hbit := bit_eq_of_encoded_byte_eq left right byte (congrFun heq byte) bit
  simpa only [byte, bit, Nat.div_add_mod'] using hbit

theorem encodeWordsLE_injective :
    Function.Injective (fun value : Words => encodeLE (wordsBits value)) := by
  intro left right heq
  have hbits := encodeLE_injective heq
  cases left with
  | mk leftLo leftHi =>
      cases right with
      | mk rightLo rightHi =>
          simp only [wordsBits] at hbits
          have hlo : leftLo = rightLo := by
            have := congrArg (BitVec.extractLsb' 0 64) hbits
            simpa only [BitVec.extractLsb'_append_eq_right] using this
          have hhi : leftHi = rightHi := by
            have := congrArg (BitVec.extractLsb' 64 64) hbits
            simpa only [BitVec.extractLsb'_append_eq_left] using this
          simp [hlo, hhi]

/-- Every 128-bit vector is exactly its little-endian list of coefficient
bits. -/
def bitVecBitsEquiv : Bits128 ≃ (Fin 128 → Bool) where
  toFun value := fun index => value.getLsb index
  invFun bits := BitVec.cast (List.length_ofFn (f := bits))
    (BitVec.ofBoolListLE (List.ofFn bits))
  left_inv value := by
    apply BitVec.eq_of_getLsbD_eq
    intro index hindex
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hindex)]
    rw [List.getElem_ofFn]
    rfl
  right_inv bits := by
    funext index
    change (BitVec.cast _ (BitVec.ofBoolListLE (List.ofFn bits))).getLsbD index = _
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by
      simp only [List.length_ofFn]
      exact index.isLt)]
    rw [List.getElem_ofFn]

/-- Coefficient bits are canonically the two elements of `ZMod 2`. -/
def boolF2Equiv : Bool ≃ F2 where
  toFun bit := if bit then 1 else 0
  invFun value := value = 1
  left_inv bit := by cases bit <;> simp
  right_inv value := by
    fin_cases value <;> decide

noncomputable def ghashBasis128 : Module.Basis (Fin 128) F2 GhashField :=
  (AdjoinRoot.powerBasis ghashModulus_monic.ne_zero).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis_dim, ghashModulus_natDegree]))

theorem ghashBasis128_apply (index : Fin 128) :
    ghashBasis128 index = (AdjoinRoot.root ghashModulus) ^ index.val := by
  rw [ghashBasis128, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis ghashModulus_monic.ne_zero).basis_eq_pow,
    AdjoinRoot.powerBasis_gen]
  rfl

/-- The exact 128 stored bits are a bijective coordinate representation of
the concrete GHASH quotient field. -/
noncomputable def bitsGhashEquiv : Bits128 ≃ GhashField :=
  bitVecBitsEquiv |>.trans
    (Equiv.piCongrRight fun _ => boolF2Equiv) |>.trans
    ghashBasis128.equivFun.toEquiv.symm

@[simp]
theorem bitsGhashEquiv_zero : bitsGhashEquiv (0 : Bits128) = 0 := by
  change ghashBasis128.equivFun.symm
    (fun index => boolF2Equiv ((0 : Bits128).getLsb index)) = 0
  have hcoordinates :
      (fun index : Fin 128 => boolF2Equiv ((0 : Bits128).getLsb index)) =
        fun _ => 0 := by
    funext index
    simp [boolF2Equiv]
  rw [hcoordinates]
  exact LinearEquiv.map_zero ghashBasis128.equivFun.symm

@[simp]
theorem bitsGhashEquiv_one : bitsGhashEquiv (1 : Bits128) = 1 := by
  change ghashBasis128.equivFun.symm
    (fun index => boolF2Equiv ((1 : Bits128).getLsb index)) = 1
  rw [← show ghashBasis128 0 = 1 by simp [ghashBasis128_apply]]
  apply ghashBasis128.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_self]
  funext index
  simp [boolF2Equiv, Finsupp.single_apply, eq_comm]

def coefficientBits (value : Bits128) : List Bool :=
  List.ofFn fun index : Fin 128 => value.getLsb index

/-- The coordinate equivalence is not an arbitrary cardinality bijection: it
is exactly little-endian evaluation in the power-basis root. -/
theorem bitsGhashEquiv_apply (value : Bits128) :
    bitsGhashEquiv value =
      BinaryPolynomial.evalAt (AdjoinRoot.root ghashModulus)
        (coefficientBits value) := by
  change ghashBasis128.equivFun.symm
      (fun index => boolF2Equiv (value.getLsb index)) = _
  rw [ghashBasis128.equivFun_symm_apply, coefficientBits,
    BinaryPolynomial.evalAt_ofFn]
  apply Finset.sum_congr rfl
  intro index _
  rw [ghashBasis128_apply]
  cases hbit : value.getLsb index <;>
    simp [boolF2Equiv, BinaryPolynomial.bitValue, hbit, Algebra.smul_def]

theorem coefficientBits_xor (left right : Bits128) :
    coefficientBits (left ^^^ right) =
      BinaryPolynomial.xorBits (coefficientBits left) (coefficientBits right) := by
  rw [coefficientBits, coefficientBits, coefficientBits,
    BinaryPolynomial.xorBits_ofFn]
  congr 1
  funext index
  change (left ^^^ right).getLsbD index =
    (left.getLsbD index != right.getLsbD index)
  rw [BitVec.getLsbD_xor]

/-- Rust's limbwise XOR is exactly addition in the concrete quotient field. -/
theorem bitsGhashEquiv_xor (left right : Bits128) :
    bitsGhashEquiv (left ^^^ right) =
      bitsGhashEquiv left + bitsGhashEquiv right := by
  rw [bitsGhashEquiv_apply, bitsGhashEquiv_apply, bitsGhashEquiv_apply,
    coefficientBits_xor, BinaryPolynomial.evalAt_xor]

def reducedCarrylessProduct (left right : Bits128) : List Bool :=
  BinaryPolynomial.reduce128 reductionBits
    (BinaryPolynomial.clmul (coefficientBits left) (coefficientBits right))

/-- Carry-less multiplication followed by the two GHASH folds denotes the
field product of the two stored values. -/
theorem eval_reducedCarrylessProduct (left right : Bits128) :
    BinaryPolynomial.evalAt (AdjoinRoot.root ghashModulus)
        (reducedCarrylessProduct left right) =
      bitsGhashEquiv left * bitsGhashEquiv right := by
  rw [reducedCarrylessProduct,
    BinaryPolynomial.evalAt_reduce128 _ reductionBits _
      root_reduction_relation,
    BinaryPolynomial.evalAt_clmul,
    ← bitsGhashEquiv_apply, ← bitsGhashEquiv_apply]

theorem bitsGhashEquiv_bijective : Function.Bijective bitsGhashEquiv :=
  bitsGhashEquiv.bijective

/-- The actual 16-byte little-endian field encoding is injective. -/
noncomputable def encodeGhashField (value : GhashField) : Fin 16 → Byte :=
  encodeLE (bitsGhashEquiv.symm value)

theorem encodeGhashField_injective : Function.Injective encodeGhashField := by
  exact encodeLE_injective.comp bitsGhashEquiv.symm.injective

theorem card_oracleHalf : Fintype.card OracleHalf = 2 ^ 128 := by
  rw [Fintype.card_fun, Fintype.card_fin]
  norm_num [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]

theorem encodeGhashField_bijective : Function.Bijective encodeGhashField := by
  apply (Fintype.bijective_iff_injective_and_card encodeGhashField).2
  exact ⟨encodeGhashField_injective, by
    rw [Fintype.card_eq_nat_card, ghashField_natCard, card_oracleHalf]⟩

/-- Reading/writing the 16 little-endian coefficient bytes is an equivalence
between concrete GHASH field values and scalar oracle prefixes. -/
noncomputable def encodeGhashFieldEquiv : GhashField ≃ OracleHalf :=
  Equiv.ofBijective encodeGhashField encodeGhashField_bijective

/-- Exact coin bijection underlying the implementation's prefix programming.
The simulator-selected scalar replaces the first half; the old first half is
carried as unused randomness, and the old second half is preserved. -/
noncomputable def programScalarCoinEquiv :
    GhashField × OracleBlock ≃ OracleBlock × OracleHalf where
  toFun coins :=
    (programScalarPrefix (encodeGhashFieldEquiv coins.1) coins.2,
      (oracleBlockSplit coins.2).1)
  invFun output :=
    (encodeGhashFieldEquiv.symm (oracleBlockSplit output.1).1,
      oracleBlockSplit.symm (output.2, (oracleBlockSplit output.1).2))
  left_inv coins := by
    apply Prod.ext
    · simp [programScalarPrefix]
    · apply oracleBlockSplit.injective
      simp [programScalarPrefix]
  right_inv output := by
    apply Prod.ext
    · apply oracleBlockSplit.injective
      simp [programScalarPrefix]
    · simp [programScalarPrefix]

@[simp]
theorem programScalarCoinEquiv_programmedBlock
    (coins : GhashField × OracleBlock) :
    (programScalarCoinEquiv coins).1 =
      programScalarPrefix (encodeGhashField coins.1) coins.2 := rfl

/-- Uniform scalar targets plus uniform original oracle blocks are exactly
uniform programmed blocks plus an independent discarded prefix.  In
particular, preserving bytes 16--31 after programming bytes 0--15 does not
change the random-oracle answer distribution. -/
theorem uniform_programScalarCoinEquiv :
    (PMF.uniformOfFintype (GhashField × OracleBlock)).map
        programScalarCoinEquiv =
      PMF.uniformOfFintype (OracleBlock × OracleHalf) := by
  exact VeiledFlock.Probability.uniform_map_equiv programScalarCoinEquiv

end VeiledFlock.Field128Serialization

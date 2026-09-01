import VeiledFlock.Concrete.Framing
import VeiledFlock.Oracle.ProgrammableOracle

/-!
# Concrete 256-bit nonce serialization

The probability ledger represents a fresh nonce as `Fin (2^256)`, while the
Rust transcript and Merkle encodings store the same value as thirty-two
little-endian bytes.  This file gives the exact conversion and proves that no
two numeric nonces have the same byte representation.
-/

namespace VeiledFlock.NonceSerialization

open VeiledFlock.Framing

abbrev NumericNonce := VeiledFlock.ProgrammableOracle.Nonce256
abbrev NonceBits := BitVec 256

/-- The canonical integer-to-256-bit-vector representation. -/
def numericNonceBits : NumericNonce ≃ NonceBits :=
  BitVec.equivFin.toEquiv.symm

/-- Byte `i` contains bits `8*i .. 8*i+7`, matching Rust's little-endian
serialization of four `u64` words. -/
def encodeNonceLE (nonce : NumericNonce) (index : Fin 32) : Byte :=
  ((numericNonceBits nonce).extractLsb' (index.val * 8) 8).toFin

private theorem bit_eq_of_encoded_byte_eq
    (left right : NonceBits) (byte : Fin 32)
    (hbyte :
      (left.extractLsb' (byte.val * 8) 8).toFin =
        (right.extractLsb' (byte.val * 8) 8).toFin)
    (bit : Fin 8) :
    left.getLsbD (byte.val * 8 + bit.val) =
      right.getLsbD (byte.val * 8 + bit.val) := by
  have hvector :
      left.extractLsb' (byte.val * 8) 8 =
        right.extractLsb' (byte.val * 8) 8 := by
    exact BitVec.toFin_injective hbyte
  have hbit := congrArg
    (fun value : BitVec 8 => value.getLsbD bit.val) hvector
  simpa only [BitVec.getLsbD_extractLsb', bit.isLt, decide_true,
    Bool.true_and] using hbit

theorem encodeNonceLE_injective : Function.Injective encodeNonceLE := by
  intro left right heq
  apply numericNonceBits.injective
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  let byte : Fin 32 :=
    ⟨index / 8, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
  let bit : Fin 8 := ⟨index % 8, Nat.mod_lt index (by omega)⟩
  have hbit := bit_eq_of_encoded_byte_eq
    (numericNonceBits left) (numericNonceBits right) byte
    (congrFun heq byte) bit
  simpa only [byte, bit, Nat.div_add_mod'] using hbit

theorem card_nonceBytes : Fintype.card Framing.Nonce256 = 2 ^ 256 := by
  rw [Fintype.card_fun, Fintype.card_fin]
  norm_num [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]

theorem encodeNonceLE_bijective : Function.Bijective encodeNonceLE := by
  apply (Fintype.bijective_iff_injective_and_card encodeNonceLE).2
  exact ⟨encodeNonceLE_injective, by
    rw [Fintype.card_fin, card_nonceBytes]⟩

/-- Exact equivalence between the ledger nonce and its production byte
encoding. -/
noncomputable def numericNonceBytes : NumericNonce ≃ Framing.Nonce256 :=
  Equiv.ofBijective encodeNonceLE encodeNonceLE_bijective

end VeiledFlock.NonceSerialization

import VeiledFlock.BinaryPolynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The concrete GHASH field polynomial

The Rust field implementation uses little-endian coefficients and the GHASH
polynomial `X^128 + X^7 + X^2 + X + 1`.  This file checks an executable
Rabin/Bezout certificate for that exact polynomial and connects the checked
bit operations to Mathlib polynomials.  The certificate generator is not
trusted: `native_decide` replays the two identities inside Lean.
-/

namespace VeiledFlock.Field128Ghash

open Polynomial
open VeiledFlock.BinaryPolynomial

set_option maxRecDepth 65536
set_option maxHeartbeats 800000

abbrev F2 := ZMod 2

def reductionBits : List Bool :=
  [true, true, true, false, false, false, false, true]

def modulusBits : List Bool :=
  xorBits reductionBits (shiftBits 128 [true])

noncomputable def ghashModulus : F2[X] :=
  evalAt X modulusBits

def r64Bits : List Bool :=
  frobenius reductionBits 64

theorem r64Bits_eq : r64Bits = frobenius reductionBits 64 := rfl

/-- An opaque-enough name that prevents elaboration from normalizing the
astronomical natural `2^64` during unrelated polynomial unification. -/
def powTwo64 : ℕ := 2 ^ 64

theorem powTwo64_eq : powTwo64 = 2 ^ 64 := rfl

private theorem dvd_X_pow_add_pair_cancel_charTwo
    {exponent : ℕ} {divisor left right : F2[X]}
    (hleft : divisor ∣ (X : F2[X]) ^ exponent + left)
    (hright : divisor ∣ (X : F2[X]) ^ exponent + right) :
    divisor ∣ left + right :=
  dvd_add_pair_cancel_charTwo hleft hright

noncomputable def r64Polynomial : F2[X] :=
  evalAt X r64Bits

theorem r64Polynomial_eq : r64Polynomial = evalAt X r64Bits := rfl

def bezoutLeftBits : List Bool :=
  natBits 128 0x34f319a5fb685836214ec51f73e3547b

def bezoutRightBits : List Bool :=
  natBits 128 0x9e4af928ddbc838a41a8cafd2c95b018

theorem frobenius128_certificate :
    bitsEquivalent (frobenius reductionBits 128) [false, true] = true := by
  native_decide

theorem bezout64_certificate :
    bitsEquivalent
      (xorBits
        (clmul bezoutLeftBits modulusBits)
        (clmul bezoutRightBits (xorBits r64Bits [false, true])))
      [true] = true := by
  native_decide

theorem reductionBits_eval {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    evalAt x reductionBits = x ^ 7 + x ^ 2 + x + 1 := by
  simp [reductionBits, evalAt, bitValue]
  ring

theorem modulusBits_eval {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    evalAt x modulusBits = x ^ 128 + x ^ 7 + x ^ 2 + x + 1 := by
  rw [modulusBits, evalAt_xor, evalAt_shift, reductionBits_eval]
  simp [evalAt, bitValue]
  ring

set_option maxRecDepth 4096 in
theorem ghashModulus_eq :
    ghashModulus = X ^ 128 + X ^ 7 + X ^ 2 + X + 1 := by
  change evalAt X modulusBits = _
  exact modulusBits_eval (R := F2[X]) X

theorem ghashModulus_monic : ghashModulus.Monic := by
  rw [ghashModulus_eq]
  monicity <;> norm_num

theorem ghashModulus_natDegree : ghashModulus.natDegree = 128 := by
  rw [ghashModulus_eq]
  compute_degree <;> norm_num

theorem ghashModulus_ne_one : ghashModulus ≠ 1 := by
  intro heq
  have := congrArg Polynomial.natDegree heq
  simp [ghashModulus_natDegree] at this

/-- The converse finite-field divisibility fact used by Rabin's criterion. -/
theorem irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Finite K] {f : K[X]} {n : ℕ}
    (hirr : Irreducible f) (hdegree : f.natDegree ∣ n) :
    f ∣ X ^ (Nat.card K) ^ n - X := by
  letI : Fact (Irreducible f) := ⟨hirr⟩
  letI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  letI : Finite (AdjoinRoot f) := Module.finite_of_finite K
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (AdjoinRoot f) := Fintype.ofFinite (AdjoinRoot f)
  rw [← AdjoinRoot.mk_eq_zero]
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  simp only [Nat.card_eq_fintype_card]
  obtain ⟨multiple, rfl⟩ := hdegree
  rw [pow_mul]
  have hfinrank : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    exact finrank_quotient_span_eq_natDegree
  have hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ f.natDegree := by
    calc
      Fintype.card (AdjoinRoot f) =
          Fintype.card K ^ Module.finrank K (AdjoinRoot f) :=
        @Module.card_eq_pow_finrank K (AdjoinRoot f) _ _ _ _ _
      _ = Fintype.card K ^ f.natDegree := by rw [hfinrank]
  rw [← hcard]
  exact sub_eq_zero.mpr (FiniteField.pow_card_pow multiple _)

theorem irreducible_natDegree_dvd_of_dvd_X_pow_card_pow_add_X
    {K : Type*} [Field K] [Finite K] [CharP K 2] {f : K[X]} {n : ℕ}
    (hirr : Irreducible f) (h : f ∣ X ^ (Nat.card K) ^ n + X) :
    f.natDegree ∣ n := by
  apply hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
  rw [sub_eq_add_neg, neg_eq_self_charTwo]
  exact h

theorem irreducible_dvd_X_pow_card_pow_add_X
    {K : Type*} [Field K] [Finite K] [CharP K 2] {f : K[X]} {n : ℕ}
    (hirr : Irreducible f) (hdegree : f.natDegree ∣ n) :
    f ∣ X ^ (Nat.card K) ^ n + X := by
  have h := irreducible_dvd_X_pow_card_pow_sub_X hirr hdegree
  rw [sub_eq_add_neg, neg_eq_self_charTwo] at h
  exact h

private noncomputable instance adjoinRootCharTwo :
    CharP (AdjoinRoot ghashModulus) 2 := by
  apply charP_of_injective_ringHom (f := AdjoinRoot.of ghashModulus)
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [degree_eq_natDegree ghashModulus_monic.ne_zero, ghashModulus_natDegree]
  norm_num

theorem root_reduction_relation :
    (AdjoinRoot.root ghashModulus) ^ 128 =
      evalAt (AdjoinRoot.root ghashModulus) reductionBits := by
  let root := AdjoinRoot.root ghashModulus
  have hzero : evalAt root modulusBits = 0 := by
    calc
      evalAt root modulusBits =
          AdjoinRoot.mk ghashModulus (evalAt X modulusBits) := by
            rw [map_evalAt, AdjoinRoot.mk_X]
      _ = AdjoinRoot.mk ghashModulus ghashModulus := rfl
      _ = 0 := AdjoinRoot.mk_self
  rw [modulusBits, evalAt_xor, evalAt_shift] at hzero
  simp [evalAt, bitValue] at hzero
  rw [add_comm] at hzero
  exact (eq_neg_of_add_eq_zero_left hzero).trans
    (neg_eq_self_charTwo (evalAt root reductionBits))

theorem ghashModulus_dvd_frobenius_congruence (rounds : ℕ) :
    ghashModulus ∣
      X ^ (2 ^ rounds) + evalAt X (frobenius reductionBits rounds) := by
  rw [← AdjoinRoot.mk_eq_zero]
  rw [map_add, map_pow, AdjoinRoot.mk_X, map_evalAt,
    AdjoinRoot.mk_X,
    evalAt_frobenius _ reductionBits root_reduction_relation]
  exact add_self_eq_zero_charTwo _

theorem ghashModulus_dvd_X_pow_128_add_X :
    ghashModulus ∣ X ^ (2 ^ 128) + X := by
  have hcongruence := ghashModulus_dvd_frobenius_congruence 128
  have heq := evalAt_eq_of_bitsEquivalent (R := F2[X]) X frobenius128_certificate
  have heq' : evalAt (X : F2[X]) (frobenius reductionBits 128) = (X : F2[X]) := by
    simpa only [evalAt, bitValue, zero_add, add_zero, zero_mul, mul_zero,
      one_mul, mul_one] using heq
  rw [heq'] at hcongruence
  exact hcongruence

theorem ghashModulus_isCoprime_r64_add_X :
    IsCoprime ghashModulus (r64Polynomial + X) := by
  refine ⟨evalAt X bezoutLeftBits, evalAt X bezoutRightBits, ?_⟩
  have heq := evalAt_eq_of_bitsEquivalent (R := F2[X]) X bezout64_certificate
  rw [evalAt_xor, evalAt_clmul, evalAt_clmul, evalAt_xor] at heq
  simpa only [ghashModulus, r64Polynomial, r64Bits, evalAt, bitValue, zero_add, add_zero,
    zero_mul, mul_zero, one_mul, mul_one] using heq

theorem ghashModulus_irreducible : Irreducible ghashModulus := by
  rw [ghashModulus_monic.irreducible_iff_lt_natDegree_lt ghashModulus_ne_one]
  intro q hqMonic hqDegree hqDvd
  rcases Finset.mem_Ioc.mp hqDegree with ⟨hqDegreePositive, hqDegreeUpper⟩
  obtain ⟨factor, hfactorIrr, hfactorDvdQ⟩ :=
    Polynomial.exists_irreducible_of_natDegree_pos hqDegreePositive
  have hfactorDvdModulus : factor ∣ ghashModulus := hfactorDvdQ.trans hqDvd
  have hfactorDvd128 : factor ∣ (X : F2[X]) ^ (2 ^ 128) + X := by
    exact dvd_trans hfactorDvdModulus ghashModulus_dvd_X_pow_128_add_X
  have hfactorDvd128' :
      factor ∣ (X : F2[X]) ^ ((Nat.card F2) ^ 128) + X := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hfactorDvd128
  have hdegreeDvd128 : factor.natDegree ∣ 128 := by
    exact irreducible_natDegree_dvd_of_dvd_X_pow_card_pow_add_X
      (n := 128) hfactorIrr hfactorDvd128'
  have hfactorDegreeLeQ : factor.natDegree ≤ q.natDegree :=
    Polynomial.natDegree_le_of_dvd hfactorDvdQ hqMonic.ne_zero
  have hfactorDegreeLe64 : factor.natDegree ≤ 64 := by
    rw [ghashModulus_natDegree] at hqDegreeUpper
    omega
  have hdegreeDvd64 : factor.natDegree ∣ 64 := by
    have hpow : factor.natDegree ∣ 2 ^ 7 := by norm_num at hdegreeDvd128 ⊢; exact hdegreeDvd128
    obtain ⟨exponent, hexponent, hdegree⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp hpow
    have hexponentLeSix : exponent ≤ 6 := by
      by_contra hnot
      have : exponent = 7 := by omega
      subst exponent
      norm_num [hdegree] at hfactorDegreeLe64
    exact (Nat.dvd_prime_pow Nat.prime_two).mpr ⟨exponent, hexponentLeSix, hdegree⟩
  have hfactorDvd64 : factor ∣ (X : F2[X]) ^ powTwo64 + X := by
    rw [powTwo64_eq]
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      irreducible_dvd_X_pow_card_pow_add_X (K := F2)
        (n := 64) hfactorIrr hdegreeDvd64
  have hcongruence64 := ghashModulus_dvd_frobenius_congruence 64
  rw [← r64Bits_eq] at hcongruence64
  rw [← r64Polynomial_eq] at hcongruence64
  rw [← powTwo64_eq] at hcongruence64
  have hfactorCongruence64 :
      factor ∣ (X : F2[X]) ^ powTwo64 + r64Polynomial := by
    exact dvd_trans hfactorDvdModulus hcongruence64
  have hfactorDvdR64AddX : factor ∣ r64Polynomial + X := by
    exact dvd_X_pow_add_pair_cancel_charTwo
      (exponent := powTwo64) hfactorCongruence64 hfactorDvd64
  exact hfactorIrr.not_isUnit
    (ghashModulus_isCoprime_r64_add_X.isUnit_of_dvd'
      hfactorDvdModulus hfactorDvdR64AddX)

/-! ## Identification with the abstract field used by the protocol proof -/

noncomputable instance ghashModulusIrreducibleFact :
    Fact (Irreducible ghashModulus) := ⟨ghashModulus_irreducible⟩

/-- The concrete quotient field represented by the Rust GHASH limbs. -/
abbrev GhashField := AdjoinRoot ghashModulus

noncomputable instance ghashFieldFinite : Finite GhashField := by
  letI : Module.Finite F2 GhashField := ghashModulus_monic.finite_adjoinRoot
  exact Module.finite_of_finite F2

theorem ghashField_finrank : Module.finrank F2 GhashField = 128 := by
  calc
    Module.finrank F2 GhashField = ghashModulus.natDegree :=
      finrank_quotient_span_eq_natDegree
    _ = 128 := ghashModulus_natDegree

theorem ghashField_natCard : Nat.card GhashField = 2 ^ 128 := by
  letI : Fintype GhashField := Fintype.ofFinite GhashField
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card GhashField =
        Fintype.card F2 ^ Module.finrank F2 GhashField :=
      @Module.card_eq_pow_finrank F2 GhashField _ _ _ _ _
    _ = 2 ^ 128 := by rw [ghashField_finrank, ZMod.card]

/-- The concrete GHASH quotient and Mathlib's canonical 128-bit binary field
are isomorphic as `ZMod 2` algebras.  The isomorphism need not be canonical;
all algebraic protocol statements are invariant under it. -/
noncomputable def ghashFieldAlgEquivCanonical :
    GhashField ≃ₐ[F2] GaloisField 2 128 :=
  GaloisField.algEquivGaloisField 2 128 ghashField_natCard

end VeiledFlock.Field128Ghash

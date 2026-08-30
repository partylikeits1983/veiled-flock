import Mathlib.FieldTheory.Finite.Extension

/-!
# Executable binary-polynomial certificates

Mathlib's `Polynomial` operations are intentionally noncomputable for a
generic coefficient ring, so `native_decide` cannot directly check the
degree-128 GHASH modulus.  This module provides a small executable list-of-bits
representation and proves its operations sound with respect to evaluation in
every characteristic-two commutative ring.  Concrete Rabin/Bezout certificates
can therefore be checked by the native kernel evaluator without adding a
trusted oracle or an axiom.
-/

namespace VeiledFlock.BinaryPolynomial

def bitValue {R : Type*} [Zero R] [One R] : Bool → R
  | false => 0
  | true => 1

/-- Little-endian polynomial evaluation: the head is the constant bit. -/
def evalAt {R : Type*} [Semiring R] (x : R) : List Bool → R
  | [] => 0
  | bit :: bits => bitValue bit + x * evalAt x bits

/-- Evaluation of a fixed-width coefficient vector as the usual finite
power-basis sum. -/
theorem evalAt_ofFn {R : Type*} [CommSemiring R]
    (x : R) {width : ℕ} (bits : Fin width → Bool) :
    evalAt x (List.ofFn bits) =
      ∑ index : Fin width, bitValue (bits index) * x ^ index.val := by
  induction width with
  | zero => simp [evalAt]
  | succ width ih =>
      rw [List.ofFn_succ, evalAt, Fin.sum_univ_succ,
        ih (fun index => bits index.succ)]
      simp only [Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro index _
        ring

theorem map_evalAt {R S : Type*} [Semiring R] [Semiring S]
    (map : R →+* S) (x : R) (bits : List Bool) :
    map (evalAt x bits) = evalAt (map x) bits := by
  induction bits with
  | nil => simp [evalAt]
  | cons bit bits ih =>
      cases bit <;> simp [evalAt, bitValue, ih]

def xorBits : List Bool → List Bool → List Bool
  | [], right => right
  | left, [] => left
  | left :: lefts, right :: rights => (left != right) :: xorBits lefts rights

theorem xorBits_ofFn {width : ℕ} (left right : Fin width → Bool) :
    xorBits (List.ofFn left) (List.ofFn right) =
      List.ofFn fun index => left index != right index := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, xorBits]
      congr 1
      exact ih (fun index => left index.succ) (fun index => right index.succ)

private theorem bitValue_xor {R : Type*} [CommRing R] [CharP R 2]
    (left right : Bool) :
    bitValue (R := R) (left != right) = bitValue left + bitValue right := by
  cases left <;> cases right <;> simp [bitValue]
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  simpa [one_add_one_eq_two] using htwo.symm

theorem evalAt_xor {R : Type*} [CommRing R] [CharP R 2]
    (x : R) (left right : List Bool) :
    evalAt x (xorBits left right) = evalAt x left + evalAt x right := by
  induction left generalizing right with
  | nil => simp [xorBits, evalAt]
  | cons left lefts ih =>
      cases right with
      | nil => simp [xorBits, evalAt]
      | cons right rights =>
          simp only [xorBits, evalAt, bitValue_xor, ih]
          ring

def allFalse : List Bool → Bool
  | [] => true
  | bit :: bits => !bit && allFalse bits

theorem evalAt_eq_zero_of_allFalse {R : Type*} [Semiring R]
    (x : R) {bits : List Bool} (hfalse : allFalse bits = true) :
    evalAt x bits = 0 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> simp_all [allFalse, evalAt, bitValue]

def bitsEquivalent (left right : List Bool) : Bool :=
  allFalse (xorBits left right)

theorem add_self_eq_zero_charTwo {R : Type*} [CommRing R] [CharP R 2]
    (value : R) : value + value = 0 := by
  calc
    value + value = (2 : R) * value := by ring
    _ = 0 * value := by
      have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
      rw [htwo]
    _ = 0 := zero_mul value

theorem neg_eq_self_charTwo {R : Type*} [CommRing R] [CharP R 2]
    (value : R) : -value = value := by
  exact (eq_neg_of_add_eq_zero_left (add_self_eq_zero_charTwo value)).symm

theorem add_pair_cancel_charTwo {R : Type*} [CommRing R] [CharP R 2]
    (repeated left right : R) :
    (repeated + left) + (repeated + right) = left + right := by
  calc
    _ = (repeated + repeated) + (left + right) := by ac_rfl
    _ = left + right := by rw [add_self_eq_zero_charTwo, zero_add]

theorem dvd_add_pair_cancel_charTwo {R : Type*} [CommRing R] [CharP R 2]
    {divisor repeated left right : R}
    (hleft : divisor ∣ repeated + left)
    (hright : divisor ∣ repeated + right) :
    divisor ∣ left + right := by
  have hsum := hleft.add hright
  rw [add_pair_cancel_charTwo] at hsum
  exact hsum

theorem dvd_pow_add_pair_cancel_charTwo {R : Type*} [CommRing R] [CharP R 2]
    (base : R) {exponent : ℕ} {divisor left right : R}
    (hleft : divisor ∣ base ^ exponent + left)
    (hright : divisor ∣ base ^ exponent + right) :
    divisor ∣ left + right :=
  dvd_add_pair_cancel_charTwo hleft hright

theorem evalAt_eq_of_bitsEquivalent {R : Type*} [CommRing R] [CharP R 2]
    (x : R) {left right : List Bool}
    (heq : bitsEquivalent left right = true) :
    evalAt x left = evalAt x right := by
  have hsum : evalAt x left + evalAt x right = 0 := by
    rw [← evalAt_xor]
    exact evalAt_eq_zero_of_allFalse x heq
  calc
    evalAt x left = evalAt x left + 0 := by simp
    _ = evalAt x left + (evalAt x right + evalAt x right) := by
      rw [add_self_eq_zero_charTwo]
    _ = (evalAt x left + evalAt x right) + evalAt x right := by ring
    _ = evalAt x right := by rw [hsum, zero_add]

def shiftBits (amount : ℕ) (bits : List Bool) : List Bool :=
  List.replicate amount false ++ bits

theorem evalAt_shift {R : Type*} [CommSemiring R]
    (x : R) (amount : ℕ) (bits : List Bool) :
    evalAt x (shiftBits amount bits) = x ^ amount * evalAt x bits := by
  induction amount with
  | zero => simp [shiftBits]
  | succ amount ih =>
      rw [show shiftBits (amount + 1) bits = false :: shiftBits amount bits by
        simp [shiftBits, List.replicate_succ]]
      simp only [evalAt, bitValue, ih, pow_succ]
      ring

/-- Carry-less multiplication. -/
def clmul : List Bool → List Bool → List Bool
  | [], _ => []
  | bit :: bits, right =>
      xorBits (if bit then right else []) (false :: clmul bits right)

theorem evalAt_clmul {R : Type*} [CommRing R] [CharP R 2]
    (x : R) (left right : List Bool) :
    evalAt x (clmul left right) = evalAt x left * evalAt x right := by
  induction left with
  | nil => simp [clmul, evalAt]
  | cons bit bits ih =>
      rw [clmul, evalAt_xor]
      cases bit <;> simp [evalAt, bitValue, ih] <;> ring

theorem evalAt_take_append_drop {R : Type*} [CommSemiring R]
    (x : R) (cut : ℕ) (bits : List Bool) :
    evalAt x bits =
      evalAt x (bits.take cut) + x ^ cut * evalAt x (bits.drop cut) := by
  induction cut generalizing bits with
  | zero => simp [evalAt]
  | succ cut ih =>
      cases bits with
      | nil => simp [evalAt]
      | cons bit bits =>
          simp only [List.take_succ_cons, List.drop_succ_cons, evalAt]
          rw [ih]
          simp only [pow_succ]
          ring

/-- One long-division fold using `x^128 = reduction`. -/
def fold128 (reduction bits : List Bool) : List Bool :=
  xorBits (bits.take 128) (clmul reduction (bits.drop 128))

theorem evalAt_fold128 {R : Type*} [CommRing R] [CharP R 2]
    (x : R) (reduction bits : List Bool)
    (hrelation : x ^ 128 = evalAt x reduction) :
    evalAt x (fold128 reduction bits) = evalAt x bits := by
  rw [fold128, evalAt_xor, evalAt_clmul, ← hrelation]
  exact (evalAt_take_append_drop x 128 bits).symm

/-- Two folds suffice for every 256-bit carry-less product under the GHASH
degree-seven reduction tail.  Soundness does not need that width fact; the
native certificate checks the concrete result. -/
def reduce128 (reduction bits : List Bool) : List Bool :=
  fold128 reduction (fold128 reduction bits)

theorem evalAt_reduce128 {R : Type*} [CommRing R] [CharP R 2]
    (x : R) (reduction bits : List Bool)
    (hrelation : x ^ 128 = evalAt x reduction) :
    evalAt x (reduce128 reduction bits) = evalAt x bits := by
  simp only [reduce128]
  rw [evalAt_fold128 x reduction _ hrelation,
    evalAt_fold128 x reduction _ hrelation]

def frobeniusStep (reduction bits : List Bool) : List Bool :=
  reduce128 reduction (clmul bits bits)

theorem evalAt_frobeniusStep {R : Type*} [CommRing R] [CharP R 2]
    (x : R) (reduction bits : List Bool)
    (hrelation : x ^ 128 = evalAt x reduction) :
    evalAt x (frobeniusStep reduction bits) = (evalAt x bits) ^ 2 := by
  rw [frobeniusStep, evalAt_reduce128 x reduction _ hrelation, evalAt_clmul]
  ring

def frobenius (reduction : List Bool) : ℕ → List Bool
  | 0 => [false, true]
  | rounds + 1 => frobeniusStep reduction (frobenius reduction rounds)

theorem evalAt_frobenius {R : Type*} [CommRing R] [CharP R 2]
    (x : R) (reduction : List Bool)
    (hrelation : x ^ 128 = evalAt x reduction) :
    ∀ rounds, evalAt x (frobenius reduction rounds) = x ^ (2 ^ rounds) := by
  intro rounds
  induction rounds with
  | zero => simp [frobenius, evalAt, bitValue]
  | succ rounds ih =>
      rw [frobenius, evalAt_frobeniusStep x reduction _ hrelation, ih]
      calc
        (x ^ 2 ^ rounds) ^ 2 = x ^ (2 ^ rounds * 2) := by rw [pow_mul]
        _ = x ^ (2 ^ (rounds + 1)) := by rw [pow_succ]

def natBits (width value : ℕ) : List Bool :=
  List.ofFn fun index : Fin width => value.testBit index

end VeiledFlock.BinaryPolynomial

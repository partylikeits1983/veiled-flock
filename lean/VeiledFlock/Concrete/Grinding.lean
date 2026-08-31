import Mathlib

/-!
# Bounded Fiat--Shamir grinding

The prover searches a fixed number of independent random-oracle answers for
one whose first `bits` bits are zero.  This file gives the exact finite
probability of exhausting the search and instantiates the two caps enforced by
the Rust full-ZK entry point.

This is a classical random-oracle statement: each attempt is represented by a
fresh uniform element of `Fin (2^bits)`, with `0` the unique successful prefix.
-/

namespace VeiledFlock.Grinding

/-- Attempt sequences containing no successful outcome. -/
def abortRuns {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (failed : Finset Outcome) (trials : ℕ) :
    Finset (Fin trials → Outcome) :=
  Fintype.piFinset fun _ => failed

@[simp]
theorem mem_abortRuns_iff {Outcome : Type*} [Fintype Outcome]
    [DecidableEq Outcome] (failed : Finset Outcome) (trials : ℕ)
    (run : Fin trials → Outcome) :
    run ∈ abortRuns failed trials ↔ ∀ trial, run trial ∈ failed := by
  simp [abortRuns]

/-- Exact count of runs in which every trial fails. -/
theorem card_abortRuns {Outcome : Type*} [Fintype Outcome]
    [DecidableEq Outcome] (failed : Finset Outcome) (trials : ℕ) :
    (abortRuns failed trials).card = failed.card ^ trials := by
  simp [abortRuns]

/-- Exact abort probability for uniform independent outcomes. -/
theorem abortProbability_eq {Outcome : Type*} [Fintype Outcome]
    [DecidableEq Outcome] (failed : Finset Outcome) (trials : ℕ) :
    ((abortRuns failed trials).card : ℚ) /
        Fintype.card (Fin trials → Outcome) =
      ((failed.card : ℚ) / Fintype.card Outcome) ^ trials := by
  rw [card_abortRuns]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_pow]

/-- Prefixes that fail a `bits`-bit grind.  Zero is the unique success. -/
def failedPrefixes (bits : ℕ) : Finset (Fin (2 ^ bits)) :=
  Finset.univ.erase 0

theorem card_failedPrefixes (bits : ℕ) :
    (failedPrefixes bits).card = 2 ^ bits - 1 := by
  simp [failedPrefixes]

/-- Exact tail of a bounded `bits`-bit grind. -/
theorem grindAbortProbability_eq (bits trials : ℕ) :
    ((abortRuns (failedPrefixes bits) trials).card : ℚ) /
        Fintype.card (Fin trials → Fin (2 ^ bits)) =
      (((2 ^ bits - 1 : ℕ) : ℚ) / (2 ^ bits : ℕ)) ^ trials := by
  rw [abortProbability_eq, card_failedPrefixes]
  simp

/-- Constants enforced by `succinct_veil.rs`.  The 4096-slot shape derives a
six-bit L0 blinding grind and permits 8192 attempts. -/
def maxBlindBits : ℕ := 6
def maxBlindTrials : ℕ := 8192
/-- Largest live Secure-profile fold grind.  Secure configurations use the
unique-decoding regime, so every fold round uses this level's full width. -/
def maxLigeritoBits : ℕ := 5
def maxLigeritoTrials : ℕ := 4096
/-- Conservative reservation of one site per positive-grind fold round, not
one site per recursive level.  Registered shapes currently emit at most 12. -/
def maxLigeritoSites : ℕ := 16

def blindAbortProbability : ℚ := (63 / 64 : ℚ) ^ maxBlindTrials
def ligeritoAbortProbability : ℚ := (31 / 32 : ℚ) ^ maxLigeritoTrials

theorem blindAbortProbability_eq :
    ((abortRuns (failedPrefixes maxBlindBits) maxBlindTrials).card : ℚ) /
        Fintype.card
          (Fin maxBlindTrials → Fin (2 ^ maxBlindBits)) =
      blindAbortProbability := by
  rw [grindAbortProbability_eq]
  change
    (((((2 ^ 6 - 1 : ℕ) : ℚ) / (2 ^ 6 : ℕ)) ^ 8192)) =
      (63 / 64 : ℚ) ^ 8192
  congr 1

theorem ligeritoAbortProbability_eq :
    ((abortRuns (failedPrefixes maxLigeritoBits) maxLigeritoTrials).card : ℚ) /
        Fintype.card
          (Fin maxLigeritoTrials → Fin (2 ^ maxLigeritoBits)) =
      ligeritoAbortProbability := by
  rw [grindAbortProbability_eq]
  change
    (((((2 ^ 5 - 1 : ℕ) : ℚ) / (2 ^ 5 : ℕ)) ^ 4096)) =
      (31 / 32 : ℚ) ^ 4096
  congr 1

/-- Per-proof union bound charged by the executable security ledger. -/
def perProofAbortBound : ℚ :=
  blindAbortProbability + maxLigeritoSites * ligeritoAbortProbability

/-- Multi-proof bounded-grinding term used by the end-to-end theorem. -/
def grindingAbortBound (proofs : ℕ) : ℚ :=
  proofs * perProofAbortBound

theorem blindAbort_lt_two_pow_neg_186 :
    blindAbortProbability < 1 / (2 : ℚ) ^ 186 := by
  let slack : ℚ := 3151 / 3200
  have hblock : (63 / 64 : ℚ) ^ 45 < slack / 2 := by
    norm_num [slack]
  have hpow : (((63 / 64 : ℚ) ^ 45) ^ 182) <
      ((slack / 2) ^ 182) :=
    pow_lt_pow_left₀ hblock (by positivity) (by norm_num)
  have hslackBlock : slack ^ 30 < (101 / 160 : ℚ) := by
    norm_num [slack]
  have hslackPow : (slack ^ 30) ^ 6 < (101 / 160 : ℚ) ^ 6 :=
    pow_lt_pow_left₀ hslackBlock (by positivity) (by norm_num)
  have hslack : slack ^ 182 * (63 / 64 : ℚ) ^ 2 < 1 / 16 := by
    rw [show 182 = 30 * 6 + 2 by norm_num, pow_add, pow_mul]
    calc
      ((slack ^ 30) ^ 6 * slack ^ 2) * (63 / 64 : ℚ) ^ 2 <
          (((101 / 160 : ℚ) ^ 6 * slack ^ 2) *
            (63 / 64 : ℚ) ^ 2) :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hslackPow (by positivity)) (by positivity)
      _ < 1 / 16 := by norm_num [slack]
  unfold blindAbortProbability maxBlindTrials
  rw [show 8192 = 45 * 182 + 2 by norm_num, pow_add, pow_mul]
  calc
    ((63 / 64 : ℚ) ^ 45) ^ 182 * (63 / 64 : ℚ) ^ 2 <
        (slack / 2) ^ 182 * (63 / 64 : ℚ) ^ 2 :=
      mul_lt_mul_of_pos_right hpow (by positivity)
    _ = (1 / 2 : ℚ) ^ 182 *
        (slack ^ 182 * (63 / 64 : ℚ) ^ 2) := by ring
    _ < (1 / 2 : ℚ) ^ 182 * (1 / 16) :=
      mul_lt_mul_of_pos_left hslack (by positivity)
    _ = 1 / (2 : ℚ) ^ 186 := by norm_num [div_pow]

theorem ligeritoAbort_lt_two_pow_neg_187 :
    ligeritoAbortProbability < 1 / (2 : ℚ) ^ 187 := by
  let slack : ℚ := 255 / 256
  have hblock : (31 / 32 : ℚ) ^ 22 < slack / 2 := by
    norm_num [slack]
  have hpow : (((31 / 32 : ℚ) ^ 22) ^ 186) <
      ((slack / 2) ^ 186) :=
    pow_lt_pow_left₀ hblock (by positivity) (by norm_num)
  have hslackBlock : slack ^ 31 < (8 / 9 : ℚ) := by
    norm_num [slack]
  have hslackPow : (slack ^ 31) ^ 6 < (8 / 9 : ℚ) ^ 6 :=
    pow_lt_pow_left₀ hslackBlock (by positivity) (by norm_num)
  have hslack : slack ^ 186 * (31 / 32 : ℚ) ^ 4 < 1 / 2 := by
    rw [show 186 = 31 * 6 by norm_num, pow_mul]
    calc
      (slack ^ 31) ^ 6 * (31 / 32 : ℚ) ^ 4 <
          (8 / 9 : ℚ) ^ 6 * (31 / 32 : ℚ) ^ 4 :=
        mul_lt_mul_of_pos_right hslackPow (by positivity)
      _ < 1 / 2 := by norm_num
  unfold ligeritoAbortProbability maxLigeritoTrials
  rw [show 4096 = 22 * 186 + 4 by norm_num, pow_add, pow_mul]
  calc
    ((31 / 32 : ℚ) ^ 22) ^ 186 * (31 / 32 : ℚ) ^ 4 <
        (slack / 2) ^ 186 * (31 / 32 : ℚ) ^ 4 :=
      mul_lt_mul_of_pos_right hpow (by positivity)
    _ = (1 / 2 : ℚ) ^ 186 *
        (slack ^ 186 * (31 / 32 : ℚ) ^ 4) := by ring
    _ < (1 / 2 : ℚ) ^ 186 * (1 / 2) :=
      mul_lt_mul_of_pos_left hslack (by positivity)
    _ = 1 / (2 : ℚ) ^ 187 := by norm_num [div_pow]

end VeiledFlock.Grinding

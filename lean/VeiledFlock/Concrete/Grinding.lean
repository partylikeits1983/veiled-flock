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

/-- Constants enforced by `succinct_veil.rs`. -/
def maxBlindBits : ℕ := 5
def maxBlindTrials : ℕ := 4096
def maxLigeritoBits : ℕ := 4
def maxLigeritoTrials : ℕ := 4096
def maxLigeritoSites : ℕ := 16

def blindAbortProbability : ℚ := (31 / 32 : ℚ) ^ maxBlindTrials
def ligeritoAbortProbability : ℚ := (15 / 16 : ℚ) ^ maxLigeritoTrials

theorem blindAbortProbability_eq :
    ((abortRuns (failedPrefixes maxBlindBits) maxBlindTrials).card : ℚ) /
        Fintype.card
          (Fin maxBlindTrials → Fin (2 ^ maxBlindBits)) =
      blindAbortProbability := by
  rw [grindAbortProbability_eq]
  change
    (((((2 ^ 5 - 1 : ℕ) : ℚ) / (2 ^ 5 : ℕ)) ^ 4096)) =
      (31 / 32 : ℚ) ^ 4096
  congr 1 <;> norm_num

theorem ligeritoAbortProbability_eq :
    ((abortRuns (failedPrefixes maxLigeritoBits) maxLigeritoTrials).card : ℚ) /
        Fintype.card
          (Fin maxLigeritoTrials → Fin (2 ^ maxLigeritoBits)) =
      ligeritoAbortProbability := by
  rw [grindAbortProbability_eq]
  change
    (((((2 ^ 4 - 1 : ℕ) : ℚ) / (2 ^ 4 : ℕ)) ^ 4096)) =
      (15 / 16 : ℚ) ^ 4096
  congr 1 <;> norm_num

/-- Per-proof union bound charged by the executable security ledger. -/
def perProofAbortBound : ℚ :=
  blindAbortProbability + maxLigeritoSites * ligeritoAbortProbability

/-- Multi-proof bounded-grinding term used by the end-to-end theorem. -/
def grindingAbortBound (proofs : ℕ) : ℚ :=
  proofs * perProofAbortBound

theorem blindAbort_lt_two_pow_neg_187 :
    blindAbortProbability < 1 / (2 : ℚ) ^ 187 := by
  native_decide

theorem ligeritoAbort_lt_two_pow_neg_381 :
    ligeritoAbortProbability < 1 / (2 : ℚ) ^ 381 := by
  native_decide

end VeiledFlock.Grinding

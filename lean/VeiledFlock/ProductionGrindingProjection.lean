import VeiledFlock.ConcreteOracle
import VeiledFlock.Grinding
import VeiledFlock.Probability

/-!
# Exact leading-bit projection used by production grinding

Rust accepts a PoW answer when the most-significant `bits` of the first
digest byte are zero.  All full-ZK production profiles use at most five bits.
This module factors an exact 32-byte oracle block into that prefix and an
independent remainder, then transfers the bounded-grinding tail verbatim to
the production block-valued tape.
-/

namespace VeiledFlock.ProductionGrindingProjection

open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.Probability

private theorem pow_split (bits : ℕ) (hbits : bits ≤ 8) :
    2 ^ 8 = 2 ^ bits * 2 ^ (8 - bits) := by
  rw [← pow_add, Nat.add_sub_of_le hbits]

/-- Split a byte into its most-significant `bits` and the remaining low
bits.  `finProdFinEquiv` represents `(high, low)` as
`low + 2^(8-bits) * high`, exactly the usual byte layout. -/
def bytePrefixSplitEquiv (bits : ℕ) (hbits : bits ≤ 8) :
    Byte ≃ Fin (2 ^ bits) × Fin (2 ^ (8 - bits)) :=
  (finCongr (by norm_num : 256 = 2 ^ 8)).trans
    (finCongr (pow_split bits hbits)) |>.trans
    (finProdFinEquiv
      (m := 2 ^ bits) (n := 2 ^ (8 - bits))).symm

/-- Literal prefix tested by `leading_zero_bits` for production profiles
whose difficulty fits in the first byte. -/
def rustLeadingPrefix (bits : ℕ) (hbits : bits ≤ 8)
    (block : OracleBlock) : Fin (2 ^ bits) :=
  (bytePrefixSplitEquiv bits hbits (block 0)).1

/-- Exact factorization of a 32-byte answer into the tested prefix and all
unobserved bits. -/
def oraclePrefixSplitEquiv (bits : ℕ) (hbits : bits ≤ 8) :
    OracleBlock ≃
      Fin (2 ^ bits) ×
        (Fin (2 ^ (8 - bits)) ×
          ({index : Fin 32 // index ≠ 0} → Byte)) :=
  (Equiv.piSplitAt (0 : Fin 32) (fun _ => Byte)).trans
    ((bytePrefixSplitEquiv bits hbits).prodCongr (Equiv.refl _)) |>.trans
    (Equiv.prodAssoc _ _ _)

@[simp]
theorem oraclePrefixSplitEquiv_fst (bits : ℕ) (hbits : bits ≤ 8)
    (block : OracleBlock) :
    (oraclePrefixSplitEquiv bits hbits block).1 =
      rustLeadingPrefix bits hbits block := by
  rfl

/-- Production's leading-zero test, restricted to the actual supported
single-byte profile range. -/
def rustLeadingZeroBitsAtLeast (bits : ℕ) (hbits : bits ≤ 8)
    (block : OracleBlock) : Prop :=
  rustLeadingPrefix bits hbits block = 0

instance (bits : ℕ) (hbits : bits ≤ 8) :
    DecidablePred (rustLeadingZeroBitsAtLeast bits hbits) :=
  fun block =>
    inferInstanceAs (Decidable (rustLeadingPrefix bits hbits block = 0))

theorem rustLeadingZeroBitsAtLeast_iff (bits : ℕ) (hbits : bits ≤ 8)
    (block : OracleBlock) :
    rustLeadingZeroBitsAtLeast bits hbits block ↔
      (block 0).val / 2 ^ (8 - bits) = 0 := by
  simp [rustLeadingZeroBitsAtLeast, rustLeadingPrefix,
    bytePrefixSplitEquiv, Fin.ext_iff, finProdFinEquiv]

/-- Split a fixed run of oracle answers coordinatewise. -/
def runPrefixSplitEquiv (bits : ℕ) (hbits : bits ≤ 8) (trials : ℕ) :
    (Fin trials → OracleBlock) ≃
      (Fin trials → Fin (2 ^ bits)) ×
        (Fin trials →
          Fin (2 ^ (8 - bits)) ×
            ({index : Fin 32 // index ≠ 0} → Byte)) :=
  (Equiv.piCongrRight
      fun _ : Fin trials => oraclePrefixSplitEquiv bits hbits).trans
    ({
      toFun := fun run => (fun trial => (run trial).1,
        fun trial => (run trial).2)
      invFun := fun runs trial => (runs.1 trial, runs.2 trial)
      left_inv := fun run => by funext trial; exact Prod.eta (run trial)
      right_inv := fun runs => by rcases runs with ⟨prefixes, rest⟩; rfl
    } :
      (Fin trials →
          Fin (2 ^ bits) ×
            (Fin (2 ^ (8 - bits)) ×
              ({index : Fin 32 // index ≠ 0} → Byte))) ≃
        (Fin trials → Fin (2 ^ bits)) ×
          (Fin trials →
            Fin (2 ^ (8 - bits)) ×
              ({index : Fin 32 // index ≠ 0} → Byte)))

@[simp]
theorem runPrefixSplitEquiv_fst (bits : ℕ) (hbits : bits ≤ 8)
    (trials : ℕ) (run : Fin trials → OracleBlock) :
    (runPrefixSplitEquiv bits hbits trials run).1 =
      fun trial => rustLeadingPrefix bits hbits (run trial) := by
  funext trial
  exact oraclePrefixSplitEquiv_fst bits hbits (run trial)

/-- Exact bounded-grinding abort set on production oracle blocks. -/
noncomputable def blockAbortRuns (bits : ℕ) (hbits : bits ≤ 8)
    (trials : ℕ) : Finset (Fin trials → OracleBlock) :=
  liftBad (runPrefixSplitEquiv bits hbits trials)
    (abortRuns (failedPrefixes bits) trials)

theorem mem_blockAbortRuns_iff (bits : ℕ) (hbits : bits ≤ 8)
    (trials : ℕ) (run : Fin trials → OracleBlock) :
    run ∈ blockAbortRuns bits hbits trials ↔
      ∀ trial, ¬rustLeadingZeroBitsAtLeast bits hbits (run trial) := by
  rw [blockAbortRuns, mem_liftBad_iff, mem_abortRuns_iff]
  rw [runPrefixSplitEquiv_fst]
  simp [failedPrefixes, rustLeadingZeroBitsAtLeast]

/-- The exact production block abort probability is the abstract prefix
probability from `Grinding`. -/
theorem blockAbortProbability_eq (bits : ℕ) (hbits : bits ≤ 8)
    (trials : ℕ) :
    ((blockAbortRuns bits hbits trials).card : ℚ) /
        Fintype.card (Fin trials → OracleBlock) =
      ((abortRuns (failedPrefixes bits) trials).card : ℚ) /
        Fintype.card (Fin trials → Fin (2 ^ bits)) := by
  exact liftBad_probability_eq (runPrefixSplitEquiv bits hbits trials)
    (abortRuns (failedPrefixes bits) trials)

theorem blindBlockAbortProbability_eq :
    ((blockAbortRuns maxBlindBits (by decide) maxBlindTrials).card : ℚ) /
        Fintype.card (Fin maxBlindTrials → OracleBlock) =
      blindAbortProbability := by
  rw [blockAbortProbability_eq]
  exact blindAbortProbability_eq

theorem ligeritoBlockAbortProbability_eq :
    ((blockAbortRuns maxLigeritoBits (by decide)
        maxLigeritoTrials).card : ℚ) /
        Fintype.card (Fin maxLigeritoTrials → OracleBlock) =
      ligeritoAbortProbability := by
  rw [blockAbortProbability_eq]
  exact ligeritoAbortProbability_eq

end VeiledFlock.ProductionGrindingProjection

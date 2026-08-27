import VeiledFlock.ChallengeSampling
import VeiledFlock.Field128Serialization
import VeiledFlock.ProductionPositionProjection

/-!
# Exact scalar projections of production oracle blocks

Every scalar squeeze reads the first 16 bytes of a fresh 32-byte random-oracle
answer as a little-endian GHASH field element.  This module retains the unused
16 bytes in explicit equivalences.  It thereby transfers the rejection and
unique-position abort events from their compact field models to the literal
oracle-block tapes consumed by Rust.  It also proves the six-block layout of a
12-field equality-point attempt.
-/

namespace VeiledFlock.ProductionScalarProjection

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.Probability
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.UniquePositionSampling

/-- Exact field parsed by `sample_f128` from one oracle block. -/
noncomputable def scalarFromBlock (block : OracleBlock) : GhashField :=
  encodeGhashFieldEquiv.symm (oracleBlockSplit block).1

/-- A scalar block consists of the parsed field and the unused high half. -/
noncomputable def scalarBlockSplitEquiv :
    OracleBlock ≃ GhashField × OracleHalf :=
  oracleBlockSplit.trans
    (encodeGhashFieldEquiv.symm.prodCongr (Equiv.refl OracleHalf))

@[simp]
theorem scalarBlockSplitEquiv_fst (block : OracleBlock) :
    (scalarBlockSplitEquiv block).1 = scalarFromBlock block := by
  rfl

/-- Coordinatewise scalar parsing, retaining every unused high half. -/
noncomputable def scalarRunSplitEquiv (trials : ℕ) :
    (Fin trials → OracleBlock) ≃
      (Fin trials → GhashField) × (Fin trials → OracleHalf) :=
  (Equiv.piCongrRight
      fun _ : Fin trials => scalarBlockSplitEquiv).trans
    ({
      toFun := fun run => (fun trial => (run trial).1,
        fun trial => (run trial).2)
      invFun := fun runs trial => (runs.1 trial, runs.2 trial)
      left_inv := fun run => by funext trial; exact Prod.eta (run trial)
      right_inv := fun runs => by rcases runs with ⟨fields, halves⟩; rfl
    } :
      (Fin trials → GhashField × OracleHalf) ≃
        (Fin trials → GhashField) × (Fin trials → OracleHalf))

@[simp]
theorem scalarRunSplitEquiv_fst (trials : ℕ)
    (run : Fin trials → OracleBlock) :
    (scalarRunSplitEquiv trials run).1 =
      fun trial => scalarFromBlock (run trial) := by
  rfl

/-- Lift any field-level rejection event to literal scalar-squeeze blocks. -/
noncomputable def scalarBlockAbortRuns (failed : Finset GhashField)
    (trials : ℕ) : Finset (Fin trials → OracleBlock) :=
  liftBad (scalarRunSplitEquiv trials) (abortRuns failed trials)

theorem mem_scalarBlockAbortRuns_iff (failed : Finset GhashField)
    (trials : ℕ) (run : Fin trials → OracleBlock) :
    run ∈ scalarBlockAbortRuns failed trials ↔
      ∀ trial, scalarFromBlock (run trial) ∈ failed := by
  rw [scalarBlockAbortRuns, mem_liftBad_iff, mem_abortRuns_iff]
  rw [scalarRunSplitEquiv_fst]

theorem scalarBlockAbortProbability_eq (failed : Finset GhashField)
    (trials : ℕ) :
    ((scalarBlockAbortRuns failed trials).card : ℚ) /
        Fintype.card (Fin trials → OracleBlock) =
      ((abortRuns failed trials).card : ℚ) /
        Fintype.card (Fin trials → GhashField) := by
  exact liftBad_probability_eq (scalarRunSplitEquiv trials)
    (abortRuns failed trials)

theorem nonzeroBlockAbortProbability_eq :
    ((scalarBlockAbortRuns zeroFailure rejectionTrials).card : ℚ) /
        Fintype.card (Fin rejectionTrials → OracleBlock) =
      nonzeroAbortBound := by
  rw [scalarBlockAbortProbability_eq]
  exact nonzeroAbortBound_eq

theorem notZeroOrOneBlockAbortProbability_eq :
    ((scalarBlockAbortRuns zeroOrOneFailure rejectionTrials).card : ℚ) /
        Fintype.card (Fin rejectionTrials → OracleBlock) =
      notZeroOrOneAbortBound := by
  rw [scalarBlockAbortProbability_eq]
  exact notZeroOrOneAbortBound_eq

/-- One scalar block split further into the low-bit position and all unused
field/oracle bits. -/
noncomputable def positionBlockSplitEquiv (bits : ℕ) (hbits : bits ≤ 128) :
    OracleBlock ≃
      Fin (2 ^ bits) ×
        (Fin (2 ^ (128 - bits)) × OracleHalf) :=
  scalarBlockSplitEquiv.trans
    ((lowSplitEquiv bits hbits).prodCongr (Equiv.refl OracleHalf)) |>.trans
    (Equiv.prodAssoc _ _ _)

@[simp]
theorem positionBlockSplitEquiv_fst (bits : ℕ) (hbits : bits ≤ 128)
    (block : OracleBlock) :
    (positionBlockSplitEquiv bits hbits block).1 =
      rustLowPosition bits (scalarFromBlock block) := by
  exact lowSplitEquiv_fst bits hbits (scalarFromBlock block)

noncomputable def positionBlockRunSplitEquiv (bits : ℕ)
    (hbits : bits ≤ 128) (trials : ℕ) :
    (Fin trials → OracleBlock) ≃
      (Fin trials → Fin (2 ^ bits)) ×
        (Fin trials → Fin (2 ^ (128 - bits)) × OracleHalf) :=
  (Equiv.piCongrRight
      fun _ : Fin trials => positionBlockSplitEquiv bits hbits).trans
    ({
      toFun := fun run => (fun trial => (run trial).1,
        fun trial => (run trial).2)
      invFun := fun runs trial => (runs.1 trial, runs.2 trial)
      left_inv := fun run => by funext trial; exact Prod.eta (run trial)
      right_inv := fun runs => by rcases runs with ⟨positions, rest⟩; rfl
    } :
      (Fin trials →
          Fin (2 ^ bits) ×
            (Fin (2 ^ (128 - bits)) × OracleHalf)) ≃
        (Fin trials → Fin (2 ^ bits)) ×
          (Fin trials → Fin (2 ^ (128 - bits)) × OracleHalf))

noncomputable def positionBlockAbortRuns (bits : ℕ)
    (hbits : bits ≤ 128) (target trials : ℕ) :
    Finset (Fin trials → OracleBlock) :=
  liftBad (positionBlockRunSplitEquiv bits hbits trials)
    (UniquePositionSampling.abortRuns (2 ^ bits) target trials)

theorem positionBlockAbortProbability_eq (bits : ℕ)
    (hbits : bits ≤ 128) (target trials : ℕ) :
    ((positionBlockAbortRuns bits hbits target trials).card : ℚ) /
        Fintype.card (Fin trials → OracleBlock) =
      ((UniquePositionSampling.abortRuns
          (2 ^ bits) target trials).card : ℚ) /
        Fintype.card (Fin trials → Fin (2 ^ bits)) := by
  exact liftBad_probability_eq
    (positionBlockRunSplitEquiv bits hbits trials)
    (UniquePositionSampling.abortRuns (2 ^ bits) target trials)

theorem hadamardPositionBlockAbortProbability_le :
    ((positionBlockAbortRuns 11 (by decide)
        queryCount samplingTrials).card : ℚ) /
        Fintype.card (Fin samplingTrials → OracleBlock) ≤
      hadamardAbortBound := by
  rw [positionBlockAbortProbability_eq]
  have hdomain : 2 ^ 11 = hadamardDomain := by decide
  rw [hdomain]
  exact hadamardAbortProbability_le

theorem linearPositionBlockAbortProbability_le :
    ((positionBlockAbortRuns 13 (by decide)
        queryCount samplingTrials).card : ℚ) /
        Fintype.card (Fin samplingTrials → OracleBlock) ≤
      linearAbortBound := by
  rw [positionBlockAbortProbability_eq]
  have hdomain : 2 ^ 13 = linearDomain := by decide
  rw [hdomain]
  exact linearAbortProbability_le

/-- Both 16-byte halves of one block are parsed as independent fields. -/
noncomputable def blockFieldsEquiv :
    OracleBlock ≃ (Fin 2 → GhashField) :=
  oracleBlockSplit.trans
    (encodeGhashFieldEquiv.symm.prodCongr encodeGhashFieldEquiv.symm) |>.trans
    (finTwoArrowEquiv GhashField).symm

/-- Six blocks are exactly the 12 fields emitted by Rust's maximum equality
suffix squeeze, in counter-major then half-major order. -/
noncomputable def equalityAttemptEquiv :
    (Fin 6 → OracleBlock) ≃
      (Fin maxEqualityPointOuterCoordinates → GhashField) :=
  (Equiv.piCongrRight fun _ : Fin 6 => blockFieldsEquiv).trans
    (Equiv.curry (Fin 6) (Fin 2) GhashField).symm |>.trans
    (Equiv.arrowCongr
      (finProdFinEquiv (m := 6) (n := 2))
      (Equiv.refl GhashField)) |>.trans
    (Equiv.arrowCongr
      (finCongr (by decide : 6 * 2 = maxEqualityPointOuterCoordinates))
      (Equiv.refl GhashField))

/-- Coordinatewise equality-attempt block layout. -/
noncomputable def equalityAttemptsEquiv (trials : ℕ) :
    (Fin trials → (Fin 6 → OracleBlock)) ≃
      (Fin trials →
        (Fin maxEqualityPointOuterCoordinates → GhashField)) :=
  Equiv.piCongrRight fun _ : Fin trials => equalityAttemptEquiv

/-- Exact equality-point abort set on the six counter blocks per attempt. -/
noncomputable def equalityBlockAbortRuns (trials : ℕ) :
    Finset (Fin trials → (Fin 6 → OracleBlock)) :=
  Finset.univ.filter fun runs =>
    equalityAttemptsEquiv trials runs ∈
      abortRuns equalityPointVectorFailure trials

theorem mem_equalityBlockAbortRuns_iff (trials : ℕ)
    (runs : Fin trials → (Fin 6 → OracleBlock)) :
    runs ∈ equalityBlockAbortRuns trials ↔
      equalityAttemptsEquiv trials runs ∈
        abortRuns equalityPointVectorFailure trials := by
  simp [equalityBlockAbortRuns]

theorem card_equalityBlockAbortRuns (trials : ℕ) :
    (equalityBlockAbortRuns trials).card =
      (abortRuns equalityPointVectorFailure trials).card := by
  refine Finset.card_equiv (equalityAttemptsEquiv trials) fun runs => ?_
  simp [equalityBlockAbortRuns]

theorem equalityBlockAbortProbability_le :
    ((equalityBlockAbortRuns rejectionTrials).card : ℚ) /
        Fintype.card
          (Fin rejectionTrials → (Fin 6 → OracleBlock)) ≤
      equalityPointAbortBound := by
  rw [card_equalityBlockAbortRuns]
  rw [Fintype.card_congr (equalityAttemptsEquiv rejectionTrials)]
  exact equalityPointAbortProbability_le

end VeiledFlock.ProductionScalarProjection

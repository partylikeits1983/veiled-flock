import VeiledFlock.Algebra.Field128Serialization
import VeiledFlock.Concrete.UniquePositionSampling

/-!
# Exact low-bit projection used by production position sampling

Rust maps a sampled `F128` to a codeword position by taking the low limb and
masking by `domain - 1`.  Both production domains are powers of two, so this
is exactly reduction of the 128 little-endian coefficient bits modulo
`2^bits`.  The equivalence below splits a uniform field element into that
low position and an independent high-bit remainder.  Consequently the exact
Rust draw stream has the uniform finite law assumed by the coupon-collector
bound.
-/

namespace VeiledFlock.ProductionPositionProjection

open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.Probability
open VeiledFlock.UniquePositionSampling

/-- A bit vector is definitionally a bounded natural number of the matching
power-of-two size. -/
def bitVecFinEquiv (width : ℕ) : BitVec width ≃ Fin (2 ^ width) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv := BitVec.ofFin_toFin
  right_inv := BitVec.toFin_ofFin

private theorem pow_split (bits : ℕ) (hbits : bits ≤ 128) :
    2 ^ 128 = 2 ^ (128 - bits) * 2 ^ bits := by
  rw [← pow_add, Nat.sub_add_cancel hbits]

/-- Exact factorization into the low `bits` used as the position and the
remaining independent coefficient bits. -/
noncomputable def lowSplitEquiv (bits : ℕ) (hbits : bits ≤ 128) :
    GhashField ≃ Fin (2 ^ bits) × Fin (2 ^ (128 - bits)) :=
  bitsGhashEquiv.symm |>.trans
    (bitVecFinEquiv 128) |>.trans
    (finCongr (pow_split bits hbits)) |>.trans
    (finProdFinEquiv (m := 2 ^ (128 - bits))
      (n := 2 ^ bits)).symm |>.trans
    (Equiv.prodComm _ _)

/-- Literal power-of-two low-bit mask on the exact stored field
representation. -/
noncomputable def rustLowPosition (bits : ℕ) (value : GhashField) :
    Fin (2 ^ bits) :=
  Fin.ofNat (2 ^ bits) (bitsGhashEquiv.symm value).toNat

@[simp]
theorem lowSplitEquiv_fst (bits : ℕ) (hbits : bits ≤ 128)
    (value : GhashField) :
    (lowSplitEquiv bits hbits value).1 = rustLowPosition bits value := by
  apply Fin.ext
  simp [lowSplitEquiv, rustLowPosition, bitVecFinEquiv,
    finProdFinEquiv]

/-- Therefore a uniform production field draw projects to an exactly uniform
power-of-two position. -/
theorem uniform_rustLowPosition (bits : ℕ) (hbits : bits ≤ 128) :
    (PMF.uniformOfFintype GhashField).map (rustLowPosition bits) =
      PMF.uniformOfFintype (Fin (2 ^ bits)) := by
  calc
    (PMF.uniformOfFintype GhashField).map (rustLowPosition bits) =
        (PMF.uniformOfFintype
          (Fin (2 ^ bits) × Fin (2 ^ (128 - bits)))).map Prod.fst := by
      apply uniform_map_eq_of_equiv (lowSplitEquiv bits hbits)
      intro value
      exact (lowSplitEquiv_fst bits hbits value).symm
    _ = PMF.uniformOfFintype (Fin (2 ^ bits)) := by
      calc
        _ = (PMF.uniformOfFintype (Fin (2 ^ bits))).map id :=
          uniform_map_ignore_right
            (A := Fin (2 ^ bits)) (B := Fin (2 ^ (128 - bits)))
            (fun value => value)
        _ = PMF.uniformOfFintype (Fin (2 ^ bits)) := PMF.map_id _

/-- Split every draw in a fixed-length run coordinatewise, then transpose the
function of pairs into a pair of functions. -/
noncomputable def runSplitEquiv (bits : ℕ) (hbits : bits ≤ 128)
    (trials : ℕ) :
    (Fin trials → GhashField) ≃
      (Fin trials → Fin (2 ^ bits)) ×
        (Fin trials → Fin (2 ^ (128 - bits))) :=
  (Equiv.piCongrRight fun _ : Fin trials => lowSplitEquiv bits hbits).trans
    ({
      toFun := fun run => (fun trial => (run trial).1,
        fun trial => (run trial).2)
      invFun := fun runs trial => (runs.1 trial, runs.2 trial)
      left_inv := fun run => by funext trial; exact Prod.eta (run trial)
      right_inv := fun runs => by rcases runs with ⟨low, high⟩; rfl
    } :
      (Fin trials →
          Fin (2 ^ bits) × Fin (2 ^ (128 - bits))) ≃
        (Fin trials → Fin (2 ^ bits)) ×
          (Fin trials → Fin (2 ^ (128 - bits))))

@[simp]
theorem runSplitEquiv_fst (bits : ℕ) (hbits : bits ≤ 128)
    (trials : ℕ) (run : Fin trials → GhashField) :
    (runSplitEquiv bits hbits trials run).1 =
      fun trial => rustLowPosition bits (run trial) := by
  funext trial
  exact lowSplitEquiv_fst bits hbits (run trial)

/-- Exact abort set on the field-valued draw tape used by Rust. -/
noncomputable def fieldAbortRuns (bits : ℕ) (hbits : bits ≤ 128)
    (target trials : ℕ) : Finset (Fin trials → GhashField) :=
  liftBad (runSplitEquiv bits hbits trials)
    (abortRuns (2 ^ bits) target trials)

theorem mem_fieldAbortRuns_iff (bits : ℕ) (hbits : bits ≤ 128)
    (target trials : ℕ) (run : Fin trials → GhashField) :
    run ∈ fieldAbortRuns bits hbits target trials ↔
      (observedPositions
        (fun trial => rustLowPosition bits (run trial))).card < target := by
  rw [fieldAbortRuns, mem_liftBad_iff]
  simp only [abortRuns, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [runSplitEquiv_fst]

/-- The production field-valued abort event has exactly the abstract uniform
position probability used by `UniquePositionSampling`. -/
theorem fieldAbortProbability_eq (bits : ℕ) (hbits : bits ≤ 128)
    (target trials : ℕ) :
    ((fieldAbortRuns bits hbits target trials).card : ℚ) /
        Fintype.card (Fin trials → GhashField) =
      ((abortRuns (2 ^ bits) target trials).card : ℚ) /
        Fintype.card (Fin trials → Fin (2 ^ bits)) := by
  exact liftBad_probability_eq (runSplitEquiv bits hbits trials)
    (abortRuns (2 ^ bits) target trials)

/-- Hadamard positions use the low 11 bits exactly. -/
theorem hadamardFieldAbortProbability_le :
    ((fieldAbortRuns 11 (by decide) queryCount samplingTrials).card : ℚ) /
        Fintype.card (Fin samplingTrials → GhashField) ≤
      hadamardAbortBound := by
  rw [fieldAbortProbability_eq]
  have hdomain : 2 ^ 11 = hadamardDomain := by decide
  rw [hdomain]
  exact hadamardAbortProbability_le

/-- Linear positions use the low 13 bits exactly. -/
theorem linearFieldAbortProbability_le :
    ((fieldAbortRuns 13 (by decide) queryCount samplingTrials).card : ℚ) /
        Fintype.card (Fin samplingTrials → GhashField) ≤
      linearAbortBound := by
  rw [fieldAbortProbability_eq]
  have hdomain : 2 ^ 13 = linearDomain := by decide
  rw [hdomain]
  exact linearAbortProbability_le

end VeiledFlock.ProductionPositionProjection

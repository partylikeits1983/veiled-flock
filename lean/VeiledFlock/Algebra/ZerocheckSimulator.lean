import Mathlib
import VeiledFlock.Algebra.BinaryPolynomial

/-!
# Zerocheck simulator solve equations

The executable ROM simulator samples two quadratic-round messages and solves
the remaining one so that the verifier's running claim reaches its public
terminal target.  This file proves the exact equations, including the
`rho = 0` and `rho = 1` branches that make the infinity coefficient vanish.
-/

namespace VeiledFlock.ZerocheckSimulator

variable {F : Type*} [Field F] [CharP F 2]

def runningWeight (rEq rho : F) : F := (1 + rho) / (1 + rEq)
def oneWeight (rEq rho : F) : F := (rEq + rho) / (1 + rEq)
def infinityWeight (rho : F) : F := rho * (1 + rho)

def foldRound (running gOne gInfinity rEq rho : F) : F :=
  runningWeight rEq rho * running + oneWeight rEq rho * gOne +
    infinityWeight rho * gInfinity

/-- Formula implemented when the infinity coefficient is nonzero.  Addition
is subtraction in the characteristic-two production field. -/
def solveInfinity (running target rEq rho randomOne : F) : F :=
  (target + runningWeight rEq rho * running +
    oneWeight rEq rho * randomOne) / infinityWeight rho

/-- Formula implemented when infinity vanishes but the one coefficient is
nonzero. -/
def solveOne (running target rEq rho randomInfinity : F) : F :=
  (target + runningWeight rEq rho * running +
    infinityWeight rho * randomInfinity) / oneWeight rEq rho

theorem foldRound_solveInfinity (running target rEq rho randomOne : F)
    (hinfinity : infinityWeight rho ≠ 0) :
    foldRound running randomOne
      (solveInfinity running target rEq rho randomOne) rEq rho = target := by
  simp only [foldRound, solveInfinity]
  field_simp
  have htwo (value : F) : value + value = 0 :=
    BinaryPolynomial.add_self_eq_zero_charTwo value
  rw [add_assoc, add_assoc]
  linear_combination htwo (runningWeight rEq rho * running) +
    htwo (oneWeight rEq rho * randomOne)

theorem foldRound_solveOne (running target rEq rho randomInfinity : F)
    (hone : oneWeight rEq rho ≠ 0) :
    foldRound running (solveOne running target rEq rho randomInfinity)
      randomInfinity rEq rho = target := by
  simp only [foldRound, solveOne]
  field_simp
  have htwo (value : F) : value + value = 0 :=
    BinaryPolynomial.add_self_eq_zero_charTwo value
  linear_combination htwo (runningWeight rEq rho * running) +
    htwo (infinityWeight rho * randomInfinity)

theorem one_add_ne_zero_of_ne_one {value : F} (hvalue : value ≠ 1) :
    1 + value ≠ 0 := by
  intro hzero
  have : value = -1 := eq_neg_of_add_eq_zero_right hzero
  rw [CharTwo.neg_eq] at this
  exact hvalue this

theorem oneWeight_eq_code (rEq rho : F) (hrEq : rEq ≠ 1) :
    rEq * runningWeight rEq rho + rho = oneWeight rEq rho := by
  simp only [runningWeight, oneWeight]
  field_simp [one_add_ne_zero_of_ne_one hrEq]
  have hcancel := BinaryPolynomial.add_self_eq_zero_charTwo (rEq * rho)
  linear_combination hcancel

theorem infinityWeight_eq_zero_iff (rho : F) :
    infinityWeight rho = 0 ↔ rho = 0 ∨ rho = 1 := by
  rw [infinityWeight, mul_eq_zero]
  constructor
  · intro h
    rcases h with hzero | hplus
    · exact Or.inl hzero
    · right
      have : rho = -1 := eq_neg_of_add_eq_zero_right hplus
      simpa only [CharTwo.neg_eq] using this
  · intro h
    rcases h with rfl | rfl
    · simp
    · have htwo : (1 : F) + 1 = 0 :=
        BinaryPolynomial.add_self_eq_zero_charTwo 1
      simp [htwo]

/-- Every non-identity `(rho,rEq)` pair reaches one of the two solver
branches.  This is the exact corner-case claim behind the Rust search for the
last non-identity recursive round. -/
theorem solver_branch_exists (rEq rho : F) (hrEq : rEq ≠ 1)
    (hnonidentity : ¬ (rho = 0 ∧ rEq = 0)) :
    infinityWeight rho ≠ 0 ∨ oneWeight rEq rho ≠ 0 := by
  by_cases hinfinity : infinityWeight rho = 0
  · right
    rw [infinityWeight_eq_zero_iff] at hinfinity
    rcases hinfinity with hrho | hrho
    · subst rho
      simp only [oneWeight, add_zero]
      exact div_ne_zero (by
        intro hrzero
        exact hnonidentity ⟨rfl, hrzero⟩)
        (one_add_ne_zero_of_ne_one hrEq)
    · subst rho
      simp only [oneWeight]
      have hden := one_add_ne_zero_of_ne_one hrEq
      exact div_ne_zero (by simpa [add_comm] using hden) hden
  · exact Or.inl hinfinity

/-- A solver can therefore always force the requested terminal target at the
selected non-identity round, while leaving one of the two messages uniformly
sampled. -/
theorem exists_solved_messages (running target rEq rho random : F)
    (hrEq : rEq ≠ 1) (hnonidentity : ¬ (rho = 0 ∧ rEq = 0)) :
    ∃ gOne gInfinity,
      foldRound running gOne gInfinity rEq rho = target := by
  rcases solver_branch_exists rEq rho hrEq hnonidentity with h | h
  · exact ⟨random, solveInfinity running target rEq rho random,
      foldRound_solveInfinity running target rEq rho random h⟩
  · exact ⟨solveOne running target rEq rho random, random,
      foldRound_solveOne running target rEq rho random h⟩

/-- A `(rho,rEq) = (0,0)` recursive round is an identity independently of
both prover messages.  This is why the Rust simulator may leave an arbitrary
suffix of such rounds after the last solved round. -/
theorem foldRound_zero_zero (running gOne gInfinity : F) :
    foldRound running gOne gInfinity 0 0 = running := by
  simp [foldRound, runningWeight, oneWeight, infinityWeight]

/-- A recursive round together with its two prover messages. -/
structure ExecutedRound where
  rEq : F
  rho : F
  gOne : F
  gInfinity : F

def ExecutedRound.parameters (round : ExecutedRound (F := F)) : F × F :=
  (round.rEq, round.rho)

def executeRounds (running : F) (rounds : List (ExecutedRound (F := F))) : F :=
  rounds.foldl (fun claim round =>
    foldRound claim round.gOne round.gInfinity round.rEq round.rho) running

def zeroMessages (parameters : List (F × F)) :
    List (ExecutedRound (F := F)) :=
  parameters.map fun parameter =>
    { rEq := parameter.1, rho := parameter.2, gOne := 0, gInfinity := 0 }

@[simp]
theorem zeroMessages_parameters (parameters : List (F × F)) :
    (zeroMessages parameters).map ExecutedRound.parameters = parameters := by
  simp [zeroMessages, ExecutedRound.parameters, Function.comp_def]

/-- Any all-identity suffix preserves the claim. -/
theorem executeRounds_zeroMessages_of_identity (running : F)
    (parameters : List (F × F))
    (hidentity : ∀ parameter ∈ parameters,
      parameter.2 = 0 ∧ parameter.1 = 0) :
    executeRounds running (zeroMessages parameters) = running := by
  induction parameters generalizing running with
  | nil => rfl
  | cons parameter tail ih =>
      have hhead := hidentity parameter (by simp)
      have htail : ∀ value ∈ tail, value.2 = 0 ∧ value.1 = 0 := by
        intro value hvalue
        exact hidentity value (by simp [hvalue])
      rcases hhead with ⟨hrho, hrEq⟩
      simp only [zeroMessages, List.map_cons, executeRounds, List.foldl_cons,
        hrho, hrEq]
      rw [foldRound_zero_zero]
      exact ih running htail

/-- Exact whole-loop simulator theorem.  If all equality coordinates avoid
one and at least one recursive pair is non-identity, messages can be chosen
so that the Rust verifier's complete fold reaches any requested public
terminal claim.  The induction implements the same "last non-identity"
strategy as `RomZerocheckSimulator`: arbitrary prefix messages, one solved
round, then an identity suffix. -/
theorem exists_executedRounds (running target random : F)
    (parameters : List (F × F))
    (hrEq : ∀ parameter ∈ parameters, parameter.1 ≠ 1)
    (hnonidentity : ∃ parameter ∈ parameters,
      ¬ (parameter.2 = 0 ∧ parameter.1 = 0)) :
    ∃ rounds : List (ExecutedRound (F := F)),
      rounds.map ExecutedRound.parameters = parameters ∧
        executeRounds running rounds = target := by
  induction parameters generalizing running with
  | nil => simp at hnonidentity
  | cons parameter tail ih =>
      by_cases htail : ∃ value ∈ tail,
          ¬ (value.2 = 0 ∧ value.1 = 0)
      · let first : ExecutedRound (F := F) :=
          { rEq := parameter.1, rho := parameter.2,
            gOne := random, gInfinity := random }
        have htailEq : ∀ value ∈ tail, value.1 ≠ 1 := by
          intro value hvalue
          exact hrEq value (by simp [hvalue])
        obtain ⟨rounds, hparameters, htarget⟩ :=
          ih (foldRound running random random parameter.1 parameter.2)
            htailEq htail
        refine ⟨first :: rounds, ?_, ?_⟩
        · simp [first, ExecutedRound.parameters, hparameters]
        · simpa [executeRounds, first] using htarget
      · have htailIdentity : ∀ value ∈ tail,
          value.2 = 0 ∧ value.1 = 0 := by
          intro value hvalue
          by_contra hvalueIdentity
          exact htail ⟨value, hvalue, hvalueIdentity⟩
        have hheadNonidentity :
            ¬ (parameter.2 = 0 ∧ parameter.1 = 0) := by
          intro hhead
          rcases hnonidentity with ⟨value, hvalue, hvalueNonidentity⟩
          rcases List.mem_cons.mp hvalue with rfl | hvalue
          · exact hvalueNonidentity hhead
          · exact hvalueNonidentity (htailIdentity value hvalue)
        obtain ⟨gOne, gInfinity, hsolved⟩ :=
          exists_solved_messages running target parameter.1 parameter.2 random
            (hrEq parameter (by simp)) hheadNonidentity
        let first : ExecutedRound (F := F) :=
          { rEq := parameter.1, rho := parameter.2,
            gOne := gOne, gInfinity := gInfinity }
        refine ⟨first :: zeroMessages tail, ?_, ?_⟩
        · simp [first, ExecutedRound.parameters]
        · simp only [executeRounds, List.foldl_cons, first]
          rw [hsolved]
          exact executeRounds_zeroMessages_of_identity target tail htailIdentity

end VeiledFlock.ZerocheckSimulator

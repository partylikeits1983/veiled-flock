import VeiledFlock.Algebra.Field128Serialization
import VeiledFlock.Concrete.ChallengeSampling
import VeiledFlock.Algebra.ZerocheckSimulator

/-!
# The production zerocheck simulator has a solve round

The optimized Rust zerocheck fixes its first recursive equality coordinate to
`PHI_8_TABLE[0xF7]`.  This file records that exact two-limb value and proves by
kernel-checked computation that it is neither zero nor one in the concrete
GHASH quotient field.  Consequently the complete recursive simulator theorem
always has a non-identity round; it does not abort or condition the random
oracle challenges on an algebraic degeneracy event.
-/

namespace VeiledFlock.ConcreteZerocheck

open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.ZerocheckSimulator

set_option maxHeartbeats 800000

private theorem mapped_ne_one_of_bits_ne_one (bits : Bits128)
    (hbits : bits ≠ 1) : bitsGhashEquiv bits ≠ 1 := by
  intro hone
  apply hbits
  apply bitsGhashEquiv.injective
  rw [bitsGhashEquiv_one]
  exact hone

private theorem mapped_ne_zero_of_bits_ne_zero (bits : Bits128)
    (hbits : bits ≠ 0) : bitsGhashEquiv bits ≠ 0 := by
  intro hzero
  apply hbits
  apply bitsGhashEquiv.injective
  rw [bitsGhashEquiv_zero]
  exact hzero

/-- The three `PHI_8_TABLE` entries selected by
`SMALL_CHAL_F8 = [0xF7, 0x53, 0xB5]`, with the same little-endian limbs as
the Rust source. -/
def smallFriendlyBits : Fin 3 → Bits128 := ![
  BitVec.ofNat 128
    ((0x1cf7a0fe8922c83f : Nat) * 2 ^ 64 + 0xd8a5ae31928b4da1),
  BitVec.ofNat 128
    ((0xffdb65d9987f058c : Nat) * 2 ^ 64 + 0xa0415e708193f42a),
  BitVec.ofNat 128
    ((0x44020450758a0366 : Nat) * 2 ^ 64 + 0x26cb812e5dc6f8a5)]

noncomputable def smallFriendly (index : Fin 3) : GhashField :=
  bitsGhashEquiv (smallFriendlyBits index)

theorem smallFriendlyBits_ne_one (index : Fin 3) :
    smallFriendlyBits index ≠ 1 := by
  fin_cases index <;> native_decide

theorem smallFriendly_ne_one (index : Fin 3) :
    smallFriendly index ≠ 1 :=
  mapped_ne_one_of_bits_ne_one _ (smallFriendlyBits_ne_one index)

/-- Stored coefficient vectors `γ`, `γ²`, `γ⁴`, and `γ⁸` used to
construct the four medium friendly coordinates. -/
def gammaPowerBits : Fin 4 → Bits128 := ![
  BitVec.ofNat 128 2,
  BitVec.ofNat 128 4,
  BitVec.ofNat 128 16,
  BitVec.ofNat 128 256]

noncomputable def gammaPower (index : Fin 4) : GhashField :=
  bitsGhashEquiv (gammaPowerBits index)

theorem gammaPowerBits_ne_one (index : Fin 4) :
    gammaPowerBits index ≠ 1 := by
  fin_cases index <;> native_decide

theorem gammaPower_ne_one (index : Fin 4) : gammaPower index ≠ 1 :=
  mapped_ne_one_of_bits_ne_one _ (gammaPowerBits_ne_one index)

noncomputable def mediumFriendly (index : Fin 4) : GhashField :=
  gammaPower index / (1 + gammaPower index)

theorem mediumFriendly_ne_one (index : Fin 4) :
    mediumFriendly index ≠ 1 := by
  have hdenominator : (1 : GhashField) + gammaPower index ≠ 0 :=
    one_add_ne_zero_of_ne_one (gammaPower_ne_one index)
  intro hone
  have heq : gammaPower index = 1 + gammaPower index := by
    have hdiv : gammaPower index / (1 + gammaPower index) = 1 := by
      simpa [mediumFriendly] using hone
    simpa using (div_eq_iff hdenominator).mp hdiv
  have honeZero : (1 : GhashField) = 0 := by
    linear_combination -heq
  exact one_ne_zero honeZero

/-- The exact seven-coordinate fixed prefix assembled by
`assemble_eq_point`. -/
noncomputable def friendlyCoordinates : Fin 7 → GhashField := ![
  smallFriendly 0, smallFriendly 1, smallFriendly 2,
  mediumFriendly 0, mediumFriendly 1, mediumFriendly 2, mediumFriendly 3]

theorem friendlyCoordinates_ne_one (index : Fin 7) :
    friendlyCoordinates index ≠ 1 := by
  fin_cases index <;>
    simp [friendlyCoordinates, smallFriendly_ne_one, mediumFriendly_ne_one]

/-- `PHI_8_TABLE[0xF7]`, copied bit-for-bit from the production Rust table.
The low limb occupies coefficients `0..63`. -/
def firstFriendlyBits : Bits128 :=
  smallFriendlyBits 0

theorem firstFriendlyBits_ne_zero : firstFriendlyBits ≠ 0 := by
  native_decide

theorem firstFriendlyBits_ne_one : firstFriendlyBits ≠ 1 := by
  native_decide

/-- The first production recursive equality coordinate, interpreted in the
proved GHASH quotient field. -/
noncomputable def firstFriendly : GhashField :=
  smallFriendly 0

theorem firstFriendly_ne_zero : firstFriendly ≠ 0 := by
  intro hzero
  apply firstFriendlyBits_ne_zero
  exact bitsGhashEquiv.injective (by
    change bitsGhashEquiv firstFriendlyBits = bitsGhashEquiv (0 : Bits128)
    rw [bitsGhashEquiv_zero]
    exact hzero)

theorem firstFriendly_ne_one : firstFriendly ≠ 1 := by
  exact smallFriendly_ne_one 0

/-- Production's fixed first coordinate rules out an all-identity recursive
loop for every random-oracle challenge `rho`. -/
theorem firstFriendly_pair_nonidentity (rho : GhashField) :
    ¬ (rho = 0 ∧ firstFriendly = 0) := by
  intro hidentity
  exact firstFriendly_ne_zero hidentity.2

/-- Concrete specialization of the whole-loop solver.  The tail consists of
the remaining six fixed friendly coordinates followed by rejection-sampled
outer coordinates; the production sampler establishes `tailEqNotOne`.
The first fixed coordinate supplies the required non-identity round for every
possible random-oracle challenge, including zero and one. -/
theorem production_exists_executedRounds
    (running target random firstRho : GhashField)
    (tail : List (GhashField × GhashField))
    (tailEqNotOne : ∀ parameter ∈ tail, parameter.1 ≠ 1) :
    ∃ rounds : List (VeiledFlock.ZerocheckSimulator.ExecutedRound
        (F := GhashField)),
      rounds.map VeiledFlock.ZerocheckSimulator.ExecutedRound.parameters =
          (firstFriendly, firstRho) :: tail ∧
        VeiledFlock.ZerocheckSimulator.executeRounds running rounds = target := by
  apply VeiledFlock.ZerocheckSimulator.exists_executedRounds
    running target random
  · intro parameter hparameter
    rcases List.mem_cons.mp hparameter with rfl | htail
    · exact firstFriendly_ne_one
    · exact tailEqNotOne parameter htail
  · exact ⟨(firstFriendly, firstRho), by simp,
      firstFriendly_pair_nonidentity firstRho⟩

/-- Recursive `(r_eq, rho)` parameters in production order: the seven fixed
friendly coordinates, followed by the accepted outer equality-point suffix. -/
noncomputable def productionParameters {outer : ℕ}
    (friendlyRhos : Fin 7 → GhashField)
    (outerEq outerRhos : Fin outer → GhashField) :
    List (GhashField × GhashField) :=
  List.ofFn (fun index => (friendlyCoordinates index, friendlyRhos index)) ++
    List.ofFn (fun index => (outerEq index, outerRhos index))

theorem productionParameters_eq_not_one {outer : ℕ}
    (friendlyRhos : Fin 7 → GhashField)
    (outerEq outerRhos : Fin outer → GhashField)
    (houter : ∀ index, outerEq index ≠ 1) :
    ∀ parameter ∈
        productionParameters friendlyRhos outerEq outerRhos,
      parameter.1 ≠ 1 := by
  intro parameter hparameter
  rw [productionParameters, List.mem_append] at hparameter
  rcases hparameter with hfixed | houterParameter
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hfixed
    exact friendlyCoordinates_ne_one index
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp houterParameter
    exact houter index

theorem productionParameters_nonidentity {outer : ℕ}
    (friendlyRhos : Fin 7 → GhashField)
    (outerEq outerRhos : Fin outer → GhashField) :
    ∃ parameter ∈ productionParameters friendlyRhos outerEq outerRhos,
      ¬ (parameter.2 = 0 ∧ parameter.1 = 0) := by
  let first : Fin 7 := ⟨0, by decide⟩
  refine ⟨(friendlyCoordinates first, friendlyRhos first), ?_, ?_⟩
  · simp [productionParameters, first]
  · intro hidentity
    have hfirst : friendlyCoordinates first = firstFriendly := rfl
    exact firstFriendly_ne_zero (hfirst ▸ hidentity.2)

/-- Fully concrete whole-loop simulation theorem.  The sole premise is the
postcondition of the production bounded equality-point sampler: every accepted
outer coordinate differs from one.  No random `rho` value is excluded. -/
theorem acceptedProduction_exists_executedRounds {outer : ℕ}
    (running target random : GhashField)
    (friendlyRhos : Fin 7 → GhashField)
    (outerEq outerRhos : Fin outer → GhashField)
    (houter : ∀ index, outerEq index ≠ 1) :
    ∃ rounds : List (VeiledFlock.ZerocheckSimulator.ExecutedRound
        (F := GhashField)),
      rounds.map VeiledFlock.ZerocheckSimulator.ExecutedRound.parameters =
          productionParameters friendlyRhos outerEq outerRhos ∧
        VeiledFlock.ZerocheckSimulator.executeRounds running rounds =
          target := by
  exact VeiledFlock.ZerocheckSimulator.exists_executedRounds
    running target random
    (productionParameters friendlyRhos outerEq outerRhos)
    (productionParameters_eq_not_one friendlyRhos outerEq outerRhos houter)
    (productionParameters_nonidentity friendlyRhos outerEq outerRhos)

/-- End-to-end connection from a successful production 4096-attempt equality
sampler to a complete accepting recursive transcript. -/
theorem boundedSampler_exists_executedRounds
    (running target random : GhashField)
    (friendlyRhos : Fin 7 → GhashField)
    (outerRuns : Fin ChallengeSampling.rejectionTrials →
      (Fin ChallengeSampling.maxEqualityPointOuterCoordinates → GhashField))
    (outerEq outerRhos :
      Fin ChallengeSampling.maxEqualityPointOuterCoordinates → GhashField)
    (haccepted : RejectionSampling.firstGood
        ChallengeSampling.equalityPointVectorFailure outerRuns = some outerEq) :
    ∃ rounds : List (VeiledFlock.ZerocheckSimulator.ExecutedRound
        (F := GhashField)),
      rounds.map VeiledFlock.ZerocheckSimulator.ExecutedRound.parameters =
          productionParameters friendlyRhos outerEq outerRhos ∧
        VeiledFlock.ZerocheckSimulator.executeRounds running rounds =
          target := by
  exact acceptedProduction_exists_executedRounds running target random
    friendlyRhos outerEq outerRhos
    (ChallengeSampling.equalityPointAccepted_ne_one haccepted)

end VeiledFlock.ConcreteZerocheck

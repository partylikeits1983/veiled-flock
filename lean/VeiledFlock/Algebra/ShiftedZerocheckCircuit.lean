import VeiledFlock.Algebra.ConcreteZerocheck

/-!
# Shifted zerocheck circuit satisfaction

The Rust shifted verifier treats every published PIOP scalar as a constant and
adds one private VEIL mask variable to recover the underlying scalar.  In the
characteristic-two production field, publishing `value + mask` therefore
recovers exactly `value`.  This file applies that identity to the full
recursive zerocheck fold and proves that the simulator transcript satisfies
the shifted verifier's sole multiplication constraint.
-/

namespace VeiledFlock.ShiftedZerocheckCircuit

open VeiledFlock.BinaryPolynomial
open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteZerocheck
open VeiledFlock.Field128Ghash
open VeiledFlock.ZerocheckSimulator

variable {F : Type*} [Field F] [CharP F 2]

def publish (value mask : F) : F := value + mask

/-- Evaluation of `constant(masked) + privateMask` in the shifted circuit. -/
def recover (masked privateMask : F) : F := masked + privateMask

@[simp]
theorem recover_publish (value mask : F) :
    recover (publish value mask) mask = value := by
  simp only [recover, publish, add_assoc]
  rw [add_self_eq_zero_charTwo, add_zero]

/-- One recursive round as seen by the shifted verifier. -/
structure MaskedRound where
  rEq : F
  rho : F
  maskedOne : F
  maskedInfinity : F
  privateOne : F
  privateInfinity : F

def maskRound (round : ExecutedRound (F := F)) (masks : F × F) :
    MaskedRound (F := F) where
  rEq := round.rEq
  rho := round.rho
  maskedOne := publish round.gOne masks.1
  maskedInfinity := publish round.gInfinity masks.2
  privateOne := masks.1
  privateInfinity := masks.2

def MaskedRound.parameters (round : MaskedRound (F := F)) : F × F :=
  (round.rEq, round.rho)

def MaskedRound.underlying (round : MaskedRound (F := F)) :
    ExecutedRound (F := F) where
  rEq := round.rEq
  rho := round.rho
  gOne := recover round.maskedOne round.privateOne
  gInfinity := recover round.maskedInfinity round.privateInfinity

@[simp]
theorem maskRound_parameters (round : ExecutedRound (F := F))
    (masks : F × F) :
    (maskRound round masks).parameters = round.parameters := rfl

@[simp]
theorem maskRound_underlying (round : ExecutedRound (F := F))
    (masks : F × F) :
    (maskRound round masks).underlying = round := by
  cases round
  simp [maskRound, MaskedRound.underlying]

/-- Mask every round with an independently indexed pair of private values. -/
def maskRounds : (rounds : List (ExecutedRound (F := F))) →
    (Fin rounds.length → F × F) → List (MaskedRound (F := F))
  | [], _ => []
  | round :: rounds, masks =>
      maskRound round (masks 0) ::
        maskRounds rounds (fun index => masks index.succ)

@[simp]
theorem maskRounds_length (rounds : List (ExecutedRound (F := F)))
    (masks : Fin rounds.length → F × F) :
    (maskRounds rounds masks).length = rounds.length := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      simp only [maskRounds, List.length_cons]
      rw [ih]

@[simp]
theorem maskRounds_parameters (rounds : List (ExecutedRound (F := F)))
    (masks : Fin rounds.length → F × F) :
    (maskRounds rounds masks).map MaskedRound.parameters =
      rounds.map ExecutedRound.parameters := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      simp only [maskRounds, List.map_cons, maskRound_parameters,
        List.cons.injEq, true_and]
      exact ih (fun index => masks index.succ)

def executeShifted (running : F) (rounds : List (MaskedRound (F := F))) : F :=
  rounds.foldl (fun claim round =>
    foldRound claim
      (recover round.maskedOne round.privateOne)
      (recover round.maskedInfinity round.privateInfinity)
      round.rEq round.rho) running

@[simp]
theorem executeShifted_maskRounds (running : F)
    (rounds : List (ExecutedRound (F := F)))
    (masks : Fin rounds.length → F × F) :
    executeShifted running (maskRounds rounds masks) =
      executeRounds running rounds := by
  induction rounds generalizing running with
  | nil => rfl
  | cons round rounds ih =>
      simp only [maskRounds, executeShifted, List.foldl_cons, maskRound,
        recover_publish, executeRounds]
      change
        executeShifted
            (foldRound running round.gOne round.gInfinity round.rEq round.rho)
            (maskRounds rounds fun index => masks index.succ) =
          executeRounds
            (foldRound running round.gOne round.gInfinity round.rEq round.rho)
            rounds
      exact ih _ _

/-- The exact Boolean meaning of the one multiplication gate emitted by
`shifted_verifier_circuit`. -/
def multiplicationConstraint (running : F)
    (rounds : List (MaskedRound (F := F)))
    (maskedA privateA maskedB privateB : F) : Prop :=
  recover maskedA privateA * recover maskedB privateB =
    executeShifted running rounds

theorem multiplicationConstraint_of_simulator
    (running finalA finalB : F)
    (rounds : List (ExecutedRound (F := F)))
    (hfinal : executeRounds running rounds = finalA * finalB)
    (roundMasks : Fin rounds.length → F × F)
    (finalMaskA finalMaskB : F) :
    multiplicationConstraint running (maskRounds rounds roundMasks)
      (publish finalA finalMaskA) finalMaskA
      (publish finalB finalMaskB) finalMaskB := by
  simp [multiplicationConstraint, hfinal]

/-- Concrete end-to-end bridge: a successful 4096-attempt production
equality-point sample yields recursive messages which satisfy the exact
shifted multiplication gate for every choice of VEIL mask variables. -/
theorem boundedSampler_shiftedMultiplication_satisfied
    (running finalA finalB random : GhashField)
    (friendlyRhos : Fin 7 → GhashField)
    (outerRuns : Fin rejectionTrials →
      (Fin maxEqualityPointOuterCoordinates → GhashField))
    (outerEq outerRhos : Fin maxEqualityPointOuterCoordinates → GhashField)
    (haccepted : RejectionSampling.firstGood equalityPointVectorFailure
      outerRuns = some outerEq) :
    ∃ rounds : List (ExecutedRound (F := GhashField)),
      rounds.map ExecutedRound.parameters =
          productionParameters friendlyRhos outerEq outerRhos ∧
        ∀ (roundMasks : Fin rounds.length → GhashField × GhashField)
          (finalMaskA finalMaskB : GhashField),
          multiplicationConstraint running (maskRounds rounds roundMasks)
            (publish finalA finalMaskA) finalMaskA
            (publish finalB finalMaskB) finalMaskB := by
  obtain ⟨rounds, hparameters, hfinal⟩ :=
    boundedSampler_exists_executedRounds running (finalA * finalB) random
      friendlyRhos outerRuns outerEq outerRhos haccepted
  refine ⟨rounds, hparameters, ?_⟩
  intro roundMasks finalMaskA finalMaskB
  exact multiplicationConstraint_of_simulator running finalA finalB rounds
    hfinal roundMasks finalMaskA finalMaskB

end VeiledFlock.ShiftedZerocheckCircuit

import VeiledFlock.Algebra.EndToEnd
import VeiledFlock.Concrete.ChallengeSampling
import VeiledFlock.Concrete.UniquePositionSampling
import VeiledFlock.Concrete.ConcreteParameters
import VeiledFlock.Concrete.Grinding
import VeiledFlock.Core.Probability

/-!
# Concrete classical-pROM security ledger

This module gives a single exact rational expression for every statistical
bad event charged by the active VEIL--FLOCK simulator.  It also specializes
the generic finite-game composition theorem to that ledger.  Subsequent
refinement modules must discharge each ledger entry for the concrete protocol;
the entries are not informal comments or floating-point diagnostics.
-/

namespace VeiledFlock.SecurityLedger

open VeiledFlock.EndToEnd

structure Parameters where
  proofs : ℕ
  programmedPoints : ℕ
  adversaryQueries : ℕ
  protocolQueriesPerProof : ℕ

def nonceSpace : ℚ := (2 : ℚ) ^ 256

/-- Exact rational analogue of `ClassicalPromZkBound`. -/
def zkBound (parameters : Parameters) : ℚ :=
  (parameters.proofs * parameters.programmedPoints *
      parameters.adversaryQueries : ℕ) / nonceSpace +
  (parameters.proofs * parameters.protocolQueriesPerProof *
      parameters.adversaryQueries : ℕ) / nonceSpace +
  ((parameters.adversaryQueries +
      parameters.proofs * parameters.protocolQueriesPerProof).choose 2 : ℕ) /
        nonceSpace +
  (4 * parameters.proofs.choose 2 : ℕ) / nonceSpace +
  parameters.proofs *
    (Grinding.blindAbortProbability +
      Grinding.maxLigeritoSites * Grinding.ligeritoAbortProbability) +
  parameters.proofs * ConcreteParameters.maxNonzeroChallengeSites *
    ChallengeSampling.nonzeroAbortBound +
  parameters.proofs * ConcreteParameters.maxNotZeroOrOneChallengeSites *
    ChallengeSampling.notZeroOrOneAbortBound +
  parameters.proofs * ChallengeSampling.equalityPointAbortBound +
  parameters.proofs *
    (∑ shape : ConcreteParameters.BatchShape,
      UniquePositionSampling.outerAbortBound shape) +
  parameters.proofs *
    (UniquePositionSampling.hadamardAbortBound +
      UniquePositionSampling.linearAbortBound)

/-- Individually auditable hybrids in the simulator proof. -/
inductive Event
  | challengePrequery
  | hiddenMerkleInput
  | oracleAnswerCollision
  | proofNonceCollision
  | outerTreeNonceCollision
  | linearTreeNonceCollision
  | hadamardTreeNonceCollision
  | blindGrindingAbort
  | ligeritoGrindingAbort
  | nonzeroChallengeAbort
  | multiplicationChallengeAbort
  | equalityPointSamplingAbort
  | outerPositionSamplingAbort
  | hadamardPositionSamplingAbort
  | linearPositionSamplingAbort
  deriving DecidableEq, Fintype

def allEvents : Finset Event :=
  {.challengePrequery, .hiddenMerkleInput, .oracleAnswerCollision,
    .proofNonceCollision, .outerTreeNonceCollision,
    .linearTreeNonceCollision, .hadamardTreeNonceCollision,
    .blindGrindingAbort, .ligeritoGrindingAbort,
    .nonzeroChallengeAbort, .multiplicationChallengeAbort,
    .equalityPointSamplingAbort,
    .outerPositionSamplingAbort,
    .hadamardPositionSamplingAbort, .linearPositionSamplingAbort}

theorem allEvents_eq_univ : allEvents = Finset.univ := by
  ext event
  fin_cases event <;> simp [allEvents]

def eventBound (parameters : Parameters) : Event → ℚ
  | .challengePrequery =>
      (parameters.proofs * parameters.programmedPoints *
        parameters.adversaryQueries : ℕ) / nonceSpace
  | .hiddenMerkleInput =>
      (parameters.proofs * parameters.protocolQueriesPerProof *
        parameters.adversaryQueries : ℕ) / nonceSpace
  | .oracleAnswerCollision =>
      ((parameters.adversaryQueries +
        parameters.proofs * parameters.protocolQueriesPerProof).choose 2 : ℕ) /
          nonceSpace
  | .proofNonceCollision =>
      (parameters.proofs.choose 2 : ℕ) / nonceSpace
  | .outerTreeNonceCollision =>
      (parameters.proofs.choose 2 : ℕ) / nonceSpace
  | .linearTreeNonceCollision =>
      (parameters.proofs.choose 2 : ℕ) / nonceSpace
  | .hadamardTreeNonceCollision =>
      (parameters.proofs.choose 2 : ℕ) / nonceSpace
  | .blindGrindingAbort =>
      parameters.proofs * Grinding.blindAbortProbability
  | .ligeritoGrindingAbort =>
      parameters.proofs * Grinding.maxLigeritoSites *
        Grinding.ligeritoAbortProbability
  | .nonzeroChallengeAbort =>
      parameters.proofs * ConcreteParameters.maxNonzeroChallengeSites *
        ChallengeSampling.nonzeroAbortBound
  | .multiplicationChallengeAbort =>
      parameters.proofs * ConcreteParameters.maxNotZeroOrOneChallengeSites *
        ChallengeSampling.notZeroOrOneAbortBound
  | .equalityPointSamplingAbort =>
      parameters.proofs * ChallengeSampling.equalityPointAbortBound
  | .outerPositionSamplingAbort =>
      parameters.proofs *
        (∑ shape : ConcreteParameters.BatchShape,
          UniquePositionSampling.outerAbortBound shape)
  | .hadamardPositionSamplingAbort =>
      parameters.proofs * UniquePositionSampling.hadamardAbortBound
  | .linearPositionSamplingAbort =>
      parameters.proofs * UniquePositionSampling.linearAbortBound

theorem sum_eventBound_eq (parameters : Parameters) :
    ∑ event, eventBound parameters event = zkBound parameters := by
  rw [← allEvents_eq_univ]
  simp [allEvents, eventBound, zkBound]
  ring

section Composition

variable {Coins View : Type*}
variable [Fintype Coins] [Nonempty Coins] [DecidableEq Coins]
variable [Fintype View] [DecidableEq View]

/-- End-to-end statistical ZK once every concrete ledger event and the
good-execution simulator identity have been discharged. -/
theorem classicalProm_e2e_zk (parameters : Parameters)
    (real simulated : Coins → View) (coinEquiv : Coins ≃ Coins)
    (bad : Event → Finset Coins)
    (hgood : ∀ coins, (∀ event, coins ∉ bad event) →
      real (coinEquiv coins) = simulated coins)
    (hbound : ∀ event,
      ((bad event).card : ℚ) / Fintype.card Coins ≤
        eventBound parameters event) :
    uniformTV real simulated ≤ zkBound parameters := by
  rw [← sum_eventBound_eq parameters]
  exact e2e_zk_of_bad_event_ledger real simulated coinEquiv bad
    (eventBound parameters) hgood hbound

/-- A bad event stated on one typed, independent component of the complete
random tape.  The local probability proof is transported to the global tape
by an explicit product equivalence, so the end-to-end theorem no longer asks
for an unstructured global cardinality assumption. -/
structure ComponentEvent (parameters : Parameters) (coins : Type*)
    (event : Event) where
  Local : Type
  Rest : Type
  localFintype : Fintype Local
  localDecidableEq : DecidableEq Local
  restFintype : Fintype Rest
  localNonempty : Nonempty Local
  restNonempty : Nonempty Rest
  split : coins ≃ Local × Rest
  badAt : Rest → Finset Local
  localBound : ∀ rest,
    ((badAt rest).card : ℚ) / Fintype.card Local ≤
      eventBound parameters event

namespace ComponentEvent

noncomputable def globalBad {parameters : Parameters} {coins : Type*}
    {event : Event} [Fintype coins] [DecidableEq coins]
    (component : ComponentEvent parameters coins event) : Finset coins := by
  letI := component.localFintype
  letI := component.localDecidableEq
  letI := component.restFintype
  exact VeiledFlock.Probability.liftFiberBad
    component.split component.badAt

theorem globalBound {parameters : Parameters} {coins : Type*}
    {event : Event} [Fintype coins] [DecidableEq coins]
    (component : ComponentEvent parameters coins event) :
    ((component.globalBad).card : ℚ) / Fintype.card coins ≤
      eventBound parameters event := by
  letI := component.localFintype
  letI := component.localDecidableEq
  letI := component.restFintype
  letI := component.localNonempty
  letI := component.restNonempty
  exact VeiledFlock.Probability.liftFiberBad_probability_le
    component.split component.badAt (eventBound parameters event)
    component.localBound

end ComponentEvent

/-- Ledger composition with all probability obligations carried by typed
components of one global tape.  Only the good-execution simulator identity
remains as a protocol-semantic obligation. -/
theorem classicalProm_e2e_zk_components (parameters : Parameters)
    (real simulated : Coins → View) (coinEquiv : Coins ≃ Coins)
    (components : ∀ event,
      ComponentEvent parameters Coins event)
    (hgood : ∀ coins,
      (∀ event, coins ∉ (components event).globalBad) →
        real (coinEquiv coins) = simulated coins) :
    uniformTV real simulated ≤ zkBound parameters := by
  apply classicalProm_e2e_zk parameters real simulated coinEquiv
    (fun event => (components event).globalBad) hgood
  intro event
  exact (components event).globalBound

end Composition

end VeiledFlock.SecurityLedger

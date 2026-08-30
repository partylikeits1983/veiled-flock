import VeiledFlock.Concrete.ConcreteRandomTape
import VeiledFlock.Production.Core.Framing

/-!
# One explicit global good event for production VEIL--FLOCK

The security ledger already assigns every probabilistic failure to a typed
coordinate of one finite tape.  This module exposes the corresponding named
predicates and defines the single `Good` event used by the final coupling.

`BadProgramConflict` is not an extra independent probability term: a runtime
programming refusal means either that an adversarial prequery occurred or that
two supposedly fresh oracle coordinates collided.  Likewise, serialized
cross-domain aliasing has probability zero because the production encoder is
injective; it is proved impossible rather than charged to the ledger.
-/

namespace VeiledFlock.ProductionGlobalGood

open VeiledFlock.ConcreteRandomTape
open VeiledFlock.EndToEnd
open VeiledFlock.ProductionFraming
open VeiledFlock.SecurityLedger

variable {Core : Type} [Fintype Core] [DecidableEq Core] [Nonempty Core]
variable (parameters : Parameters)
variable (challengePrequery :
  ComponentEvent parameters (Tape parameters Core) .challengePrequery)
variable (hiddenMerkleInput :
  ComponentEvent parameters (Tape parameters Core) .hiddenMerkleInput)

noncomputable def LedgerComponents :
    ∀ event, ComponentEvent parameters (Tape parameters Core) event :=
  ConcreteRandomTape.components parameters challengePrequery hiddenMerkleInput

noncomputable def badAt (event : Event) (tape : Tape parameters Core) : Prop :=
  tape ∈ (LedgerComponents parameters challengePrequery hiddenMerkleInput event).globalBad

/-- Every primitive ledger event has its own proved probability bound.  The
grouped names below are unions of these primitive events. -/
theorem badAt_probability_le (event : Event) :
    (((ComponentEvent.globalBad
        (LedgerComponents parameters challengePrequery hiddenMerkleInput event)
      ).card : ℚ) /
      Fintype.card (Tape parameters Core)) ≤ eventBound parameters event := by
  exact ComponentEvent.globalBound
    (LedgerComponents parameters challengePrequery hiddenMerkleInput event)

noncomputable def BadPrequery (tape : Tape parameters Core) : Prop :=
  badAt parameters challengePrequery hiddenMerkleInput .challengePrequery tape

noncomputable def BadHiddenMerkleInput (tape : Tape parameters Core) : Prop :=
  badAt parameters challengePrequery hiddenMerkleInput .hiddenMerkleInput tape

noncomputable def BadOracleAnswerCollision (tape : Tape parameters Core) : Prop :=
  badAt parameters challengePrequery hiddenMerkleInput .oracleAnswerCollision tape

noncomputable def BadNonceCollision (tape : Tape parameters Core) : Prop :=
  badAt parameters challengePrequery hiddenMerkleInput .proofNonceCollision tape ∨
  badAt parameters challengePrequery hiddenMerkleInput .outerTreeNonceCollision tape ∨
  badAt parameters challengePrequery hiddenMerkleInput .linearTreeNonceCollision tape ∨
  badAt parameters challengePrequery hiddenMerkleInput .hadamardTreeNonceCollision tape

noncomputable def BadRejectionFailure (tape : Tape parameters Core) : Prop :=
  badAt parameters challengePrequery hiddenMerkleInput .nonzeroChallengeAbort tape ∨
  badAt parameters challengePrequery hiddenMerkleInput
    .multiplicationChallengeAbort tape ∨
  badAt parameters challengePrequery hiddenMerkleInput
    .equalityPointSamplingAbort tape ∨
  badAt parameters challengePrequery hiddenMerkleInput
    .outerPositionSamplingAbort tape ∨
  badAt parameters challengePrequery hiddenMerkleInput
    .hadamardPositionSamplingAbort tape ∨
  badAt parameters challengePrequery hiddenMerkleInput
    .linearPositionSamplingAbort tape

noncomputable def BadGrindingFailure (tape : Tape parameters Core) : Prop :=
  badAt parameters challengePrequery hiddenMerkleInput .blindGrindingAbort tape ∨
  badAt parameters challengePrequery hiddenMerkleInput .ligeritoGrindingAbort tape

/-- Operational programming conflicts are exactly the already charged
prequery/freshness and oracle-collision cases, not a hidden new event. -/
noncomputable def BadProgramConflict (tape : Tape parameters Core) : Prop :=
  BadPrequery parameters challengePrequery hiddenMerkleInput tape ∨
  BadOracleAnswerCollision parameters challengePrequery hiddenMerkleInput tape ∨
  BadNonceCollision parameters challengePrequery hiddenMerkleInput tape

/-- Distinct logical production queries cannot collide after byte encoding.
This definition is useful in the failure-mode audit: it is identically false,
so no probabilistic term is needed. -/
def BadCrossDomainCollision : Prop :=
  ∃ left right : ProductionQuery,
    left ≠ right ∧ encodeProductionQuery left = encodeProductionQuery right

theorem not_badCrossDomainCollision : ¬ BadCrossDomainCollision := by
  rintro ⟨left, right, hne, heq⟩
  exact hne (encodeProductionQuery_injective heq)

/-- The one global event used by the end-to-end coupling. -/
noncomputable def Good (tape : Tape parameters Core) : Prop :=
  ∀ event,
    ¬ badAt parameters challengePrequery hiddenMerkleInput event tape

noncomputable def globalBad : Finset (Tape parameters Core) :=
  badUnion fun event =>
    (LedgerComponents parameters challengePrequery hiddenMerkleInput event).globalBad

theorem good_iff_not_mem_globalBad (tape : Tape parameters Core) :
    Good parameters challengePrequery hiddenMerkleInput tape ↔
      tape ∉ globalBad parameters challengePrequery hiddenMerkleInput := by
  unfold Good badAt globalBad LedgerComponents
  rw [mem_badUnion_iff]
  simp only [not_exists]

theorem not_good_iff_mem_globalBad (tape : Tape parameters Core) :
    ¬ Good parameters challengePrequery hiddenMerkleInput tape ↔
      tape ∈ globalBad parameters challengePrequery hiddenMerkleInput := by
  rw [good_iff_not_mem_globalBad]
  simp

/-- A primitive bad event is exactly a reason `Good` fails.  This theorem is
the formal link used when a stage equality requires freshness, successful
sampling/grinding, or collision freedom. -/
theorem badAt_implies_not_good (event : Event) (tape : Tape parameters Core)
    (hbad : badAt parameters challengePrequery hiddenMerkleInput event tape) :
    ¬ Good parameters challengePrequery hiddenMerkleInput tape := by
  intro hgood
  exact hgood event hbad

theorem badPrequery_implies_not_good (tape : Tape parameters Core) :
    BadPrequery parameters challengePrequery hiddenMerkleInput tape →
      ¬ Good parameters challengePrequery hiddenMerkleInput tape :=
  badAt_implies_not_good parameters challengePrequery hiddenMerkleInput
    .challengePrequery tape

theorem badHiddenMerkleInput_implies_not_good (tape : Tape parameters Core) :
    BadHiddenMerkleInput parameters challengePrequery hiddenMerkleInput tape →
      ¬ Good parameters challengePrequery hiddenMerkleInput tape :=
  badAt_implies_not_good parameters challengePrequery hiddenMerkleInput
    .hiddenMerkleInput tape

theorem badOracleAnswerCollision_implies_not_good
    (tape : Tape parameters Core) :
    BadOracleAnswerCollision parameters challengePrequery hiddenMerkleInput tape →
      ¬ Good parameters challengePrequery hiddenMerkleInput tape :=
  badAt_implies_not_good parameters challengePrequery hiddenMerkleInput
    .oracleAnswerCollision tape

theorem badNonceCollision_implies_not_good (tape : Tape parameters Core) :
    BadNonceCollision parameters challengePrequery hiddenMerkleInput tape →
      ¬ Good parameters challengePrequery hiddenMerkleInput tape := by
  rintro (h | h | h | h)
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .proofNonceCollision tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .outerTreeNonceCollision tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .linearTreeNonceCollision tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .hadamardTreeNonceCollision tape h

theorem badRejectionFailure_implies_not_good (tape : Tape parameters Core) :
    BadRejectionFailure parameters challengePrequery hiddenMerkleInput tape →
      ¬ Good parameters challengePrequery hiddenMerkleInput tape := by
  rintro (h | h | h | h | h | h)
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .nonzeroChallengeAbort tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .multiplicationChallengeAbort tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .equalityPointSamplingAbort tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .outerPositionSamplingAbort tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .hadamardPositionSamplingAbort tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .linearPositionSamplingAbort tape h

theorem badGrindingFailure_implies_not_good (tape : Tape parameters Core) :
    BadGrindingFailure parameters challengePrequery hiddenMerkleInput tape →
      ¬ Good parameters challengePrequery hiddenMerkleInput tape := by
  rintro (h | h)
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .blindGrindingAbort tape h
  · exact badAt_implies_not_good parameters challengePrequery
      hiddenMerkleInput .ligeritoGrindingAbort tape h

theorem badProgramConflict_implies_not_good (tape : Tape parameters Core) :
    BadProgramConflict parameters challengePrequery hiddenMerkleInput tape →
      ¬ Good parameters challengePrequery hiddenMerkleInput tape := by
  rintro (h | h | h)
  · exact badPrequery_implies_not_good parameters challengePrequery
      hiddenMerkleInput tape h
  · exact badOracleAnswerCollision_implies_not_good parameters
      challengePrequery hiddenMerkleInput tape h
  · exact badNonceCollision_implies_not_good parameters challengePrequery
      hiddenMerkleInput tape h

/-- Exact rational union bound for the complement of the explicit `Good`
event. Every summand remains visible through `SecurityLedger.zkBound`. -/
theorem global_bad_probability_le :
    ((globalBad parameters challengePrequery hiddenMerkleInput).card : ℚ) /
        Fintype.card (Tape parameters Core) ≤ zkBound parameters := by
  rw [← sum_eventBound_eq parameters]
  apply badUnionProbability_le_bounds
  intro event
  exact
    (LedgerComponents parameters challengePrequery hiddenMerkleInput event).globalBound

end VeiledFlock.ProductionGlobalGood

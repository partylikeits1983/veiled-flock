import VeiledFlock.OptionalAdaptiveOracle

/-!
# Adaptive verifier view on one shared oracle

The production protocol has a fixed causal order, but a malicious verifier is
not forced to issue oracle queries in that order.  This module represents a
bounded classical adversary whose next query can depend on its coins, every
public message released so far, and every earlier oracle answer.  A protocol
driver chooses the public snapshot visible at each cut, including cuts before
the first message, between all production stages, and after the proof.
-/

namespace VeiledFlock.ProductionAdaptiveAdversary

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.OptionalAdaptiveOracle

/-- Causal cuts of the actual production execution.  Only honest protocol
operations are ordered; adversary queries may be placed at every cut. -/
inductive ProtocolCut
  | beforeProtocol
  | afterFlock
  | afterVeil
  | afterMerkle
  | afterFiatShamir
  | afterRejection
  | afterGrinding
  | afterProof
  deriving DecidableEq, Fintype

def ProtocolCut.rank : ProtocolCut → ℕ
  | .beforeProtocol => 0
  | .afterFlock => 1
  | .afterVeil => 2
  | .afterMerkle => 3
  | .afterFiatShamir => 4
  | .afterRejection => 5
  | .afterGrinding => 6
  | .afterProof => 7

theorem protocolCut_rank_injective : Function.Injective ProtocolCut.rank := by
  intro left right heq
  cases left <;> cases right <;> simp_all [ProtocolCut.rank]

variable {Statement AdversaryCoins PublicSnapshot Point Outcome FinalState :
  Type*}

/-- A bounded adaptive classical oracle adversary.  Its API has no witness.
`nextQuery` may query at any production cut and depends on the complete prior
answer history. `none` means this bounded query slot is unused. -/
structure AdaptiveAdversary (sites : ℕ) where
  cut : Fin sites → ProtocolCut
  nextQuery : ∀ round : Fin sites,
    Statement → AdversaryCoins → PublicSnapshot →
      History (Outcome := Outcome) round → Option Point
  finish : Statement → AdversaryCoins → PublicSnapshot →
    History (Outcome := Outcome) sites → FinalState

/-- Allowed adversary class for a concrete theorem.  The query dependence is
structural in `AdaptiveAdversary`; this wrapper exposes the numerical cap used
by the prequery and collision bounds. -/
structure BoundedAdaptiveAdversary (maxQueries : ℕ) where
  sites : ℕ
  machine : AdaptiveAdversary
    (Statement := Statement) (AdversaryCoins := AdversaryCoins)
    (PublicSnapshot := PublicSnapshot) (Point := Point)
    (Outcome := Outcome) (FinalState := FinalState) sites
  sites_le : sites ≤ maxQueries

/-- Compile an adaptive adversary into the shared-oracle optional schedule.
The snapshot function is supplied by the protocol driver and therefore may
reveal exactly the messages available at that causal cut. -/
def schedule {sites : ℕ} (adversary : AdaptiveAdversary
    (Statement := Statement) (AdversaryCoins := AdversaryCoins)
    (PublicSnapshot := PublicSnapshot) (Point := Point)
    (Outcome := Outcome) (FinalState := FinalState) sites)
    (statement : Statement) (coins : AdversaryCoins)
    (snapshotAt : ∀ round : Fin sites,
      History (Outcome := Outcome) round → PublicSnapshot) :
    OptionalSchedule (Point := Point) (Outcome := Outcome) sites :=
  fun round history =>
    adversary.nextQuery round statement coins (snapshotAt round history) history

/-- Exact classical oracle interaction visible to the adversary.  Inactive
dummy slots are omitted because they never query the shared oracle. -/
def visibleQueries {sites : ℕ} (adversary : AdaptiveAdversary
    (Statement := Statement) (AdversaryCoins := AdversaryCoins)
    (PublicSnapshot := PublicSnapshot) (Point := Point)
    (Outcome := Outcome) (FinalState := FinalState) sites)
    (statement : Statement) (coins : AdversaryCoins)
    (snapshotAt : ∀ round : Fin sites,
      History (Outcome := Outcome) round → PublicSnapshot)
    (answers : History (Outcome := Outcome) sites) : List (Point × Outcome) :=
  (List.ofFn fun round =>
    ((schedule adversary statement coins snapshotAt) round
      (priorAnswers answers round), answers round)).filterMap
        (fun result => result.1.map fun point => (point, result.2))

/-- The oracle part of the verifier view: every actual query/answer pair and
the adversary's final state.  Proof-byte equality without equality of this
record is insufficient for the final ZK theorem. -/
structure OracleView where
  queries : List (Point × Outcome)
  finalState : FinalState

def view {sites : ℕ} (adversary : AdaptiveAdversary
    (Statement := Statement) (AdversaryCoins := AdversaryCoins)
    (PublicSnapshot := PublicSnapshot) (Point := Point)
    (Outcome := Outcome) (FinalState := FinalState) sites)
    (statement : Statement) (coins : AdversaryCoins)
    (snapshotAt : ∀ round : Fin sites,
      History (Outcome := Outcome) round → PublicSnapshot)
    (finalSnapshot : History (Outcome := Outcome) sites → PublicSnapshot)
    (answers : History (Outcome := Outcome) sites) :
    OracleView (Point := Point) (Outcome := Outcome)
      (FinalState := FinalState) where
  queries := visibleQueries adversary statement coins snapshotAt answers
  finalState := adversary.finish statement coins (finalSnapshot answers) answers

end VeiledFlock.ProductionAdaptiveAdversary

import VeiledFlock.Core.Birthday
import VeiledFlock.Concrete.ChallengeSampling
import VeiledFlock.Concrete.ConcreteFraming
import VeiledFlock.Concrete.Grinding
import VeiledFlock.Oracle.MerkleHiding
import VeiledFlock.Oracle.ProgrammableOracle
import VeiledFlock.Production.Core.PositionProjection
import VeiledFlock.Production.Core.GrindingProjection
import VeiledFlock.Production.Core.ScalarProjection
import VeiledFlock.Core.RepeatedEvents
import VeiledFlock.Core.SecurityLedger
import VeiledFlock.Concrete.UniquePositionSampling
import VeiledFlock.Oracle.UniversalFreshness

/-!
# Concrete finite random tape

This module gives every security-ledger event a typed coordinate in one
finite dependent-product random tape.  Events that use the same production
coin source share a coordinate: in particular, programmable challenges and
proof-nonce collisions use the same proof-nonce vector.

The two adversary-dependent events (programmable-challenge prequeries and
hidden Merkle inputs) are supplied as fiberwise components.  Every remaining
event is instantiated here from a proved finite counting lemma.
-/

namespace VeiledFlock.ConcreteRandomTape

set_option maxHeartbeats 800000

open VeiledFlock.SecurityLedger

abbrev Nonce256 := Fin (2 ^ 256)

inductive CoinKind
  | core
  | proofNonces
  | outerTreeNonces
  | linearTreeNonces
  | hadamardTreeNonces
  | oracleAnswers
  | hiddenMerkleSalts
  | blindGrinding
  | ligeritoGrinding
  | nonzeroChallenges
  | multiplicationChallenges
  | equalityPointChallenges
  | outerPositions
  | hadamardPositions
  | linearPositions
  deriving DecidableEq, Fintype

def totalOracleQueries (parameters : Parameters) : ℕ :=
  parameters.adversaryQueries +
    parameters.proofs * parameters.protocolQueriesPerProof

theorem nonceSpace_eq_card :
    nonceSpace = (Fintype.card Nonce256 : ℚ) := by
  norm_num [nonceSpace, Nonce256]

/-- Type of every independent coordinate of the global tape. -/
def CoinType (parameters : Parameters) (Core : Type) : CoinKind → Type
  | .core => Core
  | .proofNonces => Fin parameters.proofs → Nonce256
  | .outerTreeNonces => Fin parameters.proofs → Nonce256
  | .linearTreeNonces => Fin parameters.proofs → Nonce256
  | .hadamardTreeNonces => Fin parameters.proofs → Nonce256
  | .oracleAnswers => Fin (totalOracleQueries parameters) → Nonce256
  | .hiddenMerkleSalts =>
      Fin parameters.proofs →
        (Fin parameters.protocolQueriesPerProof → Nonce256)
  | .blindGrinding =>
      Fin parameters.proofs →
        (Fin Grinding.maxBlindTrials → ConcreteOracle.OracleBlock)
  | .ligeritoGrinding =>
      Fin (parameters.proofs * Grinding.maxLigeritoSites) →
        (Fin Grinding.maxLigeritoTrials → ConcreteOracle.OracleBlock)
  | .nonzeroChallenges =>
      Fin (parameters.proofs *
        ConcreteParameters.maxNonzeroChallengeSites) →
          (Fin ChallengeSampling.rejectionTrials → ConcreteOracle.OracleBlock)
  | .multiplicationChallenges =>
      Fin (parameters.proofs *
        ConcreteParameters.maxNotZeroOrOneChallengeSites) →
          (Fin ChallengeSampling.rejectionTrials → ConcreteOracle.OracleBlock)
  | .equalityPointChallenges =>
      Fin parameters.proofs →
        (Fin ChallengeSampling.rejectionTrials →
          (Fin 7 → ConcreteOracle.OracleBlock))
  | .outerPositions =>
      Fin parameters.proofs →
        (Fin UniquePositionSampling.samplingTrials →
          ConcreteOracle.OracleBlock)
  | .hadamardPositions =>
      Fin parameters.proofs →
        (Fin UniquePositionSampling.samplingTrials →
          ConcreteOracle.OracleBlock)
  | .linearPositions =>
      Fin parameters.proofs →
        (Fin UniquePositionSampling.samplingTrials →
          ConcreteOracle.OracleBlock)

noncomputable instance coinTypeFintype {parameters : Parameters}
    {Core : Type} [Fintype Core] (kind : CoinKind) :
    Fintype (CoinType parameters Core kind) := by
  cases kind <;> simp only [CoinType] <;> infer_instance

noncomputable instance coinTypeDecidableEq {parameters : Parameters}
    {Core : Type} [DecidableEq Core] (kind : CoinKind) :
    DecidableEq (CoinType parameters Core kind) := by
  cases kind <;> simp only [CoinType] <;> infer_instance

noncomputable instance coinTypeNonempty {parameters : Parameters}
    {Core : Type} [Nonempty Core] (kind : CoinKind) :
    Nonempty (CoinType parameters Core kind) := by
  cases kind <;> simp only [CoinType]
  all_goals infer_instance

/-- One complete finite source of coins for all modeled hybrids. -/
abbrev Tape (parameters : Parameters) (Core : Type) :=
  ∀ kind, CoinType parameters Core kind

abbrev OtherCoins (parameters : Parameters) (Core : Type)
    (kind : CoinKind) :=
  ∀ other : {other : CoinKind // other ≠ kind},
    CoinType parameters Core other

noncomputable def splitAt (parameters : Parameters) (Core : Type)
    (kind : CoinKind) :
    Tape parameters Core ≃
      CoinType parameters Core kind × OtherCoins parameters Core kind :=
  Equiv.piSplitAt kind (CoinType parameters Core)

section Components

variable {Core : Type} [Fintype Core] [DecidableEq Core] [Nonempty Core]
variable (parameters : Parameters)

noncomputable def constantComponent (event : Event) (kind : CoinKind)
    (bad : Finset (CoinType parameters Core kind))
    (hbound : (bad.card : ℚ) /
      Fintype.card (CoinType parameters Core kind) ≤
        eventBound parameters event) :
    ComponentEvent parameters (Tape parameters Core) event where
  Local := CoinType parameters Core kind
  Rest := OtherCoins parameters Core kind
  localFintype := inferInstance
  localDecidableEq := inferInstance
  restFintype := inferInstance
  localNonempty := inferInstance
  restNonempty := inferInstance
  split := splitAt parameters Core kind
  badAt := fun _ => bad
  localBound := fun _ => hbound

/-- Adaptive programming-prequery event on the same proof nonces later used
by the nonce-collision event.  All other tape coordinates may influence the
adversary's next query set. -/
noncomputable def challengePrequeryComponent
    {Point : Type} [DecidableEq Point]
    (programPoint : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Fin parameters.programmedPoints →
        Nonce256 → Point)
    (priorQueries : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Finset Point)
    (hinjective : ∀ rest history site,
      Function.Injective (programPoint rest history site))
    (hqueries : ∀ rest history,
      (priorQueries rest history).card ≤ parameters.adversaryQueries) :
    ComponentEvent parameters (Tape parameters Core) .challengePrequery where
  Local := CoinType parameters Core .proofNonces
  Rest := OtherCoins parameters Core .proofNonces
  localFintype := inferInstance
  localDecidableEq := inferInstance
  restFintype := inferInstance
  localNonempty := inferInstance
  restNonempty := inferInstance
  split := splitAt parameters Core .proofNonces
  badAt := fun rest =>
    Finset.univ.filter fun nonces =>
      ProgrammableOracle.runFails
        (fun history => ProgrammableOracle.badNonces
          (programPoint rest history) (priorQueries rest history))
        [] parameters.proofs nonces = true
  localBound := by
    intro rest
    change
      ((Finset.univ.filter fun nonces : Fin parameters.proofs → Nonce256 =>
        ProgrammableOracle.runFails
          (fun history => ProgrammableOracle.badNonces
            (programPoint rest history) (priorQueries rest history))
          [] parameters.proofs nonces = true).card : ℚ) /
            Fintype.card (Fin parameters.proofs → Nonce256) ≤
        (parameters.proofs * parameters.programmedPoints *
          parameters.adversaryQueries : ℕ) / nonceSpace
    have h := ProgrammableOracle.adaptiveProgrammingCollision256_le
      parameters.proofs parameters.programmedPoints parameters.adversaryQueries
      (programPoint rest) (priorQueries rest) (hinjective rest) (hqueries rest)
    have hden : ((2 ^ 256 : ℕ) : ℚ) = nonceSpace := by
      norm_num [nonceSpace]
    rw [hden] at h
    norm_num only [Nat.cast_mul]
    exact h

/-- Production-framed specialization of `challengePrequeryComponent`.
Injectivity is discharged here from the exact tagged proof-nonce field, so a
caller supplies only the transcript bytes around that field and the bounded
prior-query set. -/
noncomputable def framedChallengePrequeryComponent
    (head : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Fin parameters.programmedPoints → List Framing.Byte)
    (suffix : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Fin parameters.programmedPoints →
        Nonce256 → List Framing.Byte)
    (priorQueries : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Finset (List Framing.Byte))
    (hqueries : ∀ rest history,
      (priorQueries rest history).card ≤ parameters.adversaryQueries) :
    ComponentEvent parameters (Tape parameters Core) .challengePrequery :=
  challengePrequeryComponent parameters
    (fun rest history site nonce =>
      ConcreteFraming.transcriptPoint (head rest history site)
        (suffix rest history site) nonce)
    priorQueries
    (fun rest history site =>
      ConcreteFraming.transcriptPoint_injective
        (head rest history site) (suffix rest history site))
    hqueries

/-- Strengthened programming-prequery component.  Its bad set ranges over
every counterfactual within-proof answer history required by the interleaved
Fiat--Shamir equivalence.  Cross-history nonce recovery prevents any factor
for the number of such histories from entering the bound. -/
noncomputable def universalChallengePrequeryComponent
    {Context Point : Type} [DecidableEq Point]
    (programPoint : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Fin parameters.programmedPoints →
        Nonce256 → Context → Point)
    (priorQueries : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Finset Point)
    (hcross : ∀ rest history site leftNonce leftContext
      rightNonce rightContext,
      programPoint rest history site leftNonce leftContext =
          programPoint rest history site rightNonce rightContext →
        leftNonce = rightNonce)
    (hqueries : ∀ rest history,
      (priorQueries rest history).card ≤ parameters.adversaryQueries) :
    ComponentEvent parameters (Tape parameters Core) .challengePrequery where
  Local := CoinType parameters Core .proofNonces
  Rest := OtherCoins parameters Core .proofNonces
  localFintype := inferInstance
  localDecidableEq := inferInstance
  restFintype := inferInstance
  localNonempty := inferInstance
  restNonempty := inferInstance
  split := splitAt parameters Core .proofNonces
  badAt := fun rest ↦
    Finset.univ.filter fun nonces ↦
      ProgrammableOracle.runFails
        (fun history ↦ UniversalFreshness.badNonces
          (programPoint rest history) (priorQueries rest history))
        [] parameters.proofs nonces = true
  localBound := by
    intro rest
    change
      ((Finset.univ.filter fun nonces : Fin parameters.proofs → Nonce256 ↦
        ProgrammableOracle.runFails
          (fun history ↦ UniversalFreshness.badNonces
            (programPoint rest history) (priorQueries rest history))
          [] parameters.proofs nonces = true).card : ℚ) /
            Fintype.card (Fin parameters.proofs → Nonce256) ≤
        (parameters.proofs * parameters.programmedPoints *
          parameters.adversaryQueries : ℕ) / nonceSpace
    have hbad : ∀ history,
        (UniversalFreshness.badNonces
          (programPoint rest history) (priorQueries rest history)).card ≤
            parameters.programmedPoints * parameters.adversaryQueries := by
      intro history
      exact
        (UniversalFreshness.card_badNonces_le
          (programPoint rest history) (priorQueries rest history)
          (hcross rest history)).trans (by
            simpa only [Fintype.card_fin] using
              (Nat.mul_le_mul_left parameters.programmedPoints
                (hqueries rest history)))
    have h := ProgrammableOracle.adaptiveCollisionProbability_le
      (Nonce := Nonce256)
      (fun history ↦ UniversalFreshness.badNonces
        (programPoint rest history) (priorQueries rest history))
      (parameters.programmedPoints * parameters.adversaryQueries)
      parameters.proofs hbad
    have hden : (Fintype.card Nonce256 : ℚ) = nonceSpace := by
      rw [← nonceSpace_eq_card]
    rw [hden] at h
    simpa only [Nat.cast_mul, mul_assoc] using h

/-- Exact production-framed specialization of the universal component.  At a
fixed site the tagged proof-nonce field has the same offset under every
counterfactual suffix. -/
noncomputable def universalFramedChallengePrequeryComponent
    {Context : Type}
    (head : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Fin parameters.programmedPoints →
        List Framing.Byte)
    (suffix : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Fin parameters.programmedPoints → Context →
        Nonce256 → List Framing.Byte)
    (priorQueries : OtherCoins parameters Core .proofNonces →
      List Nonce256 → Finset (List Framing.Byte))
    (hqueries : ∀ rest history,
      (priorQueries rest history).card ≤ parameters.adversaryQueries) :
    ComponentEvent parameters (Tape parameters Core) .challengePrequery :=
  universalChallengePrequeryComponent parameters
    (fun rest history site nonce context ↦
      ConcreteFraming.transcriptPoint (head rest history site)
        (suffix rest history site context) nonce)
    priorQueries
    (fun rest history site _leftNonce _leftContext _rightNonce _rightContext ↦
      UniversalFreshness.transcriptPoint_cross_injective
        (head rest history site)
        (suffix rest history site) (suffix rest history site))
    hqueries

/-- Adaptive hidden-Merkle-input event for the independently salted inputs
charged by the protocol-oracle-query cap. -/
noncomputable def hiddenMerkleInputComponent
    {Point : Type} [DecidableEq Point]
    (point : OtherCoins parameters Core .hiddenMerkleSalts →
      List (Fin parameters.protocolQueriesPerProof → Nonce256) →
        Fin parameters.protocolQueriesPerProof → Nonce256 → Point)
    (priorQueries : OtherCoins parameters Core .hiddenMerkleSalts →
      List (Fin parameters.protocolQueriesPerProof → Nonce256) →
        Finset Point)
    (hinjective : ∀ rest history site,
      Function.Injective (point rest history site))
    (hqueries : ∀ rest history,
      (priorQueries rest history).card ≤ parameters.adversaryQueries) :
    ComponentEvent parameters (Tape parameters Core) .hiddenMerkleInput where
  Local := CoinType parameters Core .hiddenMerkleSalts
  Rest := OtherCoins parameters Core .hiddenMerkleSalts
  localFintype := inferInstance
  localDecidableEq := inferInstance
  restFintype := inferInstance
  localNonempty := inferInstance
  restNonempty := inferInstance
  split := splitAt parameters Core .hiddenMerkleSalts
  badAt := fun rest =>
    Finset.univ.filter fun assignments =>
      ProgrammableOracle.runFails
        (fun history => MerkleHiding.hiddenInputBadAssignments
          (point rest history) (priorQueries rest history))
        [] parameters.proofs assignments = true
  localBound := by
    intro rest
    change
      ((Finset.univ.filter fun assignments :
          Fin parameters.proofs →
            (Fin parameters.protocolQueriesPerProof → Nonce256) =>
        ProgrammableOracle.runFails
          (fun history => MerkleHiding.hiddenInputBadAssignments
            (point rest history) (priorQueries rest history))
          [] parameters.proofs assignments = true).card : ℚ) /
            Fintype.card (Fin parameters.proofs →
              (Fin parameters.protocolQueriesPerProof → Nonce256)) ≤
        (parameters.proofs * parameters.protocolQueriesPerProof *
          parameters.adversaryQueries : ℕ) / nonceSpace
    have h := MerkleHiding.adaptiveHiddenInputProbability_le
      (Salt := Nonce256) parameters.proofs
      parameters.protocolQueriesPerProof parameters.adversaryQueries
      (point rest) (priorQueries rest) (hinjective rest) (hqueries rest)
    rw [← nonceSpace_eq_card] at h
    norm_num only [Nat.cast_mul]
    exact h

/-- Production-framed specialization of `hiddenMerkleInputComponent`.
The exact 64-byte Merkle header and 12-byte node location precede the 32-byte
leaf salt, making every hidden input injective in its fresh salt independently
of the remaining payload suffix. -/
noncomputable def framedHiddenMerkleInputComponent
    (headerLocationPrefix : OtherCoins parameters Core .hiddenMerkleSalts →
      List (Fin parameters.protocolQueriesPerProof → Nonce256) →
        Fin parameters.protocolQueriesPerProof → Fin 76 → Framing.Byte)
    (suffix : OtherCoins parameters Core .hiddenMerkleSalts →
      List (Fin parameters.protocolQueriesPerProof → Nonce256) →
        Fin parameters.protocolQueriesPerProof → Nonce256 →
          List Framing.Byte)
    (priorQueries : OtherCoins parameters Core .hiddenMerkleSalts →
      List (Fin parameters.protocolQueriesPerProof → Nonce256) →
        Finset (List Framing.Byte))
    (hqueries : ∀ rest history,
      (priorQueries rest history).card ≤ parameters.adversaryQueries) :
    ComponentEvent parameters (Tape parameters Core) .hiddenMerkleInput :=
  hiddenMerkleInputComponent parameters
    (fun rest history site salt =>
      ConcreteFraming.merkleLeafPoint
        (headerLocationPrefix rest history site)
        (suffix rest history site) salt)
    priorQueries
    (fun rest history site =>
      ConcreteFraming.merkleLeafPoint_injective
        (headerLocationPrefix rest history site) (suffix rest history site))
    hqueries

noncomputable def oracleCollisionComponent :
    ComponentEvent parameters (Tape parameters Core)
      .oracleAnswerCollision :=
  constantComponent parameters .oracleAnswerCollision .oracleAnswers
    (Birthday.collisionRuns (Outcome := Nonce256)
      (totalOracleQueries parameters)) (by
        change
          ((Birthday.collisionRuns (Outcome := Nonce256)
            (totalOracleQueries parameters)).card : ℚ) /
              Fintype.card
                (Fin (totalOracleQueries parameters) → Nonce256) ≤
            ((totalOracleQueries parameters).choose 2 : ℚ) / nonceSpace
        have h := Birthday.collisionProbability_le
          (Outcome := Nonce256) (totalOracleQueries parameters)
        rw [← nonceSpace_eq_card] at h
        exact h)

noncomputable def proofNonceCollisionComponent :
    ComponentEvent parameters (Tape parameters Core) .proofNonceCollision :=
  constantComponent parameters .proofNonceCollision .proofNonces
    (Birthday.collisionRuns (Outcome := Nonce256) parameters.proofs) (by
      change
        ((Birthday.collisionRuns (Outcome := Nonce256)
          parameters.proofs).card : ℚ) /
            Fintype.card (Fin parameters.proofs → Nonce256) ≤
          (parameters.proofs.choose 2 : ℚ) / nonceSpace
      have h := Birthday.collisionProbability_le
        (Outcome := Nonce256) parameters.proofs
      rw [← nonceSpace_eq_card] at h
      exact h)

noncomputable def outerTreeNonceCollisionComponent :
    ComponentEvent parameters (Tape parameters Core) .outerTreeNonceCollision :=
  constantComponent parameters .outerTreeNonceCollision .outerTreeNonces
    (Birthday.collisionRuns (Outcome := Nonce256) parameters.proofs) (by
      change
        ((Birthday.collisionRuns (Outcome := Nonce256)
          parameters.proofs).card : ℚ) /
            Fintype.card (Fin parameters.proofs → Nonce256) ≤
          (parameters.proofs.choose 2 : ℚ) / nonceSpace
      have h := Birthday.collisionProbability_le
        (Outcome := Nonce256) parameters.proofs
      rw [← nonceSpace_eq_card] at h
      exact h)

noncomputable def linearTreeNonceCollisionComponent :
    ComponentEvent parameters (Tape parameters Core) .linearTreeNonceCollision :=
  constantComponent parameters .linearTreeNonceCollision .linearTreeNonces
    (Birthday.collisionRuns (Outcome := Nonce256) parameters.proofs) (by
      change
        ((Birthday.collisionRuns (Outcome := Nonce256)
          parameters.proofs).card : ℚ) /
            Fintype.card (Fin parameters.proofs → Nonce256) ≤
          (parameters.proofs.choose 2 : ℚ) / nonceSpace
      have h := Birthday.collisionProbability_le
        (Outcome := Nonce256) parameters.proofs
      rw [← nonceSpace_eq_card] at h
      exact h)

noncomputable def hadamardTreeNonceCollisionComponent :
    ComponentEvent parameters (Tape parameters Core) .hadamardTreeNonceCollision :=
  constantComponent parameters .hadamardTreeNonceCollision .hadamardTreeNonces
    (Birthday.collisionRuns (Outcome := Nonce256) parameters.proofs) (by
      change
        ((Birthday.collisionRuns (Outcome := Nonce256)
          parameters.proofs).card : ℚ) /
            Fintype.card (Fin parameters.proofs → Nonce256) ≤
          (parameters.proofs.choose 2 : ℚ) / nonceSpace
      have h := Birthday.collisionProbability_le
        (Outcome := Nonce256) parameters.proofs
      rw [← nonceSpace_eq_card] at h
      exact h)

noncomputable def blindGrindingComponent :
    ComponentEvent parameters (Tape parameters Core) .blindGrindingAbort :=
  constantComponent parameters .blindGrindingAbort .blindGrinding
    (RepeatedEvents.anyBad parameters.proofs
      (ProductionGrindingProjection.blockAbortRuns Grinding.maxBlindBits
        (by decide)
        Grinding.maxBlindTrials)) (by
      simp only [CoinType]
      refine (RepeatedEvents.anyBadProbability_le parameters.proofs _).trans ?_
      rw [ProductionGrindingProjection.blindBlockAbortProbability_eq]
      rfl)

noncomputable def ligeritoGrindingComponent :
    ComponentEvent parameters (Tape parameters Core) .ligeritoGrindingAbort :=
  constantComponent parameters .ligeritoGrindingAbort .ligeritoGrinding
    (RepeatedEvents.anyBad
      (parameters.proofs * Grinding.maxLigeritoSites)
      (ProductionGrindingProjection.blockAbortRuns Grinding.maxLigeritoBits
        (by decide)
        Grinding.maxLigeritoTrials)) (by
      simp only [CoinType]
      refine (RepeatedEvents.anyBadProbability_le
        (parameters.proofs * Grinding.maxLigeritoSites) _).trans ?_
      rw [ProductionGrindingProjection.ligeritoBlockAbortProbability_eq]
      simp only [eventBound, Nat.cast_mul]
      ring_nf
      exact le_rfl)

noncomputable def nonzeroChallengeComponent :
    ComponentEvent parameters (Tape parameters Core) .nonzeroChallengeAbort :=
  constantComponent parameters .nonzeroChallengeAbort .nonzeroChallenges
    (RepeatedEvents.anyBad
      (parameters.proofs * ConcreteParameters.maxNonzeroChallengeSites)
      (ProductionScalarProjection.scalarBlockAbortRuns
        ChallengeSampling.zeroFailure
        ChallengeSampling.rejectionTrials)) (by
      simp only [CoinType]
      refine (RepeatedEvents.anyBadProbability_le
        (parameters.proofs *
          ConcreteParameters.maxNonzeroChallengeSites) _).trans ?_
      rw [ProductionScalarProjection.nonzeroBlockAbortProbability_eq]
      simp only [eventBound, Nat.cast_mul]
      ring_nf
      exact le_rfl)

noncomputable def multiplicationChallengeComponent :
    ComponentEvent parameters (Tape parameters Core)
      .multiplicationChallengeAbort :=
  constantComponent parameters .multiplicationChallengeAbort
    .multiplicationChallenges
    (RepeatedEvents.anyBad
      (parameters.proofs *
        ConcreteParameters.maxNotZeroOrOneChallengeSites)
      (ProductionScalarProjection.scalarBlockAbortRuns
        ChallengeSampling.zeroOrOneFailure
        ChallengeSampling.rejectionTrials)) (by
      simp only [CoinType]
      refine (RepeatedEvents.anyBadProbability_le
        (parameters.proofs *
          ConcreteParameters.maxNotZeroOrOneChallengeSites) _).trans ?_
      rw [ProductionScalarProjection.notZeroOrOneBlockAbortProbability_eq]
      simp only [eventBound, Nat.cast_mul]
      ring_nf
      exact le_rfl)

noncomputable def equalityPointChallengeComponent :
    ComponentEvent parameters (Tape parameters Core)
      .equalityPointSamplingAbort :=
  constantComponent parameters .equalityPointSamplingAbort
    .equalityPointChallenges
    (RepeatedEvents.anyBad parameters.proofs
      (ProductionScalarProjection.equalityBlockAbortRuns
        ChallengeSampling.rejectionTrials)) (by
      simp only [CoinType]
      refine (RepeatedEvents.anyBadProbability_le parameters.proofs _).trans ?_
      simpa only [eventBound] using
        (mul_le_mul_of_nonneg_left
          ProductionScalarProjection.equalityBlockAbortProbability_le
          (by positivity : (0 : ℚ) ≤ parameters.proofs)))

noncomputable def hadamardPositionComponent :
    ComponentEvent parameters (Tape parameters Core)
      .hadamardPositionSamplingAbort :=
  constantComponent parameters .hadamardPositionSamplingAbort
    .hadamardPositions
    (RepeatedEvents.anyBad parameters.proofs
      (ProductionScalarProjection.positionBlockAbortRuns 11 (by decide)
        UniquePositionSampling.queryCount
        UniquePositionSampling.samplingTrials)) (by
      simp only [CoinType]
      letI : Nonempty
          (Fin UniquePositionSampling.samplingTrials →
            ConcreteOracle.OracleBlock) := inferInstance
      refine (RepeatedEvents.anyBadProbability_le parameters.proofs _).trans ?_
      simpa only [eventBound] using
        (mul_le_mul_of_nonneg_left
          ProductionScalarProjection.hadamardPositionBlockAbortProbability_le
          (by positivity : (0 : ℚ) ≤ parameters.proofs)))

/-- Failure of the shape-dependent Secure-profile outer L0 sampler.  The
single ledger event is the union over all registered production shapes, so a
`Good` tape is safe for whichever registered shape a proof uses. -/
noncomputable def outerPositionComponent :
    ComponentEvent parameters (Tape parameters Core)
      .outerPositionSamplingAbort :=
  constantComponent parameters .outerPositionSamplingAbort .outerPositions
    (RepeatedEvents.anyBad parameters.proofs
      (Finset.univ.biUnion fun shape : ConcreteParameters.BatchShape =>
        ProductionScalarProjection.positionBlockAbortRuns
          (ConcreteParameters.m shape - 11) (by cases shape <;> decide)
          (ConcreteParameters.outerL0QueryCount shape)
          UniquePositionSampling.samplingTrials)) (by
      simp only [CoinType]
      let localBad :=
        Finset.univ.biUnion fun shape : ConcreteParameters.BatchShape =>
          ProductionScalarProjection.positionBlockAbortRuns
            (ConcreteParameters.m shape - 11) (by cases shape <;> decide)
            (ConcreteParameters.outerL0QueryCount shape)
            UniquePositionSampling.samplingTrials
      refine (RepeatedEvents.anyBadProbability_le parameters.proofs
        localBad).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        ((localBad.card : ℚ) /
            Fintype.card
              (Fin UniquePositionSampling.samplingTrials →
                ConcreteOracle.OracleBlock)) ≤
            ∑ shape : ConcreteParameters.BatchShape,
              (((ProductionScalarProjection.positionBlockAbortRuns
                  (ConcreteParameters.m shape - 11)
                  (by cases shape <;> decide)
                  (ConcreteParameters.outerL0QueryCount shape)
                  UniquePositionSampling.samplingTrials).card : ℚ) /
                Fintype.card
                  (Fin UniquePositionSampling.samplingTrials →
                    ConcreteOracle.OracleBlock)) := by
              apply EndToEnd.badUnionProbability_le_sum
        _ ≤ ∑ shape : ConcreteParameters.BatchShape,
              UniquePositionSampling.outerAbortBound shape := by
              apply Finset.sum_le_sum
              intro shape _
              rw [ProductionScalarProjection.positionBlockAbortProbability_eq]
              exact UniquePositionSampling.outerAbortProbability_le shape)

noncomputable def linearPositionComponent :
    ComponentEvent parameters (Tape parameters Core)
      .linearPositionSamplingAbort :=
  constantComponent parameters .linearPositionSamplingAbort .linearPositions
    (RepeatedEvents.anyBad parameters.proofs
      (ProductionScalarProjection.positionBlockAbortRuns 13 (by decide)
        UniquePositionSampling.queryCount
        UniquePositionSampling.samplingTrials)) (by
      simp only [CoinType]
      letI : Nonempty
          (Fin UniquePositionSampling.samplingTrials →
            ConcreteOracle.OracleBlock) := inferInstance
      refine (RepeatedEvents.anyBadProbability_le parameters.proofs _).trans ?_
      simpa only [eventBound] using
        (mul_le_mul_of_nonneg_left
          ProductionScalarProjection.linearPositionBlockAbortProbability_le
          (by positivity : (0 : ℚ) ≤ parameters.proofs)))

/-- Complete concrete ledger, parameterized only by the two events whose bad
sets are selected by the adaptive adversary/oracle interaction. -/
noncomputable def components
    (challengePrequery :
      ComponentEvent parameters (Tape parameters Core) .challengePrequery)
    (hiddenMerkleInput :
      ComponentEvent parameters (Tape parameters Core) .hiddenMerkleInput) :
    ∀ event, ComponentEvent parameters (Tape parameters Core) event
  | .challengePrequery => challengePrequery
  | .hiddenMerkleInput => hiddenMerkleInput
  | .oracleAnswerCollision => oracleCollisionComponent parameters
  | .proofNonceCollision => proofNonceCollisionComponent parameters
  | .outerTreeNonceCollision => outerTreeNonceCollisionComponent parameters
  | .linearTreeNonceCollision => linearTreeNonceCollisionComponent parameters
  | .hadamardTreeNonceCollision =>
      hadamardTreeNonceCollisionComponent parameters
  | .blindGrindingAbort => blindGrindingComponent parameters
  | .ligeritoGrindingAbort => ligeritoGrindingComponent parameters
  | .nonzeroChallengeAbort => nonzeroChallengeComponent parameters
  | .multiplicationChallengeAbort =>
      multiplicationChallengeComponent parameters
  | .equalityPointSamplingAbort =>
      equalityPointChallengeComponent parameters
  | .outerPositionSamplingAbort => outerPositionComponent parameters
  | .hadamardPositionSamplingAbort => hadamardPositionComponent parameters
  | .linearPositionSamplingAbort => linearPositionComponent parameters

/-- End-to-end composition over the concrete tape.  All cardinality and
probability entries are discharged; the remaining premise is precisely the
pointwise equality of the real and simulated state machines on good tapes. -/
theorem e2e_zk_of_good_tape {View : Type} [Fintype View] [DecidableEq View]
    (challengePrequery :
      ComponentEvent parameters (Tape parameters Core) .challengePrequery)
    (hiddenMerkleInput :
      ComponentEvent parameters (Tape parameters Core) .hiddenMerkleInput)
    (real simulated : Tape parameters Core → View)
    (coinEquiv : Tape parameters Core ≃ Tape parameters Core)
    (hgood : ∀ tape,
      (∀ event, tape ∉
        ((components parameters challengePrequery hiddenMerkleInput event).globalBad)) →
      real (coinEquiv tape) = simulated tape) :
    EndToEnd.uniformTV real simulated ≤ zkBound parameters := by
  exact classicalProm_e2e_zk_components parameters real simulated coinEquiv
    (components parameters challengePrequery hiddenMerkleInput) hgood

end Components

end VeiledFlock.ConcreteRandomTape

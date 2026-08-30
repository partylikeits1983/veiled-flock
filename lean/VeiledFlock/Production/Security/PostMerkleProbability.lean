import VeiledFlock.Production.Operational.HiddenSaltTransport
import VeiledFlock.Production.Operational.OperationalGood

/-!
# Adaptive post-proof Merkle probability for the production experiment

This file specializes the hidden-salt transport to the exact production proof
and adaptive verifier.  The independent dummy salt is averaged only after the
complete real proof and query history have been fixed.
-/

namespace VeiledFlock.ProductionPostMerkleProbability

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.MerkleHiding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionHiddenSaltTransport
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionMerkleTree
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalGood
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionThreeTree

variable {AdversaryCoins FinalState : Type} [Fintype AdversaryCoins]
variable {preQueries postQueries : ℕ}

inductive PostLeafSide
  | honest
  | representative
  deriving DecidableEq

/-- Dummy salts, actual protocol/adversary coins, and the one shared oracle
table, in the ordering consumed by the global hidden-salt transport. -/
abbrev ExpandedTape (shape : BatchShape) (maxStartLength : ℕ)
    (AdversaryCoins : Type*) :=
  ExpandedProtocolCoins shape AdversaryCoins ×
    ProductionSharedOracleTable shape maxStartLength

/-- Remove the independent dummy salt and restore the operational ledger tape
ordering. -/
def originalTape (shape : BatchShape) (maxStartLength : ℕ)
    (input : ExpandedTape shape maxStartLength AdversaryCoins) :
    ProductionLedgerTape shape maxStartLength AdversaryCoins :=
  (input.1.2.1, input.2, input.1.2.2)

/-- Exact product equivalence witnessing that the dummy salt tape is an
independent uniform coordinate. -/
def expandedTapeSplit (shape : BatchShape) (maxStartLength : ℕ) :
    ExpandedTape shape maxStartLength AdversaryCoins ≃
      ProductionHiddenSalts shape ×
        ProductionLedgerTape shape maxStartLength AdversaryCoins where
  toFun input := (input.1.1, originalTape shape maxStartLength input)
  invFun input := ((input.1, (input.2.1, input.2.2.2)), input.2.2.1)
  left_inv input := by rcases input with ⟨⟨dummy, coins, adversaryCoins⟩, table⟩; rfl
  right_inv input := by rcases input with ⟨dummy, coins, table, adversaryCoins⟩; rfl

/-- The payload at one hidden production leaf after all non-salt coins and a
successful real trace have been fixed. -/
noncomputable def postLeafPayload
    (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (trace : ProductionExecutionTrace shape)
    (restCoins : ProductionCoinsWithoutHiddenSalts shape)
    (side : PostLeafSide) (site : ProductionHiddenLeafIndex shape) : List Byte :=
  let coins := productionCoinsWithHiddenSalts shape (fun _ => 0) restCoins
  let representative := publicRepresentative shape statement
  let selectedWitness := match side with
    | .honest => witness
    | .representative => representative
  let selectedCoins := match side with
    | .honest => coins
    | .representative =>
        productionProtocolCoinEquiv shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context witness representative
          trace.answers trace.tail.rest coins
  match site with
  | .inl (.inl outer) =>
      outerRowPayload shape (baseMessage shape) selectedWitness selectedCoins
        outer
  | .inl (.inr linear) => linearRowPayload shape selectedCoins linear
  | .inr hadamard =>
      hadamardRowPayload shape
        (productionLayerSpecAt shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context trace.answers trace.tail.rest
          selectedWitness selectedCoins)
        selectedWitness selectedCoins hadamard

/-- Exact bounded hidden leaf point, canonically enumerated over all three
production trees. -/
noncomputable def postLeafPoint
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (trace : ProductionExecutionTrace shape)
    (restCoins : ProductionCoinsWithoutHiddenSalts shape)
    (side : PostLeafSide)
    (site : Fin (Fintype.card (ProductionHiddenLeafIndex shape)))
    (salt : VeiledFlock.NonceSerialization.NumericNonce)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength) :
    BoundedBytes (ProductionMaxPointLength shape maxStartLength) :=
  let actualSite :=
    (Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site
  let payload := postLeafPayload shape causalSecret weights context statement
    witness trace restCoins side actualSite
  boundBytes (hiddenLeafFramedPoint shape restCoins actualSite salt payload) (by
    rcases actualSite with (outerOrLinear | hadamard)
    · rcases outerOrLinear with (outer | linear)
      · rw [hiddenLeafFramedPoint, productionLeafPoint_length]
        simpa [payload, postLeafPayload] using houter
      · rw [hiddenLeafFramedPoint, productionLeafPoint_length]
        simpa [payload, postLeafPayload] using hlinear
    · rw [hiddenLeafFramedPoint, productionLeafPoint_length]
      simpa [payload, postLeafPayload] using hhadamard)

theorem postLeafPoint_salt_injective
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (trace : ProductionExecutionTrace shape)
    (restCoins : ProductionCoinsWithoutHiddenSalts shape)
    (side : PostLeafSide)
    (site : Fin (Fintype.card (ProductionHiddenLeafIndex shape)))
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength) :
    Injective (fun salt : VeiledFlock.NonceSerialization.NumericNonce =>
      postLeafPoint shape maxStartLength causalSecret
      weights context statement witness trace restCoins side site salt houter
      hlinear hhadamard) := by
  intro left right heq
  have hunbound := congrArg unboundBytes heq
  exact hiddenLeafFramedPoint_cross shape restCoins
    ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site)
    left right
    (postLeafPayload shape causalSecret weights context statement witness trace
      restCoins side
      ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site))
    (postLeafPayload shape causalSecret weights context statement witness trace
      restCoins side
      ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site))
    hunbound

/-- Exact pre- and post-proof adaptive histories observed on one operational
tape. -/
noncomputable def completeAdversaryHistory
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    List (BoundedBytes (ProductionMaxPointLength shape maxStartLength) ×
      OracleBlock) :=
  let pre := productionPreHistory adversary statement tape.2.2 tape.2.1
  match productionRealTrace shape fallback r1csDigest causalSecret completion
      (baseMessage shape) statement witness tape.1 tape.2.1 with
  | none => pre
  | some trace =>
      pre ++ productionPostHistory adversary statement
        (some (productionTraceProof shape fallback causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          tape.1 tape.2.1 trace)) tape.2.2 pre tape.2.1

theorem completeAdversaryHistory_length_le
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    (completeAdversaryHistory shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      tape).length ≤ preQueries + postQueries := by
  let pre := productionPreHistory adversary statement tape.2.2 tape.2.1
  have hpre : pre.length ≤ preQueries := by
    unfold pre productionPreHistory
    simpa using runQueryValues_length_le
      (fun round history => adversary.preQuery round statement tape.2.2
        history) tape.2.1 (List.ofFn id) []
  unfold completeAdversaryHistory
  dsimp only
  split
  · exact le_trans (by simpa [pre] using hpre) (Nat.le_add_right _ _)
  · rename_i trace htrace
    have hpost : (productionPostHistory adversary statement
        (some (productionTraceProof shape fallback causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          tape.1 tape.2.1 trace)) tape.2.2 pre tape.2.1).length ≤
        postQueries := by
      unfold productionPostHistory
      simpa using runQueryValues_length_le
        (fun round history => adversary.postQuery round statement
          (some (productionTraceProof shape fallback causalSecret
            (baseMessage shape) (publicPositions shape) weights context witness
            tape.1 tape.2.1 trace)) tape.2.2 pre history)
        tape.2.1 (List.ofFn id) []
    simp only [List.length_append]
    exact Nat.add_le_add hpre hpost

/-! ## Independently averaged dummy-salt event -/

/-- The distinct byte strings queried by the complete adaptive adversary on
one operational tape.  This includes both pre-proof and post-proof queries. -/
noncomputable def completeMerklePointSet
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    Finset (List Byte) :=
  ((completeAdversaryHistory shape maxStartLength fallback r1csDigest
    causalSecret completion weights context adversary statement witness tape).map
      (fun call => unboundBytes call.1)).toFinset

theorem completeMerklePointSet_card_le
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    (completeMerklePointSet shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      tape).card ≤ preQueries + postQueries := by
  classical
  calc
    _ ≤ (completeAdversaryHistory shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness
        tape).length := by
      exact (List.toFinset_card_le _).trans_eq (by simp)
    _ ≤ preQueries + postQueries :=
      completeAdversaryHistory_length_le shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness tape

/-- Dummy hidden-salt vectors for which some complete adaptive query can be
parsed as a production leaf at one of the three hidden sites.  The payload is
existential, so this single event covers both the honest and public-
representative leaf families without assuming either payload is public. -/
noncomputable def dummyPostMerkleSaltAssignments
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    Finset (ProductionHiddenSalts shape) :=
  (universalHiddenInputBadAssignments
    (enumeratedHiddenLeafFramedPoint shape
      (productionCoinsHiddenSaltsEquiv shape tape.1).2)
    (completeMerklePointSet shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      tape)).map (productionHiddenSaltsFinEquiv shape).symm.toEmbedding

theorem dummyPostMerkleSaltAssignments_probability_le
    [Nonempty AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    ((dummyPostMerkleSaltAssignments shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      tape).card : ℚ) / Fintype.card (ProductionHiddenSalts shape) ≤
      (Fintype.card (ProductionHiddenLeafIndex shape) *
        (preQueries + postQueries) : ℕ) /
          Fintype.card VeiledFlock.NonceSerialization.NumericNonce := by
  classical
  let rest := (productionCoinsHiddenSaltsEquiv shape tape.1).2
  let point := enumeratedHiddenLeafFramedPoint shape rest
  let queries := completeMerklePointSet shape maxStartLength fallback
    r1csDigest causalSecret completion weights context adversary statement
    witness tape
  have hcross : ∀ site leftSalt leftPayload rightSalt rightPayload,
      point site leftSalt leftPayload = point site rightSalt rightPayload →
        leftSalt = rightSalt := by
    intro site leftSalt leftPayload rightSalt rightPayload heq
    exact hiddenLeafFramedPoint_cross shape rest
      ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site)
      leftSalt rightSalt leftPayload rightPayload heq
  have hgeneric := universalHiddenInputProbability_le point queries hcross
  have hcard :
      (dummyPostMerkleSaltAssignments shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness
        tape).card =
      (universalHiddenInputBadAssignments point queries).card :=
    Finset.card_map _
  rw [hcard]
  rw [Fintype.card_congr (productionHiddenSaltsFinEquiv shape)]
  exact hgeneric.trans (by
    gcongr
    exact_mod_cast Nat.mul_le_mul_left
      (Fintype.card (ProductionHiddenLeafIndex shape))
      (completeMerklePointSet_card_le shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness
        tape))

/-- Lift the independently averaged dummy-salt event to the complete expanded
tape. -/
noncomputable def dummyPostMerkleExpandedSet
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape) :
    Finset (ExpandedTape shape maxStartLength AdversaryCoins) :=
  VeiledFlock.Probability.liftFiberBad
    (expandedTapeSplit shape maxStartLength)
    (dummyPostMerkleSaltAssignments shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness)

theorem dummyPostMerkleExpandedSet_probability_le
    [Nonempty AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape) :
    ((dummyPostMerkleExpandedSet shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness).card :
        ℚ) / Fintype.card (ExpandedTape shape maxStartLength AdversaryCoins) ≤
      (Fintype.card (ProductionHiddenLeafIndex shape) *
        (preQueries + postQueries) : ℕ) /
          Fintype.card VeiledFlock.NonceSerialization.NumericNonce := by
  classical
  exact VeiledFlock.Probability.liftFiberBad_probability_le
    (expandedTapeSplit shape maxStartLength)
    (dummyPostMerkleSaltAssignments shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness)
    ((Fintype.card (ProductionHiddenLeafIndex shape) *
      (preQueries + postQueries) : ℕ) /
        Fintype.card VeiledFlock.NonceSerialization.NumericNonce)
    (dummyPostMerkleSaltAssignments_probability_le shape maxStartLength
      fallback r1csDigest causalSecret completion weights context adversary
      statement witness)

theorem mem_dummyPostMerkleSaltAssignments_iff
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins)
    (salts : ProductionHiddenSalts shape) :
    salts ∈ dummyPostMerkleSaltAssignments shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness tape ↔
      ∃ (site : ProductionHiddenLeafIndex shape) (payload : List Byte),
        hiddenLeafFramedPoint shape
            (productionCoinsHiddenSaltsEquiv shape tape.1).2 site
            (salts site) payload ∈
          completeMerklePointSet shape maxStartLength fallback r1csDigest
            causalSecret completion weights context adversary statement
            witness tape := by
  classical
  rw [dummyPostMerkleSaltAssignments, Finset.mem_map]
  constructor
  · rintro ⟨enumerated, hbad, heq⟩
    rw [mem_universalHiddenInputBadAssignments_iff] at hbad
    rcases hbad with ⟨site, payload, hpoint⟩
    refine ⟨(Fintype.equivFin
      (ProductionHiddenLeafIndex shape)).symm site, payload, ?_⟩
    have hsalt : salts ((Fintype.equivFin
        (ProductionHiddenLeafIndex shape)).symm site) = enumerated site := by
      rw [← heq]
      simp only [Equiv.toEmbedding_apply,
        productionHiddenSaltsFinEquiv_symm_apply, Equiv.apply_symm_apply]
    rw [hsalt]
    simpa only [enumeratedHiddenLeafFramedPoint] using hpoint
  · rintro ⟨site, payload, hpoint⟩
    let enumerated := productionHiddenSaltsFinEquiv shape salts
    refine ⟨enumerated, ?_,
      (productionHiddenSaltsFinEquiv shape).symm_apply_apply salts⟩
    rw [mem_universalHiddenInputBadAssignments_iff]
    refine ⟨Fintype.equivFin (ProductionHiddenLeafIndex shape) site,
      payload, ?_⟩
    have hsalt : enumerated
        (Fintype.equivFin (ProductionHiddenLeafIndex shape) site) =
        salts site := by
      dsimp only [enumerated]
      simp only [productionHiddenSaltsFinEquiv_apply,
        Equiv.symm_apply_apply]
    rw [hsalt]
    simpa only [enumeratedHiddenLeafFramedPoint,
      Equiv.symm_apply_apply] using hpoint

theorem completeAdversaryHistory_eq_twoPhase_of_trace
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness tape.1 tape.2.1 =
        some trace) :
    completeAdversaryHistory shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness
        tape =
      runTwoPhaseQueryValues
        (fun round history => adversary.preQuery round statement tape.2.2
          history)
        (fun pre round history => adversary.postQuery round statement
          (some (productionTraceProof shape fallback causalSecret
            (baseMessage shape) (publicPositions shape) weights context witness
            tape.1 tape.2.1 trace)) tape.2.2 pre history)
        tape.2.1 := by
  simp [completeAdversaryHistory, htrace, runTwoPhaseQueryValues,
    productionPreHistory, productionPostHistory]

/-- The concrete successful-trace salt/oracle transport used in the
post-proof event reduction. -/
noncomputable def postMerkleTransport
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    ExpandedTape shape maxStartLength AdversaryCoins ≃
      ExpandedTape shape maxStartLength AdversaryCoins :=
  productionHiddenSaltTransportEquiv
    (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest causalSecret
    completion (baseMessage shape) (publicPositions shape) weights context
    statement witness houter hlinear hhadamard hnodes

/-- The actual honest hidden-leaf family moved by `postMerkleTransport`, in
the salt-independent geometry used by that equivalence. -/
noncomputable def honestTransportPoint
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape) :
    FamilyIndex ProductionTree
      (productionTreeGeometry shape
        (saltIndependentGeometryCoins shape input.1.2.1)) →
      BoundedBytes (ProductionMaxPointLength shape maxStartLength) :=
  boundedFamilyLeafPoint
    (productionTreeGeometry shape
      (saltIndependentGeometryCoins shape input.1.2.1))
    (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
      shape (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
      (baseMessage shape) (publicPositions shape) weights context trace.answers
      trace.tail.rest witness)
    (expandedProductionTreeMaterial_fits shape
      (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
      (baseMessage shape) (publicPositions shape) weights context trace.answers
      trace.tail.rest witness houter hlinear hhadamard)
    input.1

/-- The corresponding dummy-salt hidden-leaf family after applying only the
coin projection of the transport. -/
noncomputable def dummyTransportPoint
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape) :
    FamilyIndex ProductionTree
      (productionTreeGeometry shape
        (saltIndependentGeometryCoins shape input.1.2.1)) →
      BoundedBytes (ProductionMaxPointLength shape maxStartLength) :=
  boundedFamilyLeafPoint
    (productionTreeGeometry shape
      (saltIndependentGeometryCoins shape input.1.2.1))
    (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
      shape (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
      (baseMessage shape) (publicPositions shape) weights context trace.answers
      trace.tail.rest witness)
    (expandedProductionTreeMaterial_fits shape
      (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
      (baseMessage shape) (publicPositions shape) weights context trace.answers
      trace.tail.rest witness houter hlinear hhadamard)
    (expandedHiddenSaltSwap shape AdversaryCoins input.1)

theorem honestTransportPoint_framed
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (index : FamilyIndex ProductionTree
      (productionTreeGeometry shape
        (saltIndependentGeometryCoins shape input.1.2.1))) :
    ∃ (site : ProductionHiddenLeafIndex shape) (payload : List Byte),
      unboundBytes (honestTransportPoint shape maxStartLength causalSecret
        weights context witness houter hlinear hhadamard input trace index) =
      hiddenLeafFramedPoint shape
        (productionCoinsHiddenSaltsEquiv shape input.1.2.1).2 site
        ((productionCoinsHiddenSaltsEquiv shape input.1.2.1).1 site)
        payload := by
  rcases index with ⟨tree, index⟩
  cases tree with
  | outer =>
      refine ⟨.inl (.inl index), outerRowPayload shape (baseMessage shape)
        witness input.1.2.1 index, ?_⟩
      rfl
  | veilLinear =>
      refine ⟨.inl (.inr index), linearRowPayload shape input.1.2.1 index,
        ?_⟩
      rfl
  | veilHadamard =>
      refine ⟨.inr index, hadamardRowPayload shape
        (productionLayerSpecAt shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context trace.answers trace.tail.rest
          witness input.1.2.1) witness input.1.2.1 index, ?_⟩
      rfl

theorem dummyTransportPoint_framed
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (index : FamilyIndex ProductionTree
      (productionTreeGeometry shape
        (saltIndependentGeometryCoins shape input.1.2.1))) :
    ∃ (site : ProductionHiddenLeafIndex shape) (payload : List Byte),
      unboundBytes (dummyTransportPoint shape maxStartLength causalSecret
        weights context witness houter hlinear hhadamard input trace index) =
      hiddenLeafFramedPoint shape
        (productionCoinsHiddenSaltsEquiv shape input.1.2.1).2 site
        (input.1.1 site) payload := by
  rcases index with ⟨tree, index⟩
  cases tree with
  | outer =>
      refine ⟨.inl (.inl index), outerRowPayload shape (baseMessage shape)
        witness (productionCoinsWithHiddenSalts shape input.1.1
          (productionCoinsHiddenSaltsEquiv shape input.1.2.1).2) index, ?_⟩
      rfl
  | veilLinear =>
      refine ⟨.inl (.inr index), linearRowPayload shape
        (productionCoinsWithHiddenSalts shape input.1.1
          (productionCoinsHiddenSaltsEquiv shape input.1.2.1).2) index, ?_⟩
      rfl
  | veilHadamard =>
      let coins := productionCoinsWithHiddenSalts shape input.1.1
        (productionCoinsHiddenSaltsEquiv shape input.1.2.1).2
      refine ⟨.inr index, hadamardRowPayload shape
        (productionLayerSpecAt shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context trace.answers trace.tail.rest
          witness coins) witness coins index, ?_⟩
      rfl

theorem postMerkleTransport_dummyPoint_eq_honestPoint
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness input.1.2.1 input.2 =
        some trace) :
    let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard hnodes input
    HEq
      (dummyTransportPoint shape maxStartLength causalSecret weights context
        witness houter hlinear hhadamard moved trace)
      (honestTransportPoint shape maxStartLength causalSecret weights context
        witness houter hlinear hhadamard input trace) := by
  dsimp only
  rw [postMerkleTransport,
    productionHiddenSaltTransportEquiv_apply_of_trace shape fallback
      r1csDigest causalSecret completion (baseMessage shape)
      (publicPositions shape) weights context statement witness houter hlinear
      hhadamard hnodes input trace htrace]
  rfl

theorem dummyTransportHit_implies_mem_expandedSet
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (hhit : QueryHistoryHits
      (dummyTransportPoint shape maxStartLength causalSecret weights context
        witness houter hlinear hhadamard input trace)
      (completeAdversaryHistory shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness
        (originalTape shape maxStartLength input))) :
    input ∈ dummyPostMerkleExpandedSet shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness := by
  classical
  rw [dummyPostMerkleExpandedSet,
    VeiledFlock.Probability.mem_liftFiberBad_iff]
  change input.1.1 ∈ dummyPostMerkleSaltAssignments shape maxStartLength
    fallback r1csDigest causalSecret completion weights context adversary
    statement witness (originalTape shape maxStartLength input)
  rw [mem_dummyPostMerkleSaltAssignments_iff]
  rcases hhit with ⟨call, hcall, index, hpoint⟩
  rcases dummyTransportPoint_framed shape maxStartLength causalSecret weights
    context witness houter hlinear hhadamard input trace index with
    ⟨site, payload, hframed⟩
  refine ⟨site, payload, ?_⟩
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨call, hcall, ?_⟩
  rw [hpoint, hframed]
  rfl

theorem postMerkleTransport_dummy_of_trace
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness input.1.2.1 input.2 =
        some trace) :
    let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard hnodes input
    moved.1.1 = (productionCoinsHiddenSaltsEquiv shape input.1.2.1).1 := by
  dsimp only
  rw [postMerkleTransport,
    productionHiddenSaltTransportEquiv_apply_of_trace shape fallback
      r1csDigest causalSecret completion (baseMessage shape)
      (publicPositions shape) weights context statement witness houter hlinear
      hhadamard hnodes input trace htrace]
  rfl

theorem postMerkleTransport_rest_of_trace
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness input.1.2.1 input.2 =
        some trace) :
    let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard hnodes input
    (productionCoinsHiddenSaltsEquiv shape moved.1.2.1).2 =
      (productionCoinsHiddenSaltsEquiv shape input.1.2.1).2 ∧
    moved.1.2.2 = input.1.2.2 := by
  dsimp only
  rw [postMerkleTransport,
    productionHiddenSaltTransportEquiv_apply_of_trace shape fallback
      r1csDigest causalSecret completion (baseMessage shape)
      (publicPositions shape) weights context statement witness houter hlinear
      hhadamard hnodes input trace htrace]
  constructor <;> rfl

theorem postMerkleTransport_saltIndependentCoins_of_trace
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness input.1.2.1 input.2 =
        some trace) :
    let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard hnodes input
    saltIndependentGeometryCoins shape moved.1.2.1 =
      saltIndependentGeometryCoins shape input.1.2.1 := by
  dsimp only
  rw [postMerkleTransport,
    productionHiddenSaltTransportEquiv_apply_of_trace shape fallback
      r1csDigest causalSecret completion (baseMessage shape)
      (publicPositions shape) weights context statement witness houter hlinear
      hhadamard hnodes input trace htrace]
  rfl

set_option maxHeartbeats 1600000 in
theorem honestCompleteHit_implies_dummy_union
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness input.1.2.1 input.2 =
        some trace)
    (hhit : QueryHistoryHits
      (honestTransportPoint shape maxStartLength causalSecret weights context
        witness houter hlinear hhadamard input trace)
      (completeAdversaryHistory shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness
        (originalTape shape maxStartLength input))) :
    let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard hnodes input
    input ∈ dummyPostMerkleExpandedSet shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness ∨
      moved ∈ dummyPostMerkleExpandedSet shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness := by
  classical
  let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
    causalSecret completion weights context statement witness houter hlinear
    hhadamard hnodes input
  let proof := productionTraceProof shape fallback causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    input.1.2.1 input.2 trace
  let preQuery := fun round history => adversary.preQuery round statement
    input.1.2.2 history
  let postQuery := fun pre round history => adversary.postQuery round statement
    (some proof) input.1.2.2 pre history
  let leftPoints := honestTransportPoint shape maxStartLength causalSecret
    weights context witness houter hlinear hhadamard input trace
  let rightPoints := dummyTransportPoint shape maxStartLength causalSecret
    weights context witness houter hlinear hhadamard input trace
  have hhistory : completeAdversaryHistory shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness (originalTape shape maxStartLength input) =
      runTwoPhaseQueryValues preQuery postQuery input.2 := by
    simpa [preQuery, postQuery, proof, originalTape] using
      (completeAdversaryHistory_eq_twoPhase_of_trace shape maxStartLength
        fallback r1csDigest causalSecret completion weights context adversary
        statement witness (originalTape shape maxStartLength input) trace
        htrace)
  have hoff : ∀ point,
      (∀ index, point ≠ leftPoints index) →
      (∀ index, point ≠ rightPoints index) → moved.2 point = input.2 point := by
    intro point hleft hright
    exact productionHiddenSaltTransportEquiv_oracle_off_of_trace
      (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest causalSecret
      completion (baseMessage shape) (publicPositions shape) weights context
      statement witness houter hlinear hhadamard hnodes input trace htrace point
      hleft hright
  have hhit' : QueryHistoryHits leftPoints
      (runTwoPhaseQueryValues preQuery postQuery input.2) := by
    simpa [leftPoints] using hhistory ▸ hhit
  have htransport := runTwoPhaseQueryValues_hit_transport preQuery postQuery
    leftPoints rightPoints input.2 moved.2 hoff hhit'
  rcases htransport with horiginal | htransported
  · left
    apply dummyTransportHit_implies_mem_expandedSet shape maxStartLength
      fallback r1csDigest causalSecret completion weights context adversary
      statement witness houter hlinear hhadamard input trace
    simpa [rightPoints, hhistory] using horiginal
  · right
    have hmovedTrace : productionRealTrace shape fallback r1csDigest
        causalSecret completion (baseMessage shape) statement witness
        moved.1.2.1 moved.2 = some trace := by
      have hpreserve := productionHiddenSaltTransportEquiv_trace
        (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
        causalSecret completion (baseMessage shape) (publicPositions shape)
        weights context statement witness houter hlinear hhadamard hnodes input
      simpa [moved, postMerkleTransport] using hpreserve.trans htrace
    have hmovedProof : productionTraceProof shape fallback causalSecret
        (baseMessage shape) (publicPositions shape) weights context witness
        moved.1.2.1 moved.2 trace = proof := by
      exact productionHiddenSaltTransportEquiv_proof_of_trace
        (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
        causalSecret completion (baseMessage shape) (publicPositions shape)
        weights context statement witness houter hlinear hhadamard hnodes input
        trace htrace
    have hmovedCoins : moved.1.2.2 = input.1.2.2 :=
      (postMerkleTransport_rest_of_trace shape maxStartLength fallback
        r1csDigest causalSecret completion weights context statement witness
        houter hlinear hhadamard hnodes input trace htrace).2
    have hmovedHistory : completeAdversaryHistory shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness (originalTape shape maxStartLength moved) =
        runTwoPhaseQueryValues preQuery postQuery moved.2 := by
      have hbase := completeAdversaryHistory_eq_twoPhase_of_trace shape
        maxStartLength fallback r1csDigest causalSecret completion weights
        context adversary statement witness
        (originalTape shape maxStartLength moved) trace hmovedTrace
      simpa [preQuery, postQuery, proof, originalTape, hmovedCoins,
        hmovedProof] using hbase
    rw [dummyPostMerkleExpandedSet,
      VeiledFlock.Probability.mem_liftFiberBad_iff]
    change moved.1.1 ∈ dummyPostMerkleSaltAssignments shape maxStartLength
      fallback r1csDigest causalSecret completion weights context adversary
      statement witness (originalTape shape maxStartLength moved)
    rw [mem_dummyPostMerkleSaltAssignments_iff]
    rcases htransported with ⟨call, hcall, index, hpoint⟩
    rcases honestTransportPoint_framed shape maxStartLength causalSecret
      weights context witness houter hlinear hhadamard input trace index with
      ⟨site, payload, hframed⟩
    refine ⟨site, payload, ?_⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨call, ?_, ?_⟩
    · rw [hmovedHistory]
      exact hcall
    · have hdummy := postMerkleTransport_dummy_of_trace shape maxStartLength
        fallback r1csDigest causalSecret completion weights context statement
        witness houter hlinear hhadamard hnodes input trace htrace
      have hrest := (postMerkleTransport_rest_of_trace shape maxStartLength
        fallback r1csDigest causalSecret completion weights context statement
        witness houter hlinear hhadamard hnodes input trace htrace).1
      dsimp only at hdummy hrest
      change unboundBytes call.1 = hiddenLeafFramedPoint shape
        (productionCoinsHiddenSaltsEquiv shape moved.1.2.1).2 site
        (moved.1.1 site) payload
      rw [hdummy, hrest, hpoint, hframed]

set_option maxHeartbeats 2400000 in
/-- The concrete semantic post-proof Merkle failure is covered by the
independently averaged dummy event before or after the measure-preserving
hidden-salt transport. -/
theorem badPostMerkle_implies_dummy_union
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ExpandedTape shape maxStartLength AdversaryCoins)
    (hbad : BadPostMerkle shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      (originalTape shape maxStartLength input)) :
    let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard hnodes input
    input ∈ dummyPostMerkleExpandedSet shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness ∨
      moved ∈ dummyPostMerkleExpandedSet shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness := by
  classical
  rcases hbad with ⟨trace, htrace, hnotFresh⟩
  have htrace' : productionRealTrace shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness input.1.2.1 input.2 =
        some trace := by
    simpa [realTrace, originalTape] using htrace
  let tape := originalTape shape maxStartLength input
  let post := productionPostHistory adversary statement
    (some (productionTraceProof shape fallback causalSecret
      (baseMessage shape) (publicPositions shape) weights context witness
      input.1.2.1 input.2 trace)) input.1.2.2
    (productionPreHistory adversary statement input.1.2.2 input.2) input.2
  simp only [PostMerkleFresh, AvoidsProductionMerkleTransport, couplingInput,
    adversaryRandomness, originalTape] at hnotFresh
  push_neg at hnotFresh
  rcases hnotFresh with ⟨call, hcall, hfailure⟩
  have hcases :
      (∃ index, unboundBytes call.1 = familyLeafPoint
        (productionTreeGeometry shape input.1.2.1)
        (productionTreeMaterial shape input.1.2.1 causalSecret
          (baseMessage shape) (publicPositions shape) weights context
          trace.answers trace.tail.rest witness) input.1.2.1 index) ∨
      (∃ index, unboundBytes call.1 = familyLeafPoint
        (productionTreeGeometry shape input.1.2.1)
        (productionTreeMaterial shape input.1.2.1 causalSecret
          (baseMessage shape) (publicPositions shape) weights context
          trace.answers trace.tail.rest (publicRepresentative shape statement))
        (productionProtocolCoinEquiv shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context witness
          (publicRepresentative shape statement) trace.answers trace.tail.rest
          input.1.2.1) index) := by
    by_cases hleftSafe : ∀ index, unboundBytes call.1 ≠ familyLeafPoint
        (productionTreeGeometry shape input.1.2.1)
        (productionTreeMaterial shape input.1.2.1 causalSecret
          (baseMessage shape) (publicPositions shape) weights context
          trace.answers trace.tail.rest witness) input.1.2.1 index
    · exact Or.inr (hfailure hleftSafe)
    · left
      push_neg at hleftSafe
      exact hleftSafe
  rcases hcases with hleft | hright
  · have hcompleteHit : QueryHistoryHits
        (honestTransportPoint shape maxStartLength causalSecret weights
          context witness houter hlinear hhadamard input trace)
        (completeAdversaryHistory shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement witness
          tape) := by
      rcases hleft with ⟨index, hpoint⟩
      refine ⟨call, ?_, index, ?_⟩
      · rw [completeAdversaryHistory_eq_twoPhase_of_trace shape
          maxStartLength fallback r1csDigest causalSecret completion weights
          context adversary statement witness
          (originalTape shape maxStartLength input) trace htrace']
        simp only [runTwoPhaseQueryValues, List.mem_append]
        exact Or.inr hcall
      · apply unboundBytes_injective
        rw [hpoint]
        rcases index with ⟨tree, index⟩
        cases tree <;> rfl
    exact honestCompleteHit_implies_dummy_union shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness houter hlinear hhadamard hnodes input trace htrace' hcompleteHit
  · let moved := postMerkleTransport shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard hnodes input
    let proof := productionTraceProof shape fallback causalSecret
      (baseMessage shape) (publicPositions shape) weights context witness
      input.1.2.1 input.2 trace
    let preQuery := fun round history => adversary.preQuery round statement
      input.1.2.2 history
    let postQuery := fun pre round history => adversary.postQuery round statement
      (some proof) input.1.2.2 pre history
    let leftPoints := honestTransportPoint shape maxStartLength causalSecret
      weights context witness houter hlinear hhadamard input trace
    let rightPoints := dummyTransportPoint shape maxStartLength causalSecret
      weights context witness houter hlinear hhadamard input trace
    have hhistory : completeAdversaryHistory shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness tape = runTwoPhaseQueryValues preQuery postQuery input.2 := by
      simpa [tape, preQuery, postQuery, proof, originalTape] using
        (completeAdversaryHistory_eq_twoPhase_of_trace shape maxStartLength
          fallback r1csDigest causalSecret completion weights context adversary
          statement witness (originalTape shape maxStartLength input) trace
          htrace')
    by_cases hleftHit : QueryHistoryHits leftPoints
        (completeAdversaryHistory shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement witness
          tape)
    · exact honestCompleteHit_implies_dummy_union shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness houter hlinear hhadamard hnodes input trace htrace' hleftHit
    · by_cases hrightHit : QueryHistoryHits rightPoints
          (completeAdversaryHistory shape maxStartLength fallback r1csDigest
            causalSecret completion weights context adversary statement witness
            tape)
      · exact Or.inl (dummyTransportHit_implies_mem_expandedSet shape
          maxStartLength fallback r1csDigest causalSecret completion weights
          context adversary statement witness houter hlinear hhadamard input
          trace hrightHit)
      · have hoff : ∀ point,
            (∀ index, point ≠ leftPoints index) →
            (∀ index, point ≠ rightPoints index) →
              moved.2 point = input.2 point := by
          intro point hleftOff hrightOff
          exact productionHiddenSaltTransportEquiv_oracle_off_of_trace
            (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
            causalSecret completion (baseMessage shape) (publicPositions shape)
            weights context statement witness houter hlinear hhadamard hnodes
            input trace htrace' point hleftOff hrightOff
        have htwoPhaseEq := runTwoPhaseQueryValues_eq_of_avoids preQuery
          postQuery leftPoints rightPoints input.2 moved.2 hoff (by
            rw [← hhistory]
            exact hleftHit) (by
            rw [← hhistory]
            exact hrightHit)
        have hmovedTrace : productionRealTrace shape fallback r1csDigest
            causalSecret completion (baseMessage shape) statement witness
            moved.1.2.1 moved.2 = some trace := by
          have hpreserve := productionHiddenSaltTransportEquiv_trace
            (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
            causalSecret completion (baseMessage shape) (publicPositions shape)
            weights context statement witness houter hlinear hhadamard hnodes
            input
          simpa [moved, postMerkleTransport] using hpreserve.trans htrace'
        have hmovedProof : productionTraceProof shape fallback causalSecret
            (baseMessage shape) (publicPositions shape) weights context witness
            moved.1.2.1 moved.2 trace = proof := by
          exact productionHiddenSaltTransportEquiv_proof_of_trace
            (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
            causalSecret completion (baseMessage shape) (publicPositions shape)
            weights context statement witness houter hlinear hhadamard hnodes
            input trace htrace'
        have hmovedCoins : moved.1.2.2 = input.1.2.2 :=
          (postMerkleTransport_rest_of_trace shape maxStartLength fallback
            r1csDigest causalSecret completion weights context statement
            witness houter hlinear hhadamard hnodes input trace htrace').2
        have hmovedHistory : completeAdversaryHistory shape maxStartLength
            fallback r1csDigest causalSecret completion weights context
            adversary statement witness
            (originalTape shape maxStartLength moved) =
            runTwoPhaseQueryValues preQuery postQuery moved.2 := by
          have hbase := completeAdversaryHistory_eq_twoPhase_of_trace shape
            maxStartLength fallback r1csDigest causalSecret completion weights
            context adversary statement witness
            (originalTape shape maxStartLength moved) trace hmovedTrace
          simpa [preQuery, postQuery, proof, originalTape, hmovedCoins,
            hmovedProof] using hbase
        right
        rw [dummyPostMerkleExpandedSet,
          VeiledFlock.Probability.mem_liftFiberBad_iff]
        change moved.1.1 ∈ dummyPostMerkleSaltAssignments shape maxStartLength
          fallback r1csDigest causalSecret completion weights context adversary
          statement witness (originalTape shape maxStartLength moved)
        rw [mem_dummyPostMerkleSaltAssignments_iff]
        rcases hright with ⟨index, hpoint⟩
        have hframed : ∃ (site : ProductionHiddenLeafIndex shape)
            (payload : List Byte),
            familyLeafPoint (productionTreeGeometry shape input.1.2.1)
              (productionTreeMaterial shape input.1.2.1 causalSecret
                (baseMessage shape) (publicPositions shape) weights context
                trace.answers trace.tail.rest
                (publicRepresentative shape statement))
              (productionProtocolCoinEquiv shape causalSecret
                (baseMessage shape) (publicPositions shape) weights context
                witness (publicRepresentative shape statement) trace.answers
                trace.tail.rest input.1.2.1) index =
              hiddenLeafFramedPoint shape
                (productionCoinsHiddenSaltsEquiv shape input.1.2.1).2
                site
                ((productionCoinsHiddenSaltsEquiv shape input.1.2.1).1
                  site)
                payload := by
          rcases index with ⟨tree, index⟩
          cases tree with
          | outer =>
              let movedCoins := productionProtocolCoinEquiv shape causalSecret
                (baseMessage shape) (publicPositions shape) weights context
                witness (publicRepresentative shape statement) trace.answers
                trace.tail.rest input.1.2.1
              refine ⟨.inl (.inl index), outerRowPayload shape
                (baseMessage shape) (publicRepresentative shape statement)
                movedCoins index, ?_⟩
              rfl
          | veilLinear =>
              let movedCoins := productionProtocolCoinEquiv shape causalSecret
                (baseMessage shape) (publicPositions shape) weights context
                witness (publicRepresentative shape statement) trace.answers
                trace.tail.rest input.1.2.1
              refine ⟨.inl (.inr index), linearRowPayload shape movedCoins
                index, ?_⟩
              rfl
          | veilHadamard =>
              let movedCoins := productionProtocolCoinEquiv shape causalSecret
                (baseMessage shape) (publicPositions shape) weights context
                witness (publicRepresentative shape statement) trace.answers
                trace.tail.rest input.1.2.1
              refine ⟨.inr index, hadamardRowPayload shape
                (productionLayerSpecAt shape causalSecret (baseMessage shape)
                  (publicPositions shape) weights context trace.answers
                  trace.tail.rest (publicRepresentative shape statement)
                  movedCoins) (publicRepresentative shape statement)
                movedCoins index, ?_⟩
              rfl
        rcases hframed with ⟨site, payload, hframed⟩
        refine ⟨site, payload, ?_⟩
        apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        refine ⟨call, ?_, ?_⟩
        · rw [hmovedHistory, htwoPhaseEq, ← hhistory]
          rw [completeAdversaryHistory_eq_twoPhase_of_trace shape
            maxStartLength fallback r1csDigest causalSecret completion weights
            context adversary statement witness
            (originalTape shape maxStartLength input) trace htrace']
          simp only [runTwoPhaseQueryValues, List.mem_append]
          exact Or.inr hcall
        · have hdummy := postMerkleTransport_dummy_of_trace shape
            maxStartLength fallback r1csDigest causalSecret completion weights
            context statement witness houter hlinear hhadamard hnodes input
            trace htrace'
          have hrest := (postMerkleTransport_rest_of_trace shape maxStartLength
            fallback r1csDigest causalSecret completion weights context
            statement witness houter hlinear hhadamard hnodes input trace
            htrace').1
          dsimp only at hdummy hrest
          change unboundBytes call.1 = hiddenLeafFramedPoint shape
            (productionCoinsHiddenSaltsEquiv shape moved.1.2.1).2 site
            (moved.1.1 site) payload
          rw [hdummy, hrest, hpoint]
          exact hframed

/-! ## Finite operational event and probability bound -/

noncomputable def badPostMerkleTapeSet
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape) :
    Finset (ProductionLedgerTape shape maxStartLength AdversaryCoins) :=
  by
    classical
    exact Finset.univ.filter fun tape =>
      BadPostMerkle shape maxStartLength fallback r1csDigest causalSecret
        completion weights context adversary statement witness tape

theorem mem_badPostMerkleTapeSet_iff
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    tape ∈ badPostMerkleTapeSet shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness ↔
      BadPostMerkle shape maxStartLength fallback r1csDigest causalSecret
        completion weights context adversary statement witness tape := by
  classical
  simp [badPostMerkleTapeSet]

noncomputable def liftedBadPostMerkleExpandedSet
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape) :
    Finset (ExpandedTape shape maxStartLength AdversaryCoins) :=
  by
    classical
    exact VeiledFlock.Probability.liftBad
      ((expandedTapeSplit (AdversaryCoins := AdversaryCoins) shape
        maxStartLength).trans (Equiv.prodComm _ _))
      (badPostMerkleTapeSet shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness)

noncomputable def transportedDummyPostMerkleExpandedSet
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    Finset (ExpandedTape shape maxStartLength AdversaryCoins) :=
  by
    classical
    exact Finset.univ.filter fun input =>
      postMerkleTransport shape maxStartLength fallback r1csDigest causalSecret
        completion weights context statement witness houter hlinear hhadamard
        hnodes input ∈
      dummyPostMerkleExpandedSet shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness

theorem transportedDummyPostMerkleExpandedSet_card_eq
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    (transportedDummyPostMerkleExpandedSet shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness houter hlinear hhadamard hnodes).card =
    (dummyPostMerkleExpandedSet shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness).card := by
  classical
  refine Finset.card_equiv
    (postMerkleTransport shape maxStartLength fallback r1csDigest causalSecret
      completion weights context statement witness houter hlinear hhadamard
      hnodes) fun input => ?_
  simp [transportedDummyPostMerkleExpandedSet]

theorem liftedBadPostMerkleExpandedSet_subset
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    ∀ input,
      input ∈ liftedBadPostMerkleExpandedSet shape maxStartLength fallback
          r1csDigest causalSecret completion weights context adversary statement
          witness →
        input ∈ dummyPostMerkleExpandedSet shape maxStartLength fallback
            r1csDigest causalSecret completion weights context adversary
            statement witness ∨
          input ∈ transportedDummyPostMerkleExpandedSet shape maxStartLength
            fallback r1csDigest causalSecret completion weights context
            adversary statement witness houter hlinear hhadamard hnodes := by
  classical
  intro input hinput
  rw [liftedBadPostMerkleExpandedSet,
    VeiledFlock.Probability.mem_liftBad_iff] at hinput
  have hbad : BadPostMerkle shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      (originalTape shape maxStartLength input) := by
    exact (mem_badPostMerkleTapeSet_iff shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness _).1 hinput
  have hcover := badPostMerkle_implies_dummy_union shape maxStartLength
    fallback r1csDigest causalSecret completion weights context adversary
    statement witness houter hlinear hhadamard hnodes input hbad
  rcases hcover with horiginal | hmoved
  · exact Or.inl horiginal
  · exact Or.inr (by
      simp only [transportedDummyPostMerkleExpandedSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hmoved)

set_option maxHeartbeats 1200000 in
theorem badPostMerkleTapeSet_probability_le
    [Nonempty AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    ((badPostMerkleTapeSet shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness).card :
        ℚ) /
      Fintype.card (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤
    2 * ((Fintype.card (ProductionHiddenLeafIndex shape) *
      (preQueries + postQueries) : ℕ) : ℚ) /
      Fintype.card VeiledFlock.NonceSerialization.NumericNonce := by
  classical
  let lifted := liftedBadPostMerkleExpandedSet shape maxStartLength fallback
    r1csDigest causalSecret completion weights context adversary statement
    witness
  let dummy := dummyPostMerkleExpandedSet shape maxStartLength fallback
    r1csDigest causalSecret completion weights context adversary statement
    witness
  let transported := transportedDummyPostMerkleExpandedSet shape
    maxStartLength fallback r1csDigest causalSecret completion weights context
    adversary statement witness houter hlinear hhadamard hnodes
  have hsubset : lifted ⊆ dummy ∪ transported := by
    intro input hinput
    apply Finset.mem_union.mpr
    exact liftedBadPostMerkleExpandedSet_subset shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness houter hlinear hhadamard hnodes input hinput
  have htransported : transported.card = dummy.card :=
    transportedDummyPostMerkleExpandedSet_card_eq shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness houter hlinear hhadamard hnodes
  have hcount : lifted.card ≤ 2 * dummy.card := by
    calc
      lifted.card ≤ (dummy ∪ transported).card := Finset.card_le_card hsubset
      _ ≤ dummy.card + transported.card := Finset.card_union_le _ _
      _ = 2 * dummy.card := by rw [htransported]; omega
  have hliftedProbability :
      (lifted.card : ℚ) /
          Fintype.card (ExpandedTape shape maxStartLength AdversaryCoins) =
        ((badPostMerkleTapeSet shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement
          witness).card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) := by
    dsimp only [lifted]
    unfold liftedBadPostMerkleExpandedSet
    exact VeiledFlock.Probability.liftBad_probability_eq
      ((expandedTapeSplit (AdversaryCoins := AdversaryCoins) shape
        maxStartLength).trans (Equiv.prodComm _ _))
      (badPostMerkleTapeSet shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness)
  have hdummy := dummyPostMerkleExpandedSet_probability_le shape
    maxStartLength fallback r1csDigest causalSecret completion weights context
    adversary statement witness
  rw [← hliftedProbability]
  calc
    (lifted.card : ℚ) /
        Fintype.card (ExpandedTape shape maxStartLength AdversaryCoins) ≤
      ((2 * dummy.card : ℕ) : ℚ) /
        Fintype.card (ExpandedTape shape maxStartLength AdversaryCoins) := by
          gcongr
    _ = 2 * ((dummy.card : ℚ) /
        Fintype.card (ExpandedTape shape maxStartLength AdversaryCoins)) := by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
          ring
    _ ≤ 2 * (((Fintype.card (ProductionHiddenLeafIndex shape) *
        (preQueries + postQueries) : ℕ) : ℚ) /
          Fintype.card VeiledFlock.NonceSerialization.NumericNonce) := by
      gcongr
    _ = 2 * ((Fintype.card (ProductionHiddenLeafIndex shape) *
        (preQueries + postQueries) : ℕ) : ℚ) /
          Fintype.card VeiledFlock.NonceSerialization.NumericNonce := by ring

end VeiledFlock.ProductionPostMerkleProbability

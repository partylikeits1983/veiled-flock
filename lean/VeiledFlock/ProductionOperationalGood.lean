import VeiledFlock.MerkleHiding
import VeiledFlock.ProductionOperationalTape
import VeiledFlock.UniversalFreshness

/-!
# Operational `GlobalGood` for the concrete production experiments

Every predicate in this file is evaluated on the exact tape decoded by
`ProductionOperationalTape.productionDecode`.  There are no synthetic event
coordinates and no real/simulator equality assumptions.  The named bad
events below are precisely the failures of the six fields of
`ProductionNizkCoupling.ProductionGood`.
-/

namespace VeiledFlock.ProductionOperationalGood

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.MerkleHiding
open VeiledFlock.NonceSerialization
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionMaskLayout
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionMerkleTree
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.TranscriptSchedule

section

variable {AdversaryCoins FinalState : Type} [Fintype AdversaryCoins]
variable {preQueries postQueries : ℕ}
variable (shape : BatchShape) (maxStartLength : ℕ)
variable (fallback : OracleBlock) (r1csDigest : List Byte)
variable (causalSecret : ProductionCausalSecret
  (W := Witness shape) shape)
variable (completion : Completion OracleBlock (programmedPoints shape))
variable (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
  VeiledFlock.ProductionOuterPcs.Prefix
    (K := Unit) (rounds := expectedMasks shape) →
  ProductionRest shape → Unit → PublicCoord shape → GhashField)
variable (context : History (Outcome := OracleBlock) (programmedPoints shape) →
  VeiledFlock.ProductionOuterPcs.Prefix
    (K := Unit) (rounds := expectedMasks shape) →
  VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
    (I := BaseScalarIndex shape) (P := Unit)
    (Opened := OpenedRows shape) → ProductionRest shape →
  LayerContext shape (Witness shape)
    (ProductionConcreteAlgebraic.Public shape)
    (ProductionConcreteOuter.publicStatement shape
      (publicPositions shape) (baseMessage shape)))
variable (adversary : ProductionAdversary
  (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
  shape (ProductionRest shape)
    (ProductionMaxPointLength shape maxStartLength)
    preQueries postQueries)
variable (statement : ProductionStatement shape) (witness : Witness shape)
variable (houter : 108 + 16 * (2 * outerLaneCount) ≤
  ProductionMaxPointLength shape maxStartLength)
variable (hlinear : 108 + 32 ≤
  ProductionMaxPointLength shape maxStartLength)
variable (hhadamard : 108 + 64 ≤
  ProductionMaxPointLength shape maxStartLength)

abbrev Tape :=
  ProductionLedgerTape shape maxStartLength AdversaryCoins

def couplingInput (tape : Tape shape maxStartLength (AdversaryCoins :=
    AdversaryCoins)) : ProductionCouplingInput shape maxStartLength :=
  (tape.1, tape.2.1)

def adversaryRandomness (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : AdversaryCoins :=
  tape.2.2

noncomputable def realTrace (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) :
    Option (ProductionExecutionTrace shape) :=
  productionRealTrace shape fallback r1csDigest causalSecret completion
    (baseMessage shape) statement witness tape.1 tape.2.1

/-- Rejection or grinding caused the production execution to abort. -/
noncomputable def BadTraceFailure (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  realTrace shape maxStartLength fallback r1csDigest causalSecret completion
    statement witness tape = none

noncomputable def StartBound (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape) : Prop :=
  let input := couplingInput shape maxStartLength tape
  let moved := productionMerkleCoinOracleEquivAt shape input.1
    causalSecret (baseMessage shape) (publicPositions shape) weights context
    witness (publicRepresentative shape statement) trace.answers
    trace.tail.rest houter hlinear hhadamard input
  (VeiledFlock.ProductionZerocheckSchedule.start shape
    trace.equalityPoint.2.2
    (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
      causalSecret trace.answers
      (publicRepresentative shape statement, moved.1.outer.1,
        moved.1.outer.2.1) moved.1.outer.2.2)).length ≤ maxStartLength

/-- Public byte ceiling for the zerocheck schedule's starting transcript.
It includes the exact fixed-width prelude, the six-field equality squeeze,
every permitted outer rejection attempt, and both initial masked messages. -/
def productionStartLengthBound (shape : BatchShape)
    (statement : ProductionStatement shape) (r1csDigest : List Byte) : ℕ :=
  (productionStatementDigest statement).length + r1csDigest.length + 432 +
    (10 + 16 * 6) +
    veilSamplingTrials * (10 + 16 * (m shape - kSkip - 7)) +
    2 * (10 + 16 * ell) + 2

set_option maxHeartbeats 800000 in
/-- A successful concrete trace always fits the public start budget.  Thus
`BadStartBound` carries no probability once the experiment instantiates a
large enough `maxStartLength`. -/
theorem startBound_of_trace_success
    (hmax : productionStartLengthBound shape statement r1csDigest ≤
      maxStartLength)
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape)
    (htrace : realTrace shape maxStartLength fallback r1csDigest causalSecret
      completion statement witness tape = some trace) :
    StartBound shape maxStartLength causalSecret weights context statement
      witness houter hlinear hhadamard tape trace := by
  let facts : ProductionTraceFacts shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness tape.1 tape.2.1 trace :=
    productionRealTrace_facts shape fallback r1csDigest causalSecret completion
      (baseMessage shape) statement witness tape.1 tape.2.1 trace htrace
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest tape.1.proofNonce tape.1.treeNonces.outer
    tape.1.treeNonces.veilLinear tape.1.treeNonces.veilHadamard
    trace.outerCommitment trace.linearCommitment
  have hequality := sampleEqualityPointPrefix_some_length_le
    (answerBounded fallback tape.2.1) (m shape - kSkip - 7)
    veilSamplingTrials prelude trace.equalityPoint facts.equalityPoint
  have hprefix : prelude.length =
      (productionStatementDigest statement).length + r1csDigest.length +
        432 := by
    simp only [prelude, preEqualityTranscript_length]
  rw [hprefix] at hequality
  unfold productionStartLengthBound at hmax
  simp only [StartBound,
    VeiledFlock.ProductionZerocheckSchedule.start_length]
  omega

noncomputable def BadStartBound (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  ∃ trace,
    realTrace shape maxStartLength fallback r1csDigest causalSecret completion
      statement witness tape = some trace ∧
    ¬ StartBound shape maxStartLength causalSecret weights context statement
      witness houter hlinear hhadamard tape trace

theorem not_badStartBound
    (hmax : productionStartLengthBound shape statement r1csDigest ≤
      maxStartLength)
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) :
    ¬ BadStartBound shape maxStartLength fallback r1csDigest causalSecret
      completion weights context statement witness houter hlinear hhadamard
      tape := by
  rintro ⟨trace, htrace, hnot⟩
  exact hnot (startBound_of_trace_success shape maxStartLength fallback
    r1csDigest causalSecret completion weights context statement witness
    houter hlinear hhadamard hmax tape trace htrace)

noncomputable def PreMerkleFresh (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape) : Prop :=
  let input := couplingInput shape maxStartLength tape
  AvoidsProductionMerkleTransport shape input.1 causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    (publicRepresentative shape statement) trace.answers trace.tail.rest
    input.1
    (productionPreHistory adversary statement
      (adversaryRandomness shape maxStartLength tape) input.2)

noncomputable def BadPreMerkle (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  ∃ trace,
    realTrace shape maxStartLength fallback r1csDigest causalSecret completion
      statement witness tape = some trace ∧
    ¬ PreMerkleFresh shape maxStartLength causalSecret weights context
      adversary statement witness tape trace

/-! ## Concrete pre-proof hidden-Merkle probability -/

/-- The exact production leaf framing after all non-salt coins have been
fixed.  The final argument is an arbitrary row payload, so the associated
bad set safely covers witness- and transcript-dependent payloads. -/
noncomputable def hiddenLeafFramedPoint
    (rest : ProductionCoinsWithoutHiddenSalts shape)
    (site : ProductionHiddenLeafIndex shape) (salt : NumericNonce)
    (payload : List Byte) : List Byte :=
  match site with
  | .inl (.inl outer) =>
      productionLeafPoint ⟨0, by decide⟩ ⟨0, by decide⟩
        rest.2.2.2.1.outer
        (BitVec.ofNat 64 (16 * (2 * outerLaneCount))) (m shape - 11) outer
        salt payload
  | .inl (.inr linear) =>
      productionLeafPoint ⟨6, by decide⟩ ⟨0, by decide⟩
        rest.2.2.2.1.veilLinear (BitVec.ofNat 64 32) 13 linear salt payload
  | .inr hadamard =>
      productionLeafPoint ⟨7, by decide⟩ ⟨0, by decide⟩
        rest.2.2.2.1.veilHadamard (BitVec.ofNat 64 64) 11 hadamard salt
        payload

/-- At a fixed tree and row, equality of two production leaf byte strings
recovers the 256-bit salt even when their row payloads are unrelated. -/
theorem productionLeafPoint_salt_cross
    (channel : VeiledFlock.ProductionFraming.RoChannel)
    (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : VeiledFlock.ProductionFraming.Word64) (depth : ℕ)
    (index : Fin (2 ^ depth)) (leftSalt rightSalt : NumericNonce)
    (leftPayload rightPayload : List Byte)
    (heq : productionLeafPoint channel treeDepth treeNonce leafLength depth
        index leftSalt leftPayload =
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        rightSalt rightPayload) :
    leftSalt = rightSalt := by
  have hquery :=
    VeiledFlock.ProductionFraming.encodeMerkleQuery_injective heq
  have hpayload := congrArg
    VeiledFlock.ProductionFraming.MerkleQuery.payload hquery
  change nonceBytes (numericNonceBytes leftSalt) ++ leftPayload =
    nonceBytes (numericNonceBytes rightSalt) ++ rightPayload at hpayload
  exact VeiledFlock.UniversalFreshness.fixedOffsetFrame_cross_injective
    [] (fun value => nonceBytes (numericNonceBytes value))
    (fun payload _ => payload) (fun payload _ => payload) 32
    (fun value => length_nonceBytes (numericNonceBytes value))
    (nonceBytes_injective.comp numericNonceBytes.injective)
    (by simpa only [fixedOffsetFrame, List.nil_append] using hpayload)

theorem hiddenLeafFramedPoint_cross
    (rest : ProductionCoinsWithoutHiddenSalts shape)
    (site : ProductionHiddenLeafIndex shape)
    (leftSalt rightSalt : NumericNonce)
    (leftPayload rightPayload : List Byte)
    (heq : hiddenLeafFramedPoint shape rest site leftSalt leftPayload =
      hiddenLeafFramedPoint shape rest site rightSalt rightPayload) :
    leftSalt = rightSalt := by
  rcases site with (outerOrLinear | hadamard)
  · rcases outerOrLinear with (outer | linear)
    · exact productionLeafPoint_salt_cross
        ⟨0, by decide⟩ ⟨0, by decide⟩ rest.2.2.2.1.outer
        (BitVec.ofNat 64 (16 * (2 * outerLaneCount))) (m shape - 11) outer
        leftSalt rightSalt leftPayload rightPayload (by
          simpa only [hiddenLeafFramedPoint] using heq)
    · exact productionLeafPoint_salt_cross
        ⟨6, by decide⟩ ⟨0, by decide⟩ rest.2.2.2.1.veilLinear
        (BitVec.ofNat 64 32) 13 linear leftSalt rightSalt leftPayload
        rightPayload (by simpa only [hiddenLeafFramedPoint] using heq)
  · exact productionLeafPoint_salt_cross
      ⟨7, by decide⟩ ⟨0, by decide⟩ rest.2.2.2.1.veilHadamard
      (BitVec.ofNat 64 64) 11 hadamard leftSalt rightSalt leftPayload
      rightPayload (by simpa only [hiddenLeafFramedPoint] using heq)

/-- Canonically enumerated form of `hiddenLeafFramedPoint`, matching the
`Fin hidden` indexing used by the generic finite counting theorem. -/
noncomputable def enumeratedHiddenLeafFramedPoint
    (rest : ProductionCoinsWithoutHiddenSalts shape)
    (site : Fin (Fintype.card (ProductionHiddenLeafIndex shape)))
    (salt : NumericNonce) (payload : List Byte) : List Byte :=
  hiddenLeafFramedPoint shape rest
    ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site)
    salt payload

/-- Byte strings reached by the actual adaptive adversary before receiving
the proof, after fixing all operational coordinates other than hidden salts. -/
noncomputable def preMerklePointSet
    (rest : ProductionCoinsWithoutHiddenSalts shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    Finset (List Byte) :=
  ((productionPreHistory adversary statement rest.2.2 rest.2.1).map
    (fun call => unboundBytes call.1)).toFinset

theorem preMerklePointSet_card_le
    (rest : ProductionCoinsWithoutHiddenSalts shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    (preMerklePointSet shape maxStartLength adversary statement rest).card ≤
      preQueries := by
  classical
  let history := productionPreHistory adversary statement rest.2.2 rest.2.1
  calc
    (preMerklePointSet shape maxStartLength adversary statement rest).card ≤
        (history.map (fun call => unboundBytes call.1)).length := by
      exact List.toFinset_card_le _
    _ = history.length := by simp
    _ ≤ preQueries := by
      unfold history productionPreHistory
      have hlength := runQueryValues_length_le
        (fun round current => adversary.preQuery round statement rest.2.2
          current)
        rest.2.1 (List.ofFn id) []
      simpa using hlength

/-- Hidden-salt vectors exposing any real or counterfactual production leaf
payload to the actual pre-proof query set. -/
noncomputable def badPreMerkleSaltAssignments
    (rest : ProductionCoinsWithoutHiddenSalts shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    Finset (ProductionHiddenSalts shape) :=
  (universalHiddenInputBadAssignments
    (enumeratedHiddenLeafFramedPoint shape rest.1)
    (preMerklePointSet shape maxStartLength adversary statement rest)).map
      (productionHiddenSaltsFinEquiv shape).symm.toEmbedding

theorem mem_badPreMerkleSaltAssignments_iff
    (rest : ProductionCoinsWithoutHiddenSalts shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins)
    (salts : ProductionHiddenSalts shape) :
    salts ∈ badPreMerkleSaltAssignments shape maxStartLength adversary
        statement rest ↔
      ∃ (site : ProductionHiddenLeafIndex shape) (payload : List Byte),
        hiddenLeafFramedPoint shape rest.1 site (salts site) payload ∈
          preMerklePointSet shape maxStartLength adversary statement rest := by
  classical
  rw [badPreMerkleSaltAssignments, Finset.mem_map]
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
    refine ⟨enumerated, ?_, ?_⟩
    · rw [mem_universalHiddenInputBadAssignments_iff]
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
    · exact (productionHiddenSaltsFinEquiv shape).symm_apply_apply salts

/-- Uniform hidden salts expose a pre-proof leaf input with probability at
most `hiddenLeaves * preQueries / 2^256`, on the actual operational fiber. -/
theorem badPreMerkleSaltAssignments_probability_le
    (rest : ProductionCoinsWithoutHiddenSalts shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    ((badPreMerkleSaltAssignments shape maxStartLength adversary statement
        rest).card : ℚ) /
        Fintype.card (ProductionHiddenSalts shape) ≤
      (Fintype.card (ProductionHiddenLeafIndex shape) * preQueries : ℕ) /
        Fintype.card NumericNonce := by
  classical
  let point := enumeratedHiddenLeafFramedPoint shape rest.1
  have hcross : ∀ site leftSalt leftPayload rightSalt rightPayload,
      point site leftSalt leftPayload = point site rightSalt rightPayload →
        leftSalt = rightSalt := by
    intro site leftSalt leftPayload rightSalt rightPayload heq
    exact hiddenLeafFramedPoint_cross shape rest.1
      ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site)
      leftSalt rightSalt leftPayload rightPayload heq
  have hgeneric := universalHiddenInputProbability_le
    point (preMerklePointSet shape maxStartLength adversary statement rest)
    hcross
  have hcard :
      (badPreMerkleSaltAssignments shape maxStartLength adversary statement
        rest).card =
      (universalHiddenInputBadAssignments point
        (preMerklePointSet shape maxStartLength adversary statement rest)).card :=
    Finset.card_map _
  rw [hcard]
  rw [Fintype.card_congr (productionHiddenSaltsFinEquiv shape)]
  exact hgeneric.trans (by
    gcongr
    exact_mod_cast Nat.mul_le_mul_left
      (Fintype.card (ProductionHiddenLeafIndex shape))
      (preMerklePointSet_card_le shape maxStartLength adversary statement
        rest))

/-- Every honest-side leaf point exchanged by the concrete three-tree
transport is one member of the payload-universal framed family above. -/
theorem productionLeftFamilyLeafPoint_framed
    (salts : ProductionHiddenSalts shape)
    (restCoins : ProductionCoinsWithoutHiddenSalts shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (protocolRest : ProductionRest shape)
    (index : FamilyIndex VeiledFlock.ProductionThreeTree.ProductionTree
      (productionTreeGeometry shape
        (productionCoinsWithHiddenSalts shape salts restCoins))) :
    ∃ (site : ProductionHiddenLeafIndex shape) (payload : List Byte),
      familyLeafPoint
          (productionTreeGeometry shape
            (productionCoinsWithHiddenSalts shape salts restCoins))
          (productionTreeMaterial shape
            (productionCoinsWithHiddenSalts shape salts restCoins)
            causalSecret (baseMessage shape) (publicPositions shape) weights
            context answers protocolRest witness)
          (productionCoinsWithHiddenSalts shape salts restCoins) index =
        hiddenLeafFramedPoint shape restCoins site (salts site) payload := by
  rcases index with ⟨tree, index⟩
  cases tree with
  | outer =>
      refine ⟨.inl (.inl index), outerRowPayload shape (baseMessage shape)
        witness (productionCoinsWithHiddenSalts shape salts restCoins) index,
        ?_⟩
      rfl
  | veilLinear =>
      refine ⟨.inl (.inr index), linearRowPayload shape
        (productionCoinsWithHiddenSalts shape salts restCoins) index, ?_⟩
      rfl
  | veilHadamard =>
      refine ⟨.inr index, hadamardRowPayload shape
        (productionLayerSpecAt shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context answers protocolRest witness
          (productionCoinsWithHiddenSalts shape salts restCoins))
        witness (productionCoinsWithHiddenSalts shape salts restCoins) index,
        ?_⟩
      rfl

/-- The public-representative side of the same transport uses the identical
tree nonces and hidden salts; only its row payload changes. -/
theorem productionRightFamilyLeafPoint_framed
    (salts : ProductionHiddenSalts shape)
    (restCoins : ProductionCoinsWithoutHiddenSalts shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (protocolRest : ProductionRest shape)
    (index : FamilyIndex VeiledFlock.ProductionThreeTree.ProductionTree
      (productionTreeGeometry shape
        (productionCoinsWithHiddenSalts shape salts restCoins))) :
    let coins := productionCoinsWithHiddenSalts shape salts restCoins
    let moved := productionProtocolCoinEquiv shape causalSecret
      (baseMessage shape) (publicPositions shape) weights context witness
      (publicRepresentative shape statement) answers protocolRest coins
    ∃ (site : ProductionHiddenLeafIndex shape) (payload : List Byte),
      familyLeafPoint (productionTreeGeometry shape coins)
          (productionTreeMaterial shape coins causalSecret (baseMessage shape)
            (publicPositions shape) weights context answers protocolRest
            (publicRepresentative shape statement))
          moved index =
        hiddenLeafFramedPoint shape restCoins site (salts site) payload := by
  dsimp only
  rcases index with ⟨tree, index⟩
  cases tree with
  | outer =>
      refine ⟨.inl (.inl index), outerRowPayload shape (baseMessage shape)
        (publicRepresentative shape statement)
        (productionProtocolCoinEquiv shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context witness
          (publicRepresentative shape statement) answers protocolRest
          (productionCoinsWithHiddenSalts shape salts restCoins)) index, ?_⟩
      rfl
  | veilLinear =>
      refine ⟨.inl (.inr index), linearRowPayload shape
        (productionProtocolCoinEquiv shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context witness
          (publicRepresentative shape statement) answers protocolRest
          (productionCoinsWithHiddenSalts shape salts restCoins)) index, ?_⟩
      rfl
  | veilHadamard =>
      let moved := productionProtocolCoinEquiv shape causalSecret
        (baseMessage shape) (publicPositions shape) weights context witness
        (publicRepresentative shape statement) answers protocolRest
        (productionCoinsWithHiddenSalts shape salts restCoins)
      refine ⟨.inr index, hadamardRowPayload shape
        (productionLayerSpecAt shape causalSecret (baseMessage shape)
          (publicPositions shape) weights context answers protocolRest
          (publicRepresentative shape statement) moved)
        (publicRepresentative shape statement) moved index, ?_⟩
      rfl

/-- The operational-tape event obtained by lifting the hidden-salt bad set
along the exact salt/rest product decomposition. -/
noncomputable def badPreMerkleTapeSet :
    Finset (Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) :=
  VeiledFlock.Probability.liftFiberBad
    (productionHiddenSaltsSplit shape maxStartLength AdversaryCoins)
    (badPreMerkleSaltAssignments shape maxStartLength adversary statement)

set_option maxHeartbeats 1600000 in
/-- The semantic pre-proof Merkle failure is contained in the finite event
charged to the actual hidden salts of the operational tape. -/
theorem badPreMerkle_implies_mem_tapeSet
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) :
    BadPreMerkle shape maxStartLength fallback r1csDigest causalSecret
        completion weights context adversary statement witness tape →
      tape ∈ badPreMerkleTapeSet shape maxStartLength adversary statement := by
  classical
  intro hbad
  rw [badPreMerkleTapeSet,
    VeiledFlock.Probability.mem_liftFiberBad_iff]
  let split := productionHiddenSaltsSplit shape maxStartLength AdversaryCoins
    tape
  let salts := split.1
  let rest := split.2
  change salts ∈ badPreMerkleSaltAssignments shape maxStartLength adversary
    statement rest
  rw [mem_badPreMerkleSaltAssignments_iff]
  by_contra hsafe
  rcases hbad with ⟨trace, htrace, hnotFresh⟩
  apply hnotFresh
  simp only [PreMerkleFresh, couplingInput, adversaryRandomness]
  have hcoins : productionCoinsWithHiddenSalts shape salts rest.1 = tape.1 := by
    simpa only [salts, rest, split] using
      (productionCoinsWithHiddenSalts_split shape maxStartLength
        AdversaryCoins tape)
  rw [← hcoins]
  intro call hcall
  have hcallSet : unboundBytes call.1 ∈
      preMerklePointSet shape maxStartLength adversary statement rest := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨call, ?_, rfl⟩
    simpa only [rest, split, productionHiddenSaltsSplit_snd_table,
      productionHiddenSaltsSplit_snd_adversaryCoins] using hcall
  constructor
  · intro index heq
    rcases productionLeftFamilyLeafPoint_framed shape causalSecret weights
      context witness salts rest.1 trace.answers trace.tail.rest index with
      ⟨site, payload, hframed⟩
    apply hsafe
    refine ⟨site, payload, ?_⟩
    rw [← hframed, ← heq]
    exact hcallSet
  · intro index heq
    rcases productionRightFamilyLeafPoint_framed shape causalSecret weights
      context statement witness salts rest.1 trace.answers trace.tail.rest
      index with ⟨site, payload, hframed⟩
    apply hsafe
    refine ⟨site, payload, ?_⟩
    rw [← hframed, ← heq]
    exact hcallSet

/-- Concrete probability bound for the actual pre-proof Merkle freshness
failure. -/
theorem badPreMerkleTapeSet_probability_le [Nonempty AdversaryCoins] :
    ((badPreMerkleTapeSet shape maxStartLength adversary statement).card : ℚ) /
        Fintype.card
          (Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) ≤
      (Fintype.card (ProductionHiddenLeafIndex shape) * preQueries : ℕ) /
        Fintype.card NumericNonce := by
  classical
  exact VeiledFlock.Probability.liftFiberBad_probability_le
    (productionHiddenSaltsSplit shape maxStartLength AdversaryCoins)
    (badPreMerkleSaltAssignments shape maxStartLength adversary statement)
    ((Fintype.card (ProductionHiddenLeafIndex shape) * preQueries : ℕ) /
      Fintype.card NumericNonce)
    (fun rest => badPreMerkleSaltAssignments_probability_le shape
      maxStartLength adversary statement rest)

noncomputable def PreProgrammingFresh (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape)
    (hstart : StartBound shape maxStartLength causalSecret weights context
      statement witness houter hlinear hhadamard tape trace) : Prop :=
  let input := couplingInput shape maxStartLength tape
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    (publicRepresentative shape statement) trace.answers trace.tail.rest
    houter hlinear hhadamard input
  let points := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2
    (publicRepresentative shape statement) moved.1 trace.answers hstart
  AvoidsProductionProgramPoints points
    (productionPreHistory adversary statement
      (adversaryRandomness shape maxStartLength tape) input.2)

/-- A conservative family containing every production Fiat--Shamir
programming point.  The context is the complete suffix after the fixed-offset
proof-nonce frame; quantifying over all suffixes safely covers every adaptive
answer history. -/
def proofNonceFramedProgramPoint
    (shape : BatchShape) (statement : ProductionStatement shape)
    (r1csDigest : List Byte) (_site : Fin (programmedPoints shape))
    (proofNonce : Nonce256) (suffix : List Byte) : List Byte :=
  fixedOffsetFrame
    (proofNonceHead (productionStatementDigest statement) r1csDigest)
    transcriptNonceFrame (fun _ => suffix) proofNonce

/-- Equality of two members of the conservative family at a fixed site
recovers the fresh 256-bit proof nonce, regardless of either suffix. -/
theorem proofNonceFramedProgramPoint_cross
    (site : Fin (programmedPoints shape))
    (leftNonce : Nonce256) (leftSuffix : List Byte)
    (rightNonce : Nonce256) (rightSuffix : List Byte)
    (heq : proofNonceFramedProgramPoint shape statement r1csDigest site
        leftNonce leftSuffix =
      proofNonceFramedProgramPoint shape statement r1csDigest site
        rightNonce rightSuffix) :
    leftNonce = rightNonce := by
  apply VeiledFlock.UniversalFreshness.fixedOffsetFrame_cross_injective
    (proofNonceHead (productionStatementDigest statement) r1csDigest)
    transcriptNonceFrame (fun suffix _ => suffix) (fun suffix _ => suffix) 41
    length_transcriptNonceFrame transcriptNonceFrame_injective
  simpa only [proofNonceFramedProgramPoint] using heq

/-- The finite set of byte strings actually queried by the adversary before
the proof is produced, after fixing every tape coordinate other than the
proof nonce. -/
noncomputable def prequeryPointSet
    (rest : ProductionCoinsWithoutProofNonce shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    Finset (List Byte) :=
  ((productionPreHistory adversary statement rest.2.2 rest.2.1).map
    (fun call => unboundBytes call.1)).toFinset

/-- Proof nonces for which some counterfactual production programming point
was already reached in the actual adaptive pre-proof history. -/
noncomputable def badPrequeryNonces
    (rest : ProductionCoinsWithoutProofNonce shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    Finset Nonce256 :=
  VeiledFlock.UniversalFreshness.badNonces
    (proofNonceFramedProgramPoint shape statement r1csDigest)
    (prequeryPointSet shape maxStartLength adversary statement rest)

theorem prequeryPointSet_card_le
    (rest : ProductionCoinsWithoutProofNonce shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    (prequeryPointSet shape maxStartLength adversary statement rest).card ≤
      preQueries := by
  classical
  let history := productionPreHistory adversary statement rest.2.2 rest.2.1
  calc
    (prequeryPointSet shape maxStartLength adversary statement rest).card ≤
        (history.map (fun call => unboundBytes call.1)).length := by
      exact List.toFinset_card_le _
    _ = history.length := by simp
    _ ≤ preQueries := by
      unfold history productionPreHistory
      have hlength := runQueryValues_length_le
        (fun round history =>
          adversary.preQuery round statement rest.2.2 history)
        rest.2.1 (List.ofFn id) []
      simpa using hlength

/-- The actual adaptive prequery fiber costs at most one adversarial-query
factor for each production programming site. -/
theorem badPrequeryNonces_card_le
    (rest : ProductionCoinsWithoutProofNonce shape ×
      ProductionSharedOracleTable shape maxStartLength × AdversaryCoins) :
    (badPrequeryNonces shape maxStartLength r1csDigest adversary statement
      rest).card ≤ programmedPoints shape * preQueries := by
  classical
  refine (VeiledFlock.UniversalFreshness.card_badNonces_le
    (proofNonceFramedProgramPoint shape statement r1csDigest)
    (prequeryPointSet shape maxStartLength adversary statement rest)
    ?_).trans ?_
  · intro site leftNonce leftSuffix rightNonce rightSuffix heq
    exact proofNonceFramedProgramPoint_cross shape r1csDigest statement site
      leftNonce leftSuffix rightNonce rightSuffix heq
  · simpa only [Fintype.card_fin] using Nat.mul_le_mul_left
      (programmedPoints shape)
      (prequeryPointSet_card_le shape maxStartLength adversary statement rest)

set_option maxHeartbeats 800000 in
/-- Every point that the concrete simulator programs after a successful real
trace is in the conservative proof-nonce-framed family used above. -/
theorem productionSimulatorProgramPoint_framed
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape)
    (htrace : realTrace shape maxStartLength fallback r1csDigest causalSecret
      completion statement witness tape = some trace)
    (hstart : StartBound shape maxStartLength causalSecret weights context
      statement witness houter hlinear hhadamard tape trace)
    (site : Fin (programmedPoints shape)) :
    let input := couplingInput shape maxStartLength tape
    let moved := productionMerkleCoinOracleEquivAt shape input.1
      causalSecret (baseMessage shape) (publicPositions shape) weights context
      witness (publicRepresentative shape statement) trace.answers
      trace.tail.rest houter hlinear hhadamard input
    ∃ suffix,
      unboundBytes
          (productionSimulatorProgramPoints shape maxStartLength causalSecret
            trace.equalityPoint.2.2 (publicRepresentative shape statement)
            moved.1 trace.answers hstart site) =
        proofNonceFramedProgramPoint shape statement r1csDigest site
          tape.1.proofNonce suffix := by
  classical
  let input := couplingInput shape maxStartLength tape
  let moved := productionMerkleCoinOracleEquivAt shape input.1
    causalSecret (baseMessage shape) (publicPositions shape) weights context
    witness (publicRepresentative shape statement) trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let maskTranscript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      trace.answers
      (publicRepresentative shape statement, moved.1.outer.1,
        moved.1.outer.2.1) moved.1.outer.2.2
  let start := VeiledFlock.ProductionZerocheckSchedule.start shape
    trace.equalityPoint.2.2 maskTranscript
  let step := scalarRoundStep consumeScalar
    (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
    (VeiledFlock.ProductionZerocheckSchedule.first shape maskTranscript)
    (VeiledFlock.ProductionZerocheckSchedule.second shape maskTranscript)
  let prelude := preEqualityTranscript
    (productionStatementDigest statement) r1csDigest tape.1.proofNonce
    tape.1.treeNonces.outer tape.1.treeNonces.veilLinear
    tape.1.treeNonces.veilHadamard trace.outerCommitment
    trace.linearCommitment
  let facts : ProductionTraceFacts shape fallback r1csDigest causalSecret
      completion (baseMessage shape) statement witness tape.1 tape.2.1 trace :=
    productionRealTrace_facts shape fallback r1csDigest causalSecret completion
      (baseMessage shape) statement witness tape.1 tape.2.1 trace htrace
  change ∃ suffix,
    unboundBytes
        (productionSimulatorProgramPoints shape maxStartLength causalSecret
          trace.equalityPoint.2.2 (publicRepresentative shape statement)
          moved.1 trace.answers hstart site) =
      proofNonceFramedProgramPoint shape statement r1csDigest site
        tape.1.proofNonce suffix
  have hprelude : prelude <+: trace.equalityPoint.2.2 := by
    exact sampleEqualityPointPrefix_some_prefix
      (answerBounded fallback tape.2.1) (m shape - kSkip - 7)
      veilSamplingTrials prelude trace.equalityPoint facts.equalityPoint
  have habsorbed : trace.equalityPoint.2.2 <+: start := by
    unfold start VeiledFlock.ProductionZerocheckSchedule.start
    simpa only [List.append_assoc] using
      (List.prefix_append trace.equalityPoint.2.2
        (observeScalarSlice
            (VeiledFlock.ProductionZerocheckSchedule.round1Ab shape
              maskTranscript) ++
          observeScalarSlice
            (VeiledFlock.ProductionZerocheckSchedule.round1C shape
              maskTranscript) ++ squeezeScalarTag))
  have hstartPoint : start <+:
      tracePoint (appendSchedule start step) trace.answers site := by
    obtain ⟨suffix, hsuffix⟩ :=
      VeiledFlock.TranscriptSchedule.tracePoint_appendSchedule_hasPrefix
        start step trace.answers site
    exact ⟨suffix, hsuffix.symm⟩
  have hfull : prelude <+:
      tracePoint (appendSchedule start step) trace.answers site :=
    hprelude.trans (habsorbed.trans hstartPoint)
  dsimp only [prelude] at hfull
  rw [preEqualityTranscript_proofNonce_frame
    (productionStatementDigest statement) r1csDigest tape.1.proofNonce
    tape.1.treeNonces.outer tape.1.treeNonces.veilLinear
    tape.1.treeNonces.veilHadamard trace.outerCommitment
    trace.linearCommitment] at hfull
  rcases hfull with ⟨suffix, hsuffix⟩
  refine ⟨proofNoncePreludeSuffix tape.1.treeNonces.outer
    tape.1.treeNonces.veilLinear tape.1.treeNonces.veilHadamard
    trace.outerCommitment trace.linearCommitment ++ suffix, ?_⟩
  change tracePoint (appendSchedule start step) trace.answers site =
    proofNonceFramedProgramPoint shape statement r1csDigest site
      tape.1.proofNonce
        (proofNoncePreludeSuffix tape.1.treeNonces.outer
          tape.1.treeNonces.veilLinear tape.1.treeNonces.veilHadamard
          trace.outerCommitment trace.linearCommitment ++ suffix)
  simpa only [proofNonceFramedProgramPoint, fixedOffsetFrame,
    List.append_assoc] using hsuffix.symm

noncomputable def BadPrequery (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  ∃ (trace : ProductionExecutionTrace shape)
      (hstart : StartBound shape maxStartLength causalSecret weights context
        statement witness houter hlinear hhadamard tape trace),
    realTrace shape maxStartLength fallback r1csDigest causalSecret completion
      statement witness tape = some trace ∧
    ¬ PreProgrammingFresh shape maxStartLength causalSecret weights context
      adversary statement witness houter hlinear hhadamard tape trace hstart

/-- The operational-tape event charged for adaptive prequeries.  It is lifted
along the exact proof-nonce split of the actual production randomness. -/
noncomputable def badPrequeryTapeSet :
    Finset (Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) :=
  VeiledFlock.Probability.liftFiberBad
    (productionProofNonceSplit shape maxStartLength AdversaryCoins)
    (badPrequeryNonces shape maxStartLength r1csDigest adversary statement)

set_option maxHeartbeats 1000000 in
/-- The semantic `BadPrequery` event is contained in the concrete finite
event charged by the proof-nonce count. -/
theorem badPrequery_implies_mem_tapeSet
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) :
    BadPrequery shape maxStartLength fallback r1csDigest causalSecret
        completion weights context adversary statement witness houter hlinear
        hhadamard tape →
      tape ∈ badPrequeryTapeSet shape maxStartLength r1csDigest adversary
        statement := by
  classical
  intro hbad
  rw [badPrequeryTapeSet,
    VeiledFlock.Probability.mem_liftFiberBad_iff]
  rw [productionProofNonceSplit_fst]
  let rest :=
    (productionProofNonceSplit shape maxStartLength AdversaryCoins tape).2
  by_contra hnonce
  rcases hbad with ⟨trace, hstart, htrace, hnotFresh⟩
  apply hnotFresh
  intro call hcall site heq
  obtain ⟨suffix, hframed⟩ :=
    productionSimulatorProgramPoint_framed shape maxStartLength fallback
      r1csDigest causalSecret completion weights context statement witness
      houter hlinear hhadamard tape trace htrace hstart site
  have hcallSet : unboundBytes call.1 ∈
      prequeryPointSet shape maxStartLength adversary statement rest := by
    change call ∈ productionPreHistory adversary statement tape.2.2
      tape.2.1 at hcall
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨call, ?_, rfl⟩
    simpa only [rest, productionProofNonceSplit_snd_table,
      productionProofNonceSplit_snd_adversaryCoins] using hcall
  have hframeSet :
      proofNonceFramedProgramPoint shape statement r1csDigest site
          tape.1.proofNonce suffix ∈
        prequeryPointSet shape maxStartLength adversary statement rest := by
    rw [← hframed, ← heq]
    exact hcallSet
  exact (VeiledFlock.UniversalFreshness.fresh_of_not_mem_badNonces
    (proofNonceFramedProgramPoint shape statement r1csDigest)
    (prequeryPointSet shape maxStartLength adversary statement rest)
    tape.1.proofNonce hnonce site suffix) hframeSet

/-- Concrete probability bound for the actual adaptive prequery event. -/
theorem badPrequeryTapeSet_probability_le
    [Nonempty AdversaryCoins] :
    ((badPrequeryTapeSet shape maxStartLength r1csDigest adversary statement).card :
        ℚ) /
        Fintype.card
          (Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) ≤
      (programmedPoints shape * preQueries : ℕ) /
        Fintype.card Nonce256 := by
  classical
  exact VeiledFlock.Probability.liftFiberBad_probability_le
    (productionProofNonceSplit shape maxStartLength AdversaryCoins)
    (badPrequeryNonces shape maxStartLength r1csDigest adversary statement)
    ((programmedPoints shape * preQueries : ℕ) /
      Fintype.card Nonce256)
    (fun rest => by
      have hcard := badPrequeryNonces_card_le shape maxStartLength r1csDigest
        adversary statement rest
      have hnonce : (0 : ℚ) < Fintype.card Nonce256 := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Nonce256)
      exact (div_le_div_iff_of_pos_right hnonce).2 (by exact_mod_cast hcard))

noncomputable def PostMerkleFresh (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape) : Prop :=
  let input := couplingInput shape maxStartLength tape
  AvoidsProductionMerkleTransport shape input.1 causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    (publicRepresentative shape statement) trace.answers trace.tail.rest
    input.1
    (productionPostHistory adversary statement
      (some (productionTraceProof shape fallback causalSecret
        (baseMessage shape) (publicPositions shape) weights context witness
        input.1 input.2 trace))
      (adversaryRandomness shape maxStartLength tape)
      (productionPreHistory adversary statement
        (adversaryRandomness shape maxStartLength tape) input.2)
      input.2)

noncomputable def BadPostMerkle (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  ∃ trace,
    realTrace shape maxStartLength fallback r1csDigest causalSecret completion
      statement witness tape = some trace ∧
    ¬ PostMerkleFresh shape maxStartLength fallback causalSecret weights
      context adversary statement witness tape trace

noncomputable def ProgrammingSucceeds (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape)
    (hstart : StartBound shape maxStartLength causalSecret weights context
      statement witness houter hlinear hhadamard tape trace) : Prop :=
  let input := couplingInput shape maxStartLength tape
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    (publicRepresentative shape statement) trace.answers trace.tail.rest
    houter hlinear hhadamard input
  let coupled := productionCoupledInputAt shape maxStartLength causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    (publicRepresentative shape statement) trace houter hlinear hhadamard input
    hstart
  let preState :=
    (runPreQueries adversary statement
      (adversaryRandomness shape maxStartLength tape)
      (initialSharedOracleState coupled.2)).2
  let schedule := zerocheckSimulatedByteSchedule shape causalSecret
    trace.equalityPoint.2.2 (publicRepresentative shape statement) coupled.1
    trace.answers
  (programSharedByteSchedule schedule trace.answers preState).1 = .ok ()

set_option maxHeartbeats 1000000 in
/-- Merkle-transport freshness and Fiat--Shamir prequery freshness together
make programming success deterministic.  There is no separate random
`BadProgramConflict` event once these two histories are safe. -/
theorem programmingSucceeds_of_fresh
    (fallback : OracleBlock)
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins))
    (trace : ProductionExecutionTrace shape)
    (hstart : StartBound shape maxStartLength causalSecret weights context
      statement witness houter hlinear hhadamard tape trace)
    (hmerkle : PreMerkleFresh shape maxStartLength causalSecret weights context
      adversary statement witness tape trace)
    (hprequery : PreProgrammingFresh shape maxStartLength causalSecret weights
      context adversary statement witness houter hlinear hhadamard tape trace
      hstart) :
    ProgrammingSucceeds shape maxStartLength causalSecret weights context
      adversary statement witness houter hlinear hhadamard tape trace
      hstart := by
  classical
  let input := couplingInput shape maxStartLength tape
  let right := publicRepresentative shape statement
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness right
    trace.answers trace.tail.rest houter hlinear hhadamard input
  let points := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart
  let coupled := productionCoupledInputAt shape maxStartLength causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness right
    trace houter hlinear hhadamard input hstart
  let realPre := productionPreHistory adversary statement
    (adversaryRandomness shape maxStartLength tape) input.2
  have hmerklePre : ∀ call ∈ realPre,
      moved.2 call.1 = input.2 call.1 := by
    exact productionMerkleTransport_agrees_on_safe_history shape input.1
      causalSecret (baseMessage shape) (publicPositions shape) weights context
      witness right trace.answers trace.tail.rest houter hlinear hhadamard
      fallback input realPre hmerkle
  have hprogramPre : ∀ call ∈ realPre,
      coupled.2 call.1 = moved.2 call.1 := by
    intro call hcall
    change OracleProgramming.program points
      (productionSimulatorProgramPoints_injective shape maxStartLength
        causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart)
      moved.2 moved.1.simulatedAnswers call.1 = moved.2 call.1
    apply OracleProgramming.program_off
    rintro ⟨site, heq⟩
    exact hprequery call hcall site heq.symm
  have hagreePre : ∀ call ∈ realPre,
      coupled.2 call.1 = input.2 call.1 := by
    intro call hcall
    exact (hprogramPre call hcall).trans (hmerklePre call hcall)
  have hpre : productionPreHistory adversary statement
      (adversaryRandomness shape maxStartLength tape) coupled.2 = realPre := by
    exact runQueryValues_eq_of_agrees_on_result
      (fun round history => adversary.preQuery round statement
        (adversaryRandomness shape maxStartLength tape) history)
      input.2 coupled.2 (List.ofFn id) [] hagreePre
  let preState :=
    (runPreQueries adversary statement
      (adversaryRandomness shape maxStartLength tape)
      (initialSharedOracleState coupled.2)).2
  let simSchedule := zerocheckSimulatedByteSchedule shape causalSecret
    trace.equalityPoint.2.2 right moved.1 trace.answers
  let schedule := zerocheckSimulatedByteSchedule shape causalSecret
    trace.equalityPoint.2.2 right coupled.1 trace.answers
  have hschedule : schedule = simSchedule := by
    unfold schedule simSchedule coupled
    rfl
  have hfits : ∀ site,
      (tracePoint simSchedule trace.answers site).length ≤
        ProductionMaxPointLength shape maxStartLength := by
    intro site
    exact simulatedZerocheck_tracePoint_fits shape maxStartLength causalSecret
      trace.equalityPoint.2.2 right moved.1 trace.answers hstart site
  have hinjective : Function.Injective
      (fun site => tracePoint simSchedule trace.answers site) := by
    exact productionSimulatedZerocheck_tracePoints_injective shape causalSecret
      trace.equalityPoint.2.2 right moved.1 trace.answers
  have hqueries : ∀ site,
      ¬ wasQueried preState
        (boundBytes (tracePoint simSchedule trace.answers site)
          (hfits site)) := by
    intro site hqueried
    have hreached := runPreQueries_wasQueried_mem adversary statement
      (adversaryRandomness shape maxStartLength tape) coupled.2 _ hqueried
    obtain ⟨call, hcall, hpoint⟩ := hreached
    have hcallReal : call ∈ realPre := by
      have hcallCoupled : call ∈ productionPreHistory adversary statement
          (adversaryRandomness shape maxStartLength tape) coupled.2 := by
        change call ∈ runQueryValues
          (fun round history => adversary.preQuery round statement
            (adversaryRandomness shape maxStartLength tape) history)
          coupled.2 (List.ofFn id) []
        simpa only [preState, initialSharedOracleState,
          runPreQueries_value] using hcall
      rw [hpre] at hcallCoupled
      exact hcallCoupled
    apply hprequery call hcallReal site
    rw [hpoint]
    apply unboundBytes_injective
    rfl
  have hprograms : ∀ site,
      ¬ wasProgrammed preState
        (boundBytes (tracePoint simSchedule trace.answers site)
          (hfits site)) := by
    intro site
    exact runPreQueries_not_wasProgrammed adversary statement
      (adversaryRandomness shape maxStartLength tape) coupled.2 _
  simp only [ProgrammingSucceeds]
  change (programSharedByteSchedule schedule trace.answers preState).1 = .ok ()
  rw [hschedule]
  exact programSharedByteSchedule_ok_of_fresh simSchedule trace.answers
    preState hfits hinjective hqueries hprograms

noncomputable def BadProgramConflict (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  ∃ (trace : ProductionExecutionTrace shape)
      (hstart : StartBound shape maxStartLength causalSecret weights context
        statement witness houter hlinear hhadamard tape trace),
    realTrace shape maxStartLength fallback r1csDigest causalSecret completion
      statement witness tape = some trace ∧
    ¬ ProgrammingSucceeds shape maxStartLength causalSecret weights context
      adversary statement witness houter hlinear hhadamard tape trace hstart

/-- A programming conflict can only occur if a transported Merkle point or a
future Fiat--Shamir programming point was already reached.  It has no
independent failure probability. -/
theorem badProgramConflict_implies_badPreMerkle_or_badPrequery
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins)) :
    BadProgramConflict shape maxStartLength fallback r1csDigest causalSecret
        completion weights context adversary statement witness houter hlinear
        hhadamard tape →
      BadPreMerkle shape maxStartLength fallback r1csDigest causalSecret
          completion weights context adversary statement witness tape ∨
        BadPrequery shape maxStartLength fallback r1csDigest causalSecret
          completion weights context adversary statement witness houter
          hlinear hhadamard tape := by
  rintro ⟨trace, hstart, htrace, hconflict⟩
  by_cases hmerkle : PreMerkleFresh shape maxStartLength causalSecret weights
      context adversary statement witness tape trace
  · by_cases hprequery : PreProgrammingFresh shape maxStartLength
        causalSecret weights context adversary statement witness houter
        hlinear hhadamard tape trace hstart
    · exact False.elim (hconflict (programmingSucceeds_of_fresh shape
        maxStartLength causalSecret weights context adversary statement witness
        houter hlinear hhadamard fallback tape trace hstart hmerkle hprequery))
    · exact Or.inr ⟨trace, hstart, htrace, hprequery⟩
  · exact Or.inl ⟨trace, htrace, hmerkle⟩

/-- One explicit operational good event.  Each conjunct is the complement of
a named failure of the concrete complete-view coupling. -/
noncomputable def GlobalGood (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  ¬ BadTraceFailure shape maxStartLength fallback r1csDigest causalSecret
      completion statement witness tape ∧
  ¬ BadStartBound shape maxStartLength fallback r1csDigest causalSecret
      completion weights context statement witness houter hlinear hhadamard
      tape ∧
  ¬ BadPreMerkle shape maxStartLength fallback r1csDigest causalSecret
      completion weights context adversary statement witness tape ∧
  ¬ BadPrequery shape maxStartLength fallback r1csDigest causalSecret
      completion weights context adversary statement witness houter hlinear
      hhadamard tape ∧
  ¬ BadPostMerkle shape maxStartLength fallback r1csDigest causalSecret
      completion weights context adversary statement witness tape ∧
  ¬ BadProgramConflict shape maxStartLength fallback r1csDigest causalSecret
      completion weights context adversary statement witness houter hlinear
      hhadamard tape

set_option maxRecDepth 10000 in
/-- Field-by-field bridge from the operational ledger event to the exact
`ProductionGood` required by the complete-view coupling. -/
theorem globalGood_implies_productionGood
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins))
    (hgood : GlobalGood shape maxStartLength fallback r1csDigest causalSecret
      completion weights context adversary statement witness houter hlinear
      hhadamard tape) :
    ∃ trace,
      productionRealTrace shape fallback r1csDigest causalSecret completion
        (baseMessage shape) statement witness tape.1 tape.2.1 = some trace ∧
      ProductionGood shape maxStartLength fallback r1csDigest causalSecret
        completion (baseMessage shape) (publicPositions shape) weights context
        (publicRepresentative shape) adversary statement witness tape.2.2 trace
        houter hlinear hhadamard (couplingInput shape maxStartLength tape) := by
  classical
  rcases hgood with ⟨htraceGood, hstartGood, hpreMerkleGood,
    hprequeryGood, hpostMerkleGood, hprogramGood⟩
  have htraceNe : realTrace shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness tape ≠ none := htraceGood
  rw [Option.ne_none_iff_exists] at htraceNe
  obtain ⟨trace, htrace⟩ := htraceNe
  have htrace' : realTrace shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness tape = some trace :=
    htrace.symm
  have hstart : StartBound shape maxStartLength causalSecret weights context
      statement witness houter hlinear hhadamard tape trace := by
    by_contra hnot
    exact hstartGood ⟨trace, htrace', hnot⟩
  have hpreMerkle : PreMerkleFresh shape maxStartLength causalSecret weights
      context adversary statement witness tape trace := by
    by_contra hnot
    exact hpreMerkleGood ⟨trace, htrace', hnot⟩
  have hprequery : PreProgrammingFresh shape maxStartLength causalSecret
      weights context adversary statement witness houter hlinear hhadamard
      tape trace hstart := by
    by_contra hnot
    exact hprequeryGood ⟨trace, hstart, htrace', hnot⟩
  have hpostMerkle : PostMerkleFresh shape maxStartLength fallback causalSecret
      weights context adversary statement witness tape trace := by
    by_contra hnot
    exact hpostMerkleGood ⟨trace, htrace', hnot⟩
  have hprogram : ProgrammingSucceeds shape maxStartLength causalSecret
      weights context adversary statement witness houter hlinear hhadamard
      tape trace hstart := by
    by_contra hnot
    exact hprogramGood ⟨trace, hstart, htrace', hnot⟩
  refine ⟨trace, htrace', ?_⟩
  exact {
    startBound := hstart
    traceSuccess := htrace'
    preMerkleFresh := hpreMerkle
    preProgrammingFresh := hprequery
    postMerkleFresh := hpostMerkle
    programmingSucceeds := hprogram
  }

end

end VeiledFlock.ProductionOperationalGood

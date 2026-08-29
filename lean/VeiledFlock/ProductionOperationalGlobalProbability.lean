import VeiledFlock.ProductionPostMerkleProbability
import VeiledFlock.ProductionTraceFailureProbability

/-! # One operational global bad event and its probability bound -/

namespace VeiledFlock.ProductionOperationalGlobalProbability

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.NonceSerialization
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalGood
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPostMerkleProbability
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingOperationalProbability
open VeiledFlock.ProductionTraceFailureProbability

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

/-- The four primitive operational events. `BadStartBound` is deterministic,
and `BadProgramConflict` is contained in the pre-Merkle/prequery union. -/
noncomputable def operationalGlobalBadTapeSet :
    Finset (ProductionLedgerTape shape maxStartLength AdversaryCoins) := by
  classical
  exact badTraceFailureTapeSet shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness ∪
    badPreMerkleTapeSet shape maxStartLength adversary statement ∪
    badPrequeryTapeSet shape maxStartLength r1csDigest adversary statement ∪
    badPostMerkleTapeSet shape maxStartLength fallback r1csDigest causalSecret
      completion weights context adversary statement witness

theorem mem_operationalGlobalBadTapeSet_iff
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    tape ∈ operationalGlobalBadTapeSet shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness ↔
      tape ∈ badTraceFailureTapeSet shape maxStartLength fallback r1csDigest
          causalSecret completion statement witness ∨
        tape ∈ badPreMerkleTapeSet shape maxStartLength adversary statement ∨
        tape ∈ badPrequeryTapeSet shape maxStartLength r1csDigest adversary
          statement ∨
        tape ∈ badPostMerkleTapeSet shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement witness := by
  simp [operationalGlobalBadTapeSet, or_assoc]

set_option maxHeartbeats 1000000 in
theorem not_globalGood_implies_mem_operationalGlobalBadTapeSet
    (hmax : productionStartLengthBound shape statement r1csDigest ≤
      maxStartLength)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    ¬ GlobalGood shape maxStartLength fallback r1csDigest causalSecret
        completion weights context adversary statement witness houter hlinear
        hhadamard tape →
      tape ∈ operationalGlobalBadTapeSet shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness := by
  classical
  intro hnotGood
  rw [mem_operationalGlobalBadTapeSet_iff]
  by_contra hnotMember
  push_neg at hnotMember
  rcases hnotMember with ⟨htraceSet, hpreMerkleSet, hprequerySet, hpostSet⟩
  have htrace : ¬ BadTraceFailure shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness tape := by
    intro hbad
    apply htraceSet
    simp [badTraceFailureTapeSet, hbad]
  have hstart : ¬ BadStartBound shape maxStartLength fallback r1csDigest
      causalSecret completion weights context statement witness houter hlinear
      hhadamard tape :=
    not_badStartBound shape maxStartLength fallback r1csDigest causalSecret
      completion weights context statement witness houter hlinear hhadamard
      hmax tape
  have hpreMerkle : ¬ BadPreMerkle shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      tape := by
    intro hbad
    exact hpreMerkleSet (badPreMerkle_implies_mem_tapeSet shape maxStartLength
      fallback r1csDigest causalSecret completion weights context adversary
      statement witness tape hbad)
  have hprequery : ¬ BadPrequery shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      houter hlinear hhadamard tape := by
    intro hbad
    exact hprequerySet (badPrequery_implies_mem_tapeSet shape maxStartLength
      fallback r1csDigest causalSecret completion weights context adversary
      statement witness houter hlinear hhadamard tape hbad)
  have hpostMerkle : ¬ BadPostMerkle shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      tape := by
    intro hbad
    exact hpostSet ((mem_badPostMerkleTapeSet_iff shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness tape).2 hbad)
  have hprogram : ¬ BadProgramConflict shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness
      houter hlinear hhadamard tape := by
    intro hbad
    rcases badProgramConflict_implies_badPreMerkle_or_badPrequery shape
      maxStartLength fallback r1csDigest causalSecret completion weights context
      adversary statement witness houter hlinear hhadamard tape hbad with
      hbadPreMerkle | hbadPrequery
    · exact hpreMerkle hbadPreMerkle
    · exact hprequery hbadPrequery
  exact hnotGood ⟨htrace, hstart, hpreMerkle, hprequery, hpostMerkle, hprogram⟩

/-- Hidden salted-Merkle inputs guessed before the proof. -/
def operationalPreMerkleBound (shape : BatchShape) (preQueries : ℕ) : ℚ :=
  (Fintype.card (ProductionHiddenLeafIndex shape) * preQueries : ℕ) /
    Fintype.card NumericNonce

/-- Programmed Fiat--Shamir locations guessed before programming. -/
def operationalPrequeryBound (shape : BatchShape) (preQueries : ℕ) : ℚ :=
  (programmedPoints shape * preQueries : ℕ) / Fintype.card Nonce256

/-- Hidden salted-Merkle locations guessed across both adaptive phases. -/
def operationalPostMerkleBound (shape : BatchShape)
    (preQueries postQueries : ℕ) : ℚ :=
  2 * ((Fintype.card (ProductionHiddenLeafIndex shape) *
    (preQueries + postQueries) : ℕ) : ℚ) /
    Fintype.card NumericNonce

/-- Exact symbolic failure expression for one production proof. -/
def operationalFailureBound (shape : BatchShape) (preQueries postQueries : ℕ) :
    ℚ :=
  samplingAbortBound shape + operationalPreMerkleBound shape preQueries +
    operationalPrequeryBound shape preQueries +
    operationalPostMerkleBound shape preQueries postQueries

include houter hlinear hhadamard in
theorem operationalGlobalBad_probability_le
    [Nonempty AdversaryCoins]
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    ((operationalGlobalBadTapeSet shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement witness).card :
        ℚ) /
      Fintype.card (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤
    operationalFailureBound shape preQueries postQueries := by
  classical
  let trace := badTraceFailureTapeSet (AdversaryCoins := AdversaryCoins) shape
    maxStartLength fallback r1csDigest causalSecret completion statement witness
  let preMerkle := badPreMerkleTapeSet shape maxStartLength adversary statement
  let prequery := badPrequeryTapeSet shape maxStartLength r1csDigest adversary
    statement
  let postMerkle := badPostMerkleTapeSet shape maxStartLength fallback r1csDigest
    causalSecret completion weights context adversary statement witness
  let global := operationalGlobalBadTapeSet shape maxStartLength fallback
    r1csDigest causalSecret completion weights context adversary statement
    witness
  have hcard : global.card ≤
      trace.card + preMerkle.card + prequery.card + postMerkle.card := by
    calc
      global.card ≤
          (trace ∪ preMerkle ∪ prequery).card + postMerkle.card := by
        dsimp only [global, trace, preMerkle, prequery, postMerkle]
        unfold operationalGlobalBadTapeSet
        exact Finset.card_union_le _ _
      _ ≤ ((trace ∪ preMerkle).card + prequery.card) + postMerkle.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((trace.card + preMerkle.card) + prequery.card) +
          postMerkle.card := by
        gcongr
        exact Finset.card_union_le _ _
  have hdenom : (0 : ℚ) <
      Fintype.card (ProductionLedgerTape shape maxStartLength AdversaryCoins) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card
      (ProductionLedgerTape shape maxStartLength AdversaryCoins))
  have htrace := badTraceFailure_probability_le
    (AdversaryCoins := AdversaryCoins) shape maxStartLength fallback r1csDigest
    statement witness causalSecret completion hbudget houter hlinear hnodes
  have hpreMerkle := badPreMerkleTapeSet_probability_le shape maxStartLength
    adversary statement
  have hprequery := badPrequeryTapeSet_probability_le shape maxStartLength
    r1csDigest adversary statement
  have hpostMerkle := badPostMerkleTapeSet_probability_le shape maxStartLength
    fallback r1csDigest causalSecret completion weights context adversary
    statement witness houter hlinear hhadamard hnodes
  have htrace' :
      (trace.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤
        samplingAbortBound shape := by
    simpa only [trace] using htrace
  have hpreMerkle' :
      (preMerkle.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤
        operationalPreMerkleBound shape preQueries := by
    simpa only [preMerkle, operationalPreMerkleBound] using hpreMerkle
  have hprequery' :
      (prequery.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤
        operationalPrequeryBound shape preQueries := by
    simpa only [prequery, operationalPrequeryBound] using hprequery
  have hpostMerkle' :
      (postMerkle.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤
        operationalPostMerkleBound shape preQueries postQueries := by
    simpa only [postMerkle, operationalPostMerkleBound] using hpostMerkle
  change (global.card : ℚ) /
    Fintype.card (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤ _
  calc
    (global.card : ℚ) /
        Fintype.card
          (ProductionLedgerTape shape maxStartLength AdversaryCoins) ≤
        ((trace.card + preMerkle.card + prequery.card + postMerkle.card : ℕ) :
          ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) :=
      (div_le_div_iff_of_pos_right hdenom).2 (by
            exact_mod_cast hcard)
    _ = (trace.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) +
        (preMerkle.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) +
        (prequery.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) +
        (postMerkle.card : ℚ) /
          Fintype.card
            (ProductionLedgerTape shape maxStartLength AdversaryCoins) := by
      norm_num only [Nat.cast_add]
      ring
    _ ≤ operationalFailureBound shape preQueries postQueries := by
      unfold operationalFailureBound
      exact add_le_add (add_le_add (add_le_add htrace' hpreMerkle')
        hprequery') hpostMerkle'

end

end VeiledFlock.ProductionOperationalGlobalProbability

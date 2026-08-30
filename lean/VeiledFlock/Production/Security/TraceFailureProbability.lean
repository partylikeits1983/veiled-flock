import VeiledFlock.Production.Sampling.SamplingTraceComplete

/-! # Operational probability bound for production trace failure -/

namespace VeiledFlock.ProductionTraceFailureProbability

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.Probability
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalGood
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionSamplingOperationalProbability
open VeiledFlock.ProductionSamplingOperationalTrace
open VeiledFlock.ProductionSamplingTraceComplete
open VeiledFlock.ProductionSamplingTraceEquality

variable {AdversaryCoins : Type}

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem not_badTraceFailure_of_expanded_not_samplingBad
    [Fintype AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins)
    (hnotBad : input ∉ expandedSamplingBad shape maxStartLength fallback
      r1csDigest statement witness causalSecret completion hbudget) :
    ¬ BadTraceFailure shape maxStartLength fallback r1csDigest causalSecret
      completion statement witness input.1 := by
  classical
  let answers := expandedSamplingAnswers shape maxStartLength fallback
    r1csDigest statement witness causalSecret completion hbudget input
  have hgoodRaw : expandedSamplingAnswers shape maxStartLength fallback
      r1csDigest statement witness causalSecret completion hbudget input ∉
        VeiledFlock.ProductionSamplingBadTape.globalBad shape := by
    rw [← mem_expandedSamplingBad_iff (AdversaryCoins := AdversaryCoins) shape
      maxStartLength fallback r1csDigest statement witness causalSecret
      completion hbudget input]
    exact hnotBad
  have hgood : answers ∉ VeiledFlock.ProductionSamplingBadTape.globalBad shape := by
    exact hgoodRaw
  have hprelude := originalPrelude_eq_samplingPrelude shape maxStartLength
    fallback r1csDigest statement witness input houter hlinear hnodes
  have hcoins :
      (samplingExpandedSplit shape maxStartLength input).2.1 = input.1.1 := rfl
  have hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      input.1.1
      (VeiledFlock.ProductionMerklePrelude.preEqualityTranscript
        (productionStatementDigest statement) r1csDigest
        input.1.1.proofNonce input.1.1.treeNonces.outer
        input.1.1.treeNonces.veilLinear input.1.1.treeNonces.veilHadamard
        (outerRoot shape (baseMessage shape) witness input.1.1
          (answerBounded fallback input.1.2.1))
        (linearRoot shape input.1.1 (answerBounded fallback input.1.2.1)))
      answers (answerBounded fallback input.1.2.1) := by
    intro site point hquery
    apply expandedSamplingAnswers_raw_active shape maxStartLength fallback
      r1csDigest statement witness causalSecret completion hbudget input hgood
      site point
    rw [hprelude] at hquery
    simpa only [answers, hcoins] using hquery
  rcases productionRealTrace_some_of_raw_agreement shape fallback r1csDigest
      causalSecret completion (baseMessage shape) statement witness input.1.1
      input.1.2.1 answers hgood hagrees with
    ⟨trace, htrace⟩
  intro hfailure
  exact Option.some_ne_none trace (htrace.symm.trans hfailure)

/-- The operational trace-failure event on exactly the probability space used
by the production real and simulated views. -/
noncomputable def badTraceFailureTapeSet
    [Fintype AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (statement : ProductionStatement shape) (witness : Witness shape) :
    Finset (ProductionLedgerTape shape maxStartLength AdversaryCoins) := by
  classical
  exact Finset.univ.filter fun tape =>
      BadTraceFailure shape maxStartLength fallback r1csDigest causalSecret
        completion statement witness tape

/-- Add the private inactive-coordinate tape used to make every bounded
early-exit loop a fixed finite experiment. -/
noncomputable def liftedBadTraceFailureTapeSet
    [Fintype AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (statement : ProductionStatement shape) (witness : Witness shape) :
    Finset (SamplingExpandedTape shape maxStartLength AdversaryCoins) := by
  classical
  exact liftBad (Equiv.refl _)
    (badTraceFailureTapeSet shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness)

theorem liftedBadTraceFailure_subset_samplingBad
    [Fintype AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    liftedBadTraceFailureTapeSet (AdversaryCoins := AdversaryCoins) shape
        maxStartLength fallback r1csDigest
        causalSecret completion statement witness ⊆
      expandedSamplingBad (AdversaryCoins := AdversaryCoins) shape
        maxStartLength fallback r1csDigest statement witness causalSecret
        completion hbudget := by
  classical
  intro input hfailure
  by_contra hnotBad
  have hbadTrace : BadTraceFailure shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness input.1 := by
    have hlocal : input.1 ∈ badTraceFailureTapeSet shape maxStartLength fallback
        r1csDigest causalSecret completion statement witness := by
      simpa [liftedBadTraceFailureTapeSet, liftBad] using hfailure
    simpa [badTraceFailureTapeSet] using hlocal
  exact (not_badTraceFailure_of_expanded_not_samplingBad shape maxStartLength
    fallback r1csDigest statement witness causalSecret completion hbudget
    houter hlinear hnodes input hnotBad) hbadTrace

theorem badTraceFailure_probability_le
    [Fintype AdversaryCoins] [Nonempty AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    ((badTraceFailureTapeSet (AdversaryCoins := AdversaryCoins) shape
      maxStartLength fallback r1csDigest causalSecret completion statement
      witness).card : ℚ) /
        Fintype.card (ProductionLedgerTape shape maxStartLength
          AdversaryCoins) ≤
      VeiledFlock.ProductionSamplingBadTape.samplingAbortBound shape := by
  classical
  let lifted := liftedBadTraceFailureTapeSet (AdversaryCoins := AdversaryCoins)
    shape maxStartLength fallback r1csDigest causalSecret completion statement
    witness
  let sampling := expandedSamplingBad (AdversaryCoins := AdversaryCoins) shape
    maxStartLength fallback r1csDigest statement witness causalSecret completion
    hbudget
  have hsubset : lifted ⊆ sampling :=
    liftedBadTraceFailure_subset_samplingBad shape maxStartLength fallback
      r1csDigest statement witness causalSecret completion hbudget houter hlinear
      hnodes
  have hcard : lifted.card ≤ sampling.card := Finset.card_le_card hsubset
  have hlifted :
      (lifted.card : ℚ) /
          Fintype.card (SamplingExpandedTape shape maxStartLength
            AdversaryCoins) =
        ((badTraceFailureTapeSet (AdversaryCoins := AdversaryCoins) shape
          maxStartLength fallback r1csDigest causalSecret completion statement
          witness).card : ℚ) /
          Fintype.card (ProductionLedgerTape shape maxStartLength
            AdversaryCoins) := by
    dsimp only [lifted]
    unfold liftedBadTraceFailureTapeSet
    exact liftBad_probability_eq (Equiv.refl _)
      (badTraceFailureTapeSet shape maxStartLength fallback r1csDigest
        causalSecret completion statement witness)
  rw [← hlifted]
  calc
    (lifted.card : ℚ) /
        Fintype.card (SamplingExpandedTape shape maxStartLength
          AdversaryCoins) ≤
      (sampling.card : ℚ) /
        Fintype.card (SamplingExpandedTape shape maxStartLength
          AdversaryCoins) := by gcongr
    _ ≤ VeiledFlock.ProductionSamplingBadTape.samplingAbortBound shape := by
      dsimp only [sampling]
      exact expandedSamplingBad_probability_le shape maxStartLength fallback
        r1csDigest statement witness causalSecret completion hbudget

end VeiledFlock.ProductionTraceFailureProbability

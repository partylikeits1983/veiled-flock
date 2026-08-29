import VeiledFlock.ProductionSamplingScheduleClassification
import VeiledFlock.ProductionOperationalGood

/-!
# Operational probability space for production sampling

This module factors the one shared production oracle by its actual serialized
Fiat--Shamir/PoW domain.  Merkle-derived prelude data remains in the
complement fiber; the local fiber consists of the sampling restriction and
the private inactive-coordinate tape used only to make bounded early-exit
loops a fixed finite experiment.
-/

namespace VeiledFlock.ProductionSamplingOperationalProbability

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OptionalAdaptiveOracle
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.Probability
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalGood
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingOracleSplit
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleAudit
open VeiledFlock.ProductionSamplingScheduleClassification

variable {AdversaryCoins : Type*}

abbrev SamplingDummyTape :=
  Fin (productionSamplingSlots + 1) → OracleBlock

abbrev SamplingLocal (maxPointLength : ℕ) :=
  (SamplingPoint maxPointLength → OracleBlock) × SamplingDummyTape

abbrev SamplingRest (shape : BatchShape) (maxPointLength : ℕ)
    (AdversaryCoins : Type*) :=
  ProductionCoins shape ×
    (NonSamplingPoint maxPointLength → OracleBlock) × AdversaryCoins

abbrev SamplingExpandedTape (shape : BatchShape) (maxStartLength : ℕ)
    (AdversaryCoins : Type*) :=
  ProductionLedgerTape shape maxStartLength AdversaryCoins × SamplingDummyTape

/-- Exact reindexing of the operational tape plus an independent private
dummy tape.  It splits the one shared table, rather than replacing it with
independent conceptual protocol oracles. -/
def samplingExpandedSplit (shape : BatchShape) (maxStartLength : ℕ) :
    SamplingExpandedTape shape maxStartLength AdversaryCoins ≃
      SamplingLocal (ProductionMaxPointLength shape maxStartLength) ×
        SamplingRest shape (ProductionMaxPointLength shape maxStartLength)
          AdversaryCoins where
  toFun input :=
    let split := splitSharedOracle (ProductionMaxPointLength shape
      maxStartLength) input.1.2.1
    ((split.1, input.2), (input.1.1, split.2, input.1.2.2))
  invFun input :=
    ((input.2.1,
      (splitSharedOracle (ProductionMaxPointLength shape maxStartLength)).symm
        (input.1.1, input.2.2.1), input.2.2.2), input.1.2)
  left_inv input := by
    rcases input with ⟨⟨coins, table, adversaryCoins⟩, dummy⟩
    simp
  right_inv input := by
    rcases input with ⟨⟨sampling, dummy⟩, coins, other, adversaryCoins⟩
    simp

def tableOfSplit (maxPointLength : ℕ)
    (sampling : SamplingPoint maxPointLength → OracleBlock)
    (other : NonSamplingPoint maxPointLength → OracleBlock) :
    BoundedBytes maxPointLength → OracleBlock :=
  (splitSharedOracle maxPointLength).symm (sampling, other)

def defaultSamplingTable (maxPointLength : ℕ) :
    SamplingPoint maxPointLength → OracleBlock :=
  fun _ => default

/-- The exact transcript immediately before the combined sampling schedule.
Its Merkle roots are evaluated in the non-sampling fiber; independence from
the arbitrary default sampling restriction is proved below. -/
noncomputable def samplingPrelude
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (coins : ProductionCoins shape)
    (other : NonSamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock) : List Byte :=
  let table := tableOfSplit (ProductionMaxPointLength shape maxStartLength)
    (defaultSamplingTable _) other
  let oracle := answerBounded fallback table
  let outerCommitment := outerRoot shape (baseMessage shape) witness coins oracle
  let linearCommitment := linearRoot shape coins oracle
  preEqualityTranscript (productionStatementDigest statement) r1csDigest
    coins.proofNonce coins.treeNonces.outer coins.treeNonces.veilLinear
    coins.treeNonces.veilHadamard outerCommitment linearCommitment

@[simp]
theorem samplingPrelude_length
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape) (coins : ProductionCoins shape)
    (other : NonSamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock) :
    (samplingPrelude shape maxStartLength fallback r1csDigest statement witness
      coins other).length =
      (productionStatementDigest statement).length + r1csDigest.length + 432 := by
  simp [samplingPrelude, preEqualityTranscript_length]

theorem samplingPrelude_isFiatShamir
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape) (coins : ProductionCoins shape)
    (other : NonSamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock) :
    isFiatShamirPoint
      (samplingPrelude shape maxStartLength fallback r1csDigest statement
        witness coins other) := by
  unfold samplingPrelude
  exact preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _

theorem answerBounded_tableOfSplit_nonsampling
    (maxPointLength : ℕ) (fallback : OracleBlock)
    (left right : SamplingPoint maxPointLength → OracleBlock)
    (other : NonSamplingPoint maxPointLength → OracleBlock)
    (point : List Byte) (hfit : point.length ≤ maxPointLength)
    (hother : ¬ IsSamplingBytes point) :
    answerBounded fallback (tableOfSplit maxPointLength left other) point =
      answerBounded fallback (tableOfSplit maxPointLength right other) point := by
  rw [answerBounded_of_le fallback _ point hfit,
    answerBounded_of_le fallback _ point hfit]
  let bounded := boundBytes point hfit
  have hbounded : ¬ IsSamplingPoint bounded := by
    simpa [bounded, IsSamplingPoint] using hother
  change
    (splitSharedOracle maxPointLength).symm (left, other) bounded =
      (splitSharedOracle maxPointLength).symm (right, other) bounded
  have hleft := splitSharedOracle_symm_nonsampling maxPointLength left other
    ⟨bounded, hbounded⟩
  have hright := splitSharedOracle_symm_nonsampling maxPointLength right other
    ⟨bounded, hbounded⟩
  exact hleft.trans hright.symm

theorem productionMerklePoint_not_sampling
    (role : MerkleRole) (channel : RoChannel) (treeDepth : Byte)
    (treeNonce : Nonce256) (leafLength : Word64) (level : Word32)
    (index : Word64) (payload : List Byte) :
    ¬ IsSamplingBytes
      (encodeMerklePoint role channel treeDepth treeNonce leafLength level index
        payload) := by
  unfold IsSamplingBytes
  rw [encodeMerklePoint_head]
  cases role <;> decide

theorem productionMerkleRoot_sampling_independent
    (maxPointLength : ℕ) (fallback : OracleBlock)
    (left right : SamplingPoint maxPointLength → OracleBlock)
    (other : NonSamplingPoint maxPointLength → OracleBlock)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : Word64) (depth : ℕ)
    (salts : Fin (2 ^ depth) →
      VeiledFlock.NonceSerialization.NumericNonce)
    (payload : Fin (2 ^ depth) → List Byte)
    (hleaf : ∀ index,
      108 + (payload index).length ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength) :
    VeiledFlock.ProductionMerkleTree.productionMerkleRoot
        (answerBounded fallback (tableOfSplit maxPointLength left other))
        channel treeDepth treeNonce leafLength depth salts payload =
      VeiledFlock.ProductionMerkleTree.productionMerkleRoot
        (answerBounded fallback (tableOfSplit maxPointLength right other))
        channel treeDepth treeNonce leafLength depth salts payload := by
  unfold VeiledFlock.ProductionMerkleTree.productionMerkleRoot
  apply VeiledFlock.ProductionMerkleTree.merkleRoot_congr
  · intro level index leftBlock rightBlock
    apply answerBounded_tableOfSplit_nonsampling
    · simpa using hnodes
    · exact productionMerklePoint_not_sampling .node channel treeDepth
        treeNonce leafLength (BitVec.ofNat 32 level)
          (BitVec.ofNat 64 index.val)
          (VeiledFlock.ProductionMerkleTree.oracleBlockBytes leftBlock ++
            VeiledFlock.ProductionMerkleTree.oracleBlockBytes rightBlock)
  · intro index
    apply answerBounded_tableOfSplit_nonsampling
    · rw [VeiledFlock.ProductionMerkleTree.productionLeafPoint_length]
      exact hleaf index
    · exact productionMerklePoint_not_sampling .leaf channel treeDepth
        treeNonce leafLength (BitVec.ofNat 32 depth)
          (BitVec.ofNat 64 index.val)
          (VeiledFlock.Framing.nonceBytes
            (VeiledFlock.NonceSerialization.numericNonceBytes (salts index)) ++
            payload index)

theorem outerRoot_sampling_independent
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (witness : Witness shape) (coins : ProductionCoins shape)
    (left right : SamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (other : NonSamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    outerRoot shape (baseMessage shape) witness coins
        (answerBounded fallback
          (tableOfSplit (ProductionMaxPointLength shape maxStartLength) left
            other)) =
      outerRoot shape (baseMessage shape) witness coins
        (answerBounded fallback
          (tableOfSplit (ProductionMaxPointLength shape maxStartLength) right
            other)) := by
  apply productionMerkleRoot_sampling_independent
  · intro index
    simpa [outerRowPayload] using houter
  · exact hnodes

theorem linearRoot_sampling_independent
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (coins : ProductionCoins shape)
    (left right : SamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (other : NonSamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    linearRoot shape coins
        (answerBounded fallback
          (tableOfSplit (ProductionMaxPointLength shape maxStartLength) left
            other)) =
      linearRoot shape coins
        (answerBounded fallback
          (tableOfSplit (ProductionMaxPointLength shape maxStartLength) right
            other)) := by
  apply productionMerkleRoot_sampling_independent
  · intro index
    simpa [linearRowPayload] using hlinear
  · exact hnodes

theorem samplingPrelude_eq_of_samplingTable
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape) (coins : ProductionCoins shape)
    (sampling : SamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (other : NonSamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    samplingPrelude shape maxStartLength fallback r1csDigest statement witness
        coins other =
      let table := tableOfSplit (ProductionMaxPointLength shape maxStartLength)
        sampling other
      let oracle := answerBounded fallback table
      let outerCommitment := outerRoot shape (baseMessage shape) witness coins
        oracle
      let linearCommitment := linearRoot shape coins oracle
      preEqualityTranscript (productionStatementDigest statement) r1csDigest
        coins.proofNonce coins.treeNonces.outer coins.treeNonces.veilLinear
        coins.treeNonces.veilHadamard outerCommitment linearCommitment := by
  unfold samplingPrelude
  dsimp only
  rw [outerRoot_sampling_independent shape maxStartLength fallback witness coins
    (defaultSamplingTable _) sampling other houter hnodes]
  rw [linearRoot_sampling_independent shape maxStartLength fallback coins
    (defaultSamplingTable _) sampling other hlinear hnodes]

/-- Public byte budget sufficient for the complete fixed sampling schedule. -/
def OperationalSamplingBudget
    (shape : BatchShape) (maxStartLength : ℕ)
    (r1csDigest : List Byte) (statement : ProductionStatement shape) : Prop :=
  (productionStatementDigest statement).length + r1csDigest.length + 432 +
      productionSamplingSlots * 4096 + 4096 ≤
    ProductionMaxPointLength shape maxStartLength

theorem samplingPrelude_budget
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape) (coins : ProductionCoins shape)
    (other : NonSamplingPoint (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement) :
    SamplingScheduleBudget
      (samplingPrelude shape maxStartLength fallback r1csDigest statement
        witness coins other)
      (ProductionMaxPointLength shape maxStartLength) := by
  unfold OperationalSamplingBudget at hbudget
  unfold SamplingScheduleBudget
  rw [samplingPrelude_length]
  exact hbudget

/-- The concrete local sampling bad set in one fixed coin/Merkle/adversary
fiber. -/
noncomputable def samplingBadAt
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (rest : SamplingRest shape (ProductionMaxPointLength shape maxStartLength)
      AdversaryCoins) :
    Finset (SamplingLocal (ProductionMaxPointLength shape maxStartLength)) :=
  let prelude := samplingPrelude shape maxStartLength fallback r1csDigest
    statement witness rest.1 rest.2.1
  optionalBadInputs
    (boundedFreshSchedule shape causalSecret completion witness rest.1 prelude
      (ProductionMaxPointLength shape maxStartLength)
      (freshSchedule_fits_of_budget shape causalSecret completion witness
        rest.1 prelude _
        (samplingPrelude_budget shape maxStartLength fallback r1csDigest
          statement witness rest.1 rest.2.1 hbudget))
      (freshSchedule_classified shape causalSecret completion witness rest.1
        prelude
        (samplingPrelude_isFiatShamir shape maxStartLength fallback r1csDigest
          statement witness rest.1 rest.2.1)))
    (globalBad shape)

/-- Uniform local bound in every fixed non-sampling fiber. -/
theorem samplingBadAt_probability_le
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (rest : SamplingRest shape (ProductionMaxPointLength shape maxStartLength)
      AdversaryCoins) :
    ((samplingBadAt shape maxStartLength fallback r1csDigest statement witness
      causalSecret completion hbudget rest).card : ℚ) /
        Fintype.card
          (SamplingLocal (ProductionMaxPointLength shape maxStartLength)) ≤
      samplingAbortBound shape := by
  exact productionSampling_globalBad_probability_le shape causalSecret
    completion witness rest.1
      (samplingPrelude shape maxStartLength fallback r1csDigest statement
        witness rest.1 rest.2.1)
      (ProductionMaxPointLength shape maxStartLength)
      (samplingPrelude_budget shape maxStartLength fallback r1csDigest
        statement witness rest.1 rest.2.1 hbudget)
      (samplingPrelude_isFiatShamir shape maxStartLength fallback r1csDigest
        statement witness rest.1 rest.2.1)

/-- Lift the locally bounded event to the operational tape plus the independent
inactive-coordinate tape. -/
noncomputable def expandedSamplingBad
    [Fintype AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement) :
    Finset (SamplingExpandedTape shape maxStartLength AdversaryCoins) :=
  liftFiberBad (samplingExpandedSplit shape maxStartLength)
    (samplingBadAt shape maxStartLength fallback r1csDigest statement witness
      causalSecret completion hbudget)

theorem expandedSamplingBad_probability_le
    [Fintype AdversaryCoins] [Nonempty AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement) :
    ((expandedSamplingBad (AdversaryCoins := AdversaryCoins) shape
      maxStartLength fallback r1csDigest statement witness causalSecret
      completion hbudget).card : ℚ) /
        Fintype.card (SamplingExpandedTape shape maxStartLength
          AdversaryCoins) ≤ samplingAbortBound shape := by
  classical
  exact liftFiberBad_probability_le (samplingExpandedSplit shape maxStartLength)
    (samplingBadAt shape maxStartLength fallback r1csDigest statement witness
      causalSecret completion hbudget) (samplingAbortBound shape)
      (samplingBadAt_probability_le shape maxStartLength fallback r1csDigest
        statement witness causalSecret completion hbudget)

noncomputable def expandedSamplingAnswers
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins) :
    SamplingAnswerTape :=
  let split := samplingExpandedSplit shape maxStartLength input
  let prelude := samplingPrelude shape maxStartLength fallback r1csDigest
    statement witness split.2.1 split.2.2.1
  let schedule := boundedFreshSchedule shape causalSecret completion witness
    split.2.1 prelude (ProductionMaxPointLength shape maxStartLength)
    (freshSchedule_fits_of_budget shape causalSecret completion witness
      split.2.1 prelude _
      (samplingPrelude_budget shape maxStartLength fallback r1csDigest
        statement witness split.2.1 split.2.2.1 hbudget))
    (freshSchedule_classified shape causalSecret completion witness split.2.1
      prelude (samplingPrelude_isFiatShamir shape maxStartLength fallback
        r1csDigest statement witness split.2.1 split.2.2.1))
  OptionalAdaptiveOracle.run schedule split.1.1 split.1.2

@[simp]
theorem mem_expandedSamplingBad_iff
    [Fintype AdversaryCoins]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins) :
    input ∈ expandedSamplingBad shape maxStartLength fallback r1csDigest
        statement witness causalSecret completion hbudget ↔
      expandedSamplingAnswers shape maxStartLength fallback r1csDigest
        statement witness causalSecret completion hbudget input ∈
          globalBad shape := by
  classical
  rw [expandedSamplingBad, mem_liftFiberBad_iff]
  simp [samplingBadAt, expandedSamplingAnswers]

theorem originalTable_eq_tableOfSplit
    (shape : BatchShape) (maxStartLength : ℕ)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins) :
    input.1.2.1 =
      let split := samplingExpandedSplit shape maxStartLength input
      tableOfSplit (ProductionMaxPointLength shape maxStartLength)
        split.1.1 split.2.2.1 := by
  dsimp [samplingExpandedSplit, tableOfSplit]
  exact (splitSharedOracle
    (ProductionMaxPointLength shape maxStartLength)).symm_apply_apply _ |>.symm

theorem originalPrelude_eq_samplingPrelude
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength) :
    let oracle := answerBounded fallback input.1.2.1
    let outerCommitment := outerRoot shape (baseMessage shape) witness input.1.1
      oracle
    let linearCommitment := linearRoot shape input.1.1 oracle
    preEqualityTranscript (productionStatementDigest statement) r1csDigest
        input.1.1.proofNonce input.1.1.treeNonces.outer
        input.1.1.treeNonces.veilLinear input.1.1.treeNonces.veilHadamard
        outerCommitment linearCommitment =
      let split := samplingExpandedSplit shape maxStartLength input
      samplingPrelude shape maxStartLength fallback r1csDigest statement witness
        split.2.1 split.2.2.1 := by
  let split := samplingExpandedSplit shape maxStartLength input
  have htable := originalTable_eq_tableOfSplit shape maxStartLength input
  rw [htable]
  exact (samplingPrelude_eq_of_samplingTable shape maxStartLength fallback
    r1csDigest statement witness split.2.1 split.1.1 split.2.2.1 houter
    hlinear hnodes).symm

set_option maxRecDepth 20000 in
theorem expandedSamplingAnswers_active
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte) (statement : ProductionStatement shape)
    (witness : Witness shape)
    (causalSecret : ProductionCausalSecret (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement)
    (input : SamplingExpandedTape shape maxStartLength AdversaryCoins)
    (site : Fin productionSamplingSlots) (point : List Byte)
    (hquery : freshSchedule shape causalSecret completion witness input.1.1
      (samplingPrelude shape maxStartLength fallback r1csDigest statement
        witness input.1.1
          (samplingExpandedSplit shape maxStartLength input).2.2.1)
      site
      (priorAnswers
        (expandedSamplingAnswers shape maxStartLength fallback r1csDigest
          statement witness causalSecret completion hbudget input) site) =
        some point) :
    expandedSamplingAnswers shape maxStartLength fallback r1csDigest statement
        witness causalSecret completion hbudget input site =
      answerBounded fallback input.1.2.1 point := by
  let split := samplingExpandedSplit shape maxStartLength input
  let prelude := samplingPrelude shape maxStartLength fallback r1csDigest
    statement witness split.2.1 split.2.2.1
  let hfits := freshSchedule_fits_of_budget shape causalSecret completion witness
    split.2.1 prelude (ProductionMaxPointLength shape maxStartLength)
    (samplingPrelude_budget shape maxStartLength fallback r1csDigest statement
      witness split.2.1 split.2.2.1 hbudget)
  let hclassified := freshSchedule_classified shape causalSecret completion
    witness split.2.1 prelude
      (samplingPrelude_isFiatShamir shape maxStartLength fallback r1csDigest
        statement witness split.2.1 split.2.2.1)
  let schedule := boundedFreshSchedule shape causalSecret completion witness
    split.2.1 prelude (ProductionMaxPointLength shape maxStartLength) hfits
    hclassified
  let answers := OptionalAdaptiveOracle.run schedule split.1.1 split.1.2
  have hanswers : answers = expandedSamplingAnswers shape maxStartLength fallback
      r1csDigest statement witness causalSecret completion hbudget input := by
    rfl
  have hboundedQuery : ∃ bounded,
      schedule site (priorAnswers answers site) = some bounded ∧
        unboundBytes bounded.1 = point := by
    have hquery' : freshSchedule shape causalSecret completion witness
        split.2.1 prelude site (priorAnswers answers site) = some point := by
      simpa [split, samplingExpandedSplit, prelude, hanswers] using hquery
    refine ⟨⟨boundBytes point (hfits site (priorAnswers answers site) point hquery'),
      by simpa [IsSamplingPoint] using
        hclassified site (priorAnswers answers site) point hquery'⟩, ?_, by simp⟩
    simpa only [schedule] using boundedFreshSchedule_of_raw shape causalSecret
      completion witness split.2.1 prelude
        (ProductionMaxPointLength shape maxStartLength) hfits hclassified site
        (priorAnswers answers site) point hquery'
  obtain ⟨bounded, hbounded, hunbound⟩ := hboundedQuery
  have horacle := AdaptiveOracleProgramming.oracle_tracePoint_run
    (compile schedule) (oracleDummyEquiv productionSamplingSlots
      (split.1.1, split.1.2)) site
  change (oracleDummyEquiv productionSamplingSlots (split.1.1, split.1.2))
      (tracePoint (compile schedule) answers site) = answers site at horacle
  rw [tracePoint_compile, hbounded,
    oracleDummyEquiv_real] at horacle
  have htable := originalTable_eq_tableOfSplit shape maxStartLength input
  have hfit : point.length ≤ ProductionMaxPointLength shape maxStartLength := by
    have hboundedLength : (unboundBytes bounded.1).length ≤
        ProductionMaxPointLength shape maxStartLength := by
      simp only [unboundBytes, List.Vector.toList_length]
      exact Nat.le_of_lt_succ bounded.1.1.isLt
    simpa [hunbound] using hboundedLength
  rw [answerBounded_of_le fallback input.1.2.1 point hfit, htable]
  have hboundEq : boundBytes point hfit = bounded.1 := by
    apply unboundBytes_injective
    simpa [hunbound]
  change answers site = tableOfSplit
    (ProductionMaxPointLength shape maxStartLength) split.1.1 split.2.2.1
      (boundBytes point hfit)
  rw [hboundEq]
  simpa [tableOfSplit] using horacle.symm

end VeiledFlock.ProductionSamplingOperationalProbability

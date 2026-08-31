import VeiledFlock.Production.Merkle.EqualitySampler

/-!
# Initial outer/VEIL Merkle hybrid and exact Fiat--Shamir prelude

The transcript before the first programmed zerocheck scalar contains the
outer witness root and the VEIL-linear mask root.  This file composes the two
channel-disjoint salted-leaf permutations, proves both simulated roots equal
their real roots simultaneously, serializes the literal Rust prelude, and
then transports the complete bounded equality-point sampler.
-/

namespace VeiledFlock.ProductionMerklePrelude

open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.NonceSerialization
open VeiledFlock.PairedOracleReplacement
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleTree
open VeiledFlock.ProductionTranscriptFraming

/-! Literal ASCII byte strings used by the production call path. -/

def veilFlockDomain : List Byte :=
  [118, 101, 105, 108, 45, 102, 108, 111, 99, 107, 45, 98, 108, 97, 107,
    101, 51, 45, 112, 114, 101, 105, 109, 97, 103, 101]

def blake3PreimageLabel : List Byte :=
  [102, 108, 111, 99, 107, 45, 98, 108, 97, 107, 101, 51, 45, 112, 114,
    101, 105, 109, 97, 103, 101]

def r1csLabel : List Byte :=
  [102, 108, 111, 99, 107, 45, 114, 49, 99, 115]

def treeNoncesLabel : List Byte :=
  [118, 101, 105, 108, 45, 102, 108, 111, 99, 107, 45, 116, 114, 101,
    101, 45, 110, 111, 110, 99, 101, 115]

def maskRootLabel : List Byte :=
  [118, 101, 105, 108, 45, 102, 108, 111, 99, 107, 45, 109, 97, 115,
    107, 45, 114, 111, 111, 116]

def zerocheckLabel : List Byte :=
  [102, 108, 111, 99, 107, 45, 122, 101, 114, 111, 99, 104, 101, 99, 107]

/-- Exact transcript immediately before `sample_eq_point_bounded`: public
statement binding, outer commitment root, four public nonces, VEIL-linear
root, and the zerocheck label. -/
def preEqualityTranscript (publicDigest r1csDigest : List Byte)
    (proofNonce outerTreeNonce linearTreeNonce hadamardTreeNonce : Nonce256)
    (outerRoot linearRoot : OracleBlock) : List Byte :=
  initTranscript veilFlockDomain ++
    observeLabel blake3PreimageLabel ++ observeBytes publicDigest ++
    observeLabel r1csLabel ++ observeBytes r1csDigest ++
    observeBytes (nonceBytes proofNonce) ++
    observeBytes (oracleBlockBytes outerRoot) ++
    observeLabel treeNoncesLabel ++
    observeBytes (nonceBytes outerTreeNonce) ++
    observeBytes (nonceBytes linearTreeNonce) ++
    observeBytes (nonceBytes hadamardTreeNonce) ++
    observeLabel maskRootLabel ++
    observeBytes (oracleBlockBytes linearRoot) ++
    observeLabel zerocheckLabel

/-- Public bytes preceding the fresh proof nonce in the exact Fiat--Shamir
prelude. -/
def proofNonceHead (publicDigest r1csDigest : List Byte) : List Byte :=
  initTranscript veilFlockDomain ++
    observeLabel blake3PreimageLabel ++ observeBytes publicDigest ++
    observeLabel r1csLabel ++ observeBytes r1csDigest

/-- The remaining fixed-width prelude fields after the proof nonce. -/
def proofNoncePreludeSuffix
    (outerTreeNonce linearTreeNonce hadamardTreeNonce : Nonce256)
    (outerRoot linearRoot : OracleBlock) : List Byte :=
  observeBytes (oracleBlockBytes outerRoot) ++
    observeLabel treeNoncesLabel ++
    observeBytes (nonceBytes outerTreeNonce) ++
    observeBytes (nonceBytes linearTreeNonce) ++
    observeBytes (nonceBytes hadamardTreeNonce) ++
    observeLabel maskRootLabel ++
    observeBytes (oracleBlockBytes linearRoot) ++
    observeLabel zerocheckLabel

/-- The nonce is a literal fixed-offset tagged 41-byte frame inside every
production prelude. -/
theorem preEqualityTranscript_proofNonce_frame
    (publicDigest r1csDigest : List Byte)
    (proofNonce outerTreeNonce linearTreeNonce hadamardTreeNonce : Nonce256)
    (outerRoot linearRoot : OracleBlock) :
    preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
        linearTreeNonce hadamardTreeNonce outerRoot linearRoot =
      fixedOffsetFrame (proofNonceHead publicDigest r1csDigest)
        transcriptNonceFrame
        (fun _ => proofNoncePreludeSuffix outerTreeNonce linearTreeNonce
          hadamardTreeNonce outerRoot linearRoot)
        proofNonce := by
  simp [preEqualityTranscript, proofNonceHead, proofNoncePreludeSuffix,
    fixedOffsetFrame, transcriptNonceFrame, transcriptNoncePrefix,
    observeBytes, encodeLength, encodeLEList]
  decide

/-- Exact public length of the transcript prefix.  Nonces, roots, and their
values do not affect the byte budget because every such field is fixed-width. -/
@[simp] theorem preEqualityTranscript_length
    (publicDigest r1csDigest : List Byte)
    (proofNonce outerTreeNonce linearTreeNonce hadamardTreeNonce : Nonce256)
    (outerRoot linearRoot : OracleBlock) :
    (preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
      linearTreeNonce hadamardTreeNonce outerRoot linearRoot).length =
      publicDigest.length + r1csDigest.length + 432 := by
  simp [preEqualityTranscript, veilFlockDomain, blake3PreimageLabel,
    r1csLabel, treeNoncesLabel, maskRootLabel, zerocheckLabel,
    oracleBlockBytes]
  omega

theorem preEqualityTranscript_isFiatShamir
    (publicDigest r1csDigest : List Byte)
    (proofNonce outerTreeNonce linearTreeNonce hadamardTreeNonce : Nonce256)
    (outerRoot linearRoot : OracleBlock) :
    isFiatShamirPoint
      (preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
        linearTreeNonce hadamardTreeNonce outerRoot linearRoot) := by
  simp [isFiatShamirPoint, preEqualityTranscript, initTranscript,
    veilFlockDomain, opDomain]

/-- One exact salted-leaf channel replacement. -/
noncomputable def replaceTreeOracle (oracle : List Byte → OracleBlock)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : Word64) (depth : ℕ) (hdepth : depth ≤ 64)
    (leftSalts rightSalts : Fin (2 ^ depth) → NumericNonce)
    (leftPayload rightPayload : Fin (2 ^ depth) → List Byte) :
    List Byte → OracleBlock :=
  let leftPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (leftSalts index) (leftPayload index)
  let rightPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (rightSalts index) (rightPayload index)
  let hleft := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth leftSalts leftPayload
  let hright := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth rightSalts rightPayload
  let hcross := fun _left _right equality =>
    productionLeafPoint_cross_index channel treeDepth treeNonce leafLength
      depth hdepth leftSalts rightSalts leftPayload rightPayload equality
  PairedOracleReplacement.renameOracle leftPoint rightPoint hleft hright hcross
    oracle

/-- Outer replacement followed by VEIL-linear replacement. -/
noncomputable def replaceOuterLinearOracle
    (oracle : List Byte → OracleBlock)
    (outerChannel : RoChannel) (outerTreeDepth : Byte)
    (outerTreeNonce : Nonce256) (outerLeafLength : Word64)
    (outerDepth : ℕ) (houterDepth : outerDepth ≤ 64)
    (leftOuterSalts rightOuterSalts : Fin (2 ^ outerDepth) → NumericNonce)
    (leftOuterPayload rightOuterPayload :
      Fin (2 ^ outerDepth) → List Byte)
    (linearChannel : RoChannel) (linearTreeDepth : Byte)
    (linearTreeNonce : Nonce256) (linearLeafLength : Word64)
    (linearDepth : ℕ) (hlinearDepth : linearDepth ≤ 64)
    (leftLinearSalts rightLinearSalts :
      Fin (2 ^ linearDepth) → NumericNonce)
    (leftLinearPayload rightLinearPayload :
      Fin (2 ^ linearDepth) → List Byte) : List Byte → OracleBlock :=
  replaceTreeOracle
    (replaceTreeOracle oracle outerChannel outerTreeDepth outerTreeNonce
      outerLeafLength outerDepth houterDepth leftOuterSalts rightOuterSalts
      leftOuterPayload rightOuterPayload)
    linearChannel linearTreeDepth linearTreeNonce linearLeafLength linearDepth
    hlinearDepth leftLinearSalts rightLinearSalts leftLinearPayload
    rightLinearPayload

/-- Both witness-dependent roots match simultaneously under the composed
channel-disjoint oracle permutation. -/
theorem replaceOuterLinearOracle_roots_exact
    (oracle : List Byte → OracleBlock)
    (outerChannel linearChannel : RoChannel)
    (hchannels : outerChannel ≠ linearChannel)
    (outerTreeDepth linearTreeDepth : Byte)
    (outerTreeNonce linearTreeNonce : Nonce256)
    (outerLeafLength linearLeafLength : Word64)
    (outerDepth linearDepth : ℕ)
    (houterDepth : outerDepth ≤ 64) (hlinearDepth : linearDepth ≤ 64)
    (leftOuterSalts rightOuterSalts : Fin (2 ^ outerDepth) → NumericNonce)
    (leftOuterPayload rightOuterPayload :
      Fin (2 ^ outerDepth) → List Byte)
    (leftLinearSalts rightLinearSalts :
      Fin (2 ^ linearDepth) → NumericNonce)
    (leftLinearPayload rightLinearPayload :
      Fin (2 ^ linearDepth) → List Byte) :
    let replaced := replaceOuterLinearOracle oracle outerChannel
      outerTreeDepth outerTreeNonce outerLeafLength outerDepth houterDepth
      leftOuterSalts rightOuterSalts leftOuterPayload rightOuterPayload
      linearChannel linearTreeDepth linearTreeNonce linearLeafLength
      linearDepth hlinearDepth leftLinearSalts rightLinearSalts
      leftLinearPayload rightLinearPayload
    productionMerkleRoot replaced outerChannel outerTreeDepth outerTreeNonce
          outerLeafLength outerDepth rightOuterSalts rightOuterPayload =
        productionMerkleRoot oracle outerChannel outerTreeDepth outerTreeNonce
          outerLeafLength outerDepth leftOuterSalts leftOuterPayload ∧
      productionMerkleRoot replaced linearChannel linearTreeDepth
          linearTreeNonce linearLeafLength linearDepth rightLinearSalts
          rightLinearPayload =
        productionMerkleRoot oracle linearChannel linearTreeDepth
          linearTreeNonce linearLeafLength linearDepth leftLinearSalts
          leftLinearPayload := by
  classical
  dsimp only [replaceOuterLinearOracle]
  let outerOracle := replaceTreeOracle oracle outerChannel outerTreeDepth
    outerTreeNonce outerLeafLength outerDepth houterDepth leftOuterSalts
    rightOuterSalts leftOuterPayload rightOuterPayload
  let replaced := replaceTreeOracle outerOracle linearChannel linearTreeDepth
    linearTreeNonce linearLeafLength linearDepth hlinearDepth leftLinearSalts
    rightLinearSalts leftLinearPayload rightLinearPayload
  have houterFixed := productionMerkleRoot_pairedOracle_otherChannel
    outerOracle linearChannel linearTreeDepth linearTreeNonce linearLeafLength
    linearDepth hlinearDepth leftLinearSalts rightLinearSalts
    leftLinearPayload rightLinearPayload outerChannel hchannels outerTreeDepth
    outerTreeNonce outerLeafLength outerDepth rightOuterSalts rightOuterPayload
  have houterMatched := productionMerkleRoot_pairedOracle_exact oracle
    outerChannel outerTreeDepth outerTreeNonce outerLeafLength outerDepth
    houterDepth leftOuterSalts rightOuterSalts leftOuterPayload rightOuterPayload
  have hlinearMatched := productionMerkleRoot_pairedOracle_exact outerOracle
    linearChannel linearTreeDepth linearTreeNonce linearLeafLength linearDepth
    hlinearDepth leftLinearSalts rightLinearSalts leftLinearPayload
    rightLinearPayload
  have hlinearFixed := productionMerkleRoot_pairedOracle_otherChannel oracle
    outerChannel outerTreeDepth outerTreeNonce outerLeafLength outerDepth
    houterDepth leftOuterSalts rightOuterSalts leftOuterPayload
    rightOuterPayload linearChannel hchannels.symm linearTreeDepth
    linearTreeNonce linearLeafLength linearDepth leftLinearSalts
    leftLinearPayload
  dsimp only at houterFixed houterMatched hlinearMatched hlinearFixed
  change productionMerkleRoot replaced outerChannel outerTreeDepth
      outerTreeNonce outerLeafLength outerDepth rightOuterSalts
        rightOuterPayload =
      productionMerkleRoot outerOracle outerChannel outerTreeDepth
        outerTreeNonce outerLeafLength outerDepth rightOuterSalts
        rightOuterPayload at houterFixed
  change productionMerkleRoot outerOracle outerChannel outerTreeDepth
      outerTreeNonce outerLeafLength outerDepth rightOuterSalts
        rightOuterPayload =
      productionMerkleRoot oracle outerChannel outerTreeDepth outerTreeNonce
        outerLeafLength outerDepth leftOuterSalts leftOuterPayload at houterMatched
  change productionMerkleRoot replaced linearChannel linearTreeDepth
      linearTreeNonce linearLeafLength linearDepth rightLinearSalts
        rightLinearPayload =
      productionMerkleRoot outerOracle linearChannel linearTreeDepth
        linearTreeNonce linearLeafLength linearDepth leftLinearSalts
        leftLinearPayload at hlinearMatched
  change productionMerkleRoot outerOracle linearChannel linearTreeDepth
      linearTreeNonce linearLeafLength linearDepth leftLinearSalts
        leftLinearPayload =
      productionMerkleRoot oracle linearChannel linearTreeDepth linearTreeNonce
        linearLeafLength linearDepth leftLinearSalts leftLinearPayload at hlinearFixed
  change productionMerkleRoot replaced outerChannel outerTreeDepth
        outerTreeNonce outerLeafLength outerDepth rightOuterSalts
          rightOuterPayload =
        productionMerkleRoot oracle outerChannel outerTreeDepth outerTreeNonce
          outerLeafLength outerDepth leftOuterSalts leftOuterPayload ∧
      productionMerkleRoot replaced linearChannel linearTreeDepth
        linearTreeNonce linearLeafLength linearDepth rightLinearSalts
          rightLinearPayload =
        productionMerkleRoot oracle linearChannel linearTreeDepth
          linearTreeNonce linearLeafLength linearDepth leftLinearSalts
          leftLinearPayload
  exact ⟨houterFixed.trans houterMatched,
    hlinearMatched.trans hlinearFixed⟩

/-- Consequently, the complete byte transcript just before equality-point
sampling is identical for the simulated and real witnesses. -/
theorem replaceOuterLinearOracle_preEqualityTranscript_exact
    (oracle : List Byte → OracleBlock)
    (publicDigest r1csDigest : List Byte)
    (proofNonce hadamardTreeNonce : Nonce256)
    (outerChannel linearChannel : RoChannel)
    (hchannels : outerChannel ≠ linearChannel)
    (outerTreeDepth linearTreeDepth : Byte)
    (outerTreeNonce linearTreeNonce : Nonce256)
    (outerLeafLength linearLeafLength : Word64)
    (outerDepth linearDepth : ℕ)
    (houterDepth : outerDepth ≤ 64) (hlinearDepth : linearDepth ≤ 64)
    (leftOuterSalts rightOuterSalts : Fin (2 ^ outerDepth) → NumericNonce)
    (leftOuterPayload rightOuterPayload :
      Fin (2 ^ outerDepth) → List Byte)
    (leftLinearSalts rightLinearSalts :
      Fin (2 ^ linearDepth) → NumericNonce)
    (leftLinearPayload rightLinearPayload :
      Fin (2 ^ linearDepth) → List Byte) :
    let replaced := replaceOuterLinearOracle oracle outerChannel
      outerTreeDepth outerTreeNonce outerLeafLength outerDepth houterDepth
      leftOuterSalts rightOuterSalts leftOuterPayload rightOuterPayload
      linearChannel linearTreeDepth linearTreeNonce linearLeafLength
      linearDepth hlinearDepth leftLinearSalts rightLinearSalts
      leftLinearPayload rightLinearPayload
    preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
        linearTreeNonce hadamardTreeNonce
        (productionMerkleRoot replaced outerChannel outerTreeDepth
          outerTreeNonce outerLeafLength outerDepth rightOuterSalts
          rightOuterPayload)
        (productionMerkleRoot replaced linearChannel linearTreeDepth
          linearTreeNonce linearLeafLength linearDepth rightLinearSalts
          rightLinearPayload) =
      preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
        linearTreeNonce hadamardTreeNonce
        (productionMerkleRoot oracle outerChannel outerTreeDepth outerTreeNonce
          outerLeafLength outerDepth leftOuterSalts leftOuterPayload)
        (productionMerkleRoot oracle linearChannel linearTreeDepth
          linearTreeNonce linearLeafLength linearDepth leftLinearSalts
          leftLinearPayload) := by
  dsimp only
  obtain ⟨houter, hlinear⟩ := replaceOuterLinearOracle_roots_exact oracle
    outerChannel linearChannel hchannels outerTreeDepth linearTreeDepth
    outerTreeNonce linearTreeNonce outerLeafLength linearLeafLength outerDepth
    linearDepth houterDepth hlinearDepth leftOuterSalts rightOuterSalts
    leftOuterPayload rightOuterPayload leftLinearSalts rightLinearSalts
    leftLinearPayload rightLinearPayload
  rw [houter, hlinear]

/-- The two initial salted commitments and every equality-point rejection
attempt form one exact hybrid: after the composed oracle permutation, the
simulated roots, sampled coordinates, accepted attempt, and final transcript
are byte-for-byte identical to the real execution. -/
theorem replaceOuterLinearOracle_equalitySampler_exact
    (oracle : List Byte → OracleBlock)
    (publicDigest r1csDigest : List Byte)
    (proofNonce hadamardTreeNonce : Nonce256)
    (outerChannel linearChannel : RoChannel)
    (hchannels : outerChannel ≠ linearChannel)
    (outerTreeDepth linearTreeDepth : Byte)
    (outerTreeNonce linearTreeNonce : Nonce256)
    (outerLeafLength linearLeafLength : Word64)
    (outerDepth linearDepth : ℕ)
    (houterDepth : outerDepth ≤ 64) (hlinearDepth : linearDepth ≤ 64)
    (leftOuterSalts rightOuterSalts : Fin (2 ^ outerDepth) → NumericNonce)
    (leftOuterPayload rightOuterPayload :
      Fin (2 ^ outerDepth) → List Byte)
    (leftLinearSalts rightLinearSalts :
      Fin (2 ^ linearDepth) → NumericNonce)
    (leftLinearPayload rightLinearPayload :
      Fin (2 ^ linearDepth) → List Byte)
    (outerLength trials : ℕ) :
    let replaced := replaceOuterLinearOracle oracle outerChannel
      outerTreeDepth outerTreeNonce outerLeafLength outerDepth houterDepth
      leftOuterSalts rightOuterSalts leftOuterPayload rightOuterPayload
      linearChannel linearTreeDepth linearTreeNonce linearLeafLength
      linearDepth hlinearDepth leftLinearSalts rightLinearSalts
      leftLinearPayload rightLinearPayload
    let simulatedTranscript :=
      preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
        linearTreeNonce hadamardTreeNonce
        (productionMerkleRoot replaced outerChannel outerTreeDepth
          outerTreeNonce outerLeafLength outerDepth rightOuterSalts
          rightOuterPayload)
        (productionMerkleRoot replaced linearChannel linearTreeDepth
          linearTreeNonce linearLeafLength linearDepth rightLinearSalts
          rightLinearPayload)
    let realTranscript :=
      preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
        linearTreeNonce hadamardTreeNonce
        (productionMerkleRoot oracle outerChannel outerTreeDepth outerTreeNonce
          outerLeafLength outerDepth leftOuterSalts leftOuterPayload)
        (productionMerkleRoot oracle linearChannel linearTreeDepth
          linearTreeNonce linearLeafLength linearDepth leftLinearSalts
          leftLinearPayload)
    sampleEqualityPointPrefix replaced outerLength trials simulatedTranscript =
      sampleEqualityPointPrefix oracle outerLength trials realTranscript := by
  classical
  dsimp only
  let outerOracle := replaceTreeOracle oracle outerChannel outerTreeDepth
    outerTreeNonce outerLeafLength outerDepth houterDepth leftOuterSalts
    rightOuterSalts leftOuterPayload rightOuterPayload
  let replaced := replaceTreeOracle outerOracle linearChannel linearTreeDepth
    linearTreeNonce linearLeafLength linearDepth hlinearDepth leftLinearSalts
    rightLinearSalts leftLinearPayload rightLinearPayload
  let realTranscript :=
    preEqualityTranscript publicDigest r1csDigest proofNonce outerTreeNonce
      linearTreeNonce hadamardTreeNonce
      (productionMerkleRoot oracle outerChannel outerTreeDepth outerTreeNonce
        outerLeafLength outerDepth leftOuterSalts leftOuterPayload)
      (productionMerkleRoot oracle linearChannel linearTreeDepth linearTreeNonce
        linearLeafLength linearDepth leftLinearSalts leftLinearPayload)
  have htranscript :=
    replaceOuterLinearOracle_preEqualityTranscript_exact oracle publicDigest
      r1csDigest proofNonce hadamardTreeNonce outerChannel linearChannel
      hchannels outerTreeDepth linearTreeDepth outerTreeNonce linearTreeNonce
      outerLeafLength linearLeafLength outerDepth linearDepth houterDepth
      hlinearDepth leftOuterSalts rightOuterSalts leftOuterPayload
      rightOuterPayload leftLinearSalts rightLinearSalts leftLinearPayload
      rightLinearPayload
  dsimp only at htranscript
  rw [htranscript]
  have hfiat : isFiatShamirPoint realTranscript :=
    preEqualityTranscript_isFiatShamir publicDigest r1csDigest proofNonce
      outerTreeNonce linearTreeNonce hadamardTreeNonce
      (productionMerkleRoot oracle outerChannel outerTreeDepth outerTreeNonce
        outerLeafLength outerDepth leftOuterSalts leftOuterPayload)
      (productionMerkleRoot oracle linearChannel linearTreeDepth linearTreeNonce
        linearLeafLength linearDepth leftLinearSalts leftLinearPayload)
  have hlinear := sampleEqualityPointPrefix_pairedOracle_exact outerOracle
    outerLength trials realTranscript hfiat linearChannel linearTreeDepth
    linearTreeNonce linearLeafLength linearDepth hlinearDepth leftLinearSalts
    rightLinearSalts leftLinearPayload rightLinearPayload
  have houter := sampleEqualityPointPrefix_pairedOracle_exact oracle
    outerLength trials realTranscript hfiat outerChannel outerTreeDepth
    outerTreeNonce outerLeafLength outerDepth houterDepth leftOuterSalts
    rightOuterSalts leftOuterPayload rightOuterPayload
  dsimp only [replaceOuterLinearOracle, replaceTreeOracle] at hlinear houter ⊢
  exact hlinear.trans houter

end VeiledFlock.ProductionMerklePrelude

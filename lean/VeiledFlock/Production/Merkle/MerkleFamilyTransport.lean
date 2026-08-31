import VeiledFlock.Production.Nizk.BoundedOracle

/-!
# Arbitrary finite family of production Merkle commitments

The deployed protocol has three initially salted commitment families
(`Witness`, `VeilLinear`, and `VeilHadamard`).  The Hadamard material is
constructed only after earlier transcript challenges are known, so a
hard-coded two-tree hybrid is not compositional enough.  This module treats a
finite, channel-injective family of tree materials as one oracle permutation.
Each material may be an arbitrary function of the complete simulator coin
tape, which permits later challenge-dependent material while retaining one
global finite-domain bijection.
-/

namespace VeiledFlock.ProductionMerkleFamilyTransport

open Function
open VeiledFlock.CoinOracleTransport
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.NonceSerialization
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCombinedMerkleTransport
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleTree
open VeiledFlock.ProductionTranscriptFraming

/-- One site in an arbitrary finite family of perfect production trees. -/
abbrev FamilyIndex (Tree : Type*) (geometry : Tree → TreeGeometry) :=
  Σ tree : Tree, Fin (2 ^ (geometry tree).depth)

noncomputable def familyLeafPoint {Tree Coins : Type*}
    (geometry : Tree → TreeGeometry)
    (material : ∀ tree, TreeMaterial (geometry tree) Coins)
    (coins : Coins) (site : FamilyIndex Tree geometry) : List Byte :=
  leafPoint (geometry site.1) (material site.1) coins site.2

/-- Equality of two family leaf frames recovers the tree channel. -/
theorem familyLeafPoint_channel_eq_of_eq {Tree Coins : Type*}
    (geometry : Tree → TreeGeometry)
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (leftCoins rightCoins : Coins)
    (left right : FamilyIndex Tree geometry)
    (heq : familyLeafPoint geometry leftMaterial leftCoins left =
      familyLeafPoint geometry rightMaterial rightCoins right) :
    (geometry left.1).channel = (geometry right.1).channel := by
  have hquery := encodeMerkleQuery_injective (by
    simpa only [familyLeafPoint, leafPoint, productionLeafPoint] using heq)
  exact congrArg MerkleQuery.channel hquery

theorem familyLeafPoint_injective {Tree Coins : Type*}
    (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (material : ∀ tree, TreeMaterial (geometry tree) Coins)
    (coins : Coins) : Injective (familyLeafPoint geometry material coins) := by
  intro left right heq
  have htree : left.1 = right.1 := hchannels
    (familyLeafPoint_channel_eq_of_eq geometry material material coins coins
      left right heq)
  cases left with
  | mk leftTree leftIndex =>
      cases right with
      | mk rightTree rightIndex =>
          dsimp only at htree
          subst rightTree
          have hindex : leftIndex = rightIndex :=
            productionLeafPoint_index_injective
            (geometry leftTree).channel (geometry leftTree).treeDepth
            (geometry leftTree).treeNonce (geometry leftTree).leafLength
            (geometry leftTree).depth (geometry leftTree).depth_le
            ((material leftTree).salts coins)
            ((material leftTree).payload coins) (by
              simpa [familyLeafPoint, leafPoint] using heq)
          subst rightIndex
          rfl

/-- Cross-family site recovery when both the material and the algebraic coins
have moved. -/
theorem familyLeafPoint_cross {Tree Coins : Type*}
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (coins : Coins) (left right : FamilyIndex Tree geometry)
    (heq : familyLeafPoint geometry leftMaterial coins left =
      familyLeafPoint geometry rightMaterial (coinEquiv coins) right) :
    left = right := by
  have htree : left.1 = right.1 := hchannels
    (familyLeafPoint_channel_eq_of_eq geometry leftMaterial rightMaterial
      coins (coinEquiv coins) left right heq)
  cases left with
  | mk leftTree leftIndex =>
      cases right with
      | mk rightTree rightIndex =>
          dsimp only at htree
          subst rightTree
          have hindex : leftIndex = rightIndex :=
            productionLeafPoint_cross_index
            (geometry leftTree).channel (geometry leftTree).treeDepth
            (geometry leftTree).treeNonce (geometry leftTree).leafLength
            (geometry leftTree).depth (geometry leftTree).depth_le
            ((leftMaterial leftTree).salts coins)
            ((rightMaterial leftTree).salts (coinEquiv coins))
            ((leftMaterial leftTree).payload coins)
            ((rightMaterial leftTree).payload (coinEquiv coins)) (by
              simpa [familyLeafPoint, leafPoint] using heq)
          subst rightIndex
          rfl

def FamilyFits {Tree Coins : Type*} {maxLength : ℕ}
    (geometry : Tree → TreeGeometry)
    (material : ∀ tree, TreeMaterial (geometry tree) Coins) : Prop :=
  ∀ tree, MaterialFits (maxLength := maxLength) (geometry tree)
    (material tree)

noncomputable def boundedFamilyLeafPoint {Tree Coins : Type*}
    {maxLength : ℕ} (geometry : Tree → TreeGeometry)
    (material : ∀ tree, TreeMaterial (geometry tree) Coins)
    (hfits : FamilyFits (maxLength := maxLength) geometry material)
    (coins : Coins) (site : FamilyIndex Tree geometry) :
    BoundedBytes maxLength :=
  boundBytes (familyLeafPoint geometry material coins site) (by
    exact leafPoint_fits (geometry site.1) (material site.1)
      (hfits site.1) coins site.2)

@[simp]
theorem unbound_boundedFamilyLeafPoint {Tree Coins : Type*}
    {maxLength : ℕ} (geometry : Tree → TreeGeometry)
    (material : ∀ tree, TreeMaterial (geometry tree) Coins)
    (hfits : FamilyFits (maxLength := maxLength) geometry material)
    (coins : Coins) (site : FamilyIndex Tree geometry) :
    unboundBytes (boundedFamilyLeafPoint geometry material hfits coins site) =
      familyLeafPoint geometry material coins site := rfl

theorem boundedFamilyLeafPoint_injective {Tree Coins : Type*}
    {maxLength : ℕ} (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (material : ∀ tree, TreeMaterial (geometry tree) Coins)
    (hfits : FamilyFits (maxLength := maxLength) geometry material)
    (coins : Coins) :
    Injective (boundedFamilyLeafPoint geometry material hfits coins) := by
  intro left right heq
  apply familyLeafPoint_injective geometry hchannels material coins
  simpa using congrArg unboundBytes heq

theorem boundedFamilyLeafPoint_cross {Tree Coins : Type*}
    {maxLength : ℕ} (coinEquiv : Coins ≃ Coins)
    (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial)
    (coins : Coins) (left right : FamilyIndex Tree geometry)
    (heq : boundedFamilyLeafPoint geometry leftMaterial hleft coins left =
      boundedFamilyLeafPoint geometry rightMaterial hright
        (coinEquiv coins) right) : left = right := by
  apply familyLeafPoint_cross coinEquiv geometry hchannels leftMaterial
    rightMaterial coins left right
  simpa using congrArg unboundBytes heq

/-- One explicit bijection moves the algebraic tape and every salted Merkle
family in the finite oracle simultaneously. -/
noncomputable def boundedFamilyCoinOracleEquiv
    {Tree Coins : Type*} [Finite Tree] {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial) :
    (Coins × (BoundedBytes maxLength → OracleBlock)) ≃
      (Coins × (BoundedBytes maxLength → OracleBlock)) :=
  CoinOracleTransport.coinOracleEquiv coinEquiv
    (boundedFamilyLeafPoint geometry leftMaterial hleft)
    (boundedFamilyLeafPoint geometry rightMaterial hright)
    (fun coins => boundedFamilyLeafPoint_injective geometry hchannels
      leftMaterial hleft coins)
    (fun coins => boundedFamilyLeafPoint_injective geometry hchannels
      rightMaterial hright coins)
    (fun coins => boundedFamilyLeafPoint_cross coinEquiv geometry hchannels
      leftMaterial rightMaterial hleft hright coins)

/-- Internal nodes of any family member cannot be one of the moved leaves. -/
theorem node_ne_familyLeafPoint {Tree Coins : Type*}
    (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (material : ∀ tree, TreeMaterial (geometry tree) Coins)
    (coins : Coins) (tree : Tree) (level : ℕ)
    (index : Fin (2 ^ level)) (left right : OracleBlock)
    (site : FamilyIndex Tree geometry) :
    productionNodePoint (geometry tree).channel (geometry tree).treeDepth
        (geometry tree).treeNonce level index left right ≠
      familyLeafPoint geometry material coins site := by
  classical
  intro heq
  have hquery := encodeMerkleQuery_injective (by
    simpa only [familyLeafPoint, leafPoint, productionNodePoint,
      productionLeafPoint] using heq)
  have hchannel : (geometry tree).channel = (geometry site.1).channel :=
    congrArg MerkleQuery.channel hquery
  have htree : tree = site.1 := hchannels hchannel
  subst tree
  exact productionNodePoint_ne_leafPoint (geometry site.1).channel
    (geometry site.1).treeDepth (geometry site.1).treeNonce level index left
    right (geometry site.1).leafLength (geometry site.1).depth site.2
    ((material site.1).salts coins site.2)
    ((material site.1).payload coins site.2) heq

/-- Every bounded non-leaf point keeps its answer under the family
transport. -/
theorem boundedFamilyCoinOracleEquiv_answer_off
    {Tree Coins : Type*} [Finite Tree] {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial)
    (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (point : List Byte) (hpoint : point.length ≤ maxLength)
    (hoffLeft : ∀ index,
      point ≠ familyLeafPoint geometry leftMaterial input.1 index)
    (hoffRight : ∀ index,
      point ≠ familyLeafPoint geometry rightMaterial (coinEquiv input.1)
        index) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv geometry
      hchannels leftMaterial rightMaterial hleft hright input
    answerBounded fallback transported.2 point =
      answerBounded fallback input.2 point := by
  classical
  dsimp only
  rw [answerBounded_of_le fallback _ point hpoint,
    answerBounded_of_le fallback _ point hpoint]
  apply CoinOracleTransport.coinOracleEquiv_off
  · intro index heq
    apply hoffLeft index
    simpa using congrArg unboundBytes heq
  · intro index heq
    apply hoffRight index
    simpa using congrArg unboundBytes heq

/-- Every tree root in the family is exactly preserved.  Materials may depend
on the full coin tape, including stored target answers for earlier challenges. -/
theorem boundedFamilyCoinOracleEquiv_roots_exact
    {Tree Coins : Type*} [Finite Tree] {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial)
    (hnodes : 140 ≤ maxLength) (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock)) (tree : Tree) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv geometry
      hchannels leftMaterial rightMaterial hleft hright input
    boundedRoot fallback (geometry tree) (rightMaterial tree)
        (coinEquiv input.1) transported.2 =
      boundedRoot fallback (geometry tree) (leftMaterial tree)
        input.1 input.2 := by
  classical
  dsimp only
  let leftPoint := boundedFamilyLeafPoint geometry leftMaterial hleft
  let rightPoint := boundedFamilyLeafPoint geometry rightMaterial hright
  let hleftInjective := fun coins => boundedFamilyLeafPoint_injective geometry
    hchannels leftMaterial hleft coins
  let hrightInjective := fun coins => boundedFamilyLeafPoint_injective geometry
    hchannels rightMaterial hright coins
  let hcross := fun coins => boundedFamilyLeafPoint_cross coinEquiv geometry
    hchannels leftMaterial rightMaterial hleft hright coins
  let transported := boundedFamilyCoinOracleEquiv coinEquiv geometry hchannels
    leftMaterial rightMaterial hleft hright input
  unfold boundedRoot root productionMerkleRoot
  apply merkleRoot_congr (answerBounded fallback input.2)
    (answerBounded fallback transported.2)
    (productionNodePoint (geometry tree).channel (geometry tree).treeDepth
      (geometry tree).treeNonce)
  · intro level index left right
    exact boundedFamilyCoinOracleEquiv_answer_off coinEquiv geometry hchannels
      leftMaterial rightMaterial hleft hright fallback input
      (productionNodePoint (geometry tree).channel (geometry tree).treeDepth
        (geometry tree).treeNonce level index left right)
      (by simpa using hnodes)
      (node_ne_familyLeafPoint geometry hchannels leftMaterial input.1 tree
        level index left right)
      (node_ne_familyLeafPoint geometry hchannels rightMaterial
        (coinEquiv input.1) tree level index left right)
  · intro index
    change answerBounded fallback transported.2
        (leafPoint (geometry tree) (rightMaterial tree) (coinEquiv input.1)
          index) =
      answerBounded fallback input.2
        (leafPoint (geometry tree) (leftMaterial tree) input.1 index)
    rw [answerBounded_of_le fallback transported.2 _
        (leafPoint_fits (geometry tree) (rightMaterial tree) (hright tree)
          (coinEquiv input.1) index),
      answerBounded_of_le fallback input.2 _
        (leafPoint_fits (geometry tree) (leftMaterial tree) (hleft tree)
          input.1 index)]
    exact CoinOracleTransport.coinOracleEquiv_at_right coinEquiv leftPoint
      rightPoint hleftInjective hrightInjective hcross input ⟨tree, index⟩

/-- Every bounded Fiat--Shamir query is fixed, because its role byte is
disjoint from all family leaves. -/
theorem boundedFamilyCoinOracleEquiv_answer_fiat
    {Tree Coins : Type*} [Finite Tree] {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial)
    (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (point : List Byte) (hfiat : isFiatShamirPoint point)
    (hpoint : point.length ≤ maxLength) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv geometry
      hchannels leftMaterial rightMaterial hleft hright input
    answerBounded fallback transported.2 point =
      answerBounded fallback input.2 point := by
  apply boundedFamilyCoinOracleEquiv_answer_off coinEquiv geometry hchannels
    leftMaterial rightMaterial hleft hright fallback input point hpoint
  · intro site
    exact fiatShamir_ne_merkle hfiat .leaf (geometry site.1).channel
      (geometry site.1).treeDepth (geometry site.1).treeNonce
      (geometry site.1).leafLength (BitVec.ofNat 32 (geometry site.1).depth)
      (BitVec.ofNat 64 site.2.val)
      (nonceBytes
          (numericNonceBytes ((leftMaterial site.1).salts input.1 site.2)) ++
        (leftMaterial site.1).payload input.1 site.2)
  · intro site
    exact fiatShamir_ne_merkle hfiat .leaf (geometry site.1).channel
      (geometry site.1).treeDepth (geometry site.1).treeNonce
      (geometry site.1).leafLength (BitVec.ofNat 32 (geometry site.1).depth)
      (BitVec.ofNat 64 site.2.val)
      (nonceBytes
          (numericNonceBytes
            ((rightMaterial site.1).salts (coinEquiv input.1) site.2)) ++
        (rightMaterial site.1).payload (coinEquiv input.1) site.2)

/-- Every bounded proof-of-work query is fixed by the exact role-byte
separation between `ROLE_POW` and Merkle leaves. -/
theorem boundedFamilyCoinOracleEquiv_answer_pow
    {Tree Coins : Type*} [Finite Tree] {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial)
    (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (state : Nonce256) (nonce : Word64)
    (hpoint : (encodePowPoint state nonce).length ≤ maxLength) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv geometry
      hchannels leftMaterial rightMaterial hleft hright input
    answerBounded fallback transported.2 (encodePowPoint state nonce) =
      answerBounded fallback input.2 (encodePowPoint state nonce) := by
  apply boundedFamilyCoinOracleEquiv_answer_off coinEquiv geometry hchannels
    leftMaterial rightMaterial hleft hright fallback input
    (encodePowPoint state nonce) hpoint
  · intro site
    exact (merkle_ne_pow .leaf (geometry site.1).channel
      (geometry site.1).treeDepth (geometry site.1).treeNonce
      (geometry site.1).leafLength (BitVec.ofNat 32 (geometry site.1).depth)
      (BitVec.ofNat 64 site.2.val)
      (nonceBytes
          (numericNonceBytes ((leftMaterial site.1).salts input.1 site.2)) ++
        (leftMaterial site.1).payload input.1 site.2)
      state nonce).symm
  · intro site
    exact (merkle_ne_pow .leaf (geometry site.1).channel
      (geometry site.1).treeDepth (geometry site.1).treeNonce
      (geometry site.1).leafLength (BitVec.ofNat 32 (geometry site.1).depth)
      (BitVec.ofNat 64 site.2.val)
      (nonceBytes
          (numericNonceBytes
            ((rightMaterial site.1).salts (coinEquiv input.1) site.2)) ++
        (rightMaterial site.1).payload (coinEquiv input.1) site.2)
      state nonce).symm

/-- The complete equality-point rejection sampler is fixed by an arbitrary
finite family transport, assuming its exact byte budget. -/
theorem boundedFamilyCoinOracleEquiv_equalitySampler_exact
    {Tree Coins : Type*} [Finite Tree] {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial)
    (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (outerLength trials : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + 106 +
      trials * (10 + 16 * outerLength) + 18 ≤ maxLength) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv geometry
      hchannels leftMaterial rightMaterial hleft hright input
    sampleEqualityPointPrefix (answerBounded fallback transported.2)
        outerLength trials transcript =
      sampleEqualityPointPrefix (answerBounded fallback input.2)
        outerLength trials transcript := by
  classical
  dsimp only
  apply sampleEqualityPointPrefix_oracle_congr_fiat_bounded
    (answerBounded fallback input.2)
    (answerBounded fallback
      (boundedFamilyCoinOracleEquiv coinEquiv geometry hchannels leftMaterial
        rightMaterial hleft hright input).2)
    outerLength trials maxLength transcript hfiat hbudget
  intro point hpointFiat hpointLength
  exact boundedFamilyCoinOracleEquiv_answer_fiat coinEquiv geometry hchannels
    leftMaterial rightMaterial hleft hright fallback input point hpointFiat
    hpointLength

/-- The arbitrary-family transport preserves the genuinely uniform finite
coin/oracle distribution. -/
theorem uniform_boundedFamilyCoinOracleEquiv
    {Tree Coins : Type*} [Finite Tree] {maxLength : ℕ}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (coinEquiv : Coins ≃ Coins) (geometry : Tree → TreeGeometry)
    (hchannels : Injective (fun tree => (geometry tree).channel))
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (geometry tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength) geometry leftMaterial)
    (hright : FamilyFits (maxLength := maxLength) geometry rightMaterial) :
    (PMF.uniformOfFintype
        (Coins × (BoundedBytes maxLength → OracleBlock))).map
        (boundedFamilyCoinOracleEquiv coinEquiv geometry hchannels leftMaterial
          rightMaterial hleft hright) =
      PMF.uniformOfFintype
        (Coins × (BoundedBytes maxLength → OracleBlock)) := by
  exact CoinOracleTransport.uniform_coinOracleEquiv coinEquiv
    (boundedFamilyLeafPoint geometry leftMaterial hleft)
    (boundedFamilyLeafPoint geometry rightMaterial hright)
    (fun coins => boundedFamilyLeafPoint_injective geometry hchannels
      leftMaterial hleft coins)
    (fun coins => boundedFamilyLeafPoint_injective geometry hchannels
      rightMaterial hright coins)
    (fun coins => boundedFamilyLeafPoint_cross coinEquiv geometry hchannels
      leftMaterial rightMaterial hleft hright coins)

end VeiledFlock.ProductionMerkleFamilyTransport

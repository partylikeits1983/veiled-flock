import VeiledFlock.Oracle.CoinOracleTransport
import VeiledFlock.Oracle.MerkleHiding
import VeiledFlock.Production.Merkle.MerklePrelude

/-!
# Joint outer/VEIL leaf transport along the algebraic simulator

This module combines the outer-witness and VEIL-linear salted leaves into one
injective family.  It then applies the algebraic coin equivalence and the
complement-fixing oracle permutation as one bijection.  The two channels are
framing-disjoint, so a single permutation handles both roots without applying
the algebraic equivalence twice.
-/

namespace VeiledFlock.ProductionCombinedMerkleTransport

open Function
open VeiledFlock.CoinOracleTransport
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.MerkleHiding
open VeiledFlock.NonceSerialization
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionMerkleTree
open VeiledFlock.ProductionTranscriptFraming

/-- Fixed public geometry of one production initial Merkle tree. -/
structure TreeGeometry where
  channel : RoChannel
  treeDepth : Byte
  treeNonce : Nonce256
  leafLength : Word64
  depth : ℕ
  depth_le : depth ≤ 64

/-- Salt and row-payload functions selected by a complete algebraic/random
tape. -/
structure TreeMaterial (geometry : TreeGeometry) (Coins : Type*) where
  salts : Coins → Fin (2 ^ geometry.depth) → NumericNonce
  payload : Coins → Fin (2 ^ geometry.depth) → List Byte

noncomputable def leafPoint {Coins : Type*} (geometry : TreeGeometry)
    (material : TreeMaterial geometry Coins) (coins : Coins)
    (index : Fin (2 ^ geometry.depth)) : List Byte :=
  productionLeafPoint geometry.channel geometry.treeDepth geometry.treeNonce
    geometry.leafLength geometry.depth index (material.salts coins index)
    (material.payload coins index)

noncomputable def root {Coins : Type*} (geometry : TreeGeometry)
    (material : TreeMaterial geometry Coins) (coins : Coins)
    (oracle : List Byte → OracleBlock) : OracleBlock :=
  productionMerkleRoot oracle geometry.channel geometry.treeDepth
    geometry.treeNonce geometry.leafLength geometry.depth
    (material.salts coins) (material.payload coins)

/-- Outer sites and VEIL-linear sites in one finite family. -/
abbrev CombinedIndex (outer linear : TreeGeometry) :=
  Fin (2 ^ outer.depth) ⊕ Fin (2 ^ linear.depth)

noncomputable def combinedLeafPoint {Coins : Type*}
    (outer linear : TreeGeometry)
    (outerMaterial : TreeMaterial outer Coins)
    (linearMaterial : TreeMaterial linear Coins) (coins : Coins) :
    CombinedIndex outer linear → List Byte :=
  Sum.elim (leafPoint outer outerMaterial coins)
    (leafPoint linear linearMaterial coins)

theorem leafPoint_injective {Coins : Type*} (geometry : TreeGeometry)
    (material : TreeMaterial geometry Coins) (coins : Coins) :
    Function.Injective (leafPoint geometry material coins) := by
  exact productionLeafPoint_index_injective geometry.channel
    geometry.treeDepth geometry.treeNonce geometry.leafLength geometry.depth
    geometry.depth_le (material.salts coins) (material.payload coins)

theorem leafPoint_ne_of_channel_ne {Coins : Type*}
    (left right : TreeGeometry) (hchannel : left.channel ≠ right.channel)
    (leftMaterial : TreeMaterial left Coins)
    (rightMaterial : TreeMaterial right Coins)
    (leftCoins rightCoins : Coins)
    (leftIndex : Fin (2 ^ left.depth))
    (rightIndex : Fin (2 ^ right.depth)) :
    leafPoint left leftMaterial leftCoins leftIndex ≠
      leafPoint right rightMaterial rightCoins rightIndex := by
  exact productionMerklePoint_ne_leafPoint_of_channel_ne .leaf left.channel
    right.channel hchannel left.treeDepth left.treeNonce left.leafLength
    (BitVec.ofNat 32 left.depth) (BitVec.ofNat 64 leftIndex.val)
    (nonceBytes (numericNonceBytes (leftMaterial.salts leftCoins leftIndex)) ++
      leftMaterial.payload leftCoins leftIndex)
    right.treeDepth right.treeNonce right.leafLength right.depth rightIndex
    (rightMaterial.salts rightCoins rightIndex)
    (rightMaterial.payload rightCoins rightIndex)

theorem combinedLeafPoint_injective {Coins : Type*}
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (outerMaterial : TreeMaterial outer Coins)
    (linearMaterial : TreeMaterial linear Coins) (coins : Coins) :
    Function.Injective
      (combinedLeafPoint outer linear outerMaterial linearMaterial coins) := by
  intro left right heq
  cases left with
  | inl leftOuter =>
      cases right with
      | inl rightOuter =>
          congr 1
          exact leafPoint_injective outer outerMaterial coins heq
      | inr rightLinear =>
          exact False.elim
            (leafPoint_ne_of_channel_ne outer linear hchannels outerMaterial
              linearMaterial coins coins leftOuter rightLinear heq)
  | inr leftLinear =>
      cases right with
      | inl rightOuter =>
          exact False.elim
            (leafPoint_ne_of_channel_ne outer linear hchannels outerMaterial
              linearMaterial coins coins rightOuter leftLinear heq.symm)
      | inr rightLinear =>
          congr 1
          exact leafPoint_injective linear linearMaterial coins heq

/-- Cross-family recovery after the algebraic coins have moved. -/
theorem combinedLeafPoint_cross {Coins : Type*}
    (coinEquiv : Coins ≃ Coins)
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (leftOuter : TreeMaterial outer Coins)
    (leftLinear : TreeMaterial linear Coins)
    (rightOuter : TreeMaterial outer Coins)
    (rightLinear : TreeMaterial linear Coins)
    (coins : Coins) (leftIndex rightIndex : CombinedIndex outer linear)
    (heq :
      combinedLeafPoint outer linear leftOuter leftLinear coins leftIndex =
        combinedLeafPoint outer linear rightOuter rightLinear
          (coinEquiv coins) rightIndex) :
    leftIndex = rightIndex := by
  cases leftIndex with
  | inl leftOuterIndex =>
      cases rightIndex with
      | inl rightOuterIndex =>
          congr 1
          exact productionLeafPoint_cross_index outer.channel outer.treeDepth
            outer.treeNonce outer.leafLength outer.depth outer.depth_le
            (leftOuter.salts coins) (rightOuter.salts (coinEquiv coins))
            (leftOuter.payload coins) (rightOuter.payload (coinEquiv coins))
            (by simpa [combinedLeafPoint, leafPoint] using heq)
      | inr rightLinearIndex =>
          exact False.elim
            (leafPoint_ne_of_channel_ne outer linear hchannels leftOuter
              rightLinear coins (coinEquiv coins) leftOuterIndex
              rightLinearIndex
              (by simpa [combinedLeafPoint] using heq))
  | inr leftLinearIndex =>
      cases rightIndex with
      | inl rightOuterIndex =>
          exact False.elim
            (leafPoint_ne_of_channel_ne linear outer hchannels.symm leftLinear
              rightOuter coins (coinEquiv coins) leftLinearIndex
              rightOuterIndex
              (by simpa [combinedLeafPoint] using heq))
      | inr rightLinearIndex =>
          congr 1
          exact productionLeafPoint_cross_index linear.channel linear.treeDepth
            linear.treeNonce linear.leafLength linear.depth linear.depth_le
            (leftLinear.salts coins) (rightLinear.salts (coinEquiv coins))
            (leftLinear.payload coins) (rightLinear.payload (coinEquiv coins))
            (by simpa [combinedLeafPoint, leafPoint] using heq)

/-- The load-bearing joint bijection: move all algebraic simulator coins and
both initial hidden-leaf families in the same uniform coin transformation. -/
noncomputable def combinedCoinOracleEquiv {Coins : Type*}
    (coinEquiv : Coins ≃ Coins)
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (leftOuter : TreeMaterial outer Coins)
    (leftLinear : TreeMaterial linear Coins)
    (rightOuter : TreeMaterial outer Coins)
    (rightLinear : TreeMaterial linear Coins) :
    (Coins × (List Byte → OracleBlock)) ≃
      (Coins × (List Byte → OracleBlock)) :=
  CoinOracleTransport.coinOracleEquiv coinEquiv
    (combinedLeafPoint outer linear leftOuter leftLinear)
    (combinedLeafPoint outer linear rightOuter rightLinear)
    (fun coins =>
      combinedLeafPoint_injective outer linear hchannels leftOuter leftLinear
        coins)
    (fun coins =>
      combinedLeafPoint_injective outer linear hchannels rightOuter rightLinear
        coins)
    (fun coins => combinedLeafPoint_cross coinEquiv outer linear hchannels
      leftOuter leftLinear rightOuter rightLinear coins)

theorem outerNode_ne_combinedLeaf {Coins : Type*}
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (outerMaterial : TreeMaterial outer Coins)
    (linearMaterial : TreeMaterial linear Coins) (coins : Coins)
    (level : ℕ) (index : Fin (2 ^ level))
    (left right : OracleBlock) (site : CombinedIndex outer linear) :
    productionNodePoint outer.channel outer.treeDepth outer.treeNonce level
        index left right ≠
      combinedLeafPoint outer linear outerMaterial linearMaterial coins site := by
  cases site with
  | inl outerIndex =>
      exact productionNodePoint_ne_leafPoint outer.channel outer.treeDepth
        outer.treeNonce level index left right outer.leafLength outer.depth
        outerIndex (outerMaterial.salts coins outerIndex)
        (outerMaterial.payload coins outerIndex)
  | inr linearIndex =>
      exact productionMerklePoint_ne_leafPoint_of_channel_ne .node
        outer.channel linear.channel hchannels outer.treeDepth outer.treeNonce
        (BitVec.ofNat 64 64) (BitVec.ofNat 32 level)
        (BitVec.ofNat 64 index.val)
        (oracleBlockBytes left ++ oracleBlockBytes right) linear.treeDepth
        linear.treeNonce linear.leafLength linear.depth linearIndex
        (linearMaterial.salts coins linearIndex)
        (linearMaterial.payload coins linearIndex)

theorem linearNode_ne_combinedLeaf {Coins : Type*}
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (outerMaterial : TreeMaterial outer Coins)
    (linearMaterial : TreeMaterial linear Coins) (coins : Coins)
    (level : ℕ) (index : Fin (2 ^ level))
    (left right : OracleBlock) (site : CombinedIndex outer linear) :
    productionNodePoint linear.channel linear.treeDepth linear.treeNonce level
        index left right ≠
      combinedLeafPoint outer linear outerMaterial linearMaterial coins site := by
  cases site with
  | inl outerIndex =>
      exact productionMerklePoint_ne_leafPoint_of_channel_ne .node
        linear.channel outer.channel hchannels.symm linear.treeDepth
        linear.treeNonce (BitVec.ofNat 64 64) (BitVec.ofNat 32 level)
        (BitVec.ofNat 64 index.val)
        (oracleBlockBytes left ++ oracleBlockBytes right) outer.treeDepth
        outer.treeNonce outer.leafLength outer.depth outerIndex
        (outerMaterial.salts coins outerIndex)
        (outerMaterial.payload coins outerIndex)
  | inr linearIndex =>
      exact productionNodePoint_ne_leafPoint linear.channel linear.treeDepth
        linear.treeNonce level index left right linear.leafLength linear.depth
        linearIndex (linearMaterial.salts coins linearIndex)
        (linearMaterial.payload coins linearIndex)

/-- The joint coin/oracle transport makes both initial roots exactly equal. -/
theorem combinedCoinOracleEquiv_roots_exact {Coins : Type*}
    (coinEquiv : Coins ≃ Coins)
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (leftOuter : TreeMaterial outer Coins)
    (leftLinear : TreeMaterial linear Coins)
    (rightOuter : TreeMaterial outer Coins)
    (rightLinear : TreeMaterial linear Coins)
    (input : Coins × (List Byte → OracleBlock)) :
    let transported := combinedCoinOracleEquiv coinEquiv outer linear
      hchannels leftOuter leftLinear rightOuter rightLinear input
    root outer rightOuter (coinEquiv input.1) transported.2 =
        root outer leftOuter input.1 input.2 ∧
      root linear rightLinear (coinEquiv input.1) transported.2 =
        root linear leftLinear input.1 input.2 := by
  classical
  dsimp only
  let leftPoint := combinedLeafPoint outer linear leftOuter leftLinear
  let rightPoint := combinedLeafPoint outer linear rightOuter rightLinear
  let hleft := fun coins => combinedLeafPoint_injective outer linear hchannels
    leftOuter leftLinear coins
  let hright := fun coins => combinedLeafPoint_injective outer linear hchannels
    rightOuter rightLinear coins
  let hcross := fun coins => combinedLeafPoint_cross coinEquiv outer linear
    hchannels leftOuter leftLinear rightOuter rightLinear coins
  let transported := combinedCoinOracleEquiv coinEquiv outer linear hchannels
    leftOuter leftLinear rightOuter rightLinear input
  constructor
  · unfold root productionMerkleRoot
    apply merkleRoot_congr input.2 transported.2
      (productionNodePoint outer.channel outer.treeDepth outer.treeNonce)
    · intro level index left right
      exact CoinOracleTransport.coinOracleEquiv_off coinEquiv leftPoint
        rightPoint hleft hright hcross input
        (productionNodePoint outer.channel outer.treeDepth outer.treeNonce
          level index left right)
        (outerNode_ne_combinedLeaf outer linear hchannels leftOuter leftLinear
          input.1 level index left right)
        (outerNode_ne_combinedLeaf outer linear hchannels rightOuter rightLinear
          (coinEquiv input.1) level index left right)
    · intro index
      exact CoinOracleTransport.coinOracleEquiv_at_right coinEquiv leftPoint
        rightPoint hleft hright hcross input (Sum.inl index)
  · unfold root productionMerkleRoot
    apply merkleRoot_congr input.2 transported.2
      (productionNodePoint linear.channel linear.treeDepth linear.treeNonce)
    · intro level index left right
      exact CoinOracleTransport.coinOracleEquiv_off coinEquiv leftPoint
        rightPoint hleft hright hcross input
        (productionNodePoint linear.channel linear.treeDepth linear.treeNonce
          level index left right)
        (linearNode_ne_combinedLeaf outer linear hchannels leftOuter leftLinear
          input.1 level index left right)
        (linearNode_ne_combinedLeaf outer linear hchannels rightOuter rightLinear
          (coinEquiv input.1) level index left right)
    · intro index
      exact CoinOracleTransport.coinOracleEquiv_at_right coinEquiv leftPoint
        rightPoint hleft hright hcross input (Sum.inr index)

/-- The exact Rust statement/nonce/root prelude is preserved by the joint
algebraic-coin and oracle transport. -/
theorem combinedCoinOracleEquiv_preEqualityTranscript_exact {Coins : Type*}
    (coinEquiv : Coins ≃ Coins)
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (leftOuter : TreeMaterial outer Coins)
    (leftLinear : TreeMaterial linear Coins)
    (rightOuter : TreeMaterial outer Coins)
    (rightLinear : TreeMaterial linear Coins)
    (publicDigest r1csDigest : List Byte)
    (proofNonce hadamardTreeNonce : Nonce256)
    (input : Coins × (List Byte → OracleBlock)) :
    let transported := combinedCoinOracleEquiv coinEquiv outer linear
      hchannels leftOuter leftLinear rightOuter rightLinear input
    preEqualityTranscript publicDigest r1csDigest proofNonce outer.treeNonce
        linear.treeNonce hadamardTreeNonce
        (root outer rightOuter (coinEquiv input.1) transported.2)
        (root linear rightLinear (coinEquiv input.1) transported.2) =
      preEqualityTranscript publicDigest r1csDigest proofNonce outer.treeNonce
        linear.treeNonce hadamardTreeNonce
        (root outer leftOuter input.1 input.2)
        (root linear leftLinear input.1 input.2) := by
  dsimp only
  obtain ⟨houter, hlinear⟩ := combinedCoinOracleEquiv_roots_exact coinEquiv
    outer linear hchannels leftOuter leftLinear rightOuter rightLinear input
  rw [houter, hlinear]

/-- Load-bearing pre-programming identity.  Under the single uniform
coin/oracle bijection, both hidden roots, every bounded equality-point
attempt, the selected coordinates, and the absorbed transcript immediately
before the masked round-one messages are exactly equal. -/
theorem combinedCoinOracleEquiv_equalitySampler_exact {Coins : Type*}
    (coinEquiv : Coins ≃ Coins)
    (outer linear : TreeGeometry)
    (hchannels : outer.channel ≠ linear.channel)
    (leftOuter : TreeMaterial outer Coins)
    (leftLinear : TreeMaterial linear Coins)
    (rightOuter : TreeMaterial outer Coins)
    (rightLinear : TreeMaterial linear Coins)
    (publicDigest r1csDigest : List Byte)
    (proofNonce hadamardTreeNonce : Nonce256)
    (outerLength trials : ℕ)
    (input : Coins × (List Byte → OracleBlock)) :
    let transported := combinedCoinOracleEquiv coinEquiv outer linear
      hchannels leftOuter leftLinear rightOuter rightLinear input
    let simulatedTranscript :=
      preEqualityTranscript publicDigest r1csDigest proofNonce outer.treeNonce
        linear.treeNonce hadamardTreeNonce
        (root outer rightOuter (coinEquiv input.1) transported.2)
        (root linear rightLinear (coinEquiv input.1) transported.2)
    let realTranscript :=
      preEqualityTranscript publicDigest r1csDigest proofNonce outer.treeNonce
        linear.treeNonce hadamardTreeNonce
        (root outer leftOuter input.1 input.2)
        (root linear leftLinear input.1 input.2)
    sampleEqualityPointPrefix transported.2 outerLength trials
        simulatedTranscript =
      sampleEqualityPointPrefix input.2 outerLength trials realTranscript := by
  classical
  dsimp only
  let transported := combinedCoinOracleEquiv coinEquiv outer linear hchannels
    leftOuter leftLinear rightOuter rightLinear input
  let realTranscript :=
    preEqualityTranscript publicDigest r1csDigest proofNonce outer.treeNonce
      linear.treeNonce hadamardTreeNonce
      (root outer leftOuter input.1 input.2)
      (root linear leftLinear input.1 input.2)
  have htranscript := combinedCoinOracleEquiv_preEqualityTranscript_exact
    coinEquiv outer linear hchannels leftOuter leftLinear rightOuter rightLinear
    publicDigest r1csDigest proofNonce hadamardTreeNonce input
  dsimp only at htranscript
  rw [htranscript]
  let leftPoint := combinedLeafPoint outer linear leftOuter leftLinear input.1
  let rightPoint := combinedLeafPoint outer linear rightOuter rightLinear
    (coinEquiv input.1)
  let hleft := combinedLeafPoint_injective outer linear hchannels leftOuter
    leftLinear input.1
  let hright := combinedLeafPoint_injective outer linear hchannels rightOuter
    rightLinear (coinEquiv input.1)
  let hcross := combinedLeafPoint_cross coinEquiv outer linear hchannels
    leftOuter leftLinear rightOuter rightLinear input.1
  have hfiat : isFiatShamirPoint realTranscript :=
    preEqualityTranscript_isFiatShamir publicDigest r1csDigest proofNonce
      outer.treeNonce linear.treeNonce hadamardTreeNonce
      (root outer leftOuter input.1 input.2)
      (root linear leftLinear input.1 input.2)
  have hoffLeft : ∀ current (hcurrent : isFiatShamirPoint current)
      squeezeLength counter index,
      slicePoint current squeezeLength counter ≠ leftPoint index := by
    intro current hcurrent squeezeLength counter index
    cases index with
    | inl outerIndex =>
        exact slicePoint_ne_productionLeafPoint hcurrent squeezeLength counter
          outer.channel outer.treeDepth outer.treeNonce outer.leafLength
          outer.depth outerIndex (leftOuter.salts input.1 outerIndex)
          (leftOuter.payload input.1 outerIndex)
    | inr linearIndex =>
        exact slicePoint_ne_productionLeafPoint hcurrent squeezeLength counter
          linear.channel linear.treeDepth linear.treeNonce linear.leafLength
          linear.depth linearIndex (leftLinear.salts input.1 linearIndex)
          (leftLinear.payload input.1 linearIndex)
  have hoffRight : ∀ current (hcurrent : isFiatShamirPoint current)
      squeezeLength counter index,
      slicePoint current squeezeLength counter ≠ rightPoint index := by
    intro current hcurrent squeezeLength counter index
    cases index with
    | inl outerIndex =>
        exact slicePoint_ne_productionLeafPoint hcurrent squeezeLength counter
          outer.channel outer.treeDepth outer.treeNonce outer.leafLength
          outer.depth outerIndex
          (rightOuter.salts (coinEquiv input.1) outerIndex)
          (rightOuter.payload (coinEquiv input.1) outerIndex)
    | inr linearIndex =>
        exact slicePoint_ne_productionLeafPoint hcurrent squeezeLength counter
          linear.channel linear.treeDepth linear.treeNonce linear.leafLength
          linear.depth linearIndex
          (rightLinear.salts (coinEquiv input.1) linearIndex)
          (rightLinear.payload (coinEquiv input.1) linearIndex)
  have hsampler :=
    sampleEqualityPointPrefix_renameOracle_off_exact input.2 leftPoint
      rightPoint hleft hright hcross outerLength trials realTranscript hfiat
      hoffLeft hoffRight
  dsimp only [transported, combinedCoinOracleEquiv,
    CoinOracleTransport.coinOracleEquiv] at hsampler ⊢
  exact hsampler

end VeiledFlock.ProductionCombinedMerkleTransport

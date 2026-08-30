import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Concrete.NonceSerialization
import VeiledFlock.Oracle.PairedOracleReplacement
import VeiledFlock.Production.Core.Framing

/-!
# Exact production salted-Merkle replacement

This file mirrors the mathematical data flow of
`merkle_tree_framed_salted`: independently salted leaf payloads are queried
at `ROLE_LEAF`, adjacent answers are concatenated, and each parent is queried
at `ROLE_NODE` with its exact level and index.  The root theorem uses the
pairwise oracle permutation: it maps every real leaf input to its simulated
counterpart and fixes every internal-node input.
-/

namespace VeiledFlock.ProductionMerkleTree

open Function
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.NonceSerialization
open VeiledFlock.PairedOracleReplacement
open VeiledFlock.ProductionFraming

variable {Point Outcome : Type*}

/-- Even child of a node at a perfect binary-tree level. -/
def leftChildIndex {level : ℕ} (index : Fin (2 ^ level)) :
    Fin (2 ^ (level + 1)) :=
  ⟨2 * index.val, by
    rw [pow_succ]
    omega⟩

/-- Odd child of a node at a perfect binary-tree level. -/
def rightChildIndex {level : ℕ} (index : Fin (2 ^ level)) :
    Fin (2 ^ (level + 1)) :=
  ⟨2 * index.val + 1, by
    rw [pow_succ]
    omega⟩

/-- Bottom-up evaluation of a perfect binary Merkle tree.  At the successor
case, `level` is exactly the parent level used by Rust: leaves are at the
original depth, their parents at `depth - 1`, and the root at level zero. -/
def merkleRoot (oracle : Point → Outcome)
    (nodePoint : ∀ level, Fin (2 ^ level) → Outcome → Outcome → Point) :
    (depth : ℕ) → (Fin (2 ^ depth) → Outcome) → Outcome
  | 0, leaves => leaves ⟨0, by norm_num⟩
  | depth + 1, leaves =>
      merkleRoot oracle nodePoint depth fun index =>
        oracle (nodePoint depth index
          (leaves (leftChildIndex index))
          (leaves (rightChildIndex index)))

/-- If corresponding leaf answers agree and both oracles agree at every
internal-node query, all internal levels and the final root agree. -/
theorem merkleRoot_congr
    (leftOracle rightOracle : Point → Outcome)
    (nodePoint : ∀ level, Fin (2 ^ level) → Outcome → Outcome → Point)
    (hnode : ∀ level index left right,
      rightOracle (nodePoint level index left right) =
        leftOracle (nodePoint level index left right)) :
    ∀ (depth : ℕ)
      (leftLeaves rightLeaves : Fin (2 ^ depth) → Outcome),
      (∀ index, rightLeaves index = leftLeaves index) →
        merkleRoot rightOracle nodePoint depth rightLeaves =
          merkleRoot leftOracle nodePoint depth leftLeaves
  | 0, leftLeaves, rightLeaves, hleaves => by
      exact hleaves ⟨0, by norm_num⟩
  | depth + 1, leftLeaves, rightLeaves, hleaves => by
      simp only [merkleRoot]
      apply merkleRoot_congr leftOracle rightOracle nodePoint hnode depth
      intro index
      rw [hleaves (leftChildIndex index),
        hleaves (rightChildIndex index), hnode]

def oracleBlockBytes (block : OracleBlock) : List Byte :=
  List.ofFn block

@[simp]
theorem oracleBlockBytes_length (block : OracleBlock) :
    (oracleBlockBytes block).length = 32 := by
  simp [oracleBlockBytes]

/-- Exact `ROLE_LEAF` query issued by `merkle_tree_framed_salted`.  The
header's `leafLength` is the salted leaf length, while the payload is
`salt(32) ‖ row`. -/
noncomputable def productionLeafQuery (channel : RoChannel) (treeDepth : Byte)
    (treeNonce : Nonce256) (leafLength : Word64) (depth : ℕ)
    (index : Fin (2 ^ depth)) (salt : NumericNonce)
    (payload : List Byte) : MerkleQuery where
  role := .leaf
  channel := channel
  treeDepth := treeDepth
  treeNonce := treeNonce
  leafLength := leafLength
  level := BitVec.ofNat 32 depth
  index := BitVec.ofNat 64 index.val
  payload := nonceBytes (numericNonceBytes salt) ++ payload

noncomputable def productionLeafPoint (channel : RoChannel) (treeDepth : Byte)
    (treeNonce : Nonce256) (leafLength : Word64) (depth : ℕ)
    (index : Fin (2 ^ depth)) (salt : NumericNonce)
    (payload : List Byte) : List Byte :=
  encodeMerkleQuery
    (productionLeafQuery channel treeDepth treeNonce leafLength depth index
      salt payload)

@[simp]
theorem productionLeafPoint_length (channel : RoChannel) (treeDepth : Byte)
    (treeNonce : Nonce256) (leafLength : Word64) (depth : ℕ)
    (index : Fin (2 ^ depth)) (salt : NumericNonce)
    (payload : List Byte) :
    (productionLeafPoint channel treeDepth treeNonce leafLength depth index
      salt payload).length = 108 + payload.length := by
  simp [productionLeafPoint, productionLeafQuery, encodeMerkleQuery,
    encodeMerklePoint]
  omega

/-- Exact `ROLE_NODE` query.  Rust fixes the header payload length to 64 and
concatenates the two 32-byte child answers. -/
def productionNodeQuery (channel : RoChannel) (treeDepth : Byte)
    (treeNonce : Nonce256) (level : ℕ) (index : Fin (2 ^ level))
    (left right : OracleBlock) : MerkleQuery where
  role := .node
  channel := channel
  treeDepth := treeDepth
  treeNonce := treeNonce
  leafLength := BitVec.ofNat 64 64
  level := BitVec.ofNat 32 level
  index := BitVec.ofNat 64 index.val
  payload := oracleBlockBytes left ++ oracleBlockBytes right

def productionNodePoint (channel : RoChannel) (treeDepth : Byte)
    (treeNonce : Nonce256) (level : ℕ) (index : Fin (2 ^ level))
    (left right : OracleBlock) : List Byte :=
  encodeMerkleQuery
    (productionNodeQuery channel treeDepth treeNonce level index left right)

@[simp]
theorem productionNodePoint_length (channel : RoChannel) (treeDepth : Byte)
    (treeNonce : Nonce256) (level : ℕ) (index : Fin (2 ^ level))
    (left right : OracleBlock) :
    (productionNodePoint channel treeDepth treeNonce level index left right).length =
      140 := by
  simp [productionNodePoint, productionNodeQuery, encodeMerkleQuery,
    encodeMerklePoint]

private theorem bitVecOfNat_eq_of_lt {width left right : ℕ}
    (hleft : left < 2 ^ width) (hright : right < 2 ^ width)
    (heq : BitVec.ofNat width left = BitVec.ofNat width right) :
    left = right := by
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hnat
  exact hnat

/-- The encoded 64-bit leaf location recovers the mathematical site for every
production-sized tree. -/
theorem productionLeafPoint_index_injective
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : Word64) (depth : ℕ) (hdepth : depth ≤ 64)
    (salts : Fin (2 ^ depth) → NumericNonce)
    (payload : Fin (2 ^ depth) → List Byte) :
    Function.Injective (fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (salts index) (payload index)) := by
  intro left right heq
  have hquery := encodeMerkleQuery_injective heq
  have hindex := congrArg MerkleQuery.index hquery
  change BitVec.ofNat 64 left.val = BitVec.ofNat 64 right.val at hindex
  apply Fin.ext
  apply bitVecOfNat_eq_of_lt
  · exact lt_of_lt_of_le left.isLt
      (Nat.pow_le_pow_right (by decide) hdepth)
  · exact lt_of_lt_of_le right.isLt
      (Nat.pow_le_pow_right (by decide) hdepth)
  · exact hindex

/-- Real and simulated leaf families may contain unrelated salts and payloads;
equality of two framed points still recovers their common leaf index. -/
theorem productionLeafPoint_cross_index
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : Word64) (depth : ℕ) (hdepth : depth ≤ 64)
    (leftSalts rightSalts : Fin (2 ^ depth) → NumericNonce)
    (leftPayload rightPayload : Fin (2 ^ depth) → List Byte)
    {left right : Fin (2 ^ depth)}
    (heq :
      productionLeafPoint channel treeDepth treeNonce leafLength depth left
          (leftSalts left) (leftPayload left) =
        productionLeafPoint channel treeDepth treeNonce leafLength depth right
          (rightSalts right) (rightPayload right)) :
    left = right := by
  have hquery := encodeMerkleQuery_injective heq
  have hindex := congrArg MerkleQuery.index hquery
  change BitVec.ofNat 64 left.val = BitVec.ofNat 64 right.val at hindex
  apply Fin.ext
  apply bitVecOfNat_eq_of_lt
  · exact lt_of_lt_of_le left.isLt
      (Nat.pow_le_pow_right (by decide) hdepth)
  · exact lt_of_lt_of_le right.isLt
      (Nat.pow_le_pow_right (by decide) hdepth)
  · exact hindex

/-- Role separation makes every internal-node point lie outside every salted
leaf family, regardless of payloads, positions, or salts. -/
theorem productionNodePoint_ne_leafPoint
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (level : ℕ) (nodeIndex : Fin (2 ^ level))
    (left right : OracleBlock) (leafLength : Word64) (depth : ℕ)
    (leafIndex : Fin (2 ^ depth)) (salt : NumericNonce)
    (payload : List Byte) :
    productionNodePoint channel treeDepth treeNonce level nodeIndex left right ≠
      productionLeafPoint channel treeDepth treeNonce leafLength depth
        leafIndex salt payload := by
  intro heq
  have hquery := encodeMerkleQuery_injective heq
  have hrole := congrArg MerkleQuery.role hquery
  simp [productionNodeQuery, productionLeafQuery] at hrole

/-- Distinct `RoChannel` discriminants make every point of another Merkle
tree disjoint from the selected hidden-leaf family, including both leaves and
internal nodes. -/
theorem productionMerklePoint_ne_leafPoint_of_channel_ne
    (otherRole : MerkleRole)
    (otherChannel hiddenChannel : RoChannel)
    (hchannel : otherChannel ≠ hiddenChannel)
    (otherTreeDepth : Byte) (otherTreeNonce : Nonce256)
    (otherLeafLength : Word64) (otherLevel : Word32)
    (otherIndex : Word64) (otherPayload : List Byte)
    (hiddenTreeDepth : Byte) (hiddenTreeNonce : Nonce256)
    (hiddenLeafLength : Word64) (hiddenDepth : ℕ)
    (hiddenIndex : Fin (2 ^ hiddenDepth)) (hiddenSalt : NumericNonce)
    (hiddenPayload : List Byte) :
    encodeMerklePoint otherRole otherChannel otherTreeDepth otherTreeNonce
        otherLeafLength otherLevel otherIndex otherPayload ≠
      productionLeafPoint hiddenChannel hiddenTreeDepth hiddenTreeNonce
        hiddenLeafLength hiddenDepth hiddenIndex hiddenSalt hiddenPayload := by
  intro heq
  change encodeMerkleQuery
      { role := otherRole
        channel := otherChannel
        treeDepth := otherTreeDepth
        treeNonce := otherTreeNonce
        leafLength := otherLeafLength
        level := otherLevel
        index := otherIndex
        payload := otherPayload } =
    encodeMerkleQuery
      (productionLeafQuery hiddenChannel hiddenTreeDepth hiddenTreeNonce
        hiddenLeafLength hiddenDepth hiddenIndex hiddenSalt hiddenPayload) at heq
  have hquery := encodeMerkleQuery_injective heq
  have hencodedChannel := congrArg MerkleQuery.channel hquery
  exact hchannel hencodedChannel

/-- Faithful functional model of `merkle_tree_framed_salted`'s final root. -/
noncomputable def productionMerkleRoot (oracle : List Byte → OracleBlock)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : Word64) (depth : ℕ)
    (salts : Fin (2 ^ depth) → NumericNonce)
    (payload : Fin (2 ^ depth) → List Byte) : OracleBlock :=
  merkleRoot oracle (productionNodePoint channel treeDepth treeNonce) depth
    fun index => oracle
      (productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (salts index) (payload index))

/-- On the fresh-input event, pairwise replacement of all hidden salted leaf
points preserves every node query and makes the real and simulated Merkle
roots exactly equal. -/
theorem productionMerkleRoot_pairedOracle_exact
    (oracle : List Byte → OracleBlock)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : Word64) (depth : ℕ) (hdepth : depth ≤ 64)
    (leftSalts rightSalts : Fin (2 ^ depth) → NumericNonce)
    (leftPayload rightPayload : Fin (2 ^ depth) → List Byte) :
    let leftPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (leftSalts index) (leftPayload index)
    let rightPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (rightSalts index) (rightPayload index)
    let leftInjective := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth leftSalts leftPayload
    let rightInjective := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth rightSalts rightPayload
    let cross := fun left right equality =>
      productionLeafPoint_cross_index channel treeDepth treeNonce leafLength
        depth hdepth leftSalts rightSalts leftPayload rightPayload equality
    productionMerkleRoot
        (PairedOracleReplacement.renameOracle leftPoint rightPoint
          leftInjective rightInjective cross
          oracle)
        channel treeDepth treeNonce leafLength depth rightSalts rightPayload =
      productionMerkleRoot oracle channel treeDepth treeNonce leafLength depth
        leftSalts leftPayload := by
  classical
  dsimp only
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
  let hcross : ∀ left right, leftPoint left = rightPoint right → left = right :=
    fun left right equality => productionLeafPoint_cross_index channel
      treeDepth treeNonce leafLength depth hdepth leftSalts rightSalts
      leftPayload rightPayload equality
  apply merkleRoot_congr oracle
    (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft hright
      hcross oracle)
    (productionNodePoint channel treeDepth treeNonce)
  · intro level index left right
    apply PairedOracleReplacement.renameOracle_off leftPoint rightPoint hleft
      hright hcross
    · intro leafIndex heq
      exact productionNodePoint_ne_leafPoint channel treeDepth treeNonce level
        index left right leafLength depth leafIndex (leftSalts leafIndex)
        (leftPayload leafIndex) heq
    · intro leafIndex heq
      exact productionNodePoint_ne_leafPoint channel treeDepth treeNonce level
        index left right leafLength depth leafIndex (rightSalts leafIndex)
        (rightPayload leafIndex) heq
  · intro index
    exact PairedOracleReplacement.renameOracle_at_right leftPoint rightPoint
      hleft hright hcross oracle index

/-- Replacing one channel's hidden leaves fixes the complete Merkle tree of
every other channel.  This permits the outer, VEIL-linear, and
VEIL-Hadamard replacements to be composed sequentially without undoing an
already matched root. -/
theorem productionMerkleRoot_pairedOracle_otherChannel
    (oracle : List Byte → OracleBlock)
    (hiddenChannel : RoChannel) (hiddenTreeDepth : Byte)
    (hiddenTreeNonce : Nonce256) (hiddenLeafLength : Word64)
    (hiddenDepth : ℕ) (hhiddenDepth : hiddenDepth ≤ 64)
    (leftHiddenSalts rightHiddenSalts :
      Fin (2 ^ hiddenDepth) → NumericNonce)
    (leftHiddenPayload rightHiddenPayload :
      Fin (2 ^ hiddenDepth) → List Byte)
    (otherChannel : RoChannel) (hchannel : otherChannel ≠ hiddenChannel)
    (otherTreeDepth : Byte) (otherTreeNonce : Nonce256)
    (otherLeafLength : Word64) (otherDepth : ℕ)
    (otherSalts : Fin (2 ^ otherDepth) → NumericNonce)
    (otherPayload : Fin (2 ^ otherDepth) → List Byte) :
    let leftPoint := fun index =>
      productionLeafPoint hiddenChannel hiddenTreeDepth hiddenTreeNonce
        hiddenLeafLength hiddenDepth index (leftHiddenSalts index)
        (leftHiddenPayload index)
    let rightPoint := fun index =>
      productionLeafPoint hiddenChannel hiddenTreeDepth hiddenTreeNonce
        hiddenLeafLength hiddenDepth index (rightHiddenSalts index)
        (rightHiddenPayload index)
    let hleft := productionLeafPoint_index_injective hiddenChannel
      hiddenTreeDepth hiddenTreeNonce hiddenLeafLength hiddenDepth
      hhiddenDepth leftHiddenSalts leftHiddenPayload
    let hright := productionLeafPoint_index_injective hiddenChannel
      hiddenTreeDepth hiddenTreeNonce hiddenLeafLength hiddenDepth
      hhiddenDepth rightHiddenSalts rightHiddenPayload
    let hcross := fun left right equality =>
      productionLeafPoint_cross_index hiddenChannel hiddenTreeDepth
        hiddenTreeNonce hiddenLeafLength hiddenDepth hhiddenDepth
        leftHiddenSalts rightHiddenSalts leftHiddenPayload rightHiddenPayload
        equality
    productionMerkleRoot
        (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft
          hright hcross oracle)
        otherChannel otherTreeDepth otherTreeNonce otherLeafLength otherDepth
        otherSalts otherPayload =
      productionMerkleRoot oracle otherChannel otherTreeDepth otherTreeNonce
        otherLeafLength otherDepth otherSalts otherPayload := by
  classical
  dsimp only
  let leftPoint := fun index =>
    productionLeafPoint hiddenChannel hiddenTreeDepth hiddenTreeNonce
      hiddenLeafLength hiddenDepth index (leftHiddenSalts index)
      (leftHiddenPayload index)
  let rightPoint := fun index =>
    productionLeafPoint hiddenChannel hiddenTreeDepth hiddenTreeNonce
      hiddenLeafLength hiddenDepth index (rightHiddenSalts index)
      (rightHiddenPayload index)
  let hleft := productionLeafPoint_index_injective hiddenChannel
    hiddenTreeDepth hiddenTreeNonce hiddenLeafLength hiddenDepth hhiddenDepth
    leftHiddenSalts leftHiddenPayload
  let hright := productionLeafPoint_index_injective hiddenChannel
    hiddenTreeDepth hiddenTreeNonce hiddenLeafLength hiddenDepth hhiddenDepth
    rightHiddenSalts rightHiddenPayload
  let hcross : ∀ left right, leftPoint left = rightPoint right → left = right :=
    fun left right equality => productionLeafPoint_cross_index hiddenChannel
      hiddenTreeDepth hiddenTreeNonce hiddenLeafLength hiddenDepth hhiddenDepth
      leftHiddenSalts rightHiddenSalts leftHiddenPayload rightHiddenPayload
      equality
  apply merkleRoot_congr oracle
    (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft hright
      hcross oracle)
    (productionNodePoint otherChannel otherTreeDepth otherTreeNonce)
  · intro level index left right
    apply PairedOracleReplacement.renameOracle_off leftPoint rightPoint hleft
      hright hcross
    · intro hiddenIndex heq
      exact productionMerklePoint_ne_leafPoint_of_channel_ne .node
        otherChannel hiddenChannel hchannel otherTreeDepth otherTreeNonce
        (BitVec.ofNat 64 64) (BitVec.ofNat 32 level)
        (BitVec.ofNat 64 index.val)
        (oracleBlockBytes left ++ oracleBlockBytes right) hiddenTreeDepth
        hiddenTreeNonce hiddenLeafLength hiddenDepth hiddenIndex
        (leftHiddenSalts hiddenIndex) (leftHiddenPayload hiddenIndex) heq
    · intro hiddenIndex heq
      exact productionMerklePoint_ne_leafPoint_of_channel_ne .node
        otherChannel hiddenChannel hchannel otherTreeDepth otherTreeNonce
        (BitVec.ofNat 64 64) (BitVec.ofNat 32 level)
        (BitVec.ofNat 64 index.val)
        (oracleBlockBytes left ++ oracleBlockBytes right) hiddenTreeDepth
        hiddenTreeNonce hiddenLeafLength hiddenDepth hiddenIndex
        (rightHiddenSalts hiddenIndex) (rightHiddenPayload hiddenIndex) heq
  · intro index
    apply PairedOracleReplacement.renameOracle_off leftPoint rightPoint hleft
      hright hcross
    · intro hiddenIndex heq
      exact productionMerklePoint_ne_leafPoint_of_channel_ne .leaf
        otherChannel hiddenChannel hchannel otherTreeDepth otherTreeNonce
        otherLeafLength (BitVec.ofNat 32 otherDepth)
        (BitVec.ofNat 64 index.val)
        (nonceBytes (numericNonceBytes (otherSalts index)) ++
          otherPayload index)
        hiddenTreeDepth hiddenTreeNonce hiddenLeafLength hiddenDepth
        hiddenIndex (leftHiddenSalts hiddenIndex)
        (leftHiddenPayload hiddenIndex) heq
    · intro hiddenIndex heq
      exact productionMerklePoint_ne_leafPoint_of_channel_ne .leaf
        otherChannel hiddenChannel hchannel otherTreeDepth otherTreeNonce
        otherLeafLength (BitVec.ofNat 32 otherDepth)
        (BitVec.ofNat 64 index.val)
        (nonceBytes (numericNonceBytes (otherSalts index)) ++
          otherPayload index)
        hiddenTreeDepth hiddenTreeNonce hiddenLeafLength hiddenDepth
        hiddenIndex (rightHiddenSalts hiddenIndex)
        (rightHiddenPayload hiddenIndex) heq

end VeiledFlock.ProductionMerkleTree

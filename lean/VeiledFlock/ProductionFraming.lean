import VeiledFlock.Framing

/-!
# Exact production random-oracle framing

This file mirrors `flock-core/src/ro.rs`.  It records the literal role and
magic bytes, the 64-byte Merkle header, the 12-byte little-endian location,
and the 41-byte proof-of-work point.  The main results show that each encoded
field can be recovered and that the three point-hash roles are disjoint.
-/

namespace VeiledFlock.ProductionFraming

open Function
open VeiledFlock.Framing

/-- Rust `u32` and `u64` values, represented by their exact bit widths. -/
abbrev Word32 := BitVec 32
abbrev Word64 := BitVec 64

/-- Little-endian serialization into `byteCount` bytes. -/
def encodeLE {byteCount : ℕ} (value : BitVec (byteCount * 8))
    (index : Fin byteCount) : Byte :=
  (value.extractLsb' (index.val * 8) 8).toFin

def encodeLEList {byteCount : ℕ} (value : BitVec (byteCount * 8)) :
    List Byte :=
  List.ofFn (encodeLE value)

@[simp]
theorem encodeLEList_length {byteCount : ℕ}
    (value : BitVec (byteCount * 8)) :
    (encodeLEList value).length = byteCount := by
  simp [encodeLEList]

private theorem bit_eq_of_encoded_byte_eq {byteCount : ℕ}
    (left right : BitVec (byteCount * 8)) (byte : Fin byteCount)
    (hbyte : encodeLE left byte = encodeLE right byte) (bit : Fin 8) :
    left.getLsbD (byte.val * 8 + bit.val) =
      right.getLsbD (byte.val * 8 + bit.val) := by
  have hvector :
      left.extractLsb' (byte.val * 8) 8 =
        right.extractLsb' (byte.val * 8) 8 := by
    exact BitVec.toFin_injective hbyte
  have hbit := congrArg
    (fun value : BitVec 8 => value.getLsbD bit.val) hvector
  simpa only [BitVec.getLsbD_extractLsb', bit.isLt, decide_true,
    Bool.true_and] using hbit

theorem encodeLE_injective {byteCount : ℕ} :
    Function.Injective (encodeLE (byteCount := byteCount)) := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  by_cases hbytes : byteCount = 0
  · subst hbytes
    omega
  · let byte : Fin byteCount :=
      ⟨index / 8, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
    let bit : Fin 8 := ⟨index % 8, Nat.mod_lt index (by omega)⟩
    have hbit := bit_eq_of_encoded_byte_eq left right byte
      (congrFun heq byte) bit
    simpa only [byte, bit, Nat.div_add_mod'] using hbit

theorem encodeLEList_injective {byteCount : ℕ} :
    Function.Injective (encodeLEList (byteCount := byteCount)) := by
  intro left right heq
  apply encodeLE_injective
  exact List.ofFn_injective heq

/-- Point-hash role bytes from `ro.rs`. -/
inductive MerkleRole
  | leaf
  | node
  deriving DecidableEq, Fintype

def roleByte : MerkleRole → Byte
  | .leaf => 0x10
  | .node => 0x11

theorem roleByte_injective : Function.Injective roleByte := by
  intro left right heq
  cases left <;> cases right <;> simp [roleByte] at heq ⊢

/-- The eight `RoChannel` discriminants, represented by their `repr(u8)`
byte. -/
abbrev RoChannel := Fin 8

def channelByte (channel : RoChannel) : Byte :=
  Fin.castLE (by decide) channel

theorem channelByte_injective : Function.Injective channelByte := by
  intro left right heq
  apply Fin.ext
  exact congrArg (fun value : Byte => value.val) heq

/-- Literal `b"FLOCKRO"`. -/
def roMagic : List Byte :=
  [0x46, 0x4c, 0x4f, 0x43, 0x4b, 0x52, 0x4f]

@[simp]
theorem roMagic_length : roMagic.length = 7 := by
  decide

/-- Exact 64-byte `encode_header` output. -/
def encodeHeader (role : MerkleRole) (channel : RoChannel)
    (treeDepth : Byte) (nonce : Nonce256) (leafLength : Word64) : List Byte :=
  [roleByte role] ++ roMagic ++ [channelByte channel, treeDepth] ++
    List.replicate 6 0 ++ nonceBytes nonce ++
    encodeLEList (byteCount := 8) leafLength ++ List.replicate 8 0

@[simp]
theorem encodeHeader_length (role channel treeDepth nonce leafLength) :
    (encodeHeader role channel treeDepth nonce leafLength).length = 64 := by
  simp [encodeHeader]

/-- All five fields of a production Merkle header are recoverable from its
exact byte string. -/
theorem encodeHeader_injective : Function.Injective
    (fun fields : MerkleRole × RoChannel × Byte × Nonce256 × Word64 =>
      encodeHeader fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1
        fields.2.2.2.2) := by
  intro left right heq
  have hrole := congrArg (fun bytes : List Byte => bytes.take 1) heq
  have hchannel := congrArg
    (fun bytes : List Byte => (bytes.drop 8).take 1) heq
  have hdepth := congrArg
    (fun bytes : List Byte => (bytes.drop 9).take 1) heq
  have hnonce := congrArg
    (fun bytes : List Byte => (bytes.drop 16).take 32) heq
  have hlength := congrArg
    (fun bytes : List Byte => (bytes.drop 48).take 8) heq
  simp [encodeHeader, roMagic] at hrole hchannel hdepth hnonce hlength
  have hr : left.1 = right.1 := roleByte_injective hrole
  have hc : left.2.1 = right.2.1 := channelByte_injective hchannel
  have hd : left.2.2.1 = right.2.2.1 := hdepth
  have hn : left.2.2.2.1 = right.2.2.2.1 :=
    nonceBytes_injective hnonce
  have hl : left.2.2.2.2 = right.2.2.2.2 :=
    encodeLEList_injective hlength
  rcases left with ⟨leftRole, leftChannel, leftDepth, leftNonce, leftLength⟩
  rcases right with
    ⟨rightRole, rightChannel, rightDepth, rightNonce, rightLength⟩
  simp_all

/-- Exact 12-byte `encode_location` output. -/
def encodeLocation (level : Word32) (index : Word64) : List Byte :=
  encodeLEList (byteCount := 4) level ++
    encodeLEList (byteCount := 8) index

@[simp]
theorem encodeLocation_length (level index) :
    (encodeLocation level index).length = 12 := by
  simp [encodeLocation]

theorem encodeLocation_injective : Function.Injective
    (fun fields : Word32 × Word64 =>
      encodeLocation fields.1 fields.2) := by
  intro left right heq
  have hlevel := congrArg (fun bytes : List Byte => bytes.take 4) heq
  have hindex := congrArg (fun bytes : List Byte => bytes.drop 4) heq
  simp [encodeLocation] at hlevel hindex
  exact Prod.ext (encodeLEList_injective hlevel)
    (encodeLEList_injective hindex)

/-- Exact `encode_point` byte string. -/
def encodeMerklePoint (role : MerkleRole) (channel : RoChannel)
    (treeDepth : Byte) (nonce : Nonce256) (leafLength : Word64)
    (level : Word32) (index : Word64) (payload : List Byte) : List Byte :=
  encodeHeader role channel treeDepth nonce leafLength ++
    encodeLocation level index ++ payload

/-- Exact 41-byte `encode_pow_point` byte string. -/
def encodePowPoint (state : Nonce256) (nonce : Word64) : List Byte :=
  [(0x12 : Byte)] ++ nonceBytes state ++
    encodeLEList (byteCount := 8) nonce

@[simp]
theorem encodePowPoint_length (state nonce) :
    (encodePowPoint state nonce).length = 41 := by
  simp [encodePowPoint]

/-- Complete input to one production Merkle leaf or internal-node hash. -/
structure MerkleQuery where
  role : MerkleRole
  channel : RoChannel
  treeDepth : Byte
  treeNonce : Nonce256
  leafLength : Word64
  level : Word32
  index : Word64
  payload : List Byte
  deriving DecidableEq

def encodeMerkleQuery (query : MerkleQuery) : List Byte :=
  encodeMerklePoint query.role query.channel query.treeDepth query.treeNonce
    query.leafLength query.level query.index query.payload

/-- The exact production Merkle framing is injective in every framed field and
the complete payload. -/
theorem encodeMerkleQuery_injective : Function.Injective encodeMerkleQuery := by
  intro left right heq
  have hheader := congrArg (fun bytes : List Byte => bytes.take 64) heq
  have hlocation := congrArg
    (fun bytes : List Byte => (bytes.drop 64).take 12) heq
  simp [encodeMerkleQuery, encodeMerklePoint] at hheader hlocation
  have hh :
      (left.role, left.channel, left.treeDepth, left.treeNonce,
          left.leafLength) =
        (right.role, right.channel, right.treeDepth, right.treeNonce,
          right.leafLength) :=
    encodeHeader_injective hheader
  have hl : (left.level, left.index) = (right.level, right.index) :=
    encodeLocation_injective hlocation
  cases left
  cases right
  simp_all
  simp only [encodeMerkleQuery, encodeMerklePoint] at heq
  exact List.append_cancel_left heq

structure PowQuery where
  state : Nonce256
  nonce : Word64
  deriving DecidableEq

def encodePowQuery (query : PowQuery) : List Byte :=
  encodePowPoint query.state query.nonce

theorem encodePowQuery_injective : Function.Injective encodePowQuery := by
  intro left right heq
  have hstate := congrArg
    (fun bytes : List Byte => (bytes.drop 1).take 32) heq
  have hnonce := congrArg (fun bytes : List Byte => bytes.drop 33) heq
  simp [encodePowQuery, encodePowPoint] at hstate hnonce
  cases left
  cases right
  simp_all [nonceBytes_injective.eq_iff, encodeLEList_injective.eq_iff]

/-- The streaming Fiat--Shamir oracle points always start with `OP_DOMAIN`. -/
def isFiatShamirPoint (point : List Byte) : Prop :=
  point.head? = some (0x01 : Byte)

@[simp]
theorem encodeMerklePoint_head (role channel treeDepth nonce leafLength level
    index payload) :
    (encodeMerklePoint role channel treeDepth nonce leafLength level index
      payload).head? = some (roleByte role) := by
  simp [encodeMerklePoint, encodeHeader]

@[simp]
theorem encodePowPoint_head (state nonce) :
    (encodePowPoint state nonce).head? = some (0x12 : Byte) := by
  simp [encodePowPoint]

theorem fiatShamir_ne_merkle {point : List Byte}
    (hpoint : isFiatShamirPoint point)
    (role channel treeDepth nonce leafLength level index payload) :
    point ≠ encodeMerklePoint role channel treeDepth nonce leafLength level
      index payload := by
  intro heq
  have := congrArg List.head? heq
  simp [isFiatShamirPoint] at hpoint
  rw [hpoint, encodeMerklePoint_head] at this
  cases role <;> simp [roleByte] at this

theorem fiatShamir_ne_pow {point : List Byte}
    (hpoint : isFiatShamirPoint point) (state nonce) :
    point ≠ encodePowPoint state nonce := by
  intro heq
  have := congrArg List.head? heq
  simp [isFiatShamirPoint] at hpoint
  rw [hpoint, encodePowPoint_head] at this
  have hbyte := Option.some.inj this
  have := congrArg (fun value : Byte => value.val) hbyte
  norm_num at this

theorem merkle_ne_pow (role channel treeDepth treeNonce leafLength level index
    payload state powNonce) :
    encodeMerklePoint role channel treeDepth treeNonce leafLength level index
        payload ≠
      encodePowPoint state powNonce := by
  intro heq
  have := congrArg List.head? heq
  rw [encodeMerklePoint_head, encodePowPoint_head] at this
  cases role <;>
    have hbyte := Option.some.inj this <;>
    have := congrArg (fun value : Byte => value.val) hbyte <;>
    norm_num [roleByte] at this

/-- A streaming Fiat--Shamir squeeze point, carrying the invariant established
by `FsChallenger::new` that its first byte is `OP_DOMAIN = 0x01`. -/
abbrev FiatShamirQuery := { point : List Byte // isFiatShamirPoint point }

/-- All byte strings queried by one production proof use one of these exact
three encodings. -/
inductive ProductionQuery
  | fiatShamir (query : FiatShamirQuery)
  | merkle (query : MerkleQuery)
  | pow (query : PowQuery)

def encodeProductionQuery : ProductionQuery → List Byte
  | .fiatShamir query => query.1
  | .merkle query => encodeMerkleQuery query
  | .pow query => encodePowQuery query

/-- Global domain separation and within-role framing combine into one
injective encoding for every production random-oracle query. -/
theorem encodeProductionQuery_injective :
    Function.Injective encodeProductionQuery := by
  intro left right heq
  cases left with
  | fiatShamir left =>
      cases right with
      | fiatShamir right =>
          congr 1
          exact Subtype.ext heq
      | merkle right =>
          exact False.elim (fiatShamir_ne_merkle left.property right.role
            right.channel right.treeDepth right.treeNonce right.leafLength
            right.level right.index right.payload heq)
      | pow right =>
          exact False.elim (fiatShamir_ne_pow left.property right.state
            right.nonce heq)
  | merkle left =>
      cases right with
      | fiatShamir right =>
          exact False.elim (fiatShamir_ne_merkle right.property left.role
            left.channel left.treeDepth left.treeNonce left.leafLength
            left.level left.index left.payload heq.symm)
      | merkle right =>
          congr 1
          exact encodeMerkleQuery_injective heq
      | pow right =>
          exact False.elim (merkle_ne_pow left.role left.channel
            left.treeDepth left.treeNonce left.leafLength left.level left.index
            left.payload right.state right.nonce heq)
  | pow left =>
      cases right with
      | fiatShamir right =>
          exact False.elim
            (fiatShamir_ne_pow right.property left.state left.nonce heq.symm)
      | merkle right =>
          exact False.elim (merkle_ne_pow right.role right.channel
            right.treeDepth right.treeNonce right.leafLength right.level
            right.index right.payload left.state left.nonce heq.symm)
      | pow right =>
          congr 1
          exact encodePowQuery_injective heq

end VeiledFlock.ProductionFraming

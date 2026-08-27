import VeiledFlock.ProductionMerkleFamilyTransport

/-!
# The three salted trees in the deployed VEIL--FLOCK prover

This module fixes the generic family theorem to the exact `repr(u8)` channel
discriminants used by Rust: witness = 0, VEIL linear = 6, and VEIL Hadamard =
7.  It also records the exact little-endian row serialization used by
`MerkleMatrix::new`.
-/

namespace VeiledFlock.ProductionThreeTree

open Function
open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCombinedMerkleTransport
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionTranscriptFraming

inductive ProductionTree
  | outer
  | veilLinear
  | veilHadamard
  deriving DecidableEq, Fintype

structure TreeShape where
  treeDepth : Byte
  treeNonce : Nonce256
  leafLength : Word64
  depth : ℕ
  depth_le : depth ≤ 64

def geometryOf (channel : RoChannel) (shape : TreeShape) : TreeGeometry where
  channel := channel
  treeDepth := shape.treeDepth
  treeNonce := shape.treeNonce
  leafLength := shape.leafLength
  depth := shape.depth
  depth_le := shape.depth_le

/-- Exact values of `RoChannel::{Witness, VeilLinear, VeilHadamard}`. -/
def productionGeometry (outer linear hadamard : TreeShape) :
    ProductionTree → TreeGeometry
  | .outer => geometryOf ⟨0, by decide⟩ outer
  | .veilLinear => geometryOf ⟨6, by decide⟩ linear
  | .veilHadamard => geometryOf ⟨7, by decide⟩ hadamard

theorem productionGeometry_channel_injective
    (outer linear hadamard : TreeShape) :
    Injective (fun tree =>
      (productionGeometry outer linear hadamard tree).channel) := by
  intro left right heq
  cases left <;> cases right <;> simp [productionGeometry, geometryOf] at heq ⊢

/-- Rust `matrix_bytes` for one row: each `F128` occupies its exact 16-byte
little-endian representation and columns remain in row-major order. -/
noncomputable def matrixRowBytes {columns : ℕ}
    (row : Fin columns → GhashField) : List Byte :=
  (List.ofFn row).flatMap fieldBytes

@[simp]
theorem matrixRowBytes_length {columns : ℕ}
    (row : Fin columns → GhashField) :
    (matrixRowBytes row).length = 16 * columns := by
  simp [matrixRowBytes, List.length_flatMap, List.sum_ofFn]
  omega

/-- A row-valued material fits whenever its number of columns fits the
displayed production point budget. -/
theorem matrixMaterial_fits {Coins : Type*} {maxLength columns : ℕ}
    (geometry : TreeGeometry)
    (salts : Coins → Fin (2 ^ geometry.depth) →
      VeiledFlock.NonceSerialization.NumericNonce)
    (rows : Coins → Fin (2 ^ geometry.depth) → Fin columns → GhashField)
    (hbudget : 108 + 16 * columns ≤ maxLength) :
    MaterialFits (maxLength := maxLength) geometry
      { salts := salts, payload := fun coins index =>
          matrixRowBytes (rows coins index) } := by
  intro coins index
  simpa using hbudget

/-- The three actual commitment roots are all preserved by one finite oracle
bijection, including challenge-dependent Hadamard rows. -/
theorem threeRoots_exact {Coins : Type*} {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (outer linear hadamard : TreeShape)
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (productionGeometry outer linear hadamard tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) leftMaterial)
    (hright : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) rightMaterial)
    (hnodes : 140 ≤ maxLength) (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (tree : ProductionTree) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv
      (productionGeometry outer linear hadamard)
      (productionGeometry_channel_injective outer linear hadamard)
      leftMaterial rightMaterial hleft hright input
    boundedRoot fallback (productionGeometry outer linear hadamard tree)
        (rightMaterial tree) (coinEquiv input.1) transported.2 =
      boundedRoot fallback (productionGeometry outer linear hadamard tree)
        (leftMaterial tree) input.1 input.2 := by
  exact boundedFamilyCoinOracleEquiv_roots_exact coinEquiv
    (productionGeometry outer linear hadamard)
    (productionGeometry_channel_injective outer linear hadamard)
    leftMaterial rightMaterial hleft hright hnodes fallback input tree

/-- The same three-tree transport fixes every bounded Fiat--Shamir query. -/
theorem threeTree_answer_fiat {Coins : Type*} {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (outer linear hadamard : TreeShape)
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (productionGeometry outer linear hadamard tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) leftMaterial)
    (hright : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) rightMaterial)
    (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (point : List Byte) (hfiat : isFiatShamirPoint point)
    (hpoint : point.length ≤ maxLength) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv
      (productionGeometry outer linear hadamard)
      (productionGeometry_channel_injective outer linear hadamard)
      leftMaterial rightMaterial hleft hright input
    answerBounded fallback transported.2 point =
      answerBounded fallback input.2 point := by
  exact boundedFamilyCoinOracleEquiv_answer_fiat coinEquiv
    (productionGeometry outer linear hadamard)
    (productionGeometry_channel_injective outer linear hadamard)
    leftMaterial rightMaterial hleft hright fallback input point hfiat hpoint

/-- The same transport fixes the exact 41-byte proof-of-work domain. -/
theorem threeTree_answer_pow {Coins : Type*} {maxLength : ℕ}
    (coinEquiv : Coins ≃ Coins) (outer linear hadamard : TreeShape)
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (productionGeometry outer linear hadamard tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) leftMaterial)
    (hright : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) rightMaterial)
    (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (state : Nonce256) (nonce : Word64)
    (hpoint : (encodePowPoint state nonce).length ≤ maxLength) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv
      (productionGeometry outer linear hadamard)
      (productionGeometry_channel_injective outer linear hadamard)
      leftMaterial rightMaterial hleft hright input
    answerBounded fallback transported.2 (encodePowPoint state nonce) =
      answerBounded fallback input.2 (encodePowPoint state nonce) := by
  exact boundedFamilyCoinOracleEquiv_answer_pow coinEquiv
    (productionGeometry outer linear hadamard)
    (productionGeometry_channel_injective outer linear hadamard)
    leftMaterial rightMaterial hleft hright fallback input state nonce hpoint

/-- Uniformity of the exact three-tree finite transport. -/
theorem uniform_threeTree_transport {Coins : Type*} {maxLength : ℕ}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (coinEquiv : Coins ≃ Coins) (outer linear hadamard : TreeShape)
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (productionGeometry outer linear hadamard tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) leftMaterial)
    (hright : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) rightMaterial) :
    (PMF.uniformOfFintype
        (Coins × (BoundedBytes maxLength → OracleBlock))).map
        (boundedFamilyCoinOracleEquiv coinEquiv
          (productionGeometry outer linear hadamard)
          (productionGeometry_channel_injective outer linear hadamard)
          leftMaterial rightMaterial hleft hright) =
      PMF.uniformOfFintype
        (Coins × (BoundedBytes maxLength → OracleBlock)) := by
  exact uniform_boundedFamilyCoinOracleEquiv coinEquiv
    (productionGeometry outer linear hadamard)
    (productionGeometry_channel_injective outer linear hadamard)
    leftMaterial rightMaterial hleft hright

end VeiledFlock.ProductionThreeTree

import VeiledFlock.Production.Nizk.NizkExperiment

/-!
# Concrete public-fiber representative for the BLAKE3 digest statement

The production packed witness contains `2^(m-14)` BLAKE3 instances.  Each
instance occupies 128 packed field words; its public 256-bit digest is stored
in packed words 2 and 3.  With the production 64-lane outer PCS layout these
two words occupy lanes 2 and 3 at the same high-half message position.

This module fixes that coordinate map and constructs a canonical packed word
whose public digest cells come from `ProductionStatement` and whose remaining
cells are zero.  No witness, witness-derived value, or external representative
is an input to `publicRepresentative`.
-/

namespace VeiledFlock.ProductionPublicRepresentative

open Function
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains

/-- Number of BLAKE3 instances represented by each registered `m`. -/
def instanceCount (shape : BatchShape) : ℕ :=
  2 ^ (m shape - 14)

/-- One of the two packed `F_{2^128}` halves of one public digest. -/
abbrev PublicCoord (shape : BatchShape) :=
  Fin (instanceCount shape) × Fin 2

theorem two_mul_instanceCount_eq_outerMaskSymbolsPerLane
    (shape : BatchShape) :
    2 * instanceCount shape = outerMaskSymbolsPerLane shape := by
  cases shape <;> decide

/-- Read bytes 0--15 or 16--31 of a digest as one little-endian GHASH-field
word, exactly matching Rust's two patched packed words. -/
noncomputable def digestHalf (digest : Hash256) (half : Fin 2) : GhashField :=
  encodeGhashFieldEquiv.symm fun byte =>
    digest ⟨half.val * 16 + byte.val, by omega⟩

/-- Digest carried by one physical circuit slot.  Real slots use the ordered
public batch and every remaining slot uses Rust's public constant padding
digest. -/
def paddedDigest {shape : BatchShape}
    (statement : ProductionStatement shape) (slot : ℕ) : Hash256 :=
  statement.digests.getD slot statement.paddingDigest

/-- Public value assigned to one digest coordinate. -/
noncomputable def publicValue (shape : BatchShape)
    (statement : ProductionStatement shape) (coordinate : PublicCoord shape) :
    GhashField :=
  digestHalf (paddedDigest statement coordinate.1.val) coordinate.2

/-- Exact location of Rust packed witness words 2 and 3 after splitting the
low mask half into residual and active coordinates for the outer PCS proof. -/
def publicPositions (shape : BatchShape) (coordinate : PublicCoord shape) :
    ResidualDataIndex shape × LaneIndex :=
  let position := outerMaskSymbolsPerLane shape + 2 * coordinate.1.val
  (⟨position - outerL0QueryCount shape, by
      have hcount := two_mul_instanceCount_eq_outerMaskSymbolsPerLane shape
      have hquery := outerL0QueryCount_le_maskSymbols shape
      have hinstance := coordinate.1.isLt
      dsimp only [position]
      omega⟩,
    ⟨2 + coordinate.2.val, by
      have := coordinate.2.isLt
      norm_num [LaneIndex, outerLaneCount]
      omega⟩)

theorem publicPositions_injective (shape : BatchShape) :
    Injective (publicPositions shape) := by
  rintro ⟨leftInstance, leftHalf⟩ ⟨rightInstance, rightHalf⟩ heq
  have hdata := congrArg (fun value => value.1.val) heq
  have hlane := congrArg (fun value => value.2.val) heq
  simp only [publicPositions] at hdata hlane
  have hquery := outerL0QueryCount_le_maskSymbols shape
  have hleft := leftInstance.isLt
  have hright := rightInstance.isLt
  have hcount := two_mul_instanceCount_eq_outerMaskSymbolsPerLane shape
  have hinstance : leftInstance.val = rightInstance.val := by omega
  have hhalf : leftHalf.val = rightHalf.val := by omega
  exact Prod.ext (Fin.ext hinstance) (Fin.ext hhalf)

/-- The packed witness type used by the concrete representative.  The
production outer protocol consumes this exact `BaseWord` representation. -/
abbrev Witness (shape : BatchShape) := BaseWord shape

/-- Concrete production base-message map for the specialized witness type. -/
def baseMessage (shape : BatchShape) : Witness shape → BaseWord shape := id

/-- Canonical member of the public digest fiber: public digest cells are
copied from `statement`; every non-public packed cell is zero.  This function
has only the public statement as data input. -/
noncomputable def publicRepresentative (shape : BatchShape)
    (statement : ProductionStatement shape) : Witness shape :=
  fun index =>
    ∑ coordinate : PublicCoord shape,
      if publicDataPosition shape (publicPositions shape) coordinate = index
      then publicValue shape statement coordinate
      else 0

/-- Evaluating the canonical representative at a public packed coordinate
returns exactly the corresponding statement digest half. -/
theorem publicRepresentative_at_publicPosition (shape : BatchShape)
    (statement : ProductionStatement shape) (coordinate : PublicCoord shape) :
    publicRepresentative shape statement
        (publicDataPosition shape (publicPositions shape) coordinate) =
      publicValue shape statement coordinate := by
  classical
  let position := publicDataPosition shape (publicPositions shape)
  have hinjective : Injective position := by
    intro left right heq
    apply publicPositions_injective shape
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    exact Prod.ext (Sum.inl.inj hfirst) hsecond
  change (∑ other : PublicCoord shape,
      if position other = position coordinate
      then publicValue shape statement other
      else 0) = publicValue shape statement coordinate
  simp [hinjective.eq_iff]

/-- Exact public-projection property required by the production coupling. -/
theorem publicRepresentative_projection (shape : BatchShape)
    (statement : ProductionStatement shape) :
    publicStatement shape (publicPositions shape) (baseMessage shape)
        (publicRepresentative shape statement) =
      publicValue shape statement := by
  funext coordinate
  exact publicRepresentative_at_publicPosition shape statement coordinate

/-- Relation-side public validity: the committed packed witness exposes the
digest halves carried by the public statement at precisely the production
coordinates. -/
def PublicProjectionValid (shape : BatchShape)
    (statement : ProductionStatement shape) (witness : Witness shape) : Prop :=
  publicStatement shape (publicPositions shape) (baseMessage shape) witness =
    publicValue shape statement

/-- A valid production witness and the canonical public representative have
the exact same public projection. -/
theorem witness_projection_eq_publicRepresentative (shape : BatchShape)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (hvalid : PublicProjectionValid shape statement witness) :
    publicStatement shape (publicPositions shape) (baseMessage shape) witness =
      publicStatement shape (publicPositions shape) (baseMessage shape)
        (publicRepresentative shape statement) := by
  rw [hvalid, publicRepresentative_projection]

/-- Rust accepts a nonempty real batch no larger than the selected registered
shape and pads every remaining slot with `paddingDigest`. -/
def StatementWellFormed (shape : BatchShape)
    (statement : ProductionStatement shape) : Prop :=
  0 < statement.digests.length ∧
    statement.digests.length ≤ instanceCount shape

end VeiledFlock.ProductionPublicRepresentative

import VeiledFlock.Concrete.ConcreteParameters
import VeiledFlock.Algebra.Field128Ghash
import VeiledFlock.Production.Algebra.MaskLayout
import VeiledFlock.Production.Core.ZerocheckSchedule
import VeiledFlock.Production.Core.Framing
import VeiledFlock.Production.Merkle.EqualitySampler
import VeiledFlock.Production.Outer.OuterCodeDomains
import VeiledFlock.Production.Algebra.PaddedAlgebraicE2E
import VeiledFlock.Production.Merkle.ThreeTree

/-!
# Public proof object of the production VEIL + FLOCK protocol

These structures mirror the public Rust proof at the mathematical-value
level.  Fixed production lengths use `Fin`-indexed families, so malformed
vector lengths are not inhabitants of this model.  This is deliberately not
a Rust/bincode refinement, and the main statistical-ZK theorem does not claim
one.
-/

namespace VeiledFlock.ProductionNizkProof

open VeiledFlock.ConcreteParameters
open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.ProductionMaskLayout
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionZerocheckSchedule
open VeiledFlock.ProductionThreeTree

abbrev Hash256 := Nonce256

/-- Rust `InitialTreeNonces`. -/
structure InitialTreeNonces where
  outer : Nonce256
  veilLinear : Nonce256
  veilHadamard : Nonce256
  deriving DecidableEq, Fintype, Inhabited

/-- Rust `MaskedZerocheckProof`, with all production lengths in the type. -/
structure MaskedZerocheckProof (shape : BatchShape) where
  round1Ab : Fin ell → GhashField
  round1C : Fin ell → GhashField
  multilinearRounds : Fin (zerocheckRounds shape) →
    GhashField × GhashField
  finalAEval : GhashField
  finalBEval : GhashField

/-- Rust `LincheckProof`, with its eight rounds and 64-value terminal vector
fixed by the registered production parameters. -/
structure LincheckProof where
  rounds : Fin lincheckRounds → GhashField × GhashField
  zPartial : Fin zPartialLength → GhashField

/-- Rust `MaskedRingClaim`. -/
structure MaskedRingClaim where
  witness : Fin ringWidth → GhashField
  blind : Fin ringWidth → GhashField

/-- Split the exact flat masking cursor into the public Rust proof fields. -/
def MaskedZerocheckProof.ofTranscript (shape : BatchShape)
    (transcript : MaskedTranscript shape) : MaskedZerocheckProof shape where
  round1Ab := ProductionZerocheckSchedule.round1Ab shape transcript
  round1C := ProductionZerocheckSchedule.round1C shape transcript
  multilinearRounds := fun round =>
    (transcript (zerocheckRoundIndex shape round ⟨0, by decide⟩),
      transcript (zerocheckRoundIndex shape round ⟨1, by decide⟩))
  finalAEval := transcript (finalIndex shape ⟨0, by decide⟩)
  finalBEval := transcript (finalIndex shape ⟨1, by decide⟩)

/-- Split the exact flat masking cursor into the public lincheck fields. -/
def LincheckProof.ofTranscript (shape : BatchShape)
    (transcript : MaskedTranscript shape) : LincheckProof where
  rounds := fun round =>
    (transcript (lincheckRoundIndex shape round ⟨0, by decide⟩),
      transcript (lincheckRoundIndex shape round ⟨1, by decide⟩))
  zPartial := fun index => transcript (zPartialIndex shape index)

/-- Split the terminal portion of the masking cursor into both ring claims. -/
def maskedRingClaimsOfTranscript (shape : BatchShape)
    (transcript : MaskedTranscript shape) :
    Fin ringClaimCount → MaskedRingClaim := fun claim =>
  { witness := fun coordinate =>
      transcript (ringIndex shape claim ⟨0, by decide⟩ coordinate)
    blind := fun coordinate =>
      transcript (ringIndex shape claim ⟨1, by decide⟩ coordinate) }

/-- Rust `PcsParams`. -/
inductive LigeritoProfile
  | fast
  | slim
  | secure
  deriving DecidableEq, Fintype

structure PcsParams where
  m : ℕ
  logInvRate : ℕ
  logBatchSize : ℕ
  profile : LigeritoProfile
  zk : Bool

/-- Rust `Commitment`. -/
structure Commitment where
  root : Hash256
  params : PcsParams

/-- Rust/VEIL `VectorParameters`. -/
structure VectorParameters where
  vectorLength : ℕ
  paddingLength : ℕ
  codeLength : ℕ
  numVectors : ℕ

/-- Rust/VEIL `MerkleMatrixOpening`. -/
structure MerkleMatrixOpening where
  positions : List ℕ
  rows : List GhashField
  salts : List Nonce256
  siblings : List Hash256

/-- Rust/VEIL `DotProductProof`. -/
structure DotProductProof where
  parameters : VectorParameters
  commitment : Hash256
  claimedDotProducts : List GhashField
  maskDotProduct : GhashField
  rlcVector : List GhashField
  rlcPadding : List GhashField
  opening : MerkleMatrixOpening

/-- Rust/VEIL `HadamardProof`. -/
structure HadamardProof where
  parameters : VectorParameters
  commitment : Hash256
  gamma : GhashField
  phi : List GhashField
  claimedDotProducts : Fin 3 → GhashField
  maskDotProduct : GhashField
  rlcVector : List GhashField
  rlcPadding : List GhashField
  opening : MerkleMatrixOpening

/-- Rust/VEIL `ConstraintParameters`. -/
structure ConstraintParameters where
  linearPadding : ℕ
  hadamardPadding : ℕ
  inverseRate : ℕ

/-- Rust/VEIL `ConstraintProof`. -/
structure ConstraintProof where
  parameters : ConstraintParameters
  numVariables : ℕ
  numMultiplications : ℕ
  hadamard : HadamardProof
  linear : DotProductProof

/-- Rust Ligerito `SumcheckMessage`. -/
structure SumcheckMessage where
  u0 : GhashField
  u2 : GhashField

/-- Rust Ligerito `RecursiveProof`. -/
structure RecursiveProof where
  openedRows : List (List GhashField)
  leafSalts : List Nonce256
  merkleProof : List Hash256

/-- Rust Ligerito `FinalProof`. -/
structure FinalProof where
  yr : List GhashField
  openedRows : List (List GhashField)
  merkleProof : List Hash256

/-- Rust `LigeritoProof`.  Length constraints selected by the registered
profile belong to verification, rather than being silently assumed here. -/
structure LigeritoProof where
  initialRoot : Hash256
  initialProof : RecursiveProof
  recursiveRoots : List Hash256
  recursiveProofs : List RecursiveProof
  finalProof : FinalProof
  sumcheckTranscript : List SumcheckMessage
  grindingNonces : List Word64
  oodValues : List GhashField
  foldGrindingNonces : List Word64

/-! ## Canonical recursive-opening domains

The production verifier makes the Merkle leaf domain explicit.  Only the
initial witness-dependent ZK opening is salted; every recursive opening is in
the unsalted domain.  These predicates mirror the fail-closed Rust checks at
the wire-model boundary.  They are not an extra hypothesis of the statistical
ZK theorem: the honest protocol distribution is unchanged, and recursive
Ligerito begins after the witness-independent uniform-fold boundary.
-/

/-- Salt-domain choice passed to Rust `verify_level_opens_maybe_ro`. -/
inductive LevelOpenSaltDomain
  | unsalted
  | salted
  deriving DecidableEq

/-- Exact leaf-salt shape accepted for one recursive-opening payload. -/
def RecursiveProof.matchesSaltDomain (proof : RecursiveProof) :
    LevelOpenSaltDomain → Prop
  | .unsalted => proof.leafSalts = []
  | .salted => proof.leafSalts.length = proof.openedRows.length

/-- Canonical recursive Ligerito shape enforced before verification.  For
`recursiveSteps = r`, Rust requires exactly `r` recursive roots and `r - 1`
recursive opening proofs.  All recursive openings are unsalted independently
of the initial L0 domain. -/
structure LigeritoProof.IsCanonical (proof : LigeritoProof)
    (recursiveSteps : ℕ) (initialDomain : LevelOpenSaltDomain) : Prop where
  recursiveSteps_pos : 0 < recursiveSteps
  recursiveRoots_length : proof.recursiveRoots.length = recursiveSteps
  recursiveProofs_length : proof.recursiveProofs.length = recursiveSteps - 1
  initial_matches : proof.initialProof.matchesSaltDomain initialDomain
  recursive_unsalted : ∀ recursiveProof ∈ proof.recursiveProofs,
    recursiveProof.matchesSaltDomain .unsalted

theorem LigeritoProof.IsCanonical.recursive_leafSalts_empty
    {proof : LigeritoProof} {recursiveSteps : ℕ}
    {initialDomain : LevelOpenSaltDomain}
    (hcanonical : proof.IsCanonical recursiveSteps initialDomain)
    {recursiveProof : RecursiveProof}
    (hmem : recursiveProof ∈ proof.recursiveProofs) :
    recursiveProof.leafSalts = [] := by
  exact hcanonical.recursive_unsalted recursiveProof hmem

theorem LigeritoProof.IsCanonical.initial_salt_count
    {proof : LigeritoProof} {recursiveSteps : ℕ}
    (hcanonical : proof.IsCanonical recursiveSteps .salted) :
    proof.initialProof.leafSalts.length =
      proof.initialProof.openedRows.length := by
  exact hcanonical.initial_matches

/-- Rust ring-switch opening. -/
structure RingSwitchProof where
  sHatV : Fin ringWidth → GhashField

/-- Rust optional PCS-local blinder opening.  Production preblinded mode uses
`none`, but retaining the field matches the deserialized public type. -/
structure ZkBlindOpening where
  yG : GhashField
  cGrindNonce : Word64

/-- Rust `BatchOpeningProofLigerito`. -/
structure BatchOpeningProofLigerito where
  ringSwitches : Fin ringClaimCount → RingSwitchProof
  ligerito : LigeritoProof
  zkBlind : Option ZkBlindOpening

/-- Exact PCS mode and recursive-opening shape checks enforced by the
production preblinded verifier.  The outer commitment is in ZK mode, but the
blinding challenge is supplied by the enclosing VEIL--FLOCK protocol, so the
PCS-local `zkBlind` opening must be absent.  L0 is salted and every later
recursive opening is unsalted. -/
structure BatchOpeningProofLigerito.PassesProductionModeChecks
    (proof : BatchOpeningProofLigerito) (recursiveSteps : ℕ) : Prop where
  preblinded : proof.zkBlind = none
  canonicalRecursiveShape :
    proof.ligerito.IsCanonical recursiveSteps .salted

theorem BatchOpeningProofLigerito.PassesProductionModeChecks.initial_salt_count
    {proof : BatchOpeningProofLigerito} {recursiveSteps : ℕ}
    (hvalid : proof.PassesProductionModeChecks recursiveSteps) :
    proof.ligerito.initialProof.leafSalts.length =
      proof.ligerito.initialProof.openedRows.length := by
  exact hvalid.canonicalRecursiveShape.initial_salt_count

theorem BatchOpeningProofLigerito.PassesProductionModeChecks.recursive_leafSalts_empty
    {proof : BatchOpeningProofLigerito} {recursiveSteps : ℕ}
    (hvalid : proof.PassesProductionModeChecks recursiveSteps)
    {recursiveProof : RecursiveProof}
    (hmem : recursiveProof ∈ proof.ligerito.recursiveProofs) :
    recursiveProof.leafSalts = [] := by
  exact hvalid.canonicalRecursiveShape.recursive_leafSalts_empty hmem

/-- The exact mathematical fields of Rust `VeilFlockProof`. -/
structure VeilFlockProof (shape : BatchShape) where
  proofNonce : Nonce256
  treeNonces : InitialTreeNonces
  maskedZerocheck : MaskedZerocheckProof shape
  maskedLincheck : LincheckProof
  maskedRingClaims : Fin ringClaimCount → MaskedRingClaim
  publicDirectBlindValues : Fin 1 → GhashField
  blindGrindNonce : Word64
  pcsOpen : BatchOpeningProofLigerito
  veil : ConstraintProof

/-- The exact preblinded PCS mode and recursive vector shape selected for the
registered production batch shape. -/
def VeilFlockProof.PassesProductionModeChecks {shape : BatchShape}
    (proof : VeilFlockProof shape) : Prop :=
  proof.pcsOpen.PassesProductionModeChecks (ligeritoRecursiveSteps shape)

theorem VeilFlockProof.PassesProductionModeChecks.zkBlind_eq_none
    {shape : BatchShape} {proof : VeilFlockProof shape}
    (hvalid : proof.PassesProductionModeChecks) :
    proof.pcsOpen.zkBlind = none := by
  exact hvalid.preblinded

theorem VeilFlockProof.PassesProductionModeChecks.recursive_roots_length
    {shape : BatchShape} {proof : VeilFlockProof shape}
    (hvalid : proof.PassesProductionModeChecks) :
    proof.pcsOpen.ligerito.recursiveRoots.length =
      ligeritoRecursiveSteps shape := by
  exact hvalid.canonicalRecursiveShape.recursiveRoots_length

theorem VeilFlockProof.PassesProductionModeChecks.recursive_proofs_length
    {shape : BatchShape} {proof : VeilFlockProof shape}
    (hvalid : proof.PassesProductionModeChecks) :
    proof.pcsOpen.ligerito.recursiveProofs.length =
      ligeritoRecursiveSteps shape - 1 := by
  exact hvalid.canonicalRecursiveShape.recursiveProofs_length

/-- The canonical public bundle verified by the production entry point. -/
structure VeilFlockProofBundle (shape : BatchShape) where
  digests : List Hash256
  commitment : Commitment
  proof : VeilFlockProof shape

/-- Canonical production PCS checks lifted to the public proof bundle. -/
def VeilFlockProofBundle.PassesProductionModeChecks {shape : BatchShape}
    (bundle : VeilFlockProofBundle shape) : Prop :=
  bundle.proof.PassesProductionModeChecks

/-- Public input to the formal experiment.  The registered R1CS is selected by
`shape`; the digest batch is the public statement carried by the bundle. -/
structure ProductionStatement (_shape : BatchShape) where
  digests : List Hash256

/-! ## Complete proof object of the formal production protocol

The recursive Ligerito Rust structures above record the intended wire-level
target for a separate future implementation-refinement theorem; no such
refinement is claimed here.  The cryptographic model already uses the stronger
conservative PCS observation: the complete folded word, both raw L0 opening
families, and all public-direct blinder evaluations. `FormalVeilFlockProof` is
the exact joint output of those existing executable Lean components. It
deliberately exposes at least what the production verifier sees; no unmodeled
Rust proof field is filled by an arbitrary value.
-/

/-- Complete FLOCK outer-PCS plus VEIL algebraic output at the registered
production dimensions. -/
abbrev ProductionAlgebraicProof (shape : BatchShape) (Rest : Type*) :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.View
    (K := Unit) (I := VeiledFlock.ProductionOuterCodeDomains.BaseScalarIndex shape)
    (P := Unit)
    (Opened := VeiledFlock.ProductionOuterCodeDomains.OpenedRows shape)
    (Rest := Rest) (rounds := expectedMasks shape) shape

/-- Every successful output of the formal production protocol.  Rejection or
grinding failure is represented by `none` at the enclosing experiment level.
The three roots are computed by `productionMerkleRoot`; every challenge and
sampling transcript is retained so joint, rather than marginal, behavior is
observable. -/
structure FormalVeilFlockProof (shape : BatchShape) (Rest : Type*) where
  proofNonce : Nonce256
  treeNonces : InitialTreeNonces
  roots : ProductionTree → OracleBlock
  equalityPoint :
    VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7)
  programmedAnswers :
    VeiledFlock.AdaptiveOracleProgramming.History
      (Outcome := OracleBlock) (programmedPoints shape)
  algebraic : ProductionAlgebraicProof shape Rest
  blindChallenge : GhashField
  multiplicationAlpha : GhashField
  linearRho : GhashField
  hadamardRho : GhashField
  productCoefficient : GhashField
  linearPositions : Finset (Fin linearCodeLength)
  hadamardPositions : Finset (Fin hadamardCodeLength)
  blindGrindingNonce : Word64
  ligeritoGrindingNonces : List Word64
  finalTranscript : List Byte

end VeiledFlock.ProductionNizkProof

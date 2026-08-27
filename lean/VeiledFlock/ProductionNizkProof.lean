import VeiledFlock.ConcreteParameters
import VeiledFlock.Field128Ghash
import VeiledFlock.ProductionMaskLayout
import VeiledFlock.ProductionZerocheckSchedule
import VeiledFlock.ProductionFraming
import VeiledFlock.ProductionEqualitySampler
import VeiledFlock.ProductionOuterCodeDomains
import VeiledFlock.ProductionPaddedAlgebraicE2E
import VeiledFlock.ProductionThreeTree

/-!
# Public proof object of the production VEIL + FLOCK protocol

These structures mirror the public Rust proof at the mathematical-value
level.  Fixed production lengths use `Fin`-indexed families, so malformed
vector lengths are not inhabitants of this model.  This is deliberately not
a Rust/bincode refinement: the latter remains a separate theorem.
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

/-- The canonical public bundle verified by the production entry point. -/
structure VeilFlockProofBundle (shape : BatchShape) where
  digests : List Hash256
  commitment : Commitment
  proof : VeilFlockProof shape

/-- Public input to the formal experiment.  The registered R1CS is selected by
`shape`; the digest batch is the public statement carried by the bundle. -/
structure ProductionStatement (_shape : BatchShape) where
  digests : List Hash256

/-! ## Complete proof object of the formal production protocol

The recursive Ligerito Rust structures above are the wire-level target of the
later implementation-refinement theorem.  The cryptographic model already
uses the stronger conservative PCS observation: the complete folded word,
both raw L0 opening families, and all public-direct blinder evaluations.
`FormalVeilFlockProof` is the exact joint output of those existing executable
Lean components.  It deliberately exposes at least what the production
verifier sees; no unmodeled Rust proof field is filled by an arbitrary value.
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

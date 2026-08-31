import VeiledFlock.Production.Nizk.BoundedOracle
import VeiledFlock.Production.Operational.CausalOperational
import VeiledFlock.Production.Merkle.ChallengeSampler
import VeiledFlock.Production.Core.Grinding
import VeiledFlock.Production.Core.GrindingProjection
import VeiledFlock.Production.Merkle.MerklePrelude
import VeiledFlock.Production.Nizk.NizkAdversary
import VeiledFlock.Production.Core.PositionProjection
import VeiledFlock.Production.Algebra.ShiftedCompiler
import VeiledFlock.Production.Merkle.UniquePositionSampler

/-!
# Concrete production VEIL + FLOCK security experiments

This module is the executable security-experiment boundary.  It does not take
a prover, simulator, transcript renderer, or any real/simulator agreement as
an argument.  The bodies invoke the existing production FLOCK mask machine,
the complete conservative outer-PCS/VEIL algebraic computation, the three
salted Merkle trees, exact Fiat--Shamir/rejection samplers, and bounded
first-success grinding against one `SharedOracleState`.

The relation-specific arguments are the formal public R1CS semantics already
required by `ProductionConcreteAlgebraic`; they are not replacement
algorithms for any protocol stage.  The simulator receives a public-state
constructor from the public statement and never receives the honest witness.
-/

namespace VeiledFlock.ProductionNizkExperiment

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.NonceSerialization
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionCodeDomains
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionMerkleTree
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPaddedAlgebraicE2E
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionShiftedCompiler
open VeiledFlock.ProductionThreeTree
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionUniquePositionSampler
open VeiledFlock.ProductionVeilCore
open VeiledFlock.ProductionVeilLayer
open VeiledFlock.TranscriptSchedule
open VeiledFlock.ProductionZerocheckSchedule

/-- Public FS/rejection outputs consumed by the algebraic FLOCK + VEIL
execution.  All position maps are constructed from the successful exact
bounded samplers, and their injectivity is retained in the type. -/
structure ProductionRest (shape : BatchShape) where
  equalityPoint :
    VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7)
  outerPositions : QueryIndex shape → CodeIndex shape
  outerPositions_injective : Injective outerPositions
  linearPositions : Fin veilQueryCount → Fin linearCodeLength
  linearPositions_injective : Injective linearPositions
  hadamardPositions : Fin veilQueryCount → Fin hadamardCodeLength
  hadamardPositions_injective : Injective hadamardPositions
  outerChallenge : GhashField
  blindChallenge : GhashField
  multiplicationAlpha : GhashField
  linearRho : GhashField
  hadamardRho : GhashField
  productCoefficient : GhashField
  outerChallenge_ne_zero : outerChallenge ≠ 0
  blindChallenge_ne_zero : blindChallenge ≠ 0
  multiplicationAlpha_ne_zero : multiplicationAlpha ≠ 0
  multiplicationAlpha_ne_one : multiplicationAlpha ≠ 1
  linearRho_ne_zero : linearRho ≠ 0
  hadamardRho_ne_zero : hadamardRho ≠ 0
  productCoefficient_ne_zero : productCoefficient ≠ 0

noncomputable section

/-- Honest/simulator private randomness other than the random-oracle table.
The programmed-answer tape is simulator randomness; the honest experiment
does not read it. -/
structure ProductionCoins (shape : BatchShape) where
  outer : VeiledFlock.ProductionOuterPaddedPcs.PreCoins
    (K := Unit) (I := BaseScalarIndex shape)
    (Pad := ActivePadding shape) (rounds := expectedMasks shape)
  layer : LayerCoins shape
  proofNonce : Nonce256
  treeNonces : InitialTreeNonces
  outerSalts : Fin (2 ^ (m shape - 11)) → NumericNonce
  linearSalts : Fin (2 ^ 13) → NumericNonce
  hadamardSalts : Fin (2 ^ 11) → NumericNonce
  simulatedAnswers : History (Outcome := OracleBlock) (programmedPoints shape)
  deriving Inhabited

/-- Product representation used only to put the mathematically finite uniform
distribution on the complete production coin record. -/
abbrev ProductionCoinTuple (shape : BatchShape) :=
  VeiledFlock.ProductionOuterPaddedPcs.PreCoins
      (K := Unit) (I := BaseScalarIndex shape)
      (Pad := ActivePadding shape) (rounds := expectedMasks shape) ×
    LayerCoins shape × Nonce256 × InitialTreeNonces ×
      (Fin (2 ^ (m shape - 11)) → NumericNonce) ×
      (Fin (2 ^ 13) → NumericNonce) ×
      (Fin (2 ^ 11) → NumericNonce) ×
      History (Outcome := OracleBlock) (programmedPoints shape)

def productionCoinsEquiv (shape : BatchShape) :
    ProductionCoins shape ≃ ProductionCoinTuple shape where
  toFun coins :=
    (coins.outer, coins.layer, coins.proofNonce, coins.treeNonces,
      coins.outerSalts, coins.linearSalts, coins.hadamardSalts,
      coins.simulatedAnswers)
  invFun coins :=
    { outer := coins.1
      layer := coins.2.1
      proofNonce := coins.2.2.1
      treeNonces := coins.2.2.2.1
      outerSalts := coins.2.2.2.2.1
      linearSalts := coins.2.2.2.2.2.1
      hadamardSalts := coins.2.2.2.2.2.2.1
      simulatedAnswers := coins.2.2.2.2.2.2.2 }
  left_inv coins := by cases coins; rfl
  right_inv coins := by
    rcases coins with ⟨outer, layer, proofNonce, treeNonces, outerSalts,
      linearSalts, hadamardSalts, simulatedAnswers⟩
    rfl

noncomputable instance productionCoinsFintype (shape : BatchShape) :
    Fintype (ProductionCoins shape) :=
  letI : Fintype (VeiledFlock.ProductionOuterPaddedPcs.PreCoins
      (K := Unit) (I := BaseScalarIndex shape)
      (Pad := ActivePadding shape) (rounds := expectedMasks shape)) :=
    Fintype.ofFinite _
  letI : Fintype (LayerCoins shape) := Fintype.ofFinite _
  letI : Fintype (Fin (2 ^ (m shape - 11)) → NumericNonce) :=
    Fintype.ofFinite _
  letI : Fintype (Fin (2 ^ 13) → NumericNonce) := Fintype.ofFinite _
  letI : Fintype (Fin (2 ^ 11) → NumericNonce) := Fintype.ofFinite _
  letI : Fintype
      (History (Outcome := OracleBlock) (programmedPoints shape)) :=
    Fintype.ofFinite _
  Fintype.ofEquiv (ProductionCoinTuple shape)
    (productionCoinsEquiv shape).symm

end

abbrev ProductionMaxPointLength (shape : BatchShape)
    (maxStartLength : ℕ) :=
  maxPointLengthFromBound (programmedPoints shape) maxStartLength 54

/-- Interpret the one bounded table as the byte-list oracle consumed by every
existing production component. -/
noncomputable def sharedByteOracle {maxPointLength : ℕ}
    (fallback : OracleBlock) (state : SharedOracleState maxPointLength) :
    List Byte → OracleBlock :=
  answerBounded fallback state.table

/-- Split a 128-column outer Merkle row into the 64 message lanes followed by
the 64 PCS-blinder lanes, exactly as the wide initial L0 matrix. -/
noncomputable def outerRowPayload {W : Type*} (shape : BatchShape)
    (baseMessage : W → BaseWord shape) (witness : W)
    (coins : ProductionCoins shape) (row : Fin (2 ^ (m shape - 11))) :
    List Byte :=
  let message := VeiledFlock.ProductionOuterPaddedPcs.fullMessage
    (fun _ : Unit ↦ baseMessage) (fun _ : Unit ↦ basePaddingEmbed shape)
    () witness coins.outer.1
  let encodedMessage := encodeBaseWord shape message
  let encodedBlind := encodeBaseWord shape coins.outer.2.1
  let rowIndex : CodeIndex shape :=
    (finCongr (outerCodePositions_eq_pow shape)).symm row
  let split : Fin (2 * outerLaneCount) ≃ LaneIndex ⊕ LaneIndex :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  matrixRowBytes fun column ↦ match split column with
    | .inl lane => encodedMessage rowIndex lane
    | .inr lane => encodedBlind rowIndex lane

/-- Exact outer initial L0 root. -/
noncomputable def outerRoot {W : Type*} (shape : BatchShape)
    (baseMessage : W → BaseWord shape) (witness : W)
    (coins : ProductionCoins shape) (oracle : List Byte → OracleBlock) :
    OracleBlock :=
  productionMerkleRoot oracle ⟨0, by decide⟩ ⟨0, by decide⟩
    coins.treeNonces.outer (BitVec.ofNat 64 (16 * (2 * outerLaneCount)))
    (m shape - 11) coins.outerSalts
    (outerRowPayload shape baseMessage witness coins)

/-- Build the algebraic coin tuple after all exact public samplers have
produced their `ProductionRest`. -/
def algebraicCoins {shape : BatchShape}
    (coins : ProductionCoins shape) (rest : ProductionRest shape) :
    AlgebraicCoins (Rest := ProductionRest shape) shape :=
  (coins.outer, coins.layer, rest)

/-- Deterministic ascending enumeration performed after Rust's `BTreeSet`
position sampler.  The resulting function is injective by construction. -/
noncomputable def positionsOfFinset {domain target : ℕ}
    (positions : Finset (Fin domain)) (hcard : positions.card = target) :
    Fin target → Fin domain :=
  Finset.orderEmbOfFin positions hcard

theorem positionsOfFinset_injective {domain target : ℕ}
    (positions : Finset (Fin domain)) (hcard : positions.card = target) :
    Function.Injective (positionsOfFinset positions hcard) :=
  (Finset.orderEmbOfFin positions hcard).injective

/-- The initial VEIL-linear commitment is made to the exact padded mask
vector and its additive mask column.  This matches production's placeholder
circuit commitment before the challenge-instantiated shifted circuit exists. -/
noncomputable def linearRowPayload (shape : BatchShape)
    (coins : ProductionCoins shape) (row : Fin (2 ^ 13)) : List Byte :=
  let masks : Fin (expectedMasks shape) → GhashField :=
    fun index ↦ coins.outer.2.2 index ()
  let logical := paddedMessage shape masks coins.layer.1
  let linearCoins := coins.layer.2.1
  let rowIndex : Fin linearCodeLength :=
    (finCongr (by decide : linearCodeLength = 2 ^ 13)).symm row
  matrixRowBytes fun column : Fin 2 ↦
    if hdata : column.val < 1 then
      linearCodeword shape logical
        (linearCoins.2 (Sum.inl ⟨column.val, hdata⟩)) rowIndex
    else
      linearCodeword shape linearCoins.1
        (linearCoins.2 (Sum.inr ())) rowIndex

/-- Exact initial VEIL-linear root in random-oracle channel 6. -/
noncomputable def linearRoot (shape : BatchShape)
    (coins : ProductionCoins shape) (oracle : List Byte → OracleBlock) :
    OracleBlock :=
  productionMerkleRoot oracle ⟨6, by decide⟩ ⟨0, by decide⟩
    coins.treeNonces.veilLinear (BitVec.ofNat 64 32) 13 coins.linearSalts
    (linearRowPayload shape coins)

/-- Complete four-column Hadamard matrix row: the three product columns
derived by the concrete correlated VEIL compiler, followed by its additive
mask column. -/
noncomputable def hadamardRowPayload {W Public : Type*} (shape : BatchShape)
    (spec : VeiledFlock.ProductionCorrelatedLayerSpec.Spec shape W
      Public)
    (witness : W) (coins : ProductionCoins shape)
    (row : Fin (2 ^ 11)) : List Byte :=
  let hadamardCoins := coins.layer.2.2.1
  let message :=
    VeiledFlock.ProductionCorrelatedVeilLayer.hadamardMessage
      spec.multiplicationSecret witness coins.layer.1
  let rowIndex : Fin hadamardCodeLength :=
    (finCongr (by decide : hadamardCodeLength = 2 ^ 11)).symm row
  matrixRowBytes fun column : Fin 4 ↦
    if hdata : column.val < 3 then
      let data : Fin 3 := ⟨column.val, hdata⟩
      hadamardCodeword (message data)
        (hadamardCoins.2 (Sum.inl data)) rowIndex
    else
      hadamardCodeword hadamardCoins.1
        (hadamardCoins.2 (Sum.inr ())) rowIndex

/-- Exact VEIL-Hadamard root in random-oracle channel 7. -/
noncomputable def hadamardRoot {W Public : Type*} (shape : BatchShape)
    (spec : VeiledFlock.ProductionCorrelatedLayerSpec.Spec shape W
      Public)
    (witness : W) (coins : ProductionCoins shape)
    (oracle : List Byte → OracleBlock) : OracleBlock :=
  productionMerkleRoot oracle ⟨7, by decide⟩ ⟨0, by decide⟩
    coins.treeNonces.veilHadamard (BitVec.ofNat 64 64) 11
    coins.hadamardSalts (hadamardRowPayload shape spec witness coins)

/-- The concrete joint FLOCK/outer-PCS/VEIL algebraic execution.  No proof
component is supplied as an argument: this invokes the existing complete
production view constructor directly. -/
noncomputable def productionAlgebraicProof
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (rest : ProductionRest shape) :
    ProductionAlgebraicProof shape (ProductionRest shape) :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.view shape
    (closedSecret shape (fun _ ↦ causalSecret) answers)
    (fun _ current ↦ current.outerChallenge)
    (fun _ ↦ baseMessage) (fun _ ↦ basePaddingEmbed shape)
    (fun current ↦ baseOpening shape current.outerPositions)
    (publicDirectFunctional shape publicPositions (weights answers))
    (fun history outer current ↦
      ProductionConcreteAlgebraic.layerSpec
        (context answers history outer current))
    witness (algebraicCoins coins rest)

/-- Characteristic two turns rejection of `1` into the exact nondegeneracy
premise used by the multiplication-padding compiler. -/
theorem one_add_ne_zero_of_ne_one (value : GhashField) (hvalue : value ≠ 1) :
    1 + value ≠ 0 := by
  intro hzero
  apply hvalue
  have hone : value + 1 = 0 := by simpa [add_comm] using hzero
  have hneg : value = -1 := eq_neg_of_add_eq_zero_left hone
  simpa [VeiledFlock.BinaryPolynomial.neg_eq_self_charTwo] using hneg

/-- Unbounded byte-level version of the honest production zerocheck schedule.
The initial two masked slices use the empty oracle prefix.  Every later pair
is recomputed from exactly the answers reached so far through `completion`,
so this is the prefix-causal schedule executed by the real prover. -/
noncomputable def zerocheckRealByteSchedule {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (absorbedPrefix : List Byte) (witness : W)
    (coins : ProductionCoins shape) :
    Schedule (Point := List Byte) (Outcome := OracleBlock) :=
  let startTranscript :=
    VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  appendSchedule
    (ProductionZerocheckSchedule.start shape absorbedPrefix startTranscript)
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
        causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2)
      (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
        causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2))

/-- The simulator's exact look-ahead zerocheck schedule.  The selected full
answer vector closes the causal secret before any point is programmed; the
schedule is then installed online in the same shared oracle. -/
noncomputable def zerocheckSimulatedByteSchedule {W : Type*}
    (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    Schedule (Point := List Byte) (Outcome := OracleBlock) :=
  let transcript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (simulatedState, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  appendSchedule
    (ProductionZerocheckSchedule.start shape absorbedPrefix transcript)
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (ProductionZerocheckSchedule.first shape transcript)
      (ProductionZerocheckSchedule.second shape transcript))

/-- Real-prover challenger bytes after the last FLOCK scalar and its two
masked round messages have been absorbed.  This is the final state of the
same prefix-adaptive schedule used by `zerocheckRealByteSchedule`; later
round messages are not computed from an empty oracle completion. -/
noncomputable def afterZerocheck {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (absorbedPrefix : List Byte) (witness : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    List Byte :=
  let startTranscript :=
    VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
      causalSecret completion
      (witness, coins.outer.1, coins.outer.2.1) coins.outer.2.2
  appendState
    (ProductionZerocheckSchedule.start shape absorbedPrefix startTranscript)
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
        causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2)
      (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
        causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2))
    (programmedPoints shape) answers

/-- Simulator challenger bytes after its complete programmed FLOCK schedule.
This is the final state of `zerocheckSimulatedByteSchedule` and depends only
on the public representative, simulator coins, and selected answer tape. -/
noncomputable def afterSimulatedZerocheck {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    List Byte :=
  let transcript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (simulatedState, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  appendState
    (ProductionZerocheckSchedule.start shape absorbedPrefix transcript)
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (ProductionZerocheckSchedule.first shape transcript)
      (ProductionZerocheckSchedule.second shape transcript))
    (programmedPoints shape) answers

/-- Successful rejection/grinding suffix needed to build the formal proof. -/
structure ProductionTail (shape : BatchShape) where
  rest : ProductionRest shape
  outerPositionSet : Finset (Fin (2 ^ (m shape - 11)))
  linearPositionSet : Finset (Fin linearCodeLength)
  hadamardPositionSet : Finset (Fin hadamardCodeLength)
  blindGrindingNonce : Word64
  ligeritoGrindingNonces : List Word64
  finalTranscript : List Byte

/-- The observable outputs of the exact rejection and grinding loops, before
the deterministic proof certificates needed by `ProductionRest` are attached.
Separating data from proof terms makes oracle transport state the actual joint
distribution equality without depending on proof irrelevance artifacts. -/
structure ProductionTailRaw (shape : BatchShape) where
  outerSet : Finset (Fin (2 ^ (m shape - 11)))
  linearSetPow : Finset (Fin (2 ^ 13))
  hadamardSetPow : Finset (Fin (2 ^ 11))
  blindChallenge : GhashField
  multiplicationAlpha : GhashField
  outerChallenge : GhashField
  linearRho : GhashField
  hadamardRho : GhashField
  productCoefficient : GhashField
  blindGrindingNonce : Word64
  ligeritoGrindingNonces : List Word64
  finalTranscript : List Byte

/-- The exact production blind-grinding predicate, named so both execution
and transport use definitionally the same decision procedure. -/
def blindGrindingGood (shape : BatchShape) : OracleBlock → Prop :=
  rustLeadingZeroBitsAtLeast (blindGrindingBits shape)
    (blindGrindingBits_le_eight shape)

noncomputable instance (shape : BatchShape) :
    DecidablePred (blindGrindingGood shape) := by
  unfold blindGrindingGood
  infer_instance

/-- The exact Secure-profile predicate at one flattened fold-grinding site. -/
def ligeritoGrindingGood (shape : BatchShape) (site : ℕ) :
    OracleBlock → Prop :=
  rustLeadingZeroBitsAtLeast (ligeritoFoldGrindingBitsAt shape site)
    (ligeritoFoldGrindingBitsAt_le_eight shape site)

noncomputable instance (shape : BatchShape) (site : ℕ) :
    DecidablePred (ligeritoGrindingGood shape site) := by
  unfold ligeritoGrindingGood
  infer_instance

/-- Execute `remaining` exact production first-success Ligerito grinding
loops in transcript order, beginning at flattened fold site `site`.  This
never chooses an arbitrary valid nonce. -/
noncomputable def grindLigeritoSites (shape : BatchShape)
    (oracle : List Byte → OracleBlock) :
    ℕ → ℕ → List Byte → Option (List Word64 × List Byte)
  | _, 0, transcript => some ([], transcript)
  | site, remaining + 1, transcript =>
      let state : Nonce256 := oracle (scalarPoint transcript)
      match grindPowBounded
          (ligeritoGrindingGood shape site)
          oracle state maxLigeritoTrials with
      | none => none
      | some nonce =>
          match grindLigeritoSites shape oracle (site + 1) remaining
              (afterGrind transcript nonce) with
          | none => none
          | some (nonces, finalTranscript) =>
              some (nonce :: nonces, finalTranscript)

/-- Execute the exact production FS/rejection/grinding control flow and retain
all jointly observable results.  No proof-only fields occur in this trace. -/
noncomputable def sampleProductionTailRaw (shape : BatchShape)
    (oracle : List Byte → OracleBlock) (transcript : List Byte) :
    Option (ProductionTailRaw shape) :=
  let grindState : Nonce256 := oracle (scalarPoint transcript)
  match grindPowBounded (blindGrindingGood shape) oracle grindState
      maxBlindTrials with
  | none => none
  | some blindNonce =>
    let afterBlindGrind := afterGrind transcript blindNonce
    match sampleNonzero oracle veilSamplingTrials afterBlindGrind with
    | none => none
    | some (blindChallenge, afterBlind) =>
      match sampleNotZeroOrOne oracle veilSamplingTrials afterBlind with
      | none => none
      | some (multiplicationAlpha, afterAlpha) =>
        match sampleNonzero oracle veilSamplingTrials afterAlpha with
        | none => none
        | some (outerChallenge, afterOuterChallenge) =>
          match sampleUniquePositions (rustLowPosition (m shape - 11))
              (outerL0QueryCount shape) veilSamplingTrials oracle
              afterOuterChallenge with
          | none => none
          | some (outerSet, afterOuterPositions) =>
            match sampleUniquePositions (rustLowPosition 13) veilQueryCount
                veilSamplingTrials oracle afterOuterPositions with
            | none => none
            | some (linearSetPow, afterLinearPositions) =>
              match sampleNonzero oracle veilSamplingTrials
                  afterLinearPositions with
              | none => none
              | some (linearRho, afterLinearRho) =>
                match sampleUniquePositions (rustLowPosition 11) veilQueryCount
                    veilSamplingTrials oracle afterLinearRho with
                | none => none
                | some (hadamardSetPow, afterHadamardPositions) =>
                  match sampleNonzero oracle veilSamplingTrials
                      afterHadamardPositions with
                  | none => none
                  | some (hadamardRho, afterHadamardRho) =>
                    match sampleNonzero oracle veilSamplingTrials
                        afterHadamardRho with
                    | none => none
                    | some (productCoefficient, afterProduct) =>
                      match grindLigeritoSites shape oracle 0
                          (ligeritoPositiveFoldGrindingSites shape) afterProduct with
                      | none => none
                      | some (ligeritoGrindingNonces, finalTranscript) =>
                        some {
                          outerSet := outerSet
                          linearSetPow := linearSetPow
                          hadamardSetPow := hadamardSetPow
                          blindChallenge := blindChallenge
                          multiplicationAlpha := multiplicationAlpha
                          outerChallenge := outerChallenge
                          linearRho := linearRho
                          hadamardRho := hadamardRho
                          productCoefficient := productCoefficient
                          blindGrindingNonce := blindNonce
                          ligeritoGrindingNonces := ligeritoGrindingNonces
                          finalTranscript := finalTranscript }

/-- The exact bounded FS/rejection/grinding tail shared by the real prover
and simulator.  Every accepted-set proof stored in `ProductionRest` is
derived from the successful concrete sampler call immediately above it. -/
noncomputable def sampleProductionTailOriginal (shape : BatchShape)
    (oracle : List Byte → OracleBlock)
    (equalityPoint : VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7))
    (transcript : List Byte) :
    Option (ProductionTail shape) := by
  classical
  let grindState : Nonce256 := oracle (scalarPoint transcript)
  match hblindGrind : grindPowBounded
      (blindGrindingGood shape)
      oracle grindState maxBlindTrials with
  | none => exact none
  | some blindNonce =>
    let afterBlindGrind := afterGrind transcript blindNonce
    match hblind : sampleNonzero oracle veilSamplingTrials afterBlindGrind with
    | none => exact none
    | some (blindChallenge, afterBlind) =>
      match halpha : sampleNotZeroOrOne oracle veilSamplingTrials afterBlind with
      | none => exact none
      | some (multiplicationAlpha, afterAlpha) =>
        match houterChallenge : sampleNonzero oracle veilSamplingTrials afterAlpha with
        | none => exact none
        | some (outerChallenge, afterOuterChallenge) =>
          match houter : sampleUniquePositions
              (rustLowPosition (m shape - 11)) (outerL0QueryCount shape)
              veilSamplingTrials oracle afterOuterChallenge with
          | none => exact none
          | some (outerSet, afterOuterPositions) =>
            match hlinear : sampleUniquePositions (rustLowPosition 13)
                veilQueryCount veilSamplingTrials oracle afterOuterPositions with
            | none => exact none
            | some (linearSetPow, afterLinearPositions) =>
              match hlinearRho : sampleNonzero oracle veilSamplingTrials
                  afterLinearPositions with
              | none => exact none
              | some (linearRho, afterLinearRho) =>
                match hhadamard : sampleUniquePositions (rustLowPosition 11)
                    veilQueryCount veilSamplingTrials oracle afterLinearRho with
                | none => exact none
                | some (hadamardSetPow, afterHadamardPositions) =>
                  match hhadamardRho : sampleNonzero oracle veilSamplingTrials
                      afterHadamardPositions with
                  | none => exact none
                  | some (hadamardRho, afterHadamardRho) =>
                    match hproduct : sampleNonzero oracle veilSamplingTrials
                        afterHadamardRho with
                    | none => exact none
                    | some (productCoefficient, afterProduct) =>
                      match hligerito : grindLigeritoSites shape oracle 0
                          (ligeritoPositiveFoldGrindingSites shape)
                          afterProduct with
                      | none => exact none
                      | some (ligeritoNonces, finalTranscript) =>
                        have houterCard : outerSet.card =
                            outerL0QueryCount shape :=
                          collectUnique_some_card
                            (rustLowPosition (m shape - 11))
                            (outerL0QueryCount shape) veilSamplingTrials oracle
                            afterOuterChallenge ∅ outerSet afterOuterPositions
                            (by simpa [sampleUniquePositions] using houter)
                        have hlinearCardPow : linearSetPow.card =
                            veilQueryCount :=
                          collectUnique_some_card (rustLowPosition 13)
                            veilQueryCount veilSamplingTrials oracle
                            afterOuterPositions ∅ linearSetPow
                            afterLinearPositions
                            (by simpa [sampleUniquePositions] using hlinear)
                        have hhadamardCardPow : hadamardSetPow.card =
                            veilQueryCount :=
                          collectUnique_some_card (rustLowPosition 11)
                            veilQueryCount veilSamplingTrials oracle
                            afterLinearRho ∅ hadamardSetPow
                            afterHadamardPositions
                            (by simpa [sampleUniquePositions] using hhadamard)
                        let outerPow := positionsOfFinset outerSet houterCard
                        let outerPositions : QueryIndex shape → CodeIndex shape :=
                          fun index ↦
                            (finCongr (outerCodePositions_eq_pow shape)).symm
                              (outerPow index)
                        let linearCast : Fin (2 ^ 13) → Fin linearCodeLength :=
                          (finCongr (by decide : linearCodeLength = 2 ^ 13)).symm
                        let hadamardCast : Fin (2 ^ 11) →
                            Fin hadamardCodeLength :=
                          (finCongr (by decide : hadamardCodeLength = 2 ^ 11)).symm
                        let linearSet := linearSetPow.map
                          ⟨linearCast, (finCongr
                            (by decide : linearCodeLength = 2 ^ 13)).symm.injective⟩
                        let hadamardSet := hadamardSetPow.map
                          ⟨hadamardCast, (finCongr
                            (by decide : hadamardCodeLength = 2 ^ 11)).symm.injective⟩
                        have hlinearCard : linearSet.card = veilQueryCount := by
                          simpa [linearSet] using hlinearCardPow
                        have hhadamardCard : hadamardSet.card = veilQueryCount := by
                          simpa [hadamardSet] using hhadamardCardPow
                        let linearPositions :=
                          positionsOfFinset linearSet hlinearCard
                        let hadamardPositions :=
                          positionsOfFinset hadamardSet hhadamardCard
                        exact some {
                          rest := {
                            equalityPoint := equalityPoint
                            outerPositions := outerPositions
                            outerPositions_injective :=
                              (finCongr
                                (outerCodePositions_eq_pow shape)).symm.injective.comp
                                (positionsOfFinset_injective outerSet houterCard)
                            linearPositions := linearPositions
                            linearPositions_injective :=
                              positionsOfFinset_injective linearSet hlinearCard
                            hadamardPositions := hadamardPositions
                            hadamardPositions_injective :=
                              positionsOfFinset_injective hadamardSet hhadamardCard
                            outerChallenge := outerChallenge
                            blindChallenge := blindChallenge
                            multiplicationAlpha := multiplicationAlpha
                            linearRho := linearRho
                            hadamardRho := hadamardRho
                            productCoefficient := productCoefficient
                            outerChallenge_ne_zero :=
                              sampleNonzero_some_ne_zero oracle veilSamplingTrials
                                afterAlpha outerChallenge afterOuterChallenge
                                houterChallenge
                            blindChallenge_ne_zero :=
                              sampleNonzero_some_ne_zero oracle veilSamplingTrials
                                afterBlindGrind blindChallenge afterBlind hblind
                            multiplicationAlpha_ne_zero :=
                              (sampleNotZeroOrOne_some oracle veilSamplingTrials
                                afterBlind multiplicationAlpha afterAlpha halpha).1
                            multiplicationAlpha_ne_one :=
                              (sampleNotZeroOrOne_some oracle veilSamplingTrials
                                afterBlind multiplicationAlpha afterAlpha halpha).2
                            linearRho_ne_zero :=
                              sampleNonzero_some_ne_zero oracle veilSamplingTrials
                                afterLinearPositions linearRho afterLinearRho
                                hlinearRho
                            hadamardRho_ne_zero :=
                              sampleNonzero_some_ne_zero oracle veilSamplingTrials
                                afterHadamardPositions hadamardRho afterHadamardRho
                                hhadamardRho
                            productCoefficient_ne_zero :=
                              sampleNonzero_some_ne_zero oracle veilSamplingTrials
                                afterHadamardRho productCoefficient afterProduct
                                hproduct }
                          outerPositionSet := outerSet
                          linearPositionSet := linearSet
                          hadamardPositionSet := hadamardSet
                          blindGrindingNonce := blindNonce
                          ligeritoGrindingNonces := ligeritoNonces
                          finalTranscript := finalTranscript }

/-- Deterministically attach the cardinality and accepted-set certificates
which `ProductionRest` retains.  Every condition here is guaranteed by the
successful concrete sampler producing `raw`; the branches make that invariant
explicit and keep certificate construction independent of the oracle. -/
noncomputable def finishProductionTailRaw (shape : BatchShape)
    (equalityPoint : VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7))
    (raw : ProductionTailRaw shape) : Option (ProductionTail shape) := by
  classical
  if houterCard : raw.outerSet.card = outerL0QueryCount shape then
    if hlinearCardPow : raw.linearSetPow.card = veilQueryCount then
      if hhadamardCardPow : raw.hadamardSetPow.card = veilQueryCount then
        if houterChallenge : raw.outerChallenge ≠ 0 then
          if hblindChallenge : raw.blindChallenge ≠ 0 then
            if halphaZero : raw.multiplicationAlpha ≠ 0 then
              if halphaOne : raw.multiplicationAlpha ≠ 1 then
                if hlinearRho : raw.linearRho ≠ 0 then
                  if hhadamardRho : raw.hadamardRho ≠ 0 then
                    if hproduct : raw.productCoefficient ≠ 0 then
                      let outerPow := positionsOfFinset raw.outerSet houterCard
                      let outerPositions : QueryIndex shape → CodeIndex shape :=
                        fun index ↦
                          (finCongr (outerCodePositions_eq_pow shape)).symm
                            (outerPow index)
                      let linearCast : Fin (2 ^ 13) → Fin linearCodeLength :=
                        (finCongr
                          (by decide : linearCodeLength = 2 ^ 13)).symm
                      let hadamardCast : Fin (2 ^ 11) →
                          Fin hadamardCodeLength :=
                        (finCongr
                          (by decide : hadamardCodeLength = 2 ^ 11)).symm
                      let linearSet := raw.linearSetPow.map
                        ⟨linearCast, (finCongr
                          (by decide : linearCodeLength = 2 ^ 13)).symm.injective⟩
                      let hadamardSet := raw.hadamardSetPow.map
                        ⟨hadamardCast, (finCongr
                          (by decide : hadamardCodeLength = 2 ^ 11)).symm.injective⟩
                      have hlinearCard : linearSet.card = veilQueryCount := by
                        simpa [linearSet] using hlinearCardPow
                      have hhadamardCard : hadamardSet.card = veilQueryCount := by
                        simpa [hadamardSet] using hhadamardCardPow
                      let linearPositions :=
                        positionsOfFinset linearSet hlinearCard
                      let hadamardPositions :=
                        positionsOfFinset hadamardSet hhadamardCard
                      exact some {
                        rest := {
                          equalityPoint := equalityPoint
                          outerPositions := outerPositions
                          outerPositions_injective :=
                            (finCongr
                              (outerCodePositions_eq_pow shape)).symm.injective.comp
                              (positionsOfFinset_injective raw.outerSet houterCard)
                          linearPositions := linearPositions
                          linearPositions_injective :=
                            positionsOfFinset_injective linearSet hlinearCard
                          hadamardPositions := hadamardPositions
                          hadamardPositions_injective :=
                            positionsOfFinset_injective hadamardSet hhadamardCard
                          outerChallenge := raw.outerChallenge
                          blindChallenge := raw.blindChallenge
                          multiplicationAlpha := raw.multiplicationAlpha
                          linearRho := raw.linearRho
                          hadamardRho := raw.hadamardRho
                          productCoefficient := raw.productCoefficient
                          outerChallenge_ne_zero := houterChallenge
                          blindChallenge_ne_zero := hblindChallenge
                          multiplicationAlpha_ne_zero := halphaZero
                          multiplicationAlpha_ne_one := halphaOne
                          linearRho_ne_zero := hlinearRho
                          hadamardRho_ne_zero := hhadamardRho
                          productCoefficient_ne_zero := hproduct }
                        outerPositionSet := raw.outerSet
                        linearPositionSet := linearSet
                        hadamardPositionSet := hadamardSet
                        blindGrindingNonce := raw.blindGrindingNonce
                        ligeritoGrindingNonces := raw.ligeritoGrindingNonces
                        finalTranscript := raw.finalTranscript }
                    else exact none
                  else exact none
                else exact none
              else exact none
            else exact none
          else exact none
        else exact none
      else exact none
    else exact none
  else exact none

/-- The exact bounded FS/rejection/grinding tail shared by the real prover and
simulator, with deterministic proof certificates attached after the complete
observable sampling trace has been fixed. -/
noncomputable def sampleProductionTail (shape : BatchShape)
    (oracle : List Byte → OracleBlock)
    (equalityPoint : VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7))
    (transcript : List Byte) : Option (ProductionTail shape) :=
  (sampleProductionTailRaw shape oracle transcript).bind
    (finishProductionTailRaw shape equalityPoint)

/-- Canonical public serialization present in both experiments before any
proof-dependent bytes.  Rust refinement of list-length framing is deliberately
outside this cryptographic experiment milestone. -/
def productionStatementDigest {shape : BatchShape}
    (statement : ProductionStatement shape) : List Byte :=
  statement.digests.flatMap nonceBytes

/-- All successful public control-flow data produced by the real protocol
before the final proof record is assembled.  This is not extra randomness:
`productionRealTrace` below deterministically derives it from the concrete
coins and the one bounded random-oracle table. -/
structure ProductionExecutionTrace (shape : BatchShape) where
  outerCommitment : OracleBlock
  linearCommitment : OracleBlock
  equalityPoint :
    VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7)
  answers : History (Outcome := OracleBlock) (programmedPoints shape)
  tail : ProductionTail shape

/-- Pure projection of the successful real execution from the shared table.
It follows the same causal order as `productionRealProof`; the state-monad
version additionally records audit events but never mutates the table while
the honest prover is querying it. -/
noncomputable def productionRealTrace
    {W : Type*}
    {maxPointLength : ℕ} (shape : BatchShape)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape)
    (table : BoundedBytes maxPointLength → OracleBlock) :
    Option (ProductionExecutionTrace shape) :=
  let oracle := answerBounded fallback table
  let outerCommitment := outerRoot shape baseMessage witness coins oracle
  let linearCommitment := linearRoot shape coins oracle
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest coins.proofNonce coins.treeNonces.outer
    coins.treeNonces.veilLinear coins.treeNonces.veilHadamard
    outerCommitment linearCommitment
  match sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
      veilSamplingTrials prelude with
  | none => none
  | some equalityPoint =>
      let schedule := zerocheckRealByteSchedule shape causalSecret completion
        equalityPoint.2.2 witness coins
      let answers := AdaptiveOracleProgramming.run schedule oracle
        (programmedPoints shape)
      let postZerocheck := afterZerocheck shape causalSecret completion
        equalityPoint.2.2 witness coins answers
      match sampleProductionTail shape oracle equalityPoint postZerocheck with
      | none => none
      | some tail => some {
          outerCommitment := outerCommitment
          linearCommitment := linearCommitment
          equalityPoint := equalityPoint
          answers := answers
          tail := tail }

/-- Assemble the public production proof from the already-computed concrete
components.  Keeping this record construction separate makes component
transport theorems rewrite the complete proof without unfolding the large
FLOCK/VEIL computations. -/
def assembleProductionProof (shape : BatchShape)
    (coins : ProductionCoins shape)
    (equalityPoint : VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (tail : ProductionTail shape)
    (algebraic : ProductionAlgebraicProof shape (ProductionRest shape))
    (outerCommitment linearCommitment hadamardCommitment : OracleBlock) :
    FormalVeilFlockProof shape (ProductionRest shape) :=
  {
    proofNonce := coins.proofNonce
    treeNonces := coins.treeNonces
    roots := fun tree ↦ match tree with
      | .outer => outerCommitment
      | .veilLinear => linearCommitment
      | .veilHadamard => hadamardCommitment
    equalityPoint := equalityPoint
    programmedAnswers := answers
    algebraic := algebraic
    blindChallenge := tail.rest.blindChallenge
    multiplicationAlpha := tail.rest.multiplicationAlpha
    linearRho := tail.rest.linearRho
    hadamardRho := tail.rest.hadamardRho
    productCoefficient := tail.rest.productCoefficient
    linearPositions := tail.linearPositionSet
    hadamardPositions := tail.hadamardPositionSet
    blindGrindingNonce := tail.blindGrindingNonce
    ligeritoGrindingNonces := tail.ligeritoGrindingNonces
    finalTranscript := tail.finalTranscript
  }

/-- Construct the full successful formal proof after the exact equality
sampler and causal FLOCK schedule. -/
noncomputable def finishProductionProof
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (witness : W) (coins : ProductionCoins shape)
    (equalityPoint : VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (tail : ProductionTail shape) (oracle : List Byte → OracleBlock)
    (outerCommitment linearCommitment : OracleBlock) :
    FormalVeilFlockProof shape (ProductionRest shape) :=
  let algebraic := productionAlgebraicProof shape causalSecret baseMessage
    publicPositions weights context answers witness coins tail.rest
  let layerContext :=
    context answers algebraic.2.1 algebraic.2.2.1 tail.rest
  let spec := ProductionConcreteAlgebraic.layerSpec layerContext
  let hadamardCommitment := hadamardRoot shape spec witness coins oracle
  assembleProductionProof shape coins equalityPoint answers tail algebraic
    outerCommitment linearCommitment hadamardCommitment

/-- Assemble the final proof from the deterministic successful execution
trace. -/
noncomputable def productionProofOfTrace
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (witness : W) (coins : ProductionCoins shape)
    (oracle : List Byte → OracleBlock)
    (trace : ProductionExecutionTrace shape) :
    FormalVeilFlockProof shape (ProductionRest shape) :=
  finishProductionProof shape causalSecret baseMessage publicPositions weights
    context witness coins trace.equalityPoint trace.answers trace.tail oracle
    trace.outerCommitment trace.linearCommitment

/-- Concrete real production protocol.  It computes all three Merkle roots,
the bounded equality sampler, the causally adaptive FLOCK schedule, all VEIL
rejection samplers, first-success grinding, and the complete algebraic view
from the honest witness and production coins. -/
noncomputable def productionRealProof
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ} (shape : BatchShape)
    (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape) :
    SharedOracleM maxPointLength
      (Option (FormalVeilFlockProof shape (ProductionRest shape))) :=
  fun initialState =>
  let oracle := sharedByteOracle fallback initialState
  let outerCommitment := outerRoot shape baseMessage witness coins oracle
  let linearCommitment := linearRoot shape coins oracle
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest coins.proofNonce coins.treeNonces.outer
    coins.treeNonces.veilLinear coins.treeNonces.veilHadamard
    outerCommitment linearCommitment
  match sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
      veilSamplingTrials prelude with
  | none => (none, initialState)
  | some equalityPoint =>
      let schedule := zerocheckRealByteSchedule shape causalSecret completion
        equalityPoint.2.2 witness coins
      let scheduleResult :=
        runSharedByteSchedule fallback .fiatShamir schedule
          (programmedPoints shape) initialState
      let answers := scheduleResult.1
      let stateAfterSchedule := scheduleResult.2
      let liveOracle := sharedByteOracle fallback stateAfterSchedule
      let postZerocheck := afterZerocheck shape causalSecret completion
        equalityPoint.2.2 witness coins answers
      match sampleProductionTail shape liveOracle equalityPoint postZerocheck with
      | none => (none, stateAfterSchedule)
      | some tail =>
          (some (finishProductionProof shape causalSecret baseMessage
              publicPositions weights context witness coins equalityPoint
              answers tail liveOracle outerCommitment linearCommitment),
            stateAfterSchedule)

/-- The proof value returned by the stateful real execution is exactly the
proof assembled from `productionRealTrace`.  The separate final state only
adds causal query audit events; its table is unchanged. -/
theorem productionRealProof_value
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ} (shape : BatchShape)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape)
    (state : SharedOracleState maxPointLength) :
    (productionRealProof shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context statement witness coins
      state).1 =
    (productionRealTrace shape fallback r1csDigest causalSecret completion
      baseMessage statement witness coins state.table).map
      (productionProofOfTrace shape causalSecret baseMessage publicPositions
        weights context witness coins
        (answerBounded fallback state.table)) := by
  simp only [productionRealProof, productionRealTrace]
  dsimp only [sharedByteOracle]
  split
  · rfl
  · rename_i equalityPoint hequality
    rw [runSharedByteSchedule_value]
    rw [runSharedByteSchedule_table]
    split <;> rfl

/-- The real prover only queries the shared oracle.  Consequently its full
execution audit may grow, but the underlying random-function table is
unchanged on every success or fail-closed branch. -/
theorem productionRealProof_table
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ} (shape : BatchShape)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape)
    (state : SharedOracleState maxPointLength) :
    (productionRealProof shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context statement witness coins
      state).2.table = state.table := by
  unfold productionRealProof
  dsimp only
  split
  · rfl
  · rename_i equalityPoint hequality
    let schedule := zerocheckRealByteSchedule shape causalSecret completion
      equalityPoint.2.2 witness coins
    let scheduleResult := runSharedByteSchedule fallback .fiatShamir schedule
      (programmedPoints shape) state
    have htable : scheduleResult.2.table = state.table :=
      runSharedByteSchedule_table fallback .fiatShamir schedule
        state
    change (match sampleProductionTail shape
      (sharedByteOracle fallback scheduleResult.2) equalityPoint
      (afterZerocheck shape causalSecret completion equalityPoint.2.2 witness
        coins scheduleResult.1) with
      | none => (none, scheduleResult.2)
      | some tail => (_, scheduleResult.2)).2.table = state.table
    split <;> exact htable

/-- Concrete witness-free production simulator.  Its only state constructor
is `publicRepresentative statement`, computed from the public statement.
No honest witness occurs in this definition's arguments or body.  The
selected scalar answers are installed causally in the same shared oracle
table observed by the adversary. -/
noncomputable def productionSimulatedProof
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ} (shape : BatchShape)
    (fallback : OracleBlock)
    (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (_completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (publicRepresentative : ProductionStatement shape → W)
    (statement : ProductionStatement shape) (coins : ProductionCoins shape) :
    SharedOracleM maxPointLength
      (Option (FormalVeilFlockProof shape (ProductionRest shape))) :=
  fun initialState =>
  let simulatedState := publicRepresentative statement
  let oracle := sharedByteOracle fallback initialState
  let outerCommitment := outerRoot shape baseMessage simulatedState coins oracle
  let linearCommitment := linearRoot shape coins oracle
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest coins.proofNonce coins.treeNonces.outer
    coins.treeNonces.veilLinear coins.treeNonces.veilHadamard
    outerCommitment linearCommitment
  match sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
      veilSamplingTrials prelude with
  | none => (none, initialState)
  | some equalityPoint =>
      let schedule := zerocheckSimulatedByteSchedule shape causalSecret
        equalityPoint.2.2 simulatedState coins coins.simulatedAnswers
      let programming := programSharedByteSchedule schedule
        coins.simulatedAnswers initialState
      match programming.1 with
      | .error _ => (none, programming.2)
      | .ok _ =>
          let stateAfterProgramming := programming.2
          let liveOracle := sharedByteOracle fallback stateAfterProgramming
          let postZerocheck := afterSimulatedZerocheck shape causalSecret
            equalityPoint.2.2 simulatedState coins coins.simulatedAnswers
          match sampleProductionTail shape liveOracle equalityPoint
              postZerocheck with
          | none => (none, stateAfterProgramming)
          | some tail =>
              (some (finishProductionProof shape causalSecret baseMessage
                  publicPositions weights context simulatedState coins
                  equalityPoint coins.simulatedAnswers tail liveOracle
                  outerCommitment linearCommitment),
                stateAfterProgramming)

/-- Concrete execution equation for the successful branch of the production
simulator.  This is a reduction lemma for the actual stateful simulator, not
an assumed coupling: the equality sample, programming success, and tail sample
determine its returned proof and final shared-oracle state definitionally. -/
theorem productionSimulatedProof_of_success
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ} (shape : BatchShape)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (publicRepresentative : ProductionStatement shape → W)
    (statement : ProductionStatement shape) (coins : ProductionCoins shape)
    (state : SharedOracleState maxPointLength)
    (equalityPoint :
      VeiledFlock.ProductionEqualitySampler.EqualitySample
        (m shape - kSkip - 7))
    (hequality :
      let simulatedState := publicRepresentative statement
      let oracle := sharedByteOracle fallback state
      let outerCommitment := outerRoot shape baseMessage simulatedState coins oracle
      let linearCommitment := linearRoot shape coins oracle
      let prelude := preEqualityTranscript (productionStatementDigest statement)
        r1csDigest coins.proofNonce coins.treeNonces.outer
        coins.treeNonces.veilLinear coins.treeNonces.veilHadamard
        outerCommitment linearCommitment
      sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
        veilSamplingTrials prelude = some equalityPoint)
    (hprogram :
      let schedule := zerocheckSimulatedByteSchedule shape causalSecret
        equalityPoint.2.2 (publicRepresentative statement) coins
        coins.simulatedAnswers
      (programSharedByteSchedule schedule coins.simulatedAnswers state).1 = .ok ())
    (tail : ProductionTail shape)
    (htail :
      let schedule := zerocheckSimulatedByteSchedule shape causalSecret
        equalityPoint.2.2 (publicRepresentative statement) coins
        coins.simulatedAnswers
      let programmed := programSharedByteSchedule schedule coins.simulatedAnswers state
      sampleProductionTail shape (sharedByteOracle fallback programmed.2)
        equalityPoint (afterSimulatedZerocheck shape causalSecret
          equalityPoint.2.2 (publicRepresentative statement) coins
          coins.simulatedAnswers) = some tail) :
    let simulatedState := publicRepresentative statement
    let oracle := sharedByteOracle fallback state
    let outerCommitment := outerRoot shape baseMessage simulatedState coins oracle
    let linearCommitment := linearRoot shape coins oracle
    let schedule := zerocheckSimulatedByteSchedule shape causalSecret
      equalityPoint.2.2 simulatedState coins coins.simulatedAnswers
    let programmed := programSharedByteSchedule schedule coins.simulatedAnswers state
    productionSimulatedProof shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context publicRepresentative statement
      coins state =
        (some (finishProductionProof shape causalSecret baseMessage
          publicPositions weights context simulatedState coins equalityPoint
          coins.simulatedAnswers tail (sharedByteOracle fallback programmed.2)
          outerCommitment linearCommitment), programmed.2) := by
  simp only [productionSimulatedProof, hequality, hprogram, htail]

/-! ## Complete adaptive malicious-verifier experiments -/

variable {AdversaryCoins FinalState : Type}

/-- The complete real security experiment.  Pre-proof adversarial queries,
all honest protocol oracle work, and proof-dependent post-proof queries are
sequenced in one `StateM SharedOracleState`; no oracle table is copied or
replaced between phases. -/
noncomputable def productionRealView
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength preQueries postQueries : ℕ} (shape : BatchShape)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape) maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (witness : W)
    (protocolCoins : ProductionCoins shape)
    (adversaryCoins : AdversaryCoins) :
    SharedOracleM maxPointLength
      (ProductionView (AdversaryCoins := AdversaryCoins)
        (FinalState := FinalState) shape (ProductionRest shape)
        maxPointLength) := fun initialState =>
  let preRun := runPreQueries adversary statement adversaryCoins initialState
  let preHistory := preRun.1
  let proofRun := productionRealProof shape fallback r1csDigest causalSecret
    completion baseMessage publicPositions weights context statement witness
    protocolCoins preRun.2
  let proof := proofRun.1
  let postRun := runPostQueries adversary statement proof adversaryCoins
    preHistory proofRun.2
  let postHistory := postRun.1
  ({
    statement := statement
    adversaryRandomness := adversaryCoins
    proof := proof
    oracleView := finishOracleView adversary statement proof adversaryCoins
      preHistory postHistory
  }, postRun.2)

/-- The complete simulated security experiment with the identical adversary
and phase schedule.  Its API is structurally witness-free: after the public
statement it takes only simulator/protocol coins and a public-state
constructor. -/
noncomputable def productionSimulatedView
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength preQueries postQueries : ℕ} (shape : BatchShape)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (publicRepresentative : ProductionStatement shape → W)
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape) maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (protocolCoins : ProductionCoins shape)
    (adversaryCoins : AdversaryCoins) :
    SharedOracleM maxPointLength
      (ProductionView (AdversaryCoins := AdversaryCoins)
        (FinalState := FinalState) shape (ProductionRest shape)
        maxPointLength) := fun initialState =>
  let preRun := runPreQueries adversary statement adversaryCoins initialState
  let preHistory := preRun.1
  let proofRun := productionSimulatedProof shape fallback r1csDigest causalSecret
    completion baseMessage publicPositions weights context publicRepresentative
    statement protocolCoins preRun.2
  let proof := proofRun.1
  let postRun := runPostQueries adversary statement proof adversaryCoins
    preHistory proofRun.2
  let postHistory := postRun.1
  ({
    statement := statement
    adversaryRandomness := adversaryCoins
    proof := proof
    oracleView := finishOracleView adversary statement proof adversaryCoins
      preHistory postHistory
  }, postRun.2)

/-- The complete simulator view contains at most the statically allotted
adaptive query slots.  This is a pathwise statement about the actual query
history stored in `ProductionView`, not an expectation or an admissibility
assumption. -/
theorem productionSimulatedView_query_length_le
    {PublicCoord W AdversaryCoins FinalState : Type} [Fintype PublicCoord]
    {maxPointLength preQueries postQueries : ℕ} (shape : BatchShape)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (publicRepresentative : ProductionStatement shape → W)
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape) maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (protocolCoins : ProductionCoins shape)
    (adversaryCoins : AdversaryCoins)
    (initialState : SharedOracleState maxPointLength) :
    ((productionSimulatedView shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context publicRepresentative adversary
      statement protocolCoins adversaryCoins initialState).1.oracleView.queries.length) ≤
        preQueries + postQueries := by
  let preRun := runPreQueries adversary statement adversaryCoins initialState
  let preHistory := preRun.1
  let proofRun := productionSimulatedProof shape fallback r1csDigest causalSecret
    completion baseMessage publicPositions weights context publicRepresentative
    statement protocolCoins preRun.2
  let proof := proofRun.1
  let postRun := runPostQueries adversary statement proof adversaryCoins
    preHistory proofRun.2
  let postHistory := postRun.1
  have hpre : preHistory.length ≤ preQueries := by
    rw [show preHistory = (runPreQueries adversary statement adversaryCoins
      initialState).1 by rfl, runPreQueries_value]
    simpa using runQueryValues_length_le
      (fun round history ↦ adversary.preQuery round statement adversaryCoins
        history)
      initialState.table (List.ofFn id) []
  have hpost : postHistory.length ≤ postQueries := by
    rw [show postHistory = (runPostQueries adversary statement proof
      adversaryCoins preHistory proofRun.2).1 by rfl, runPostQueries_value]
    simpa using runQueryValues_length_le
      (fun round history ↦ adversary.postQuery round statement proof
        adversaryCoins preHistory history)
      proofRun.2.table (List.ofFn id) []
  change (preHistory ++ postHistory).length ≤ preQueries + postQueries
  simpa only [List.length_append] using Nat.add_le_add hpre hpost

end VeiledFlock.ProductionNizkExperiment

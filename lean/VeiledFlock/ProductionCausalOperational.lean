import VeiledFlock.ProductionCausalScheduleTransport
import VeiledFlock.ProductionCoupledOperational

/-!
# Causal production operational simulator

This module instantiates the lookahead operational simulator with the exact
flat mask cursor and `FsChallenger` byte schedule.  Unlike the lower-level
theorem, it exposes no per-round serialization assumptions.  Oracle-prefix
causality and the algebraic view equivalence discharge them internally.
-/

namespace VeiledFlock.ProductionCausalOperational

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalMaskTranscript
open VeiledFlock.ProductionCausalScheduleTransport
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionZerocheckSchedule
open VeiledFlock.TranscriptSchedule

variable {Direct PublicCoord W Rest FullView : Type*}
variable [Fintype PublicCoord]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]

abbrev State (shape : BatchShape) :=
  VeiledFlock.ProductionOuterPaddedPcs.State
    (I := BaseScalarIndex shape) (Pad := ActivePadding shape) (W := W)

abbrev AlgebraicCoins (shape : BatchShape) :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
    (K := Unit) (I := BaseScalarIndex shape)
    (Pad := ActivePadding shape) (Rest := Rest)
    (rounds := expectedMasks shape) shape

abbrev AlgebraicView (shape : BatchShape) :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.View
    (K := Unit) (I := BaseScalarIndex shape) (P := Direct)
    (Opened := OpenedRows shape) (Rest := Rest)
    (rounds := expectedMasks shape) shape

abbrev ProductionCausalSecret (shape : BatchShape) :=
  VeiledFlock.ProductionCausalMaskTranscript.CausalSecret
    (W := State (W := W) shape) shape

def closedSecret (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : Rest) :
    Secret (F := GhashField) (I := Unit)
      (W := State (W := W) shape) :=
  closeSecret (VeiledFlock.ProductionMaskCausality.available shape)
    (VeiledFlock.ProductionMaskCausality.available_le_sites shape)
    (causalSecret rest) answers

noncomputable def coinTranscript (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (witness : W) (coins : AlgebraicCoins (Rest := Rest) shape) :
    MaskedTranscript shape :=
  transcript shape (causalSecret coins.2.2) answers
    (witness, coins.1.1, coins.1.2.1) coins.1.2.2

noncomputable def honestStart (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (absorbedPrefix : AlgebraicCoins (Rest := Rest) shape →
      List Byte)
    (witness : W) (coins : AlgebraicCoins (Rest := Rest) shape) :
    List Byte :=
  start shape (absorbedPrefix coins)
    (honestStartTranscript shape (causalSecret coins.2.2) completion
      (witness, coins.1.1, coins.1.2.1) coins.1.2.2)

noncomputable def simulatorStart (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : AlgebraicCoins (Rest := Rest) shape →
      History (Outcome := OracleBlock) (programmedPoints shape) → List Byte)
    (witness : W) (coins : AlgebraicCoins (Rest := Rest) shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    List Byte :=
  start shape (absorbedPrefix coins answers)
    (coinTranscript shape causalSecret answers witness coins)

noncomputable def honestFirst (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : AlgebraicCoins (Rest := Rest) shape) :
    ∀ oracleRounds,
      History (Outcome := OracleBlock) (oracleRounds + 1) → GhashField :=
  VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
    (causalSecret coins.2.2) completion
    (witness, coins.1.1, coins.1.2.1) coins.1.2.2

noncomputable def honestSecond (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : AlgebraicCoins (Rest := Rest) shape) :
    ∀ oracleRounds,
      History (Outcome := OracleBlock) (oracleRounds + 1) → GhashField :=
  VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
    (causalSecret coins.2.2) completion
    (witness, coins.1.1, coins.1.2.1) coins.1.2.2

noncomputable def simulatorFirst (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (witness : W) (coins : AlgebraicCoins (Rest := Rest) shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    ∀ oracleRounds,
      History (Outcome := OracleBlock) (oracleRounds + 1) → GhashField :=
  first shape (coinTranscript shape causalSecret answers witness coins)

noncomputable def simulatorSecond (shape : BatchShape)
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (witness : W) (coins : AlgebraicCoins (Rest := Rest) shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    ∀ oracleRounds,
      History (Outcome := OracleBlock) (oracleRounds + 1) → GhashField :=
  second shape (coinTranscript shape causalSecret answers witness coins)

/-- The production algebraic translation, closed against the externally
causal honest message function. -/
noncomputable def productionAnswerEquiv
    (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Function.Injective (positions rest))
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (challenge : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) → Rest →
        GhashField)
    (hchallenge : ∀ answers history rest,
      challenge answers history rest ≠ 0)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) → Rest → Direct →
        PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Direct)
        (Opened := OpenedRows shape) → Rest →
      LayerContext shape W (Public shape)
        (publicStatement shape publicPositions baseMessage))
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    AlgebraicCoins (Rest := Rest) shape ≃ AlgebraicCoins (Rest := Rest) shape :=
  VeiledFlock.ProductionCoupledOperational.answerEquiv shape positions
    hpositions (closedSecret shape causalSecret) challenge hchallenge
    baseMessage publicPositions weights context left right answers

/-- Projecting the complete production view equality onto its adaptive mask
history gives the exact full transcript equality consumed by the causal byte
transport. -/
theorem coinTranscript_productionAnswerEquiv
    (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Function.Injective (positions rest))
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (challenge : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) → Rest →
        GhashField)
    (hchallenge : ∀ answers history rest,
      challenge answers history rest ≠ 0)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) → Rest → Direct →
        PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Direct)
        (Opened := OpenedRows shape) → Rest →
      LayerContext shape W (Public shape)
        (publicStatement shape publicPositions baseMessage))
    (representative : Public shape → W)
    (hrepresentative : ∀ publicInput,
      publicStatement shape publicPositions baseMessage
        (representative publicInput) = publicInput)
    (witness : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (coins : AlgebraicCoins (Rest := Rest) shape) :
    let simulatedWitness := representative
      (publicStatement shape publicPositions baseMessage witness)
    coinTranscript shape causalSecret answers simulatedWitness
        (productionAnswerEquiv shape positions hpositions causalSecret
          challenge hchallenge baseMessage publicPositions weights context
          witness simulatedWitness answers coins) =
      coinTranscript shape causalSecret answers witness coins := by
  classical
  dsimp only
  let simulatedWitness := representative
    (publicStatement shape publicPositions baseMessage witness)
  let layer := fun history outer rest ↦
    ProductionConcreteAlgebraic.layerSpec
      (context answers history outer rest)
  have hview :=
    VeiledFlock.ProductionPaddedAlgebraicE2E.view_coinEquiv shape
      (closedSecret shape causalSecret answers)
      (challenge answers) (hchallenge answers)
      (fun _ ↦ baseMessage) (fun _ ↦ basePaddingEmbed shape)
      (fun rest ↦ baseOpening shape (positions rest))
      (fun rest ↦ outerPaddingQueryEquiv shape (positions rest)
        (hpositions rest))
      (opening_paddingEmbed shape positions hpositions)
      (publicDirectFunctional shape publicPositions (weights answers))
      (publicStatement shape publicPositions baseMessage)
      (publicDirect_kernel shape publicPositions baseMessage (weights answers))
      layer
      (fun _ _ _ ↦ ProductionConcreteAlgebraic.layerSpec_statement _)
      witness simulatedWitness
      (by
        exact (hrepresentative
          (publicStatement shape publicPositions baseMessage witness)).symm)
      coins
  have hhistory := congrArg (fun view ↦ view.2.1) hview
  exact congrArg (fun history site ↦ history site ()) hhistory.symm

/-- Exact honest-to-Rust-shaped simulator identity with the literal mask
cursor and causal challenger schedule.  The sole remaining transcript premise
is equality of the absorbed prefix before the two round-one slices; every
round-one and recursive field/byte transport fact is proved internally. -/
theorem publicSimulator_causal_exact
    (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Function.Injective (positions rest))
    (causalSecret : Rest → ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (challenge : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) → Rest →
        GhashField)
    (hchallenge : ∀ answers history rest,
      challenge answers history rest ≠ 0)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) → Rest → Direct →
        PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      Prefix (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Direct)
        (Opened := OpenedRows shape) → Rest →
      LayerContext shape W (Public shape)
        (publicStatement shape publicPositions baseMessage))
    (representative : Public shape → W)
    (hrepresentative : ∀ publicInput,
      publicStatement shape publicPositions baseMessage
        (representative publicInput) = publicInput)
    (witness : W)
    (maxStartLength : ℕ)
    (realPrefix : AlgebraicCoins (Rest := Rest) shape → List Byte)
    (simulatedPrefix : AlgebraicCoins (Rest := Rest) shape →
      History (Outcome := OracleBlock) (programmedPoints shape) → List Byte)
    (hrealStart : ∀ coins,
      (honestStart shape causalSecret completion realPrefix witness coins).length ≤
        maxStartLength)
    (hsimulatedStart : ∀ coins answers,
      (simulatorStart shape causalSecret simulatedPrefix
        (representative
          (publicStatement shape publicPositions baseMessage witness))
        coins answers).length ≤ maxStartLength)
    (hprefixTransport : ∀ coins answers,
      simulatedPrefix
          (productionAnswerEquiv shape positions hpositions causalSecret
            challenge hchallenge baseMessage publicPositions weights context
            witness
            (representative
              (publicStatement shape publicPositions baseMessage witness))
            answers coins) answers =
        realPrefix coins)
    (continueWith : AlgebraicView
        (Direct := Direct) (Rest := Rest) shape →
      Oracle
        (Point := BoundedBytes
          (maxPointLengthFromBound (programmedPoints shape)
            maxStartLength 54))
        (Outcome := OracleBlock) →
      History (Outcome := OracleBlock) (programmedPoints shape) → FullView) :
    let secret := closedSecret shape causalSecret
    let simulatedWitness := representative
      (publicStatement shape publicPositions baseMessage witness)
    let layer := fun answers history outer rest ↦
      ProductionConcreteAlgebraic.layerSpec
        (context answers history outer rest)
    let realState := fun coins answers ↦
      VeiledFlock.ProductionPaddedAlgebraicE2E.view shape (secret answers)
        (challenge answers) (fun _ ↦ baseMessage)
        (fun _ ↦ basePaddingEmbed shape)
        (fun rest ↦ baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions (weights answers))
        (layer answers) witness coins
    let simulatedState := fun coins answers ↦
      VeiledFlock.ProductionPaddedAlgebraicE2E.view shape (secret answers)
        (challenge answers) (fun _ ↦ baseMessage)
        (fun _ ↦ basePaddingEmbed shape)
        (fun rest ↦ baseOpening shape (positions rest))
        (publicDirectFunctional shape publicPositions (weights answers))
        (layer answers) simulatedWitness coins
    let realStart := honestStart shape causalSecret completion realPrefix witness
    let simulatedStart := simulatorStart shape causalSecret simulatedPrefix
      simulatedWitness
    let realFirst := honestFirst shape causalSecret completion witness
    let realSecond := honestSecond shape causalSecret completion witness
    let simulatedFirst := simulatorFirst shape causalSecret simulatedWitness
    let simulatedSecond := simulatorSecond shape causalSecret simulatedWitness
    let realSchedule := fun coins ↦
      scalarSchedule (programmedPoints shape) maxStartLength realStart
        hrealStart VeiledFlock.Field128Serialization.encodeGhashField
        realFirst realSecond coins
    let simulatedSchedule := fun coins answers ↦
      scalarSchedule (programmedPoints shape) maxStartLength
        (fun algebraic ↦ simulatedStart algebraic answers)
        (fun algebraic ↦ hsimulatedStart algebraic answers)
        VeiledFlock.Field128Serialization.encodeGhashField
        (fun algebraic ↦ simulatedFirst algebraic answers)
        (fun algebraic ↦ simulatedSecond algebraic answers) coins
    (PMF.uniformOfFintype
      (AlgebraicCoins (Rest := Rest) shape ×
        Oracle
          (Point := BoundedBytes
            (maxPointLengthFromBound (programmedPoints shape)
              maxStartLength 54))
          (Outcome := OracleBlock))).map
        (VeiledFlock.LookaheadOperationalSimulator.honestMachine
          realState realSchedule continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.LookaheadScalarPrefixSimulator.ScalarSimulatorCoins
          (Point := BoundedBytes
            (maxPointLengthFromBound (programmedPoints shape)
              maxStartLength 54))
          (programmedPoints shape) simulatedSchedule)).map
        (VeiledFlock.LookaheadScalarPrefixSimulator.programmedMachine
          (programmedPoints shape) simulatedState simulatedSchedule
          (fun coins answers ↦
            scalarSchedule_injective (programmedPoints shape) maxStartLength
              (fun algebraic ↦ simulatedStart algebraic answers)
              (fun algebraic ↦ hsimulatedStart algebraic answers)
              VeiledFlock.Field128Serialization.encodeGhashField
              (fun algebraic ↦ simulatedFirst algebraic answers)
              (fun algebraic ↦ simulatedSecond algebraic answers)
              coins answers)
          continueWith) := by
  classical
  dsimp only
  apply VeiledFlock.ProductionCoupledOperational.publicSimulator_operational_exact
    shape positions hpositions (programmedPoints shape) maxStartLength
    (closedSecret shape causalSecret) challenge hchallenge baseMessage
    publicPositions weights context representative hrepresentative witness
    (honestStart shape causalSecret completion realPrefix witness)
    (simulatorStart shape causalSecret simulatedPrefix
      (representative
        (publicStatement shape publicPositions baseMessage witness)))
    hrealStart hsimulatedStart
    (honestFirst shape causalSecret completion witness)
    (honestSecond shape causalSecret completion witness)
    (simulatorFirst shape causalSecret
      (representative
        (publicStatement shape publicPositions baseMessage witness)))
    (simulatorSecond shape causalSecret
      (representative
        (publicStatement shape publicPositions baseMessage witness)))
  · intro coins answers
    let simulatedWitness := representative
      (publicStatement shape publicPositions baseMessage witness)
    let translated := productionAnswerEquiv shape positions hpositions
      causalSecret challenge hchallenge baseMessage publicPositions weights
      context witness simulatedWitness answers coins
    have htranscript := coinTranscript_productionAnswerEquiv shape positions
      hpositions causalSecret challenge hchallenge baseMessage publicPositions
      weights context representative hrepresentative witness answers coins
    exact VeiledFlock.ProductionCausalScheduleTransport.start_transport shape
      (causalSecret coins.2.2) completion answers
      (witness, coins.1.1, coins.1.2.1) coins.1.2.2
      (coinTranscript shape causalSecret answers simulatedWitness translated)
      (by
        simpa only [simulatedWitness, translated, coinTranscript] using
          htranscript)
      (hprefixTransport coins answers)
  · intro coins answers oracleRounds hle
    let simulatedWitness := representative
      (publicStatement shape publicPositions baseMessage witness)
    let translated := productionAnswerEquiv shape positions hpositions
      causalSecret challenge hchallenge baseMessage publicPositions weights
      context witness simulatedWitness answers coins
    have htranscript := coinTranscript_productionAnswerEquiv shape positions
      hpositions causalSecret challenge hchallenge baseMessage publicPositions
      weights context representative hrepresentative witness answers coins
    exact VeiledFlock.ProductionCausalScheduleTransport.first_transport shape
      (causalSecret coins.2.2) completion answers
      (witness, coins.1.1, coins.1.2.1) coins.1.2.2
      (coinTranscript shape causalSecret answers simulatedWitness translated)
      (by
        simpa only [simulatedWitness, translated, coinTranscript] using
          htranscript)
      oracleRounds hle
  · intro coins answers oracleRounds hle
    let simulatedWitness := representative
      (publicStatement shape publicPositions baseMessage witness)
    let translated := productionAnswerEquiv shape positions hpositions
      causalSecret challenge hchallenge baseMessage publicPositions weights
      context witness simulatedWitness answers coins
    have htranscript := coinTranscript_productionAnswerEquiv shape positions
      hpositions causalSecret challenge hchallenge baseMessage publicPositions
      weights context representative hrepresentative witness answers coins
    exact VeiledFlock.ProductionCausalScheduleTransport.second_transport shape
      (causalSecret coins.2.2) completion answers
      (witness, coins.1.1, coins.1.2.1) coins.1.2.2
      (coinTranscript shape causalSecret answers simulatedWitness translated)
      (by
        simpa only [simulatedWitness, translated, coinTranscript] using
          htranscript)
      oracleRounds hle

end VeiledFlock.ProductionCausalOperational

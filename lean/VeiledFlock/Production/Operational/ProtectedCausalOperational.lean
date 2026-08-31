import VeiledFlock.Production.Operational.CausalOperational
import VeiledFlock.Oracle.ProtectedLookaheadScalarPrefixSimulator

/-!
# Protected causal production simulator

This theorem combines the exact production algebraic translation, literal
`FsChallenger` byte schedule, causal flat mask cursor, 128-bit-prefix oracle
programming, and preservation of an arbitrary finite family of prior
adversary queries.  On the freshness event its full view is exactly equal to
the public simulator's view.
-/

namespace VeiledFlock.ProductionProtectedCausalOperational

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionZerocheckSchedule
open VeiledFlock.ProtectedAdaptiveOracle
open VeiledFlock.TranscriptSchedule

variable {Direct PublicCoord W Rest Prior FullView : Type*}
variable [Fintype PublicCoord]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Finite Prior]

omit [DecidableEq Rest] in
/-- Exact protected operational simulator.  The only protocol/refinement
premise left is transport of the absorbed pre-zerocheck prefix. -/
theorem publicSimulator_causal_protected_exact
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
    (fixedPoints : Prior →
      BoundedBytes
        (maxPointLengthFromBound (programmedPoints shape) maxStartLength 54))
    (hfixed : Function.Injective fixedPoints)
    (hfresh : ∀ coins answers prior site,
      fixedPoints prior ≠
        tracePoint
          (scalarSchedule (programmedPoints shape) maxStartLength
            (fun algebraic ↦
              simulatorStart shape causalSecret simulatedPrefix
                (representative
                  (publicStatement shape publicPositions baseMessage witness))
                algebraic answers)
            (fun algebraic ↦ hsimulatedStart algebraic answers)
            VeiledFlock.Field128Serialization.encodeGhashField
            (fun algebraic ↦
              simulatorFirst shape causalSecret
                (representative
                  (publicStatement shape publicPositions baseMessage witness))
                algebraic answers)
            (fun algebraic ↦
              simulatorSecond shape causalSecret
                (representative
                  (publicStatement shape publicPositions baseMessage witness))
                algebraic answers)
            coins) answers site)
    (continueWith : AlgebraicView
        (Direct := Direct) (Rest := Rest) shape →
      (Prior → OracleBlock) →
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
        (VeiledFlock.ProtectedLookaheadOperationalSimulator.honestMachine
          realState fixedPoints realSchedule continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.ProtectedLookaheadScalarPrefixSimulator.ScalarSimulatorCoins
          (Point := BoundedBytes
            (maxPointLengthFromBound (programmedPoints shape)
              maxStartLength 54))
          (programmedPoints shape) fixedPoints simulatedSchedule)).map
        (VeiledFlock.ProtectedLookaheadScalarPrefixSimulator.programmedMachine
          (programmedPoints shape) simulatedState fixedPoints simulatedSchedule
          (fun coins answers ↦
            ProtectedAdaptiveOracle.points_injective fixedPoints
              (simulatedSchedule coins answers) answers hfixed
              (scalarSchedule_injective (programmedPoints shape)
                maxStartLength
                (fun algebraic ↦ simulatedStart algebraic answers)
                (fun algebraic ↦ hsimulatedStart algebraic answers)
                VeiledFlock.Field128Serialization.encodeGhashField
                (fun algebraic ↦ simulatedFirst algebraic answers)
                (fun algebraic ↦ simulatedSecond algebraic answers)
                coins answers)
              (hfresh coins answers))
          continueWith) := by
  classical
  dsimp only
  let simulatedWitness := representative
    (publicStatement shape publicPositions baseMessage witness)
  let layer := fun answers history outer rest ↦
    ProductionConcreteAlgebraic.layerSpec
      (context answers history outer rest)
  let realState := fun coins answers ↦
    VeiledFlock.ProductionPaddedAlgebraicE2E.view shape
      (closedSecret shape causalSecret answers)
      (challenge answers) (fun _ ↦ baseMessage)
      (fun _ ↦ basePaddingEmbed shape)
      (fun rest ↦ baseOpening shape (positions rest))
      (publicDirectFunctional shape publicPositions (weights answers))
      (layer answers) witness coins
  let simulatedState := fun coins answers ↦
    VeiledFlock.ProductionPaddedAlgebraicE2E.view shape
      (closedSecret shape causalSecret answers)
      (challenge answers) (fun _ ↦ baseMessage)
      (fun _ ↦ basePaddingEmbed shape)
      (fun rest ↦ baseOpening shape (positions rest))
      (publicDirectFunctional shape publicPositions (weights answers))
      (layer answers) simulatedWitness coins
  let realSchedule := fun coins ↦
    scalarSchedule (programmedPoints shape) maxStartLength
      (honestStart shape causalSecret completion realPrefix witness)
      hrealStart VeiledFlock.Field128Serialization.encodeGhashField
      (honestFirst shape causalSecret completion witness)
      (honestSecond shape causalSecret completion witness) coins
  let simulatedSchedule := fun coins answers ↦
    scalarSchedule (programmedPoints shape) maxStartLength
      (fun algebraic ↦
        simulatorStart shape causalSecret simulatedPrefix simulatedWitness
          algebraic answers)
      (fun algebraic ↦ hsimulatedStart algebraic answers)
      VeiledFlock.Field128Serialization.encodeGhashField
      (fun algebraic ↦
        simulatorFirst shape causalSecret simulatedWitness algebraic answers)
      (fun algebraic ↦
        simulatorSecond shape causalSecret simulatedWitness algebraic answers)
      coins
  let algebraicEquiv := fun answers ↦
    productionAnswerEquiv shape positions hpositions causalSecret challenge
      hchallenge baseMessage publicPositions weights context witness
      simulatedWitness answers
  apply
    VeiledFlock.ProtectedLookaheadScalarPrefixSimulator.honest_simulator_exact
      (answerEquiv := algebraicEquiv)
  · intro coins answers
    exact VeiledFlock.ProductionPaddedAlgebraicE2E.view_coinEquiv shape
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
      (layer answers)
      (fun _ _ _ ↦ ProductionConcreteAlgebraic.layerSpec_statement _)
      witness simulatedWitness
      (by
        exact (hrepresentative
          (publicStatement shape publicPositions baseMessage witness)).symm)
      coins
  · intro coins answers site
    apply scalarSchedule_tracePoint_eq (programmedPoints shape)
      maxStartLength
      (honestStart shape causalSecret completion realPrefix witness)
      (fun algebraic ↦
        simulatorStart shape causalSecret simulatedPrefix simulatedWitness
          algebraic answers)
      hrealStart (fun algebraic ↦ hsimulatedStart algebraic answers)
      VeiledFlock.Field128Serialization.encodeGhashField
      (honestFirst shape causalSecret completion witness)
      (honestSecond shape causalSecret completion witness)
      (fun algebraic ↦
        simulatorFirst shape causalSecret simulatedWitness algebraic answers)
      (fun algebraic ↦
        simulatorSecond shape causalSecret simulatedWitness algebraic answers)
      coins (algebraicEquiv answers coins) answers
    · let translated := algebraicEquiv answers coins
      have htranscript := coinTranscript_productionAnswerEquiv shape positions
        hpositions causalSecret challenge hchallenge baseMessage publicPositions
        weights context representative hrepresentative witness answers coins
      exact VeiledFlock.ProductionCausalScheduleTransport.start_transport shape
        (causalSecret coins.2.2) completion answers
        (witness, coins.1.1, coins.1.2.1) coins.1.2.2
        (coinTranscript shape causalSecret answers simulatedWitness translated)
        (by
          simpa only [translated, algebraicEquiv, simulatedWitness,
            coinTranscript] using htranscript)
        (hprefixTransport coins answers)
    · intro oracleRounds hle
      let translated := algebraicEquiv answers coins
      have htranscript := coinTranscript_productionAnswerEquiv shape positions
        hpositions causalSecret challenge hchallenge baseMessage publicPositions
        weights context representative hrepresentative witness answers coins
      exact VeiledFlock.ProductionCausalScheduleTransport.first_transport shape
        (causalSecret coins.2.2) completion answers
        (witness, coins.1.1, coins.1.2.1) coins.1.2.2
        (coinTranscript shape causalSecret answers simulatedWitness translated)
        (by
          simpa only [translated, algebraicEquiv, simulatedWitness,
            coinTranscript] using htranscript)
        oracleRounds hle
    · intro oracleRounds hle
      let translated := algebraicEquiv answers coins
      have htranscript := coinTranscript_productionAnswerEquiv shape positions
        hpositions causalSecret challenge hchallenge baseMessage publicPositions
        weights context representative hrepresentative witness answers coins
      exact VeiledFlock.ProductionCausalScheduleTransport.second_transport shape
        (causalSecret coins.2.2) completion answers
        (witness, coins.1.1, coins.1.2.1) coins.1.2.2
        (coinTranscript shape causalSecret answers simulatedWitness translated)
        (by
          simpa only [translated, algebraicEquiv, simulatedWitness,
            coinTranscript] using htranscript)
        oracleRounds hle
end VeiledFlock.ProductionProtectedCausalOperational

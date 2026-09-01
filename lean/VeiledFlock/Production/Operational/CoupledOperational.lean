import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Oracle.LookaheadScalarPrefixSimulator
import VeiledFlock.Algebra.Field128Serialization
import VeiledFlock.Production.Algebra.ConcreteAlgebraic

/-!
# Production VEIL--FLOCK coupled operational simulator

This module instantiates the unchanged-oracle Fiat--Shamir coupling with the
exact production algebraic coin translation and the 32-byte scalar schedule.
The only serialization obligations exposed to the Rust refinement are the
bytes before the first programmed scalar and the two 16-byte field messages
emitted at each reached recursive round.  Schedule distinctness is proved
internally from the implementation's fixed 54-byte transcript growth.
-/

namespace VeiledFlock.ProductionCoupledOperational

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.Framing
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.TranscriptSchedule

variable {K Direct PublicCoord W Rest FullView : Type*}
variable {rounds : ℕ}
variable [Fintype K] [DecidableEq K] [Fintype (K → GhashField)]
variable [Fintype PublicCoord]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]

abbrev AlgebraicCoins (shape : BatchShape) :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
    (K := K) (I := BaseScalarIndex shape)
    (Pad := ActivePadding shape) (Rest := Rest)
    (rounds := rounds) shape

abbrev AlgebraicView (shape : BatchShape) :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.View
    (K := K) (I := BaseScalarIndex shape) (P := Direct)
    (Opened := OpenedRows shape) (Rest := Rest)
    (rounds := rounds) shape

/-- The unique production algebraic translation selected by the complete
vector of Fiat--Shamir oracle blocks. -/
noncomputable def answerEquiv
    (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Injective (positions rest))
    {sites : ℕ}
    (secret : History (Outcome := OracleBlock) sites → Rest →
      Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := BaseScalarIndex shape) (Pad := ActivePadding shape) (W := W)))
    (challenge : History (Outcome := OracleBlock) sites →
      Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ answers history rest,
      challenge answers history rest ≠ 0)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord →
      ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) sites →
      Prefix (K := K) (rounds := rounds) → Rest → Direct →
      PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) sites →
      Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Direct)
        (Opened := OpenedRows shape) → Rest →
      LayerContext shape W (Public shape)
        (publicStatement shape publicPositions baseMessage))
    (left right : W)
    (answers : History (Outcome := OracleBlock) sites) :
    AlgebraicCoins (K := K) (Rest := Rest) (rounds := rounds) shape ≃
      AlgebraicCoins (K := K) (Rest := Rest) (rounds := rounds) shape :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.coinEquiv shape (secret answers)
    (challenge answers) (hchallenge answers)
    (fun _ ↦ baseMessage) (fun _ ↦ basePaddingEmbed shape)
    (fun rest ↦ baseOpening shape (positions rest))
    (fun rest ↦ outerPaddingQueryEquiv shape (positions rest)
      (hpositions rest))
    (opening_paddingEmbed shape positions hpositions)
    (publicDirectFunctional shape publicPositions (weights answers))
    (fun history outer rest ↦
      ProductionConcreteAlgebraic.layerSpec
        (context answers history outer rest))
    left right

omit [Fintype K] [DecidableEq K] [DecidableEq Rest] in
/-- Exact honest-to-operational-simulator distributional identity for one
production proof.  The full oracle is available to `continueWith`, hence this
covers arbitrary bounded adaptive queries after the proof.  The three byte
transport premises are the deliberately small Rust-refinement boundary. -/
theorem publicSimulator_operational_exact
    (shape : BatchShape)
    (positions : Rest → QueryIndex shape → CodeIndex shape)
    (hpositions : ∀ rest, Injective (positions rest))
    (sites maxStartLength : ℕ)
    (secret : History (Outcome := OracleBlock) sites → Rest →
      Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := BaseScalarIndex shape) (Pad := ActivePadding shape) (W := W)))
    (challenge : History (Outcome := OracleBlock) sites →
      Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ answers history rest,
      challenge answers history rest ≠ 0)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord →
      ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) sites →
      Prefix (K := K) (rounds := rounds) → Rest → Direct →
      PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) sites →
      Prefix (K := K) (rounds := rounds) →
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
    (realStart :
      AlgebraicCoins (K := K) (Rest := Rest) (rounds := rounds) shape →
        List Byte)
    (simulatedStart :
      AlgebraicCoins (K := K) (Rest := Rest) (rounds := rounds) shape →
        History (Outcome := OracleBlock) sites → List Byte)
    (hrealStart : ∀ coins,
      (realStart coins).length ≤ maxStartLength)
    (hsimulatedStart : ∀ coins answers,
      (simulatedStart coins answers).length ≤ maxStartLength)
    (realFirst realSecond :
      AlgebraicCoins (K := K) (Rest := Rest) (rounds := rounds) shape →
        ∀ oracleRounds,
          History (Outcome := OracleBlock) (oracleRounds + 1) → GhashField)
    (simulatedFirst simulatedSecond :
      AlgebraicCoins (K := K) (Rest := Rest) (rounds := rounds) shape →
        History (Outcome := OracleBlock) sites → ∀ oracleRounds,
          History (Outcome := OracleBlock) (oracleRounds + 1) → GhashField)
    (hstartTransport : ∀ coins answers,
      simulatedStart
          (answerEquiv shape positions hpositions secret challenge hchallenge
            baseMessage publicPositions weights context witness
            (representative
              (publicStatement shape publicPositions baseMessage witness))
            answers coins) answers =
        realStart coins)
    (hfirstTransport : ∀ coins answers oracleRounds
      (hle : oracleRounds + 1 ≤ sites),
      simulatedFirst
          (answerEquiv shape positions hpositions secret challenge hchallenge
            baseMessage publicPositions weights context witness
            (representative
              (publicStatement shape publicPositions baseMessage witness))
            answers coins) answers
          oracleRounds
          (fun site ↦ answers (Fin.castLE hle site)) =
        realFirst coins oracleRounds
          (fun site ↦ answers (Fin.castLE hle site)))
    (hsecondTransport : ∀ coins answers oracleRounds
      (hle : oracleRounds + 1 ≤ sites),
      simulatedSecond
          (answerEquiv shape positions hpositions secret challenge hchallenge
            baseMessage publicPositions weights context witness
            (representative
              (publicStatement shape publicPositions baseMessage witness))
            answers coins) answers
          oracleRounds
          (fun site ↦ answers (Fin.castLE hle site)) =
        realSecond coins oracleRounds
          (fun site ↦ answers (Fin.castLE hle site)))
    (continueWith : AlgebraicView
        (K := K) (Direct := Direct) (Rest := Rest) (rounds := rounds) shape →
      Oracle
        (Point := BoundedBytes
          (maxPointLengthFromBound sites maxStartLength 54))
        (Outcome := OracleBlock) →
      History (Outcome := OracleBlock) sites → FullView) :
    let statement := publicStatement shape publicPositions baseMessage
    let simulatedWitness := representative (statement witness)
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
    let realSchedule := fun coins ↦
      scalarSchedule sites maxStartLength realStart hrealStart
        encodeGhashField realFirst realSecond coins
    let simulatedSchedule := fun coins answers ↦
      scalarSchedule sites maxStartLength
        (fun algebraic ↦ simulatedStart algebraic answers)
        (fun algebraic ↦ hsimulatedStart algebraic answers)
        encodeGhashField
        (fun algebraic ↦ simulatedFirst algebraic answers)
        (fun algebraic ↦ simulatedSecond algebraic answers) coins
    (PMF.uniformOfFintype
      (AlgebraicCoins (K := K) (Rest := Rest) (rounds := rounds) shape ×
        Oracle
          (Point := BoundedBytes
            (maxPointLengthFromBound sites maxStartLength 54))
          (Outcome := OracleBlock))).map
        (VeiledFlock.LookaheadOperationalSimulator.honestMachine
          realState realSchedule continueWith) =
      (PMF.uniformOfFintype
        (VeiledFlock.LookaheadScalarPrefixSimulator.ScalarSimulatorCoins
          (Point := BoundedBytes
            (maxPointLengthFromBound sites maxStartLength 54))
          sites simulatedSchedule)).map
        (VeiledFlock.LookaheadScalarPrefixSimulator.programmedMachine sites
          simulatedState simulatedSchedule
          (fun coins answers ↦
            scalarSchedule_injective sites maxStartLength
              (fun algebraic ↦ simulatedStart algebraic answers)
              (fun algebraic ↦ hsimulatedStart algebraic answers)
              encodeGhashField
              (fun algebraic ↦ simulatedFirst algebraic answers)
              (fun algebraic ↦ simulatedSecond algebraic answers)
              coins answers)
          continueWith) := by
  classical
  dsimp only
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
  let realSchedule := fun coins ↦
    scalarSchedule sites maxStartLength realStart hrealStart
      encodeGhashField realFirst realSecond coins
  let simulatedSchedule := fun coins answers ↦
    scalarSchedule sites maxStartLength
      (fun algebraic ↦ simulatedStart algebraic answers)
      (fun algebraic ↦ hsimulatedStart algebraic answers)
      encodeGhashField
      (fun algebraic ↦ simulatedFirst algebraic answers)
      (fun algebraic ↦ simulatedSecond algebraic answers) coins
  let algebraicEquiv := fun answers ↦
    answerEquiv shape positions hpositions secret challenge hchallenge
      baseMessage publicPositions weights context witness simulatedWitness
      answers
  apply VeiledFlock.LookaheadScalarPrefixSimulator.honest_simulator_exact
    (answerEquiv := algebraicEquiv)
  · intro coins answers
    exact VeiledFlock.ProductionPaddedAlgebraicE2E.view_coinEquiv shape
      (secret answers) (challenge answers) (hchallenge answers)
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
    apply scalarSchedule_tracePoint_eq sites maxStartLength realStart
      (fun algebraic ↦ simulatedStart algebraic answers)
      hrealStart (fun algebraic ↦ hsimulatedStart algebraic answers)
      encodeGhashField realFirst realSecond
      (fun algebraic ↦ simulatedFirst algebraic answers)
      (fun algebraic ↦ simulatedSecond algebraic answers) coins
      (algebraicEquiv answers coins) answers
    · exact hstartTransport coins answers
    · exact hfirstTransport coins answers
    · exact hsecondTransport coins answers

end VeiledFlock.ProductionCoupledOperational

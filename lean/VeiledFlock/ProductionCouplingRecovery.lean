import VeiledFlock.ProductionNizkViewCoupling

/-!
# Recovering the successful production coupling

The pointwise real/simulator theorem uses a trace-indexed reparameterization.
For the statistical-distance theorem that map must be shown to preserve the
uniform operational distribution, rather than being accepted as a coupling
assumption.  This file supplies the first concrete step: on a fixed successful
trace the original production coins and oracle table are recovered exactly
from the transported input.
-/

namespace VeiledFlock.ProductionCouplingRecovery

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.OracleProgramming
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs

/-- Replacing the same finite oracle coordinates twice retains only the last
replacement. -/
theorem program_program {Point Outcome : Type*} [Fintype Point]
    [DecidableEq Point] {sites : ℕ} (points : Fin sites → Point)
    (hinjective : Injective points) (oracle : Point → Outcome)
    (first second : Fin sites → Outcome) :
    program points hinjective
        (program points hinjective oracle first) second =
      program points hinjective oracle second := by
  apply (splitOracle points hinjective).injective
  simp [program]

/-- The part of a successful execution trace needed to invert the concrete
coin/oracle transport. -/
structure ProductionCouplingContext (shape : BatchShape) where
  equalityPoint :
    VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7)
  answers : History (Outcome := OracleBlock) (programmedPoints shape)
  rest : ProductionRest shape

def ProductionCouplingContext.ofTrace {shape : BatchShape}
    (trace : ProductionExecutionTrace shape) :
    ProductionCouplingContext shape :=
  { equalityPoint := trace.equalityPoint
    answers := trace.answers
    rest := trace.tail.rest }

def ProductionCouplingContext.ofProof {shape : BatchShape}
    (proof : FormalVeilFlockProof shape (ProductionRest shape)) :
    ProductionCouplingContext shape :=
  { equalityPoint := proof.equalityPoint
    answers := proof.programmedAnswers
    rest := proof.algebraic.1 }

@[simp]
theorem ProductionCouplingContext.ofProof_productionTraceProof
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxStartLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (witness : W) (coins : ProductionCoins shape)
    (table : BoundedBytes (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)
    (trace : ProductionExecutionTrace shape) :
    ProductionCouplingContext.ofProof
        (productionTraceProof shape fallback causalSecret baseMessage
          publicPositions weights context witness coins table trace) =
      ProductionCouplingContext.ofTrace trace := by
  rfl

/-- Inverse of the successful fixed-trace transport.  The simulator's answer
tape stores the honest answers.  The independent answer tape is recovered
from the transported oracle at the simulator programming points; programming
the honest answers back restores the Merkle-transported oracle before the
three-tree equivalence is inverted. -/
noncomputable def recoverProductionCouplingAt
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (left right : W) (fiber : ProductionCouplingContext shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (output : ProductionCouplingInput shape maxStartLength)
    (hstart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        fiber.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret fiber.answers
          (right, output.1.outer.1, output.1.outer.2.1)
          output.1.outer.2.2)).length ≤ maxStartLength) :
    ProductionCouplingInput shape maxStartLength := by
  let points := productionSimulatorProgramPoints shape maxStartLength
    causalSecret fiber.equalityPoint.2.2 right output.1 fiber.answers hstart
  let hinjective := productionSimulatorProgramPoints_injective shape
    maxStartLength causalSecret fiber.equalityPoint.2.2 right output.1
    fiber.answers hstart
  let independentAnswers := fun site ↦ output.2 (points site)
  let movedCoins := withSimulatedAnswers shape output.1 independentAnswers
  let movedOracle := program points hinjective output.2 fiber.answers
  exact (productionMerkleCoinOracleEquivAt shape movedCoins causalSecret
    baseMessage publicPositions weights context left right fiber.answers
    fiber.rest houter hlinear hhadamard).symm (movedCoins, movedOracle)

/-- Total recovery function used to transport equality between successful
fibers without carrying a dependent start-length proof in its API.  The
failure branch is irrelevant on successful production tapes. -/
noncomputable def recoverProductionCoupling
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (left right : W) (fiber : ProductionCouplingContext shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (output : ProductionCouplingInput shape maxStartLength) :
    ProductionCouplingInput shape maxStartLength := by
  classical
  by_cases hstart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        fiber.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret fiber.answers
          (right, output.1.outer.1, output.1.outer.2.1)
          output.1.outer.2.2)).length ≤ maxStartLength
  · exact recoverProductionCouplingAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context left right fiber houter
      hlinear hhadamard output hstart
  · exact output

theorem recoverProductionCoupling_of_start
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (left right : W) (fiber : ProductionCouplingContext shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (output : ProductionCouplingInput shape maxStartLength)
    (hstart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        fiber.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret fiber.answers
          (right, output.1.outer.1, output.1.outer.2.1)
          output.1.outer.2.2)).length ≤ maxStartLength) :
    recoverProductionCoupling shape maxStartLength causalSecret baseMessage
        publicPositions weights context left right fiber houter hlinear
        hhadamard output =
      recoverProductionCouplingAt shape maxStartLength causalSecret baseMessage
        publicPositions weights context left right fiber houter hlinear
        hhadamard output hstart := by
  unfold recoverProductionCoupling
  split
  · congr 1
  · rename_i hnot
    exfalso
    apply hnot
    exact hstart

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- The explicit recovery map is a left inverse of the exact coupling at every
successful real trace. -/
theorem recoverProductionCouplingAt_apply
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape) (maxStartLength : ℕ)
    (fallback : OracleBlock)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (publicStatement shape publicPositions baseMessage))
    (left right : W)
    (hpublic : publicStatement shape publicPositions baseMessage left =
      publicStatement shape publicPositions baseMessage right)
    (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (input : ProductionCouplingInput shape maxStartLength)
    (hstart :
      let moved := productionMerkleCoinOracleEquivAt shape input.1
        causalSecret baseMessage publicPositions weights context left right
        trace.answers trace.tail.rest houter hlinear hhadamard input
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        trace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret trace.answers
          (right, moved.1.outer.1, moved.1.outer.2.1)
          moved.1.outer.2.2)).length ≤ maxStartLength)
    (hrun : AdaptiveOracleProgramming.run
      (zerocheckRealByteSchedule shape causalSecret completion
        trace.equalityPoint.2.2 left input.1)
      (answerBounded fallback input.2) (programmedPoints shape) =
        trace.answers)
    (hfiat : isFiatShamirPoint trace.equalityPoint.2.2) :
    let output := productionCoupledInputAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context left right trace houter
      hlinear hhadamard input hstart
    recoverProductionCouplingAt shape maxStartLength causalSecret baseMessage
      publicPositions weights context left right
      (ProductionCouplingContext.ofTrace trace) houter hlinear hhadamard
      output (by simpa only [ProductionCouplingContext.ofTrace, output,
        productionCoupledInputAt,
        withSimulatedAnswers_outer] using hstart) = input := by
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let forwardPoints := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart
  let forwardInjective := productionSimulatorProgramPoints_injective shape
    maxStartLength causalSecret trace.equalityPoint.2.2 right moved.1
    trace.answers hstart
  let output : ProductionCouplingInput shape maxStartLength :=
    (withSimulatedAnswers shape moved.1 trace.answers,
      program forwardPoints forwardInjective moved.2 moved.1.simulatedAnswers)
  have houtputStart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        trace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret trace.answers
          (right, output.1.outer.1, output.1.outer.2.1)
          output.1.outer.2.2)).length ≤ maxStartLength := by
    simpa only [output, withSimulatedAnswers_outer] using hstart
  let recoveryPoints := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2 right output.1 trace.answers
    houtputStart
  let recoveryInjective := productionSimulatorProgramPoints_injective shape
    maxStartLength causalSecret trace.equalityPoint.2.2 right output.1
    trace.answers houtputStart
  have hpoints : recoveryPoints = forwardPoints := by
    funext site
    rfl
  subst recoveryPoints
  have hinjectives : recoveryInjective = forwardInjective := Subsingleton.elim _ _
  subst recoveryInjective
  have hanswer (site : Fin (programmedPoints shape)) :
      moved.2 (forwardPoints site) = trace.answers site := by
    have hfit := simulatedZerocheck_tracePoint_fits shape maxStartLength
      causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart
      site
    have h := productionMerkleCoinOracleEquivAt_answer_simulatorPoint shape
      fallback causalSecret completion baseMessage publicPositions weights
      context left right hpublic trace houter hlinear hhadamard input hrun
      hfiat site
    dsimp only at h
    rw [answerBounded_of_le fallback moved.2 _ hfit] at h
    simpa only [forwardPoints, productionSimulatorProgramPoints] using h
  have hindependent :
      (fun site ↦ output.2 (forwardPoints site)) =
        moved.1.simulatedAnswers := by
    funext site
    dsimp only [output]
    exact program_at forwardPoints forwardInjective moved.2
      moved.1.simulatedAnswers site
  have horacle :
      program forwardPoints forwardInjective output.2 trace.answers =
        moved.2 := by
    dsimp only [output]
    rw [program_program]
    have hexisting :
        (fun site ↦ moved.2 (forwardPoints site)) = trace.answers := by
      funext site
      exact hanswer site
    rw [← hexisting]
    exact program_existing forwardPoints forwardInjective moved.2
  have hcoins :
      withSimulatedAnswers shape output.1
          (fun site ↦ output.2 (forwardPoints site)) = moved.1 := by
    rw [hindependent]
    rfl
  have hpoints' :
      productionSimulatorProgramPoints shape maxStartLength causalSecret
        trace.equalityPoint.2.2 right output.1 trace.answers houtputStart =
        forwardPoints := hpoints
  have horacle' :
      program
          (productionSimulatorProgramPoints shape maxStartLength causalSecret
            trace.equalityPoint.2.2 right output.1 trace.answers houtputStart)
          (productionSimulatorProgramPoints_injective shape maxStartLength
            causalSecret trace.equalityPoint.2.2 right output.1 trace.answers
            houtputStart)
          output.2 trace.answers = moved.2 := by
    cases hpoints'
    exact horacle
  have hcoins' :
      withSimulatedAnswers shape output.1
          (fun site ↦ output.2
            (productionSimulatorProgramPoints shape maxStartLength
              causalSecret trace.equalityPoint.2.2 right output.1
              trace.answers houtputStart site)) = moved.1 := by
    simpa only [hpoints'] using hcoins
  change recoverProductionCouplingAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context left right
      (ProductionCouplingContext.ofTrace trace) houter hlinear hhadamard output
      houtputStart = input
  simp only [ProductionCouplingContext.ofTrace]
  unfold recoverProductionCouplingAt
  dsimp only
  rw [hcoins', horacle']
  exact (productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest houter hlinear hhadamard).symm_apply_apply input

end VeiledFlock.ProductionCouplingRecovery

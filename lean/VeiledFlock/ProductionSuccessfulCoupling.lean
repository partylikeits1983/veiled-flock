import VeiledFlock.ProductionCouplingRecovery
import VeiledFlock.FiniteSubtypeExtension
import VeiledFlock.ProductionOperationalGood

/-!
# The concrete successful production coupling is injective

The complete real/simulator equality is indexed by the actual successful
production trace.  Here that trace-indexed map is lifted to the operational
sample space and proved injective.  The proof recovers its indexing context
from the output of the actual witness-free simulator, then applies the exact
fixed-fiber recovery theorem.
-/

namespace VeiledFlock.ProductionSuccessfulCoupling

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionCouplingRecovery
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalGood
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.FiniteSubtypeExtension

section

variable {AdversaryCoins FinalState : Type} [Fintype AdversaryCoins]
variable {preQueries postQueries : ℕ}
variable (shape : BatchShape) (maxStartLength : ℕ)
variable (fallback : OracleBlock) (r1csDigest : List Byte)
variable (causalSecret : ProductionCausalSecret
  (W := Witness shape) shape)
variable (completion : Completion OracleBlock (programmedPoints shape))
variable (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
  VeiledFlock.ProductionOuterPcs.Prefix
    (K := Unit) (rounds := expectedMasks shape) →
  ProductionRest shape → Unit → PublicCoord shape → GhashField)
variable (context : History (Outcome := OracleBlock) (programmedPoints shape) →
  VeiledFlock.ProductionOuterPcs.Prefix
    (K := Unit) (rounds := expectedMasks shape) →
  VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
    (I := BaseScalarIndex shape) (P := Unit)
    (Opened := OpenedRows shape) → ProductionRest shape →
  LayerContext shape (Witness shape)
    (ProductionConcreteAlgebraic.Public shape)
    (ProductionConcreteOuter.publicStatement shape
      (publicPositions shape) (baseMessage shape)))
variable (statement : ProductionStatement shape) (witness : Witness shape)
variable (hvalid : PublicProjectionValid shape statement witness)
variable (houter : 108 + 16 * (2 * outerLaneCount) ≤
  ProductionMaxPointLength shape maxStartLength)
variable (hlinear : 108 + 32 ≤
  ProductionMaxPointLength shape maxStartLength)
variable (hhadamard : 108 + 64 ≤
  ProductionMaxPointLength shape maxStartLength)
variable (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
variable (hmax : productionStartLengthBound shape statement r1csDigest ≤
  maxStartLength)

abbrev Tape :=
  ProductionLedgerTape shape maxStartLength AdversaryCoins

/-- Successful operational tapes.  Aborting rejection/grinding executions
are outside this subtype and are charged to `BadTraceFailure`. -/
noncomputable def SuccessfulTape (tape : Tape shape maxStartLength
    (AdversaryCoins := AdversaryCoins)) : Prop :=
  ∃ trace, productionRealTrace shape fallback r1csDigest causalSecret
    completion (baseMessage shape) statement witness tape.1 tape.2.1 =
      some trace

noncomputable def successfulTrace
    (tape : {tape : Tape shape maxStartLength
      (AdversaryCoins := AdversaryCoins) //
        SuccessfulTape shape maxStartLength fallback r1csDigest causalSecret
          completion statement witness tape}) :
    ProductionExecutionTrace shape :=
  Classical.choose tape.property

theorem successfulTrace_spec
    (tape : {tape : Tape shape maxStartLength
      (AdversaryCoins := AdversaryCoins) //
        SuccessfulTape shape maxStartLength fallback r1csDigest causalSecret
          completion statement witness tape}) :
    productionRealTrace shape fallback r1csDigest causalSecret completion
      (baseMessage shape) statement witness tape.1.1 tape.1.2.1 =
        some (successfulTrace shape maxStartLength fallback r1csDigest
          causalSecret completion statement witness tape) :=
  Classical.choose_spec tape.property

/-- Coupling input selected by the actual successful real trace. -/
noncomputable def successfulCouplingInput
    (tape : {tape : Tape shape maxStartLength
      (AdversaryCoins := AdversaryCoins) //
        SuccessfulTape shape maxStartLength fallback r1csDigest causalSecret
          completion statement witness tape}) :
    ProductionCouplingInput shape maxStartLength := by
  let trace := successfulTrace shape maxStartLength fallback r1csDigest
    causalSecret completion statement witness tape
  let input : ProductionCouplingInput shape maxStartLength :=
    (tape.1.1, tape.1.2.1)
  have htrace := successfulTrace_spec shape maxStartLength fallback r1csDigest
    causalSecret completion statement witness tape
  have hstart := startBound_of_trace_success shape maxStartLength fallback
    r1csDigest causalSecret completion weights context statement witness
    houter hlinear hhadamard hmax tape.1 trace htrace
  exact productionCoupledInputAt shape maxStartLength causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    (publicRepresentative shape statement) trace houter hlinear hhadamard
    input hstart

/-- The successful coupling on the complete operational tape; adversarial
private coins are retained exactly. -/
noncomputable def successfulCoupling
    (tape : {tape : Tape shape maxStartLength
      (AdversaryCoins := AdversaryCoins) //
        SuccessfulTape shape maxStartLength fallback r1csDigest causalSecret
          completion statement witness tape}) :
    Tape shape maxStartLength (AdversaryCoins := AdversaryCoins) :=
  let coupled := successfulCouplingInput shape maxStartLength fallback
    r1csDigest causalSecret completion weights context statement witness
    houter hlinear hhadamard hmax tape
  (coupled.1, coupled.2, tape.1.2.2)

theorem initial_programming_ok
    (trace : ProductionExecutionTrace shape)
    (coins : ProductionCoins shape)
    (table : ProductionSharedOracleTable shape maxStartLength)
    (hstart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        trace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret trace.answers
          (publicRepresentative shape statement, coins.outer.1,
            coins.outer.2.1) coins.outer.2.2)).length ≤ maxStartLength) :
    let schedule := zerocheckSimulatedByteSchedule shape causalSecret
      trace.equalityPoint.2.2 (publicRepresentative shape statement) coins
      trace.answers
    (programSharedByteSchedule schedule trace.answers
      (initialSharedOracleState table)).1 = .ok () := by
  dsimp only
  let schedule := zerocheckSimulatedByteSchedule shape causalSecret
    trace.equalityPoint.2.2 (publicRepresentative shape statement) coins
    trace.answers
  refine programSharedByteSchedule_ok_of_fresh schedule trace.answers
      (initialSharedOracleState table) ?_ ?_ ?_ ?_
  · exact simulatedZerocheck_tracePoint_fits shape maxStartLength
      causalSecret trace.equalityPoint.2.2
      (publicRepresentative shape statement) coins trace.answers hstart
  · exact productionSimulatedZerocheck_tracePoints_injective shape
      causalSecret trace.equalityPoint.2.2
      (publicRepresentative shape statement) coins trace.answers
  · intro site
    rintro ⟨call, hmem, _⟩
    simp [initialSharedOracleState] at hmem
  · intro site
    rintro ⟨programming, hmem, _⟩
    simp [initialSharedOracleState] at hmem

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
include hvalid hnodes in
/-- Running the actual witness-free simulator on a successful transported
input yields the concrete real trace proof. -/
theorem successfulCoupling_simulatedProof
    (tape : {tape : Tape shape maxStartLength
      (AdversaryCoins := AdversaryCoins) //
        SuccessfulTape shape maxStartLength fallback r1csDigest causalSecret
          completion statement witness tape}) :
    let trace := successfulTrace shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness tape
    let coupled := successfulCouplingInput shape maxStartLength fallback
      r1csDigest causalSecret completion weights context statement witness
      houter hlinear hhadamard hmax tape
    (productionSimulatedProof shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context
      (publicRepresentative shape) statement coupled.1
      (initialSharedOracleState coupled.2)).1 =
        some (productionTraceProof shape fallback causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          tape.1.1 tape.1.2.1 trace) := by
  dsimp only
  let trace := successfulTrace shape maxStartLength fallback r1csDigest
    causalSecret completion statement witness tape
  let input : ProductionCouplingInput shape maxStartLength :=
    (tape.1.1, tape.1.2.1)
  have htrace := successfulTrace_spec shape maxStartLength fallback r1csDigest
    causalSecret completion statement witness tape
  let facts := productionRealTrace_facts shape fallback r1csDigest causalSecret
    completion (baseMessage shape) statement witness input.1 input.2 trace
    htrace
  have hstartOperational := startBound_of_trace_success shape maxStartLength fallback
    r1csDigest causalSecret completion weights context statement witness
    houter hlinear hhadamard hmax tape.1 trace htrace
  have hstart :
      let moved := productionMerkleCoinOracleEquivAt shape input.1
        causalSecret (baseMessage shape) (publicPositions shape) weights context
        witness (publicRepresentative shape statement) trace.answers
        trace.tail.rest houter hlinear hhadamard input
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        trace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret trace.answers
          (publicRepresentative shape statement, moved.1.outer.1,
            moved.1.outer.2.1) moved.1.outer.2.2)).length ≤
        maxStartLength := by
    simpa only [StartBound, couplingInput] using hstartOperational
  let coupled := productionCoupledInputAt shape maxStartLength causalSecret
    (baseMessage shape) (publicPositions shape) weights context witness
    (publicRepresentative shape statement) trace houter hlinear hhadamard
    input hstart
  have hpublic := witness_projection_eq_publicRepresentative shape statement
    witness hvalid
  have hok := initial_programming_ok shape maxStartLength causalSecret statement
    trace coupled.1 coupled.2 (by
      simpa only [coupled, productionCoupledInputAt,
        withSimulatedAnswers_outer] using hstart)
  have hrun := productionSimulatedProof_of_trace shape maxStartLength fallback
    r1csDigest causalSecret completion (baseMessage shape)
    (publicPositions shape) weights context statement witness
    (publicRepresentative shape statement) hpublic trace houter hlinear
    hhadamard hnodes input hstart facts (initialSharedOracleState coupled.2)
    rfl hok
  exact hrun.1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
include hvalid houter hlinear hhadamard hnodes hmax in
/-- The concrete successful real-to-simulator coupling is injective on the
actual operational tape.  No equality or coupling premise is assumed. -/
theorem successfulCoupling_injective :
    Function.Injective
      (successfulCoupling (AdversaryCoins := AdversaryCoins) shape
        maxStartLength fallback r1csDigest causalSecret completion weights
        context statement witness houter hlinear hhadamard hmax) := by
  classical
  intro left right heq
  let leftTrace := successfulTrace shape maxStartLength fallback r1csDigest
    causalSecret completion statement witness left
  let rightTrace := successfulTrace shape maxStartLength fallback r1csDigest
    causalSecret completion statement witness right
  let leftInput : ProductionCouplingInput shape maxStartLength :=
    (left.1.1, left.1.2.1)
  let rightInput : ProductionCouplingInput shape maxStartLength :=
    (right.1.1, right.1.2.1)
  let leftCoupled := successfulCouplingInput
    (AdversaryCoins := AdversaryCoins) shape maxStartLength fallback r1csDigest
    causalSecret completion weights context statement witness houter hlinear
    hhadamard hmax left
  let rightCoupled := successfulCouplingInput
    (AdversaryCoins := AdversaryCoins) shape maxStartLength fallback r1csDigest
    causalSecret completion weights context statement witness houter hlinear
    hhadamard hmax right
  have hcoupled : leftCoupled = rightCoupled := by
    change (leftCoupled.1, leftCoupled.2, left.1.2.2) =
      (rightCoupled.1, rightCoupled.2, right.1.2.2) at heq
    apply Prod.ext
    · exact congrArg (fun tape => tape.1) heq
    · exact congrArg (fun tape => tape.2.1) heq
  have hadversary : left.1.2.2 = right.1.2.2 := by
    change (leftCoupled.1, leftCoupled.2, left.1.2.2) =
      (rightCoupled.1, rightCoupled.2, right.1.2.2) at heq
    exact congrArg (fun tape => tape.2.2) heq
  have hsim := congrArg
    (fun coupled : ProductionCouplingInput shape maxStartLength =>
      (productionSimulatedProof shape fallback r1csDigest causalSecret
        completion (baseMessage shape) (publicPositions shape) weights context
        (publicRepresentative shape) statement coupled.1
        (initialSharedOracleState coupled.2)).1) hcoupled
  have hsimLeft := successfulCoupling_simulatedProof
    (AdversaryCoins := AdversaryCoins) shape maxStartLength fallback r1csDigest
    causalSecret completion weights context statement witness hvalid houter
    hlinear hhadamard hnodes hmax left
  have hsimRight := successfulCoupling_simulatedProof
    (AdversaryCoins := AdversaryCoins) shape maxStartLength fallback r1csDigest
    causalSecret completion weights context statement witness hvalid houter
    hlinear hhadamard hnodes hmax right
  change
    (productionSimulatedProof shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context
      (publicRepresentative shape) statement leftCoupled.1
      (initialSharedOracleState leftCoupled.2)).1 =
    (productionSimulatedProof shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context
      (publicRepresentative shape) statement rightCoupled.1
      (initialSharedOracleState rightCoupled.2)).1 at hsim
  change
    (productionSimulatedProof shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context
      (publicRepresentative shape) statement leftCoupled.1
      (initialSharedOracleState leftCoupled.2)).1 =
        some (productionTraceProof shape fallback causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          leftInput.1 leftInput.2 leftTrace) at hsimLeft
  change
    (productionSimulatedProof shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context
      (publicRepresentative shape) statement rightCoupled.1
      (initialSharedOracleState rightCoupled.2)).1 =
        some (productionTraceProof shape fallback causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          rightInput.1 rightInput.2 rightTrace) at hsimRight
  rw [hsimLeft, hsimRight] at hsim
  have hproof :
      productionTraceProof shape fallback causalSecret (baseMessage shape)
          (publicPositions shape) weights context witness leftInput.1
          leftInput.2 leftTrace =
        productionTraceProof shape fallback causalSecret (baseMessage shape)
          (publicPositions shape) weights context witness rightInput.1
          rightInput.2 rightTrace :=
    Option.some.inj hsim
  have hfiber := congrArg ProductionCouplingContext.ofProof hproof
  simp only [ProductionCouplingContext.ofProof_productionTraceProof] at hfiber
  have leftTraceSpec := successfulTrace_spec shape maxStartLength fallback
    r1csDigest causalSecret completion statement witness left
  have rightTraceSpec := successfulTrace_spec shape maxStartLength fallback
    r1csDigest causalSecret completion statement witness right
  let leftFacts := productionRealTrace_facts shape fallback r1csDigest
    causalSecret completion (baseMessage shape) statement witness leftInput.1
    leftInput.2 leftTrace leftTraceSpec
  let rightFacts := productionRealTrace_facts shape fallback r1csDigest
    causalSecret completion (baseMessage shape) statement witness rightInput.1
    rightInput.2 rightTrace rightTraceSpec
  have leftFiat : isFiatShamirPoint leftTrace.equalityPoint.2.2 := by
    let prelude := preEqualityTranscript (productionStatementDigest statement)
      r1csDigest leftInput.1.proofNonce leftInput.1.treeNonces.outer
      leftInput.1.treeNonces.veilLinear leftInput.1.treeNonces.veilHadamard
      leftTrace.outerCommitment leftTrace.linearCommitment
    have hprelude : isFiatShamirPoint prelude :=
      preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _
    exact sampleEqualityPointPrefix_some_isFiatShamir
      (answerBounded fallback leftInput.2) (m shape - kSkip - 7)
      veilSamplingTrials prelude hprelude leftTrace.equalityPoint
      leftFacts.equalityPoint
  have rightFiat : isFiatShamirPoint rightTrace.equalityPoint.2.2 := by
    let prelude := preEqualityTranscript (productionStatementDigest statement)
      r1csDigest rightInput.1.proofNonce rightInput.1.treeNonces.outer
      rightInput.1.treeNonces.veilLinear rightInput.1.treeNonces.veilHadamard
      rightTrace.outerCommitment rightTrace.linearCommitment
    have hprelude : isFiatShamirPoint prelude :=
      preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _
    exact sampleEqualityPointPrefix_some_isFiatShamir
      (answerBounded fallback rightInput.2) (m shape - kSkip - 7)
      veilSamplingTrials prelude hprelude rightTrace.equalityPoint
      rightFacts.equalityPoint
  have leftStartOperational := startBound_of_trace_success shape
    maxStartLength fallback r1csDigest causalSecret completion weights context
    statement witness houter hlinear hhadamard hmax left.1 leftTrace
    leftTraceSpec
  have rightStartOperational := startBound_of_trace_success shape
    maxStartLength fallback r1csDigest causalSecret completion weights context
    statement witness houter hlinear hhadamard hmax right.1 rightTrace
    rightTraceSpec
  have leftStart :
      let moved := productionMerkleCoinOracleEquivAt shape leftInput.1
        causalSecret (baseMessage shape) (publicPositions shape) weights context
        witness (publicRepresentative shape statement) leftTrace.answers
        leftTrace.tail.rest houter hlinear hhadamard leftInput
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        leftTrace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret leftTrace.answers
          (publicRepresentative shape statement, moved.1.outer.1,
            moved.1.outer.2.1) moved.1.outer.2.2)).length ≤
        maxStartLength := by
    simpa only [StartBound, couplingInput] using leftStartOperational
  have rightStart :
      let moved := productionMerkleCoinOracleEquivAt shape rightInput.1
        causalSecret (baseMessage shape) (publicPositions shape) weights context
        witness (publicRepresentative shape statement) rightTrace.answers
        rightTrace.tail.rest houter hlinear hhadamard rightInput
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        rightTrace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret rightTrace.answers
          (publicRepresentative shape statement, moved.1.outer.1,
            moved.1.outer.2.1) moved.1.outer.2.2)).length ≤
        maxStartLength := by
    simpa only [StartBound, couplingInput] using rightStartOperational
  have hpublic := witness_projection_eq_publicRepresentative shape statement
    witness hvalid
  have hrecoverLeft := recoverProductionCouplingAt_apply shape maxStartLength
    fallback causalSecret completion (baseMessage shape) (publicPositions shape)
    weights context witness (publicRepresentative shape statement) hpublic
    leftTrace houter hlinear hhadamard leftInput leftStart leftFacts.answers
    leftFiat
  have hrecoverRight := recoverProductionCouplingAt_apply shape maxStartLength
    fallback causalSecret completion (baseMessage shape) (publicPositions shape)
    weights context witness (publicRepresentative shape statement) hpublic
    rightTrace houter hlinear hhadamard rightInput rightStart
    rightFacts.answers rightFiat
  change recoverProductionCouplingAt shape maxStartLength causalSecret
      (baseMessage shape) (publicPositions shape) weights context witness
      (publicRepresentative shape statement)
      (ProductionCouplingContext.ofTrace leftTrace) houter hlinear hhadamard
      leftCoupled _ = leftInput at hrecoverLeft
  change recoverProductionCouplingAt shape maxStartLength causalSecret
      (baseMessage shape) (publicPositions shape) weights context witness
      (publicRepresentative shape statement)
      (ProductionCouplingContext.ofTrace rightTrace) houter hlinear hhadamard
      rightCoupled _ = rightInput at hrecoverRight
  have hleftCoupled : leftCoupled =
      productionCoupledInputAt shape maxStartLength causalSecret
        (baseMessage shape) (publicPositions shape) weights context witness
        (publicRepresentative shape statement) leftTrace houter hlinear
        hhadamard leftInput leftStart := by
    rfl
  have hrightCoupled : rightCoupled =
      productionCoupledInputAt shape maxStartLength causalSecret
        (baseMessage shape) (publicPositions shape) weights context witness
        (publicRepresentative shape statement) rightTrace houter hlinear
        hhadamard rightInput rightStart := by
    rfl
  have leftCoupledStart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        (ProductionCouplingContext.ofTrace leftTrace).equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret (ProductionCouplingContext.ofTrace leftTrace).answers
          (publicRepresentative shape statement, leftCoupled.1.outer.1,
            leftCoupled.1.outer.2.1) leftCoupled.1.outer.2.2)).length ≤
        maxStartLength := by
    rw [hleftCoupled]
    simpa only [ProductionCouplingContext.ofTrace, productionCoupledInputAt,
      withSimulatedAnswers_outer] using leftStart
  have rightCoupledStart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        (ProductionCouplingContext.ofTrace rightTrace).equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret (ProductionCouplingContext.ofTrace rightTrace).answers
          (publicRepresentative shape statement, rightCoupled.1.outer.1,
            rightCoupled.1.outer.2.1) rightCoupled.1.outer.2.2)).length ≤
        maxStartLength := by
    rw [hrightCoupled]
    simpa only [ProductionCouplingContext.ofTrace, productionCoupledInputAt,
      withSimulatedAnswers_outer] using rightStart
  have hrecoverTotalLeft :
      recoverProductionCoupling shape maxStartLength causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          (publicRepresentative shape statement)
          (ProductionCouplingContext.ofTrace leftTrace) houter hlinear
          hhadamard leftCoupled = leftInput := by
    rw [recoverProductionCoupling_of_start shape maxStartLength causalSecret
      (baseMessage shape) (publicPositions shape) weights context witness
      (publicRepresentative shape statement)
      (ProductionCouplingContext.ofTrace leftTrace) houter hlinear hhadamard
      leftCoupled leftCoupledStart]
    exact hrecoverLeft
  have hrecoverTotalRight :
      recoverProductionCoupling shape maxStartLength causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          (publicRepresentative shape statement)
          (ProductionCouplingContext.ofTrace rightTrace) houter hlinear
          hhadamard rightCoupled = rightInput := by
    rw [recoverProductionCoupling_of_start shape maxStartLength causalSecret
      (baseMessage shape) (publicPositions shape) weights context witness
      (publicRepresentative shape statement)
      (ProductionCouplingContext.ofTrace rightTrace) houter hlinear hhadamard
      rightCoupled rightCoupledStart]
    exact hrecoverRight
  have hinput : leftInput = rightInput := by
    have hpairs :
        (ProductionCouplingContext.ofTrace leftTrace, leftCoupled) =
          (ProductionCouplingContext.ofTrace rightTrace, rightCoupled) := by
      apply Prod.ext
      · exact hfiber
      · exact hcoupled
    have hrecover := congrArg
      (fun pair : ProductionCouplingContext shape ×
          ProductionCouplingInput shape maxStartLength =>
        recoverProductionCoupling shape maxStartLength causalSecret
          (baseMessage shape) (publicPositions shape) weights context witness
          (publicRepresentative shape statement) pair.1 houter hlinear
          hhadamard pair.2)
      hpairs
    exact hrecoverTotalLeft.symm.trans
      (hrecover.trans hrecoverTotalRight)
  apply Subtype.ext
  apply Prod.ext
  · change left.1.1 = right.1.1
    have hcoins := congrArg
      (fun input : ProductionCouplingInput shape maxStartLength => input.1)
      hinput
    exact hcoins
  · apply Prod.ext
    · change left.1.2.1 = right.1.2.1
      have htable := congrArg
        (fun input : ProductionCouplingInput shape maxStartLength => input.2)
        hinput
      exact htable
    · change left.1.2.2 = right.1.2.2
      exact hadversary

/-- A permutation of the entire operational tape whose successful branch is
exactly the concrete production coupling.  Its arbitrary complement branch is
never used cryptographically; all aborting tapes are in the explicit bad set. -/
noncomputable def productionCoinEquiv :
    Tape shape maxStartLength (AdversaryCoins := AdversaryCoins) ≃
      Tape shape maxStartLength (AdversaryCoins := AdversaryCoins) :=
  extend
    (SuccessfulTape shape maxStartLength fallback r1csDigest causalSecret
      completion statement witness)
    (successfulCoupling (AdversaryCoins := AdversaryCoins) shape
      maxStartLength fallback r1csDigest causalSecret completion weights
      context statement witness houter hlinear hhadamard hmax)
    (successfulCoupling_injective (AdversaryCoins := AdversaryCoins) shape
      maxStartLength fallback r1csDigest causalSecret completion weights
      context statement witness hvalid houter hlinear hhadamard hnodes hmax)

@[simp]
theorem productionCoinEquiv_apply_success
    (tape : Tape shape maxStartLength (AdversaryCoins := AdversaryCoins))
    (hsuccess : SuccessfulTape shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness tape) :
    productionCoinEquiv (AdversaryCoins := AdversaryCoins) shape
        maxStartLength fallback r1csDigest causalSecret completion weights
        context statement witness hvalid houter hlinear hhadamard hnodes hmax
        tape =
      successfulCoupling (AdversaryCoins := AdversaryCoins) shape
        maxStartLength fallback r1csDigest causalSecret completion weights
        context statement witness houter hlinear hhadamard hmax
        ⟨tape, hsuccess⟩ := by
  exact extend_apply_mem
    (SuccessfulTape shape maxStartLength fallback r1csDigest causalSecret
      completion statement witness)
    (successfulCoupling (AdversaryCoins := AdversaryCoins) shape
      maxStartLength fallback r1csDigest causalSecret completion weights
      context statement witness houter hlinear hhadamard hmax)
    (successfulCoupling_injective (AdversaryCoins := AdversaryCoins) shape
      maxStartLength fallback r1csDigest causalSecret completion weights
      context statement witness hvalid houter hlinear hhadamard hnodes hmax)
    tape hsuccess

end

end VeiledFlock.ProductionSuccessfulCoupling

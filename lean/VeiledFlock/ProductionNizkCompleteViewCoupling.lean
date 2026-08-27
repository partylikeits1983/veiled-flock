import VeiledFlock.ProductionNizkViewCoupling

/-!
# Complete production adversary-view equality on `Good`

This module connects the concrete VEIL+FLOCK proof coupling to the bounded
adaptive classical random-oracle adversary.  Both executions use one shared
table; equality covers the proof, all adversarial query/answer pairs, and the
adversary's final state/output stored in `ProductionView`.
-/

namespace VeiledFlock.ProductionNizkCoupling

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleProgramming
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPositionProjection

/-- The actual production real-to-simulator input map, with its causal start
bound taken from the concrete `Good` execution rather than repeated as a
dependent theorem argument. -/
noncomputable def productionCoupledInputOnGood
    {PublicCoord W : Type*} {AdversaryCoins FinalState : Type}
    [Fintype PublicCoord]
    {preQueries postQueries : ℕ}
    (shape : BatchShape) (maxStartLength : ℕ)
    (fallback : OracleBlock) (r1csDigest : List Byte)
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
        (VeiledFlock.ProductionConcreteOuter.publicStatement shape
          publicPositions baseMessage))
    (publicRepresentative : ProductionStatement shape → W)
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : W)
    (adversaryCoins : AdversaryCoins) (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ProductionCouplingInput shape maxStartLength)
    (hgood : ProductionGood shape maxStartLength fallback r1csDigest
      causalSecret completion baseMessage publicPositions weights context
      publicRepresentative adversary statement witness adversaryCoins trace
      houter hlinear hhadamard input) :
    ProductionCouplingInput shape maxStartLength :=
  productionCoupledInputAt shape maxStartLength causalSecret baseMessage
    publicPositions weights context witness (publicRepresentative statement)
    trace houter hlinear hhadamard input hgood.startBound

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem production_real_sim_equal_on_good
    {PublicCoord W : Type*} {AdversaryCoins FinalState : Type}
    [Fintype PublicCoord]
    {preQueries postQueries : ℕ}
    (shape : BatchShape) (maxStartLength : ℕ)
    (fallback : OracleBlock) (r1csDigest : List Byte)
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
        (VeiledFlock.ProductionConcreteOuter.publicStatement shape
          publicPositions baseMessage))
    (publicRepresentative : ProductionStatement shape → W)
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : W)
    (hpublic :
      VeiledFlock.ProductionConcreteOuter.publicStatement shape
        publicPositions baseMessage witness =
      VeiledFlock.ProductionConcreteOuter.publicStatement shape
        publicPositions baseMessage (publicRepresentative statement))
    (adversaryCoins : AdversaryCoins) (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ProductionCouplingInput shape maxStartLength)
    (hgood : ProductionGood shape maxStartLength fallback r1csDigest
      causalSecret completion baseMessage publicPositions weights context
      publicRepresentative adversary statement witness adversaryCoins trace
      houter hlinear hhadamard input) :
    let coupled := productionCoupledInputOnGood shape maxStartLength fallback
      r1csDigest causalSecret completion baseMessage publicPositions weights
      context publicRepresentative adversary statement witness adversaryCoins
      trace houter hlinear hhadamard input hgood
    (productionRealView shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context adversary statement witness
      input.1 adversaryCoins (initialSharedOracleState input.2)).1 =
    (productionSimulatedView shape fallback r1csDigest causalSecret completion
      baseMessage publicPositions weights context publicRepresentative adversary
      statement coupled.1 adversaryCoins
      (initialSharedOracleState coupled.2)).1 := by
  dsimp only
  let right := publicRepresentative statement
  let hstart := hgood.startBound
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context witness right trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let points := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart
  let hinjective := productionSimulatorProgramPoints_injective shape
    maxStartLength causalSecret trace.equalityPoint.2.2 right moved.1
    trace.answers hstart
  let coupled := productionCoupledInputOnGood shape maxStartLength fallback
    r1csDigest causalSecret completion baseMessage publicPositions weights
    context publicRepresentative adversary statement witness adversaryCoins
    trace houter hlinear hhadamard input hgood
  let realPre := productionPreHistory adversary statement adversaryCoins input.2
  have hmerklePre : ∀ call ∈ realPre,
      moved.2 call.1 = input.2 call.1 := by
    exact productionMerkleTransport_agrees_on_safe_history shape input.1
      causalSecret baseMessage publicPositions weights context witness right
      trace.answers trace.tail.rest houter hlinear hhadamard fallback input
      realPre hgood.preMerkleFresh
  have hprogramPre : ∀ call ∈ realPre,
      coupled.2 call.1 = moved.2 call.1 := by
    intro call hcall
    change OracleProgramming.program points hinjective moved.2
      moved.1.simulatedAnswers call.1 = moved.2 call.1
    apply OracleProgramming.program_off
    rintro ⟨site, heq⟩
    exact hgood.preProgrammingFresh call hcall site heq.symm
  have hagreePre : ∀ call ∈ realPre,
      coupled.2 call.1 = input.2 call.1 := by
    intro call hcall
    exact (hprogramPre call hcall).trans (hmerklePre call hcall)
  have hpre : productionPreHistory adversary statement adversaryCoins
      coupled.2 = realPre := by
    exact runQueryValues_eq_of_agrees_on_result
      (fun round history => adversary.preQuery round statement
        adversaryCoins history) input.2 coupled.2 (List.ofFn id) [] hagreePre
  let realInitial := initialSharedOracleState input.2
  let simInitial := initialSharedOracleState coupled.2
  let realPreRun := runPreQueries adversary statement adversaryCoins realInitial
  let simPreRun := runPreQueries adversary statement adversaryCoins simInitial
  have hrealPreValue : realPreRun.1 = realPre := by
    rw [runPreQueries_value]
    rfl
  have hsimPreValue : simPreRun.1 = realPre := by
    rw [runPreQueries_value]
    exact hpre
  have hrealPreTable : realPreRun.2.table = input.2 := by
    rw [runPreQueries_table]
    rfl
  have hsimPreTable : simPreRun.2.table = coupled.2 := by
    rw [runPreQueries_table]
    rfl
  let realProof := productionTraceProof shape fallback causalSecret baseMessage
    publicPositions weights context witness input.1 input.2 trace
  have facts : ProductionTraceFacts shape fallback r1csDigest causalSecret
      completion baseMessage statement witness input.1 input.2 trace :=
    productionRealTrace_facts shape fallback r1csDigest causalSecret completion
      baseMessage statement witness input.1 input.2 trace hgood.traceSuccess
  have hrealProof :
      (productionRealProof shape fallback r1csDigest causalSecret completion
        baseMessage publicPositions weights context statement witness input.1
        realPreRun.2).1 = some realProof := by
    rw [productionRealProof_value]
    rw [hrealPreTable]
    rw [hgood.traceSuccess]
    rfl
  have hrealProofTable :
      (productionRealProof shape fallback r1csDigest causalSecret completion
        baseMessage publicPositions weights context statement witness input.1
        realPreRun.2).2.table = input.2 := by
    rw [productionRealProof_table, hrealPreTable]
  have hok :
      let schedule := zerocheckSimulatedByteSchedule shape causalSecret
        trace.equalityPoint.2.2 right coupled.1 trace.answers
      (programSharedByteSchedule schedule trace.answers simPreRun.2).1 =
        .ok () := by
    exact hgood.programmingSucceeds
  have hsimProof := productionSimulatedProof_of_trace shape maxStartLength
    fallback r1csDigest causalSecret completion baseMessage publicPositions
    weights context statement witness right hpublic trace houter hlinear
    hhadamard hnodes input hstart facts simPreRun.2 hsimPreTable hok
  let realProofRun := productionRealProof shape fallback r1csDigest
    causalSecret completion baseMessage publicPositions weights context
    statement witness input.1 realPreRun.2
  let simProofRun := productionSimulatedProof shape fallback r1csDigest
    causalSecret completion baseMessage publicPositions weights context
    publicRepresentative statement coupled.1 simPreRun.2
  have hrealProofValue : realProofRun.1 = some realProof := hrealProof
  have hrealProofTable' : realProofRun.2.table = input.2 := hrealProofTable
  have hsimProofValue : simProofRun.1 = some realProof := hsimProof.1
  have hsimProofTable : simProofRun.2.table = moved.2 := hsimProof.2
  let realPost := productionPostHistory adversary statement (some realProof)
    adversaryCoins realPre input.2
  have hmerklePost : ∀ call ∈ realPost,
      moved.2 call.1 = input.2 call.1 := by
    exact productionMerkleTransport_agrees_on_safe_history shape input.1
      causalSecret baseMessage publicPositions weights context witness right
      trace.answers trace.tail.rest houter hlinear hhadamard fallback input
      realPost hgood.postMerkleFresh
  have hpost : productionPostHistory adversary statement (some realProof)
      adversaryCoins realPre moved.2 = realPost := by
    exact runQueryValues_eq_of_agrees_on_result
      (fun round history => adversary.postQuery round statement
        (some realProof) adversaryCoins realPre history)
      input.2 moved.2 (List.ofFn id) [] hmerklePost
  let realPostRun := runPostQueries adversary statement realProofRun.1
    adversaryCoins realPreRun.1 realProofRun.2
  let simPostRun := runPostQueries adversary statement simProofRun.1
    adversaryCoins simPreRun.1 simProofRun.2
  have hrealPostValue : realPostRun.1 = realPost := by
    rw [runPostQueries_value]
    rw [hrealProofValue, hrealPreValue, hrealProofTable']
    rfl
  have hsimPostValue : simPostRun.1 = realPost := by
    rw [runPostQueries_value]
    rw [hsimProofValue, hsimPreValue, hsimProofTable]
    exact hpost
  unfold productionRealView productionSimulatedView
  change
    ({
      statement := statement
      adversaryRandomness := adversaryCoins
      proof := realProofRun.1
      oracleView := finishOracleView adversary statement realProofRun.1
        adversaryCoins realPreRun.1 realPostRun.1
    } : ProductionView shape (ProductionRest shape)
      (ProductionMaxPointLength shape maxStartLength)) =
    ({
      statement := statement
      adversaryRandomness := adversaryCoins
      proof := simProofRun.1
      oracleView := finishOracleView adversary statement simProofRun.1
        adversaryCoins simPreRun.1 simPostRun.1
    } : ProductionView shape (ProductionRest shape)
      (ProductionMaxPointLength shape maxStartLength))
  rw [hrealProofValue, hsimProofValue, hrealPreValue, hsimPreValue,
    hrealPostValue, hsimPostValue]

end VeiledFlock.ProductionNizkCoupling

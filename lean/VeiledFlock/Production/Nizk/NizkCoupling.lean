import VeiledFlock.Production.Core.GlobalGood
import VeiledFlock.Production.Nizk.NizkExperiment
import VeiledFlock.Production.Sampling.SamplingJoint

/-!
# Concrete coupling for the production VEIL + FLOCK NIZK

This module constructs the single coin/oracle reparameterization used by the
production real/simulator equality theorem.  Unlike the generic pipeline
lemmas, every definition below is specialized to `ProductionCoins`,
`FormalVeilFlockProof`, and the concrete production execution.
-/

namespace VeiledFlock.ProductionNizkCoupling

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.NonceSerialization
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.OracleProgramming
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionCombinedMerkleTransport
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPositionProjection
open VeiledFlock.ProductionThreeTree
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionUniquePositionSampler
open VeiledFlock.TranscriptSchedule

/-- The part of `ProductionCoins` changed by the joint FLOCK/outer-PCS/VEIL
witness transport. -/
abbrev ProductionPrivateCoins (shape : BatchShape) :=
  VeiledFlock.ProductionOuterPaddedPcs.PreCoins
      (K := Unit) (I := BaseScalarIndex shape)
      (Pad := ActivePadding shape) (rounds := expectedMasks shape) ×
    VeiledFlock.ProductionVeilLayer.LayerCoins shape

/-- Lift the existing answer-indexed production algebraic equivalence from
the algebraic tuple to just the private portion of `ProductionCoins`.  The
sampled `ProductionRest` is fixed by this equivalence; it is public transcript
data, not prover randomness. -/
noncomputable def productionPrivateCoinEquiv
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) :
    ProductionPrivateCoins shape ≃ ProductionPrivateCoins shape := by
  let full := productionAnswerEquiv shape
    (fun current : ProductionRest shape ↦ current.outerPositions)
    (fun current : ProductionRest shape ↦ current.outerPositions_injective)
    (fun _ ↦ causalSecret)
    (fun _ _ (current : ProductionRest shape) ↦ current.outerChallenge)
    (fun _ _ (current : ProductionRest shape) ↦
      current.outerChallenge_ne_zero)
    baseMessage publicPositions weights context left right answers
  refine
    { toFun := fun coins ↦
        let moved := full (coins.1, coins.2, rest)
        (moved.1, moved.2.1)
      invFun := fun coins ↦
        let moved := full.symm (coins.1, coins.2, rest)
        (moved.1, moved.2.1)
      left_inv := ?_
      right_inv := ?_ }
  · intro coins
    let input : AlgebraicCoins (Rest := ProductionRest shape) shape :=
      (coins.1, coins.2, rest)
    have hrest : (full input).2.2 = rest := by
      rfl
    have harg : ((full input).1, (full input).2.1, rest) = full input := by
      rcases hfull : full input with ⟨outer, layer, movedRest⟩
      rw [hfull] at hrest
      change movedRest = rest at hrest
      subst movedRest
      rfl
    change
      (((full.symm ((full input).1, (full input).2.1, rest)).1,
        (full.symm ((full input).1, (full input).2.1, rest)).2.1) = coins)
    rw [harg, full.symm_apply_apply]
  · intro coins
    let input : AlgebraicCoins (Rest := ProductionRest shape) shape :=
      (coins.1, coins.2, rest)
    have hrest : (full.symm input).2.2 = rest := by
      rfl
    have harg : ((full.symm input).1, (full.symm input).2.1, rest) =
        full.symm input := by
      rcases hfull : full.symm input with ⟨outer, layer, movedRest⟩
      rw [hfull] at hrest
      change movedRest = rest at hrest
      subst movedRest
      rfl
    change
      (((full ((full.symm input).1, (full.symm input).2.1, rest)).1,
        (full ((full.symm input).1, (full.symm input).2.1, rest)).2.1) = coins)
    rw [harg, full.apply_symm_apply]

/-- Concrete answer/rest-indexed witness transport on the complete production
coin record.  Proof/tree nonces, all three salt families, and the simulator's
answer tape are preserved exactly. -/
noncomputable def productionProtocolCoinEquiv
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) :
    ProductionCoins shape ≃ ProductionCoins shape where
  toFun coins :=
    let moved := productionPrivateCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest
      (coins.outer, coins.layer)
    { outer := moved.1
      layer := moved.2
      proofNonce := coins.proofNonce
      treeNonces := coins.treeNonces
      outerSalts := coins.outerSalts
      linearSalts := coins.linearSalts
      hadamardSalts := coins.hadamardSalts
      simulatedAnswers := coins.simulatedAnswers }
  invFun coins :=
    let moved := (productionPrivateCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest).symm
      (coins.outer, coins.layer)
    { outer := moved.1
      layer := moved.2
      proofNonce := coins.proofNonce
      treeNonces := coins.treeNonces
      outerSalts := coins.outerSalts
      linearSalts := coins.linearSalts
      hadamardSalts := coins.hadamardSalts
      simulatedAnswers := coins.simulatedAnswers }
  left_inv coins := by
    let privateEquiv := productionPrivateCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest
    have hprivate := privateEquiv.symm_apply_apply (coins.outer, coins.layer)
    rcases coins with ⟨outer, layer, proofNonce, treeNonces, outerSalts,
      linearSalts, hadamardSalts, simulatedAnswers⟩
    change
      ProductionCoins.mk
          (privateEquiv.symm (privateEquiv (outer, layer))).1
          (privateEquiv.symm (privateEquiv (outer, layer))).2
          proofNonce treeNonces outerSalts linearSalts hadamardSalts
          simulatedAnswers =
        ProductionCoins.mk outer layer proofNonce treeNonces outerSalts
          linearSalts hadamardSalts simulatedAnswers
    rw [hprivate]
  right_inv coins := by
    let privateEquiv := productionPrivateCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest
    have hprivate := privateEquiv.apply_symm_apply (coins.outer, coins.layer)
    rcases coins with ⟨outer, layer, proofNonce, treeNonces, outerSalts,
      linearSalts, hadamardSalts, simulatedAnswers⟩
    change
      ProductionCoins.mk
          (privateEquiv (privateEquiv.symm (outer, layer))).1
          (privateEquiv (privateEquiv.symm (outer, layer))).2
          proofNonce treeNonces outerSalts linearSalts hadamardSalts
          simulatedAnswers =
        ProductionCoins.mk outer layer proofNonce treeNonces outerSalts
          linearSalts hadamardSalts simulatedAnswers
    rw [hprivate]

@[simp]
theorem productionProtocolCoinEquiv_proofNonce
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (coins : ProductionCoins shape) :
    (productionProtocolCoinEquiv shape causalSecret baseMessage publicPositions
      weights context left right answers rest coins).proofNonce =
        coins.proofNonce := rfl

/-- The lifted concrete equivalence preserves the complete conservative
FLOCK/outer-PCS/VEIL proof value.  This theorem derives the equality directly
from the existing production algebraic theorem; it is not an assumption of the
end-to-end coupling. -/
theorem productionAlgebraicProof_coinEquiv
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (left right : W)
    (hpublic : publicStatement shape publicPositions baseMessage left =
      publicStatement shape publicPositions baseMessage right)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (coins : ProductionCoins shape) :
    productionAlgebraicProof shape causalSecret baseMessage publicPositions
        weights context answers left coins rest =
      productionAlgebraicProof shape causalSecret baseMessage publicPositions
        weights context answers right
        (productionProtocolCoinEquiv shape causalSecret baseMessage
          publicPositions weights context left right answers rest coins) rest := by
  let full := productionAnswerEquiv shape
    (fun current : ProductionRest shape ↦ current.outerPositions)
    (fun current : ProductionRest shape ↦ current.outerPositions_injective)
    (fun _ ↦ causalSecret)
    (fun _ _ (current : ProductionRest shape) ↦ current.outerChallenge)
    (fun _ _ (current : ProductionRest shape) ↦
      current.outerChallenge_ne_zero)
    baseMessage publicPositions weights context left right answers
  have hview :=
    VeiledFlock.ProductionPaddedAlgebraicE2E.view_coinEquiv shape
      (closedSecret shape (fun _ ↦ causalSecret) answers)
      (fun _ (current : ProductionRest shape) ↦ current.outerChallenge)
      (fun _ (current : ProductionRest shape) ↦
        current.outerChallenge_ne_zero)
      (fun _ ↦ baseMessage) (fun _ ↦ basePaddingEmbed shape)
      (fun current : ProductionRest shape ↦
        baseOpening shape current.outerPositions)
      (fun current : ProductionRest shape ↦
        outerPaddingQueryEquiv shape current.outerPositions
        current.outerPositions_injective)
      (opening_paddingEmbed shape
        (fun current : ProductionRest shape ↦ current.outerPositions)
        (fun current : ProductionRest shape ↦
          current.outerPositions_injective))
      (publicDirectFunctional shape publicPositions (weights answers))
      (publicStatement shape publicPositions baseMessage)
      (publicDirect_kernel shape publicPositions baseMessage (weights answers))
      (fun history outer current ↦
        ProductionConcreteAlgebraic.layerSpec
          (context answers history outer current))
      (fun _ _ _ ↦ ProductionConcreteAlgebraic.layerSpec_statement _)
      left right hpublic (algebraicCoins coins rest)
  change
    VeiledFlock.ProductionPaddedAlgebraicE2E.view shape
        (closedSecret shape (fun _ ↦ causalSecret) answers)
        (fun _ (current : ProductionRest shape) ↦ current.outerChallenge)
        (fun _ ↦ baseMessage) (fun _ ↦ basePaddingEmbed shape)
        (fun current : ProductionRest shape ↦
          baseOpening shape current.outerPositions)
        (publicDirectFunctional shape publicPositions (weights answers))
        (fun history outer current ↦
          ProductionConcreteAlgebraic.layerSpec
            (context answers history outer current))
        left (algebraicCoins coins rest) =
      VeiledFlock.ProductionPaddedAlgebraicE2E.view shape
        (closedSecret shape (fun _ ↦ causalSecret) answers)
        (fun _ (current : ProductionRest shape) ↦ current.outerChallenge)
        (fun _ ↦ baseMessage) (fun _ ↦ basePaddingEmbed shape)
        (fun current : ProductionRest shape ↦
          baseOpening shape current.outerPositions)
        (publicDirectFunctional shape publicPositions (weights answers))
        (fun history outer current ↦
          ProductionConcreteAlgebraic.layerSpec
            (context answers history outer current))
        right (full (algebraicCoins coins rest)) at hview
  have hrest : (full (algebraicCoins coins rest)).2.2 = rest := by
    rfl
  have hmoved :
      algebraicCoins
          (productionProtocolCoinEquiv shape causalSecret baseMessage
            publicPositions weights context left right answers rest coins)
          rest =
        full (algebraicCoins coins rest) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact hrest.symm
  change
    productionAlgebraicProof shape causalSecret baseMessage publicPositions
        weights context answers left coins rest =
      VeiledFlock.ProductionPaddedAlgebraicE2E.view shape
        (closedSecret shape (fun _ ↦ causalSecret) answers)
        (fun _ (current : ProductionRest shape) ↦ current.outerChallenge)
        (fun _ ↦ baseMessage) (fun _ ↦ basePaddingEmbed shape)
        (fun current : ProductionRest shape ↦
          baseOpening shape current.outerPositions)
        (publicDirectFunctional shape publicPositions (weights answers))
        (fun history outer current ↦
          ProductionConcreteAlgebraic.layerSpec
            (context answers history outer current))
        right
        (algebraicCoins
          (productionProtocolCoinEquiv shape causalSecret baseMessage
            publicPositions weights context left right answers rest coins) rest)
  rw [hmoved]
  exact hview

/-- Project the concrete algebraic equality to the exact flat FLOCK mask
transcript consumed by the production challenger. -/
theorem productionMaskTranscript_coinEquiv
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (left right : W)
    (hpublic : publicStatement shape publicPositions baseMessage left =
      publicStatement shape publicPositions baseMessage right)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (coins : ProductionCoins shape) :
    let moved := productionProtocolCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest coins
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
        answers (right, moved.outer.1, moved.outer.2.1) moved.outer.2.2 =
      VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
        answers (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2 := by
  dsimp only
  have hproof := productionAlgebraicProof_coinEquiv shape causalSecret
    baseMessage publicPositions weights context left right hpublic answers rest
    coins
  have hhistory := congrArg (fun proof ↦ proof.2.1) hproof
  exact congrArg (fun history site ↦ history site ()) hhistory.symm

/-- After the concrete FLOCK/VEIL coin transport, every reached simulator
programming point is byte-for-byte the point queried by the honest causal
schedule.  Counterfactual histories are intentionally not compared. -/
theorem productionZerocheck_tracePoint_coinEquiv
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (absorbedPrefix : List Byte)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (coins : ProductionCoins shape)
    (site : Fin (programmedPoints shape)) :
    let moved := productionProtocolCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest coins
    tracePoint
        (zerocheckSimulatedByteSchedule shape causalSecret absorbedPrefix right
          moved answers) answers site =
      tracePoint
        (zerocheckRealByteSchedule shape causalSecret completion absorbedPrefix
          left coins) answers site := by
  dsimp only
  let moved := productionProtocolCoinEquiv shape causalSecret baseMessage
    publicPositions weights context left right answers rest coins
  let simulatedTranscript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (right, moved.outer.1, moved.outer.2.1) moved.outer.2.2
  let honestStartTranscript :=
    VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
      causalSecret completion (left, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  have htranscript : simulatedTranscript =
      VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
        answers (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2 := by
    exact productionMaskTranscript_coinEquiv shape causalSecret baseMessage
      publicPositions weights context left right hpublic answers rest coins
  apply tracePoint_appendSchedule_eq_of_traceSteps
    (ProductionZerocheckSchedule.start shape absorbedPrefix
      honestStartTranscript)
    (ProductionZerocheckSchedule.start shape absorbedPrefix
      simulatedTranscript)
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
        causalSecret completion (left, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2)
      (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
        causalSecret completion (left, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2))
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (ProductionZerocheckSchedule.first shape simulatedTranscript)
      (ProductionZerocheckSchedule.second shape simulatedTranscript))
    answers
  · exact VeiledFlock.ProductionCausalScheduleTransport.start_transport shape
      causalSecret completion answers
      (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2
      simulatedTranscript htranscript rfl
  · intro round hle
    simp only [scalarRoundStep]
    rw [VeiledFlock.ProductionCausalScheduleTransport.first_transport shape
      causalSecret completion answers
      (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2
      simulatedTranscript htranscript round hle]
    rw [VeiledFlock.ProductionCausalScheduleTransport.second_transport shape
      causalSecret completion answers
      (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2
      simulatedTranscript htranscript round hle]

/-- The honest byte schedule has pairwise-distinct reached points. -/
theorem productionRealZerocheck_tracePoints_injective
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (absorbedPrefix : List Byte) (witness : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    Injective (tracePoints
      (zerocheckRealByteSchedule shape causalSecret completion absorbedPrefix
        witness coins) answers) := by
  exact scalarProgrammingPoints_injective
    (ProductionZerocheckSchedule.start shape absorbedPrefix
      (VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
        causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2))
    consumeScalar consumeScalar_length
    (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
    (encodeField_length VeiledFlock.Field128Serialization.encodeGhashField)
    (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2)
    (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2) answers

/-- The simulator look-ahead byte schedule has pairwise-distinct programmed
points for every proposed answer vector. -/
theorem productionSimulatedZerocheck_tracePoints_injective
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    Injective (tracePoints
      (zerocheckSimulatedByteSchedule shape causalSecret absorbedPrefix
        simulatedState coins answers) answers) := by
  let transcript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (simulatedState, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  exact scalarProgrammingPoints_injective
    (ProductionZerocheckSchedule.start shape absorbedPrefix transcript)
    consumeScalar consumeScalar_length
    (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
    (encodeField_length VeiledFlock.Field128Serialization.encodeGhashField)
    (ProductionZerocheckSchedule.first shape transcript)
    (ProductionZerocheckSchedule.second shape transcript) answers

/-! ## Three production Merkle families at a fixed coupling fiber -/

@[simp]
theorem outerRowPayload_length {W : Type*} (shape : BatchShape)
    (baseMessage : W → BaseWord shape) (witness : W)
    (coins : ProductionCoins shape) (row : Fin (2 ^ (m shape - 11))) :
    (outerRowPayload shape baseMessage witness coins row).length =
      16 * (2 * outerLaneCount) := by
  simp [outerRowPayload, matrixRowBytes_length]

@[simp]
theorem linearRowPayload_length (shape : BatchShape)
    (coins : ProductionCoins shape) (row : Fin (2 ^ 13)) :
    (linearRowPayload shape coins row).length = 32 := by
  simpa [linearRowPayload] using
    (matrixRowBytes_length (row := fun column : Fin 2 ↦
      if hdata : column.val < 1 then
        linearCodeword shape
          (paddedMessage shape
            (fun index ↦ coins.outer.2.2 index ()) coins.layer.1)
          (coins.layer.2.1.2 (Sum.inl ⟨column.val, hdata⟩))
          ((finCongr (by decide : linearCodeLength = 2 ^ 13)).symm row)
      else
        linearCodeword shape coins.layer.2.1.1
          (coins.layer.2.1.2 (Sum.inr ()))
          ((finCongr (by decide : linearCodeLength = 2 ^ 13)).symm row)))

@[simp]
theorem hadamardRowPayload_length {W Public : Type*} (shape : BatchShape)
    (spec : VeiledFlock.ProductionCorrelatedLayerSpec.Spec shape W Public)
    (witness : W) (coins : ProductionCoins shape)
    (row : Fin (2 ^ 11)) :
    (hadamardRowPayload shape spec witness coins row).length = 64 := by
  simpa [hadamardRowPayload] using
    (matrixRowBytes_length (row := fun column : Fin 4 ↦
      if hdata : column.val < 3 then
        let data : Fin 3 := ⟨column.val, hdata⟩
        hadamardCodeword
          (VeiledFlock.ProductionCorrelatedVeilLayer.hadamardMessage
            spec.multiplicationSecret witness coins.layer.1 data)
          (coins.layer.2.2.1.2 (Sum.inl data))
          ((finCongr (by decide : hadamardCodeLength = 2 ^ 11)).symm row)
      else
        hadamardCodeword coins.layer.2.2.1.1
          (coins.layer.2.2.1.2 (Sum.inr ()))
          ((finCongr (by decide : hadamardCodeLength = 2 ^ 11)).symm row)))

/-- The three fixed geometries used by one production proof.  The algebraic
coin transport preserves these nonces definitionally. -/
def productionTreeShapes (shape : BatchShape) (coins : ProductionCoins shape) :
    ProductionTree → TreeShape
  | .outer =>
      { treeDepth := ⟨0, by decide⟩
        treeNonce := coins.treeNonces.outer
        leafLength := BitVec.ofNat 64 (16 * (2 * outerLaneCount))
        depth := m shape - 11
        depth_le := by cases shape <;> decide }
  | .veilLinear =>
      { treeDepth := ⟨0, by decide⟩
        treeNonce := coins.treeNonces.veilLinear
        leafLength := BitVec.ofNat 64 32
        depth := 13
        depth_le := by decide }
  | .veilHadamard =>
      { treeDepth := ⟨0, by decide⟩
        treeNonce := coins.treeNonces.veilHadamard
        leafLength := BitVec.ofNat 64 64
        depth := 11
        depth_le := by decide }

/-- The accepted challenge-dependent VEIL layer specification used to build
the Hadamard commitment in the complete production proof. -/
noncomputable def productionLayerSpecAt
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (coins : ProductionCoins shape) :
    VeiledFlock.ProductionCorrelatedLayerSpec.Spec shape W
      (ProductionConcreteAlgebraic.Public
        (PublicCoord := PublicCoord) shape) :=
  let algebraic := productionAlgebraicProof shape causalSecret baseMessage
    publicPositions weights context answers witness coins rest
  ProductionConcreteAlgebraic.layerSpec
    (context answers algebraic.2.1 algebraic.2.2.1 rest)

/-- All three exact salted leaf families used by `finishProductionProof`.
The Hadamard material is allowed to depend on the complete accepted algebraic
state, matching its actual causal position after rejection sampling. -/
noncomputable def productionTreeMaterial
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W) :
    ∀ tree,
      VeiledFlock.ProductionCombinedMerkleTransport.TreeMaterial
        (productionGeometry
          (productionTreeShapes shape geometryCoins .outer)
          (productionTreeShapes shape geometryCoins .veilLinear)
          (productionTreeShapes shape geometryCoins .veilHadamard) tree)
        (ProductionCoins shape)
  | .outer =>
      { salts := fun coins ↦ coins.outerSalts
        payload := fun coins ↦
          outerRowPayload shape baseMessage witness coins }
  | .veilLinear =>
      { salts := fun coins ↦ coins.linearSalts
        payload := fun coins ↦ linearRowPayload shape coins }
  | .veilHadamard =>
      { salts := fun coins ↦ coins.hadamardSalts
        payload := fun coins ↦
          hadamardRowPayload shape
            (productionLayerSpecAt shape causalSecret baseMessage
              publicPositions weights context answers rest witness coins)
            witness coins }

/-- Shared concrete geometry of the three production commitment domains at
one coupling fiber. -/
def productionTreeGeometry (shape : BatchShape)
    (geometryCoins : ProductionCoins shape) : ProductionTree → TreeGeometry :=
  productionGeometry
    (productionTreeShapes shape geometryCoins .outer)
    (productionTreeShapes shape geometryCoins .veilLinear)
    (productionTreeShapes shape geometryCoins .veilHadamard)

theorem productionTreeGeometry_channel_injective (shape : BatchShape)
    (geometryCoins : ProductionCoins shape) :
    Injective (fun tree =>
      (productionTreeGeometry shape geometryCoins tree).channel) := by
  exact ProductionThreeTree.productionGeometry_channel_injective
    (productionTreeShapes shape geometryCoins .outer)
    (productionTreeShapes shape geometryCoins .veilLinear)
    (productionTreeShapes shape geometryCoins .veilHadamard)

/-- Concrete byte-budget proof for all three salted leaf families. -/
theorem productionTreeMaterial_fits
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength) :
    FamilyFits (maxLength := maxPointLength)
      (productionTreeGeometry shape geometryCoins)
      (productionTreeMaterial shape geometryCoins causalSecret baseMessage
        publicPositions weights context answers rest witness) := by
  intro tree coins index
  cases tree with
  | outer =>
      simpa [productionTreeGeometry, productionTreeMaterial] using houter
  | veilLinear =>
      simpa [productionTreeGeometry, productionTreeMaterial] using hlinear
  | veilHadamard =>
      simpa [productionTreeGeometry, productionTreeMaterial] using hhadamard

/-- The concrete joint FLOCK/VEIL/Merkle reparameterization at fixed realized
Fiat--Shamir answers and accepted rejection/grinding output.  It moves the
complete protocol coin record and all three actual serialized salted-leaf
families in one finite-oracle equivalence. -/
noncomputable def productionMerkleCoinOracleEquivAt
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength) :
    (ProductionCoins shape ×
        (BoundedBytes maxPointLength → OracleBlock)) ≃
      (ProductionCoins shape ×
        (BoundedBytes maxPointLength → OracleBlock)) :=
  let coinEquiv := productionProtocolCoinEquiv shape causalSecret baseMessage
    publicPositions weights context left right answers rest
  let geometry := productionTreeGeometry shape geometryCoins
  let leftMaterial := productionTreeMaterial shape geometryCoins causalSecret
    baseMessage publicPositions weights context answers rest left
  let rightMaterial := productionTreeMaterial shape geometryCoins causalSecret
    baseMessage publicPositions weights context answers rest right
  boundedFamilyCoinOracleEquiv coinEquiv geometry
    (productionTreeGeometry_channel_injective shape geometryCoins)
    leftMaterial rightMaterial
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left houter hlinear hhadamard)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right houter hlinear hhadamard)

/-- The oracle part of the three-tree transport does not obscure its concrete
algebraic coin projection. -/
@[simp]
theorem productionMerkleCoinOracleEquivAt_coins
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock)) :
    (productionMerkleCoinOracleEquivAt shape geometryCoins causalSecret
      baseMessage publicPositions weights context left right answers rest
      houter hlinear hhadamard input).1 =
      productionProtocolCoinEquiv shape causalSecret baseMessage
        publicPositions weights context left right answers rest input.1 := by
  rfl

/-- Every one of the three concrete production roots is preserved by the
single algebraic/Merkle transport. -/
theorem productionMerkleCoinOracleEquivAt_roots
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength) (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (tree : ProductionTree) :
    let coinEquiv := productionProtocolCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest
    let transported := productionMerkleCoinOracleEquivAt shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard input
    VeiledFlock.ProductionBoundedOracle.boundedRoot fallback
        (productionTreeGeometry shape geometryCoins tree)
        (productionTreeMaterial shape geometryCoins causalSecret baseMessage
          publicPositions weights context answers rest right tree)
        (coinEquiv input.1) transported.2 =
      VeiledFlock.ProductionBoundedOracle.boundedRoot fallback
        (productionTreeGeometry shape geometryCoins tree)
        (productionTreeMaterial shape geometryCoins causalSecret baseMessage
          publicPositions weights context answers rest left tree)
        input.1 input.2 := by
  dsimp only
  exact threeRoots_exact
    (productionProtocolCoinEquiv shape causalSecret baseMessage publicPositions
      weights context left right answers rest)
    (productionTreeShapes shape geometryCoins .outer)
    (productionTreeShapes shape geometryCoins .veilLinear)
    (productionTreeShapes shape geometryCoins .veilHadamard)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left houter hlinear hhadamard)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right houter hlinear hhadamard)
    hnodes fallback input tree

/-- The concrete three-tree transport is pointwise invisible on every
bounded Fiat--Shamir input. -/
theorem productionMerkleCoinOracleEquivAt_answer_fiat
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (point : List Byte) (hfiat : isFiatShamirPoint point)
    (hpoint : point.length ≤ maxPointLength) :
    let transported := productionMerkleCoinOracleEquivAt shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard input
    answerBounded fallback transported.2 point =
      answerBounded fallback input.2 point := by
  exact boundedFamilyCoinOracleEquiv_answer_fiat
    (productionProtocolCoinEquiv shape causalSecret baseMessage publicPositions
      weights context left right answers rest)
    (productionTreeGeometry shape geometryCoins)
    (productionTreeGeometry_channel_injective shape geometryCoins)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left houter hlinear hhadamard)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right houter hlinear hhadamard)
    fallback input point hfiat hpoint

/-- The same concrete transport is pointwise invisible on every bounded
first-success grinding input. -/
theorem productionMerkleCoinOracleEquivAt_answer_pow
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (state : Nonce256) (nonce : Word64)
    (hpoint : (encodePowPoint state nonce).length ≤ maxPointLength) :
    let transported := productionMerkleCoinOracleEquivAt shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard input
    answerBounded fallback transported.2 (encodePowPoint state nonce) =
      answerBounded fallback input.2 (encodePowPoint state nonce) := by
  exact boundedFamilyCoinOracleEquiv_answer_pow
    (productionProtocolCoinEquiv shape causalSecret baseMessage publicPositions
      weights context left right answers rest)
    (productionTreeGeometry shape geometryCoins)
    (productionTreeGeometry_channel_injective shape geometryCoins)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left houter hlinear hhadamard)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right houter hlinear hhadamard)
    fallback input state nonce hpoint

/-- Fiat--Shamir-domain invisibility without a separate length premise: both
bounded adapters return the public fallback outside the finite universe. -/
theorem productionMerkleCoinOracleEquivAt_answer_fiat_all
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (point : List Byte) (hfiat : isFiatShamirPoint point) :
    let transported := productionMerkleCoinOracleEquivAt shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard input
    answerBounded fallback transported.2 point =
      answerBounded fallback input.2 point := by
  by_cases hpoint : point.length ≤ maxPointLength
  · exact productionMerkleCoinOracleEquivAt_answer_fiat shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard fallback input point hfiat hpoint
  · simp [answerBounded, hpoint]

/-- PoW-domain invisibility with the same fail-closed out-of-budget case. -/
theorem productionMerkleCoinOracleEquivAt_answer_pow_all
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (state : Nonce256) (nonce : Word64) :
    let transported := productionMerkleCoinOracleEquivAt shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard input
    answerBounded fallback transported.2 (encodePowPoint state nonce) =
      answerBounded fallback input.2 (encodePowPoint state nonce) := by
  by_cases hpoint : (encodePowPoint state nonce).length ≤ maxPointLength
  · exact productionMerkleCoinOracleEquivAt_answer_pow shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard fallback input state nonce hpoint
  · have hlength : ¬41 ≤ maxPointLength := by
      simpa using hpoint
    simp [answerBounded, hlength]

/-- Outside both the honest and simulated concrete salted-leaf families, the
complete three-tree transport leaves a bounded oracle answer unchanged. -/
theorem productionMerkleCoinOracleEquivAt_answer_off
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (point : List Byte) (hpoint : point.length ≤ maxPointLength)
    (hoffLeft : ∀ index,
      point ≠ familyLeafPoint (productionTreeGeometry shape geometryCoins)
        (productionTreeMaterial shape geometryCoins causalSecret baseMessage
          publicPositions weights context answers rest left) input.1 index)
    (hoffRight : ∀ index,
      point ≠ familyLeafPoint (productionTreeGeometry shape geometryCoins)
        (productionTreeMaterial shape geometryCoins causalSecret baseMessage
          publicPositions weights context answers rest right)
        (productionProtocolCoinEquiv shape causalSecret baseMessage
          publicPositions weights context left right answers rest input.1)
        index) :
    let transported := productionMerkleCoinOracleEquivAt shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard input
    answerBounded fallback transported.2 point =
      answerBounded fallback input.2 point := by
  exact boundedFamilyCoinOracleEquiv_answer_off
    (productionProtocolCoinEquiv shape causalSecret baseMessage publicPositions
      weights context left right answers rest)
    (productionTreeGeometry shape geometryCoins)
    (productionTreeGeometry_channel_injective shape geometryCoins)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left)
    (productionTreeMaterial shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest left houter hlinear hhadamard)
    (productionTreeMaterial_fits shape geometryCoins causalSecret baseMessage
      publicPositions weights context answers rest right houter hlinear hhadamard)
    fallback input point hpoint hoffLeft hoffRight

/-! ## Exact transport of the complete rejection/grinding tail -/

/-- A successful equality-suffix attempt strictly advances the Fiat--Shamir
transcript.  This exposes the causal boundary used to keep later programming
points invisible to the earlier equality sampler. -/
theorem sampleUntilAccepted_some_length
    (leftOracle : List Byte → OracleBlock)
    (length trials : ℕ) (transcript : List Byte)
    (answer : Fin length → GhashField) (finalTranscript : List Byte)
    (hlength : 1 ≤ length)
    (hsome : VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted
        leftOracle length trials transcript = some (answer, finalTranscript)) :
    transcript.length < finalTranscript.length := by
  induction trials generalizing transcript with
  | zero =>
      simp [VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted] at hsome
  | succ trials ih =>
      simp only [VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted]
        at hsome
      split at hsome
      · have hpair := Option.some.inj hsome
        have hfinal :
            (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript
              (VeiledFlock.ProductionEqualitySampler.sampleSlice leftOracle
                transcript length)).length = finalTranscript.length :=
          congrArg (fun pair ↦ pair.2.length) hpair
        rw [VeiledFlock.ProductionTranscriptFraming.afterSlice_length] at hfinal
        omega
      · have hnext := ih
          (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript
            (VeiledFlock.ProductionEqualitySampler.sampleSlice leftOracle
              transcript length)) hsome
        rw [VeiledFlock.ProductionTranscriptFraming.afterSlice_length] at hnext
        omega

/-- A successful whole-vector rejection sample preserves the Fiat--Shamir
domain of its complete reabsorbed transcript. -/
theorem sampleUntilAccepted_some_isFiatShamir
    (oracle : List Byte → OracleBlock)
    (length trials : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (answer : Fin length → GhashField) (finalTranscript : List Byte)
    (hsome : VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted
      oracle length trials transcript = some (answer, finalTranscript)) :
    isFiatShamirPoint finalTranscript := by
  induction trials generalizing transcript with
  | zero =>
      simp [VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted] at hsome
  | succ trials ih =>
      simp only [VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted]
        at hsome
      split at hsome
      · have hpair := Option.some.inj hsome
        have hfinal :
            VeiledFlock.ProductionEqualitySampler.sampleSliceNext oracle
              transcript length = finalTranscript := congrArg Prod.snd hpair
        rw [← hfinal]
        exact VeiledFlock.ProductionEqualitySampler.sampleSliceNext_isFiatShamir
          hfiat oracle length
      · exact ih _
          (VeiledFlock.ProductionEqualitySampler.sampleSliceNext_isFiatShamir
            hfiat oracle length) hsome

/-- The final transcript returned by the complete equality-point sampler is
still a Fiat--Shamir transcript. -/
theorem sampleEqualityPointPrefix_some_isFiatShamir
    (oracle : List Byte → OracleBlock) (outerLength trials : ℕ)
    (transcript : List Byte) (hfiat : isFiatShamirPoint transcript)
    (sample : VeiledFlock.ProductionEqualitySampler.EqualitySample outerLength)
    (hsome : sampleEqualityPointPrefix oracle outerLength trials transcript =
      some sample) :
    isFiatShamirPoint sample.2.2 := by
  unfold sampleEqualityPointPrefix at hsome
  let afterSkip :=
    VeiledFlock.ProductionEqualitySampler.sampleSliceNext oracle transcript 6
  have hafterSkip : isFiatShamirPoint afterSkip :=
    VeiledFlock.ProductionEqualitySampler.sampleSliceNext_isFiatShamir
      hfiat oracle 6
  change
    (match VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted oracle
        outerLength trials afterSkip with
      | none => none
      | some (outer, finalPrefix) =>
          some (VeiledFlock.ProductionEqualitySampler.sampleSlice oracle
            transcript 6, outer, finalPrefix)) = some sample at hsome
  generalize hloop :
      VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted oracle
        outerLength trials afterSkip = result at hsome
  cases result with
  | none =>
      simp only at hsome
      cases hsome
  | some result =>
      simp only at hsome
      have hrecord := Option.some.inj hsome
      have hfinal := sampleUntilAccepted_some_isFiatShamir oracle outerLength
        trials afterSkip hafterSkip result.1 result.2 hloop
      rw [← congrArg (fun value ↦ value.2.2) hrecord]
      exact hfinal

/-- Changing only points at or after the successful final transcript cannot
alter any answer, rejection, or retry visible in the successful suffix. -/
theorem sampleUntilAccepted_eq_of_agrees_below_success
    (leftOracle rightOracle : List Byte → OracleBlock)
    (length trials : ℕ) (transcript : List Byte)
    (answer : Fin length → GhashField) (finalTranscript : List Byte)
    (hlength : 1 ≤ length)
    (hsome : VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted
      leftOracle length trials transcript = some (answer, finalTranscript))
    (hagrees : ∀ point, point.length < finalTranscript.length →
      rightOracle point = leftOracle point) :
    VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted rightOracle
        length trials transcript = some (answer, finalTranscript) := by
  induction trials generalizing transcript with
  | zero =>
      simp [VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted] at hsome
  | succ trials ih =>
      simp only [VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted]
        at hsome ⊢
      by_cases haccepted : VeiledFlock.ProductionEqualitySampler.accepted
          (VeiledFlock.ProductionEqualitySampler.sampleSlice leftOracle
            transcript length)
      · simp only [if_pos haccepted] at hsome
        have hquery : transcript.length + 18 < finalTranscript.length := by
          have hpair := Option.some.inj hsome
          have hfinal :
              (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript
                (VeiledFlock.ProductionEqualitySampler.sampleSlice leftOracle
                  transcript length)).length = finalTranscript.length :=
            congrArg (fun pair ↦ pair.2.length) hpair
          rw [VeiledFlock.ProductionTranscriptFraming.afterSlice_length]
            at hfinal
          omega
        have hslice :=
          VeiledFlock.ProductionEqualitySampler.sampleSlice_oracle_congr
            leftOracle rightOracle transcript length
            (fun counter ↦ hagrees _ (by simpa using hquery))
        rw [hslice]
        simp only [if_pos haccepted]
        exact hsome
      · simp only [if_neg haccepted] at hsome
        have hquery : transcript.length + 18 < finalTranscript.length := by
          have hnext := sampleUntilAccepted_some_length leftOracle length
            trials
            (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript
              (VeiledFlock.ProductionEqualitySampler.sampleSlice leftOracle
                transcript length)) answer finalTranscript hlength hsome
          rw [VeiledFlock.ProductionTranscriptFraming.afterSlice_length]
            at hnext
          omega
        have hslice :=
          VeiledFlock.ProductionEqualitySampler.sampleSlice_oracle_congr
            leftOracle rightOracle transcript length
            (fun counter ↦ hagrees _ (by simpa using hquery))
        rw [hslice]
        simp only [if_neg haccepted]
        exact ih
          (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript
            (VeiledFlock.ProductionEqualitySampler.sampleSlice leftOracle
              transcript length)) hsome

/-- The complete equality-point output is unchanged by any oracle
reparameterization supported strictly after its realized final transcript. -/
theorem sampleEqualityPointPrefix_eq_of_agrees_below_success
    (leftOracle rightOracle : List Byte → OracleBlock)
    (outerLength trials : ℕ) (transcript : List Byte)
    (sample : VeiledFlock.ProductionEqualitySampler.EqualitySample outerLength)
    (hlength : 1 ≤ outerLength)
    (hsome : VeiledFlock.ProductionEqualitySampler.sampleEqualityPointPrefix
      leftOracle outerLength trials transcript = some sample)
    (hagrees : ∀ point, point.length < sample.2.2.length →
      rightOracle point = leftOracle point) :
    VeiledFlock.ProductionEqualitySampler.sampleEqualityPointPrefix
        rightOracle outerLength trials transcript = some sample := by
  rcases sample with ⟨skip, outer, finalTranscript⟩
  let leftSkip := VeiledFlock.ProductionEqualitySampler.sampleSlice
    leftOracle transcript 6
  have hloop : VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted
      leftOracle outerLength trials
        (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript leftSkip) =
      some (outer, finalTranscript) := by
    change
      (match VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted
          leftOracle outerLength trials
          (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript leftSkip)
       with
       | none => none
       | some (foundOuter, foundFinal) =>
           some (leftSkip, foundOuter, foundFinal)) =
        some (skip, outer, finalTranscript) at hsome
    generalize hresult :
      VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted leftOracle
        outerLength trials
        (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript leftSkip) =
          result at hsome
    cases result with
    | none => simp at hsome
    | some result =>
        rcases result with ⟨foundOuter, foundFinal⟩
        simp only at hsome
        have htriple := Option.some.inj hsome
        have htail : (foundOuter, foundFinal) =
            (outer, finalTranscript) := congrArg Prod.snd htriple
        exact congrArg some htail
  have hfinal := sampleUntilAccepted_some_length leftOracle outerLength trials
    (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript leftSkip)
    outer finalTranscript hlength hloop
  have hskipQuery : transcript.length + 18 < finalTranscript.length := by
    rw [VeiledFlock.ProductionTranscriptFraming.afterSlice_length] at hfinal
    omega
  have hskip : VeiledFlock.ProductionEqualitySampler.sampleSlice rightOracle
      transcript 6 = leftSkip := by
    dsimp only [leftSkip]
    apply VeiledFlock.ProductionEqualitySampler.sampleSlice_oracle_congr
      leftOracle rightOracle
    intro counter
    exact hagrees _ (by simpa using hskipQuery)
  have hskipValue : leftSkip = skip := by
    change
      (match VeiledFlock.ProductionEqualitySampler.sampleUntilAccepted
          leftOracle outerLength trials
          (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript leftSkip)
       with
       | none => none
       | some (foundOuter, foundFinal) =>
           some (leftSkip, foundOuter, foundFinal)) =
        some (skip, outer, finalTranscript) at hsome
    rw [hloop] at hsome
    exact congrArg (fun value ↦ value.1) (Option.some.inj hsome)
  simp only [VeiledFlock.ProductionEqualitySampler.sampleEqualityPointPrefix]
  rw [hskip, sampleUntilAccepted_eq_of_agrees_below_success leftOracle
    rightOracle outerLength trials
    (VeiledFlock.ProductionTranscriptFraming.afterSlice transcript leftSkip)
    outer finalTranscript hlength hloop hagrees, hskipValue]

/-- Every simulator programming point is strictly later than the complete
equality-point transcript which selected it. -/
theorem simulatedZerocheck_tracePoint_longer
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (site : Fin (programmedPoints shape)) :
    absorbedPrefix.length <
      (tracePoint
        (zerocheckSimulatedByteSchedule shape causalSecret absorbedPrefix
          simulatedState coins answers) answers site).length := by
  let transcript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (simulatedState, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  change absorbedPrefix.length <
    (tracePoint
      (appendSchedule
        (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
          transcript)
        (scalarRoundStep consumeScalar
          (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
          (VeiledFlock.ProductionZerocheckSchedule.first shape transcript)
          (VeiledFlock.ProductionZerocheckSchedule.second shape transcript)))
      answers site).length
  rw [tracePoint_appendSchedule_length _ _ 54]
  · rw [VeiledFlock.ProductionZerocheckSchedule.start_length]
    omega
  · exact scalarRoundStep_length consumeScalar consumeScalar_length
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (encodeField_length
        VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionZerocheckSchedule.first shape transcript)
      (VeiledFlock.ProductionZerocheckSchedule.second shape transcript)

/-- The same concrete points fit the one production bounded-oracle universe
whenever the serialized starting state satisfies its public bound. -/
theorem simulatedZerocheck_tracePoint_fits
    {W : Type*} (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (hstart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret answers
          (simulatedState, coins.outer.1, coins.outer.2.1)
          coins.outer.2.2)).length ≤ maxStartLength)
    (site : Fin (programmedPoints shape)) :
    (tracePoint
      (zerocheckSimulatedByteSchedule shape causalSecret absorbedPrefix
        simulatedState coins answers) answers site).length ≤
      ProductionMaxPointLength shape maxStartLength := by
  let transcript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (simulatedState, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  change
    (tracePoint
      (appendSchedule
        (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
          transcript)
        (scalarRoundStep consumeScalar
          (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
          (VeiledFlock.ProductionZerocheckSchedule.first shape transcript)
          (VeiledFlock.ProductionZerocheckSchedule.second shape transcript)))
      answers site).length ≤
      maxPointLengthFromBound (programmedPoints shape) maxStartLength 54
  rw [tracePoint_appendSchedule_length _ _ 54]
  · exact Nat.add_le_add_right
      (Nat.add_le_add hstart
        (Nat.mul_le_mul_right 54 (Nat.le_of_lt site.isLt))) 8
  · exact scalarRoundStep_length consumeScalar consumeScalar_length
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (encodeField_length
        VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionZerocheckSchedule.first shape transcript)
      (VeiledFlock.ProductionZerocheckSchedule.second shape transcript)

/-- Every simulator programming point remains in the Fiat--Shamir domain
because the append-only zerocheck transcript retains the accepted equality
sampler transcript as a byte prefix. -/
theorem simulatedZerocheck_tracePoint_isFiatShamir
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (hfiat : isFiatShamirPoint absorbedPrefix)
    (site : Fin (programmedPoints shape)) :
    isFiatShamirPoint
      (tracePoint
        (zerocheckSimulatedByteSchedule shape causalSecret absorbedPrefix
          simulatedState coins answers) answers site) := by
  let transcript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (simulatedState, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  obtain ⟨suffix, hsuffix⟩ := tracePoint_appendSchedule_hasPrefix
    (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
      transcript)
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionZerocheckSchedule.first shape transcript)
      (VeiledFlock.ProductionZerocheckSchedule.second shape transcript))
    answers site
  change isFiatShamirPoint
    (tracePoint
      (appendSchedule
        (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
          transcript)
        (scalarRoundStep consumeScalar
          (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
          (VeiledFlock.ProductionZerocheckSchedule.first shape transcript)
          (VeiledFlock.ProductionZerocheckSchedule.second shape transcript)))
      answers site)
  rw [hsuffix]
  have hnonempty : absorbedPrefix ≠ [] := by
    intro hempty
    simp [isFiatShamirPoint, hempty] at hfiat
  simpa [isFiatShamirPoint, VeiledFlock.ProductionZerocheckSchedule.start,
    hnonempty] using hfiat

/-! ## Concrete simulator programming family -/

/-- Replace only the simulator's independently sampled answer tape.  Every
honest-prover coin and every Merkle salt/nonce is definitionally unchanged. -/
def withSimulatedAnswers (shape : BatchShape) (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    ProductionCoins shape :=
  { coins with simulatedAnswers := answers }

@[simp]
theorem withSimulatedAnswers_outer (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).outer = coins.outer := rfl

@[simp]
theorem withSimulatedAnswers_layer (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).layer = coins.layer := rfl

@[simp]
theorem withSimulatedAnswers_proofNonce (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).proofNonce = coins.proofNonce :=
  rfl

@[simp]
theorem withSimulatedAnswers_treeNonces (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).treeNonces = coins.treeNonces :=
  rfl

@[simp]
theorem withSimulatedAnswers_outerSalts (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).outerSalts = coins.outerSalts :=
  rfl

@[simp]
theorem withSimulatedAnswers_linearSalts (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).linearSalts = coins.linearSalts :=
  rfl

@[simp]
theorem withSimulatedAnswers_hadamardSalts (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).hadamardSalts =
      coins.hadamardSalts := rfl

@[simp]
theorem withSimulatedAnswers_answers (shape : BatchShape)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape)) :
    (withSimulatedAnswers shape coins answers).simulatedAnswers = answers := rfl

/-- The actual byte strings programmed by `productionSimulatedProof`, embedded
in the one bounded production oracle universe. -/
noncomputable def productionSimulatorProgramPoints
    {W : Type*} (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (hstart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret answers
          (simulatedState, coins.outer.1, coins.outer.2.1)
          coins.outer.2.2)).length ≤ maxStartLength) :
    Fin (programmedPoints shape) →
      BoundedBytes (ProductionMaxPointLength shape maxStartLength) :=
  fun site => boundBytes
    (tracePoint
      (zerocheckSimulatedByteSchedule shape causalSecret absorbedPrefix
        simulatedState coins answers) answers site)
    (simulatedZerocheck_tracePoint_fits shape maxStartLength causalSecret
      absorbedPrefix simulatedState coins answers hstart site)

theorem productionSimulatorProgramPoints_injective
    {W : Type*} (shape : BatchShape) (maxStartLength : ℕ)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (absorbedPrefix : List Byte) (simulatedState : W)
    (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (hstart :
      (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret answers
          (simulatedState, coins.outer.1, coins.outer.2.1)
          coins.outer.2.2)).length ≤ maxStartLength) :
    Injective (productionSimulatorProgramPoints shape maxStartLength
      causalSecret absorbedPrefix simulatedState coins answers hstart) := by
  intro left right heq
  apply productionSimulatedZerocheck_tracePoints_injective shape causalSecret
    absorbedPrefix simulatedState coins answers
  exact congrArg unboundBytes heq

/-- The concrete input space transformed by the pointwise production
coupling: one complete protocol coin tape and the one finite oracle table. -/
abbrev ProductionCouplingInput (shape : BatchShape) (maxStartLength : ℕ) :=
  ProductionCoins shape ×
    (BoundedBytes (ProductionMaxPointLength shape maxStartLength) →
      OracleBlock)

/-- Concrete real-to-simulator input map at one successful production trace.

First it applies the joint FLOCK/VEIL/three-Merkle transport.  It then swaps
the simulator's independent answer tape into the future programming points
and stores the realized honest answers in `ProductionCoins.simulatedAnswers`.
Thus the old independent answer tape is retained in the oracle rather than
discarded. -/
noncomputable def productionCoupledInputAt
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
    (left right : W) (trace : ProductionExecutionTrace shape)
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
          moved.1.outer.2.2)).length ≤ maxStartLength) :
    ProductionCouplingInput shape maxStartLength := by
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let points := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart
  let hinjective := productionSimulatorProgramPoints_injective shape
    maxStartLength causalSecret trace.equalityPoint.2.2 right moved.1
    trace.answers hstart
  exact
    (withSimulatedAnswers shape moved.1 trace.answers,
      program points hinjective moved.2 moved.1.simulatedAnswers)

@[simp]
theorem productionCoupledInputAt_answers
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
    (left right : W) (trace : ProductionExecutionTrace shape)
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
          moved.1.outer.2.2)).length ≤ maxStartLength) :
    (productionCoupledInputAt shape maxStartLength causalSecret baseMessage
      publicPositions weights context left right trace houter hlinear hhadamard
      input hstart).1.simulatedAnswers = trace.answers := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The single concrete FLOCK/VEIL/three-Merkle transport preserves the full
successful public proof.  In particular this is one structure equality, not
a list of independently simulated proof-field marginals. -/
theorem productionProofOfTrace_coinOracleEquiv
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape)
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
    (left right : W)
    (hpublic : publicStatement shape publicPositions baseMessage left =
      publicStatement shape publicPositions baseMessage right)
    (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength) (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock)) :
    let moved := productionMerkleCoinOracleEquivAt shape input.1
      causalSecret baseMessage publicPositions weights context left right
      trace.answers trace.tail.rest houter hlinear hhadamard input
    productionProofOfTrace shape causalSecret baseMessage publicPositions
        weights context right moved.1 (answerBounded fallback moved.2) trace =
      productionProofOfTrace shape causalSecret baseMessage publicPositions
        weights context left input.1 (answerBounded fallback input.2) trace := by
  let moved := productionMerkleCoinOracleEquivAt shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard input
  change
    productionProofOfTrace shape causalSecret baseMessage publicPositions
        weights context right moved.1 (answerBounded fallback moved.2) trace =
      productionProofOfTrace shape causalSecret baseMessage publicPositions
        weights context left input.1 (answerBounded fallback input.2) trace
  have hmovedCoins : moved.1 =
      productionProtocolCoinEquiv shape causalSecret baseMessage
        publicPositions weights context left right trace.answers
        trace.tail.rest input.1 := by
    exact productionMerkleCoinOracleEquivAt_coins shape input.1
      causalSecret baseMessage publicPositions weights context left right
      trace.answers trace.tail.rest houter hlinear hhadamard input
  have hroot := productionMerkleCoinOracleEquivAt_roots shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard hnodes fallback input
    (.veilHadamard)
  change hadamardRoot shape
      (productionLayerSpecAt shape causalSecret baseMessage publicPositions
        weights context trace.answers trace.tail.rest right moved.1)
      right moved.1 (answerBounded fallback moved.2) =
    hadamardRoot shape
      (productionLayerSpecAt shape causalSecret baseMessage publicPositions
        weights context trace.answers trace.tail.rest left input.1)
      left input.1 (answerBounded fallback input.2) at hroot
  have halgebraic := productionAlgebraicProof_coinEquiv shape causalSecret
    baseMessage publicPositions weights context left right hpublic
    trace.answers trace.tail.rest input.1
  rw [hmovedCoins] at hroot
  unfold productionLayerSpecAt at hroot
  rw [← halgebraic] at hroot
  rw [hmovedCoins]
  unfold productionProofOfTrace finishProductionProof
  rw [← halgebraic]
  dsimp only
  rw [hroot]
  unfold assembleProductionProof productionProtocolCoinEquiv
  rfl

/-- Concrete equations exposed by one successful run of the actual real
production protocol.  These are consequences of `productionRealTrace`, not
coupling assumptions. -/
structure ProductionTraceFacts {W : Type*} {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape)
    (table : BoundedBytes maxPointLength → OracleBlock)
    (trace : ProductionExecutionTrace shape) : Prop where
  outerCommitment : outerRoot shape baseMessage witness coins
      (answerBounded fallback table) = trace.outerCommitment
  linearCommitment : linearRoot shape coins (answerBounded fallback table) =
      trace.linearCommitment
  equalityPoint : sampleEqualityPointPrefix (answerBounded fallback table)
      (m shape - kSkip - 7) veilSamplingTrials
      (preEqualityTranscript (productionStatementDigest statement) r1csDigest
        coins.proofNonce coins.treeNonces.outer coins.treeNonces.veilLinear
        coins.treeNonces.veilHadamard trace.outerCommitment
        trace.linearCommitment) = some trace.equalityPoint
  answers : AdaptiveOracleProgramming.run
      (zerocheckRealByteSchedule shape causalSecret completion
        trace.equalityPoint.2.2 witness coins)
      (answerBounded fallback table) (programmedPoints shape) = trace.answers
  tail : sampleProductionTail shape (answerBounded fallback table)
      trace.equalityPoint
      (afterZerocheck shape causalSecret completion trace.equalityPoint.2.2
        witness coins trace.answers) = some trace.tail

/-- Eliminate a successful real trace into the five exact equations used by
the concrete coupling proof. -/
theorem productionRealTrace_facts
    {W : Type*} {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape)
    (table : BoundedBytes maxPointLength → OracleBlock)
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion baseMessage statement witness coins table = some trace) :
    ProductionTraceFacts shape fallback r1csDigest causalSecret completion
      baseMessage statement witness coins table trace := by
  let oracle := answerBounded fallback table
  let outerCommitment := outerRoot shape baseMessage witness coins oracle
  let linearCommitment := linearRoot shape coins oracle
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest coins.proofNonce coins.treeNonces.outer
    coins.treeNonces.veilLinear coins.treeNonces.veilHadamard outerCommitment
    linearCommitment
  change
    (match sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
        veilSamplingTrials prelude with
      | none => none
      | some equalityPoint =>
          let schedule := zerocheckRealByteSchedule shape causalSecret
            completion equalityPoint.2.2 witness coins
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
              tail := tail }) = some trace at htrace
  generalize hequality : sampleEqualityPointPrefix oracle
    (m shape - kSkip - 7) veilSamplingTrials prelude = equalityResult at htrace
  cases equalityResult with
  | none => contradiction
  | some equalityPoint =>
      simp only at htrace
      let schedule := zerocheckRealByteSchedule shape causalSecret completion
        equalityPoint.2.2 witness coins
      let answers := AdaptiveOracleProgramming.run schedule oracle
        (programmedPoints shape)
      let postZerocheck := afterZerocheck shape causalSecret completion
        equalityPoint.2.2 witness coins answers
      generalize htail : sampleProductionTail shape oracle equalityPoint
        postZerocheck = tailResult at htrace
      cases tailResult with
      | none => cases htrace
      | some tail =>
          simp only at htrace
          have hrecord := Option.some.inj htrace
          subst trace
          exact {
            outerCommitment := rfl
            linearCommitment := rfl
            equalityPoint := hequality
            answers := rfl
            tail := htail }

/-- At every actual simulator programming point, the Merkle-transported
oracle already contains the corresponding honest causal answer. -/
theorem productionMerkleCoinOracleEquivAt_answer_simulatorPoint
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock)
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
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (hrun : AdaptiveOracleProgramming.run
      (zerocheckRealByteSchedule shape causalSecret completion
        trace.equalityPoint.2.2 left input.1)
      (answerBounded fallback input.2) (programmedPoints shape) =
        trace.answers)
    (hfiat : isFiatShamirPoint trace.equalityPoint.2.2)
    (site : Fin (programmedPoints shape)) :
    let moved := productionMerkleCoinOracleEquivAt shape input.1
      causalSecret baseMessage publicPositions weights context left right
      trace.answers trace.tail.rest houter hlinear hhadamard input
    answerBounded fallback moved.2
        (tracePoint
          (zerocheckSimulatedByteSchedule shape causalSecret
            trace.equalityPoint.2.2 right moved.1 trace.answers)
          trace.answers site) = trace.answers site := by
  let moved := productionMerkleCoinOracleEquivAt shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard input
  let movedProtocolCoins := productionProtocolCoinEquiv shape causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest input.1
  have hmovedCoins : moved.1 = movedProtocolCoins := by
    exact productionMerkleCoinOracleEquivAt_coins shape input.1 causalSecret
      baseMessage publicPositions weights context left right trace.answers
      trace.tail.rest houter hlinear hhadamard input
  let simulatedPoint := tracePoint
    (zerocheckSimulatedByteSchedule shape causalSecret trace.equalityPoint.2.2
      right moved.1 trace.answers) trace.answers site
  let realPoint := tracePoint
    (zerocheckRealByteSchedule shape causalSecret completion
      trace.equalityPoint.2.2 left input.1) trace.answers site
  have hsimFiat : isFiatShamirPoint simulatedPoint := by
    exact simulatedZerocheck_tracePoint_isFiatShamir shape causalSecret
      trace.equalityPoint.2.2 right moved.1 trace.answers hfiat site
  have hmerkle : answerBounded fallback moved.2 simulatedPoint =
      answerBounded fallback input.2 simulatedPoint := by
    exact productionMerkleCoinOracleEquivAt_answer_fiat_all shape input.1
      causalSecret baseMessage publicPositions weights context left right
      trace.answers trace.tail.rest houter hlinear hhadamard fallback input
      simulatedPoint hsimFiat
  have hpoint : simulatedPoint = realPoint := by
    change tracePoint
        (zerocheckSimulatedByteSchedule shape causalSecret
          trace.equalityPoint.2.2 right moved.1 trace.answers)
        trace.answers site = _
    rw [hmovedCoins]
    exact productionZerocheck_tracePoint_coinEquiv shape causalSecret
      completion baseMessage publicPositions weights context left right hpublic
      trace.equalityPoint.2.2 trace.answers trace.tail.rest input.1 site
  have hreal : answerBounded fallback input.2 realPoint = trace.answers site := by
    have horacle := oracle_tracePoint_run
      (zerocheckRealByteSchedule shape causalSecret completion
        trace.equalityPoint.2.2 left input.1)
      (answerBounded fallback input.2) site
    rw [hrun] at horacle
    exact horacle
  change answerBounded fallback moved.2 simulatedPoint = trace.answers site
  rw [hmerkle, hpoint, hreal]

/-- The final simulator zerocheck transcript is exactly the final state of
the real prefix-adaptive schedule after the concrete FLOCK/VEIL coin
transport.  This theorem is why the real and simulated experiments use
separate post-zerocheck definitions. -/
theorem afterSimulatedZerocheck_coinEquiv
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape)
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
    (absorbedPrefix : List Byte)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (coins : ProductionCoins shape) :
    let moved := productionProtocolCoinEquiv shape causalSecret baseMessage
      publicPositions weights context left right answers rest coins
    afterSimulatedZerocheck shape causalSecret absorbedPrefix right moved
        answers =
      afterZerocheck shape causalSecret completion absorbedPrefix left coins
        answers := by
  dsimp only
  let moved := productionProtocolCoinEquiv shape causalSecret baseMessage
    publicPositions weights context left right answers rest coins
  let simulatedTranscript :=
    VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
      answers (right, moved.outer.1, moved.outer.2.1) moved.outer.2.2
  let honestStartTranscript :=
    VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
      causalSecret completion (left, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  have htranscript : simulatedTranscript =
      VeiledFlock.ProductionCausalMaskTranscript.transcript shape causalSecret
        answers (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2 := by
    exact productionMaskTranscript_coinEquiv shape causalSecret baseMessage
      publicPositions weights context left right hpublic answers rest coins
  unfold afterSimulatedZerocheck afterZerocheck
  apply appendState_eq_of_traceSteps
    (ProductionZerocheckSchedule.start shape absorbedPrefix
      honestStartTranscript)
    (ProductionZerocheckSchedule.start shape absorbedPrefix
      simulatedTranscript)
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
        causalSecret completion (left, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2)
      (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
        causalSecret completion (left, coins.outer.1, coins.outer.2.1)
        coins.outer.2.2))
    (scalarRoundStep consumeScalar
      (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
      (ProductionZerocheckSchedule.first shape simulatedTranscript)
      (ProductionZerocheckSchedule.second shape simulatedTranscript))
    answers
  · exact VeiledFlock.ProductionCausalScheduleTransport.start_transport shape
      causalSecret completion answers
      (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2
      simulatedTranscript htranscript rfl
  · intro round hle
    simp only [scalarRoundStep]
    rw [VeiledFlock.ProductionCausalScheduleTransport.first_transport shape
      causalSecret completion answers
      (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2
      simulatedTranscript htranscript round hle]
    rw [VeiledFlock.ProductionCausalScheduleTransport.second_transport shape
      causalSecret completion answers
      (left, coins.outer.1, coins.outer.2.1) coins.outer.2.2
      simulatedTranscript htranscript round hle]
  · exact le_rfl

/-- A successful concrete simulator programming pass restores the exact
Merkle-transported oracle table.  The initially sampled simulator answers are
stored at the future programmed coordinates by `productionCoupledInputAt`,
and the reached honest answers are then installed by the shared state machine. -/
theorem productionProgramming_restores_moved
    {PublicCoord W : Type*} [Fintype PublicCoord]
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
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
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤ ProductionMaxPointLength shape maxStartLength)
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
    (hfiat : isFiatShamirPoint trace.equalityPoint.2.2)
    (state : SharedOracleState (ProductionMaxPointLength shape maxStartLength))
    (hstate : state.table =
      (productionCoupledInputAt shape maxStartLength causalSecret baseMessage
        publicPositions weights context left right trace houter hlinear
        hhadamard input hstart).2)
    (hok :
      let coupled := productionCoupledInputAt shape maxStartLength causalSecret
        baseMessage publicPositions weights context left right trace houter
        hlinear hhadamard input hstart
      let schedule := zerocheckSimulatedByteSchedule shape causalSecret
        trace.equalityPoint.2.2 right coupled.1 trace.answers
      (programSharedByteSchedule schedule trace.answers state).1 = .ok ()) :
    let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
      baseMessage publicPositions weights context left right trace.answers
      trace.tail.rest houter hlinear hhadamard input
    let coupled := productionCoupledInputAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context left right trace houter
      hlinear hhadamard input hstart
    let schedule := zerocheckSimulatedByteSchedule shape causalSecret
      trace.equalityPoint.2.2 right coupled.1 trace.answers
    (programSharedByteSchedule schedule trace.answers state).2.table =
      moved.2 := by
  dsimp only
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let coupled := productionCoupledInputAt shape maxStartLength causalSecret
    baseMessage publicPositions weights context left right trace houter hlinear
    hhadamard input hstart
  let schedule := zerocheckSimulatedByteSchedule shape causalSecret
    trace.equalityPoint.2.2 right coupled.1 trace.answers
  let simSchedule := zerocheckSimulatedByteSchedule shape causalSecret
    trace.equalityPoint.2.2 right moved.1 trace.answers
  have hcoupledCoins : coupled.1 = withSimulatedAnswers shape moved.1
      trace.answers := by rfl
  have hcoupledTable : coupled.2 = OracleProgramming.program
      (productionSimulatorProgramPoints shape maxStartLength causalSecret
        trace.equalityPoint.2.2 right moved.1 trace.answers hstart)
      (productionSimulatorProgramPoints_injective shape maxStartLength
        causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart)
      moved.2 moved.1.simulatedAnswers := by rfl
  have hschedule : schedule = simSchedule := by
    unfold schedule
    rw [hcoupledCoins]
    rfl
  change (programSharedByteSchedule schedule trace.answers state).1 = .ok ()
    at hok
  change (programSharedByteSchedule schedule trace.answers state).2.table =
    moved.2
  rw [hschedule] at hok ⊢
  have hfits : ∀ site, (tracePoint simSchedule trace.answers site).length ≤
      ProductionMaxPointLength shape maxStartLength := by
    intro site
    exact simulatedZerocheck_tracePoint_fits shape maxStartLength causalSecret
      trace.equalityPoint.2.2 right moved.1 trace.answers hstart site
  apply programSharedByteSchedule_restores simSchedule trace.answers moved.2 state
    hfits
  · intro site
    have hanswer := productionMerkleCoinOracleEquivAt_answer_simulatorPoint
      shape fallback causalSecret completion baseMessage publicPositions
      weights context left right hpublic trace houter hlinear hhadamard input
      hrun hfiat site
    have hfit := hfits site
    have hfit' :
        (tracePoint (zerocheckSimulatedByteSchedule shape causalSecret
          trace.equalityPoint.2.2 right moved.1 trace.answers)
          trace.answers site).length ≤
          ProductionMaxPointLength shape maxStartLength := by
      simpa only [simSchedule] using hfit
    dsimp only at hanswer
    rw [answerBounded_of_le fallback moved.2 _ hfit'] at hanswer
    simpa only [simSchedule, Subsingleton.elim (hfits site) hfit'] using
      hanswer
  · intro point hoff
    rw [hstate, hcoupledTable]
    apply OracleProgramming.program_off
    rintro ⟨site, heq⟩
    apply hoff site
    unfold simSchedule
    exact heq.symm
  · exact hok

theorem afterGrind_isFiatShamir {transcript : List Byte}
    (hfiat : isFiatShamirPoint transcript) (nonce : Word64) :
    isFiatShamirPoint (afterGrind transcript nonce) := by
  have hnonempty : transcript ≠ [] := by
    intro hempty
    simp [isFiatShamirPoint, hempty] at hfiat
  simpa [isFiatShamirPoint, afterGrind, hnonempty] using hfiat

theorem sampleScalarUntil_some_isFiatShamir
    (good : GhashField → Prop) [DecidablePred good]
    (oracle : List Byte → OracleBlock) (trials : ℕ)
    (transcript : List Byte) (hfiat : isFiatShamirPoint transcript)
    (value : GhashField) (next : List Byte)
    (hsome : sampleScalarUntil good oracle trials transcript =
      some (value, next)) :
    isFiatShamirPoint next := by
  induction trials generalizing transcript with
  | zero => simp [sampleScalarUntil] at hsome
  | succ trials ih =>
      simp only [sampleScalarUntil] at hsome
      split at hsome
      · have hpair := Option.some.inj hsome
        have hnext : (sampleScalar oracle transcript).2 = next :=
          congrArg Prod.snd hpair
        rw [← hnext]
        exact sampleScalar_next_isFiatShamir hfiat oracle
      · exact ih (sampleScalar oracle transcript).2
          (sampleScalar_next_isFiatShamir hfiat oracle) hsome

theorem collectUnique_some_isFiatShamir {domain : ℕ}
    (position : GhashField → Fin domain) (target : ℕ)
    (oracle : List Byte → OracleBlock) (trials : ℕ)
    (transcript : List Byte) (hfiat : isFiatShamirPoint transcript)
    (selected : Finset (Fin domain)) (result : Finset (Fin domain))
    (next : List Byte)
    (hsome : collectUnique position target oracle trials transcript selected =
      some (result, next)) :
    isFiatShamirPoint next := by
  induction trials generalizing transcript selected with
  | zero =>
      simp only [collectUnique] at hsome
      split at hsome
      · have hpair := Option.some.inj hsome
        have hnext : transcript = next := congrArg Prod.snd hpair
        rw [← hnext]
        exact hfiat
      · contradiction
  | succ trials ih =>
      simp only [collectUnique] at hsome
      split at hsome
      · have hpair := Option.some.inj hsome
        have hnext : transcript = next := congrArg Prod.snd hpair
        rw [← hnext]
        exact hfiat
      · exact ih (sampleScalar oracle transcript).2
          (sampleScalar_next_isFiatShamir hfiat oracle) _ hsome

theorem grindLigeritoSites_oracle_congr
    (leftOracle rightOracle : List Byte → OracleBlock)
    (sites : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hscalar : ∀ point, isFiatShamirPoint point →
      rightOracle point = leftOracle point)
    (hpow : ∀ state nonce,
      rightOracle (encodePowPoint state nonce) =
        leftOracle (encodePowPoint state nonce)) :
    grindLigeritoSites rightOracle sites transcript =
      grindLigeritoSites leftOracle sites transcript := by
  induction sites generalizing transcript with
  | zero => rfl
  | succ sites ih =>
      have hstate : rightOracle (scalarPoint transcript) =
          leftOracle (scalarPoint transcript) :=
        hscalar _ (scalarPoint_isFiatShamir hfiat)
      have hgrind := grindPowBounded_oracle_congr
        (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide))
        leftOracle rightOracle (leftOracle (scalarPoint transcript))
        maxLigeritoTrials (fun candidate _ => hpow _ _)
      let continueRight : Option Word64 →
          Option (List Word64 × List Byte)
        | none => none
        | some nonce =>
            match grindLigeritoSites rightOracle sites
                (afterGrind transcript nonce) with
            | none => none
            | some (nonces, finalTranscript) =>
                some (nonce :: nonces, finalTranscript)
      let continueLeft : Option Word64 →
          Option (List Word64 × List Byte)
        | none => none
        | some nonce =>
            match grindLigeritoSites leftOracle sites
                (afterGrind transcript nonce) with
            | none => none
            | some (nonces, finalTranscript) =>
                some (nonce :: nonces, finalTranscript)
      calc
        grindLigeritoSites rightOracle (sites + 1) transcript =
            continueRight
              (grindPowBounded
                (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide))
                rightOracle (rightOracle (scalarPoint transcript))
                maxLigeritoTrials) := by
              simp only [grindLigeritoSites, continueRight]
              congr 3
        _ = continueRight
              (grindPowBounded
                (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide))
                leftOracle (leftOracle (scalarPoint transcript))
                maxLigeritoTrials) := by
              apply congrArg continueRight
              rw [hstate]
              exact hgrind
        _ = continueLeft
              (grindPowBounded
                (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide))
                leftOracle (leftOracle (scalarPoint transcript))
                maxLigeritoTrials) := by
              generalize hresult : grindPowBounded
                (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide))
                leftOracle (leftOracle (scalarPoint transcript))
                maxLigeritoTrials = result
              cases result with
              | none => rfl
              | some nonce =>
                  simp only [continueRight, continueLeft]
                  rw [ih (afterGrind transcript nonce)
                    (afterGrind_isFiatShamir hfiat nonce)]
        _ = grindLigeritoSites leftOracle (sites + 1) transcript := by
              simp only [grindLigeritoSites, continueLeft]
              congr 3

/-- Equality of the entire observable tail trace, including retry-derived
transcripts, all sampled position sets, the first successful grinding nonces,
and the final transcript.  This is joint equality, not marginal equality. -/
theorem sampleProductionTailRaw_oracle_congr
    (shape : BatchShape)
    (leftOracle rightOracle : List Byte → OracleBlock)
    (transcript : List Byte) (hfiat : isFiatShamirPoint transcript)
    (hscalar : ∀ point, isFiatShamirPoint point →
      rightOracle point = leftOracle point)
    (hpow : ∀ state nonce,
      rightOracle (encodePowPoint state nonce) =
        leftOracle (encodePowPoint state nonce)) :
    sampleProductionTailRaw shape rightOracle transcript =
      sampleProductionTailRaw shape leftOracle transcript := by
  simp only [sampleProductionTailRaw]
  have hstate : rightOracle (scalarPoint transcript) =
      leftOracle (scalarPoint transcript) :=
    hscalar _ (scalarPoint_isFiatShamir hfiat)
  rw [hstate]
  rw [grindPowBounded_oracle_congr blindGrindingGood leftOracle rightOracle
    (leftOracle (scalarPoint transcript)) maxBlindTrials
    (fun candidate _ => hpow _ _)]
  split
  · rfl
  · rename_i blindNonce hblindNonce
    have hafterBlind : isFiatShamirPoint (afterGrind transcript blindNonce) :=
      afterGrind_isFiatShamir hfiat blindNonce
    have hblind := sampleScalarUntil_oracle_congr_fiat_bounded nonzero leftOracle
      rightOracle veilSamplingTrials
      ((afterGrind transcript blindNonce).length + veilSamplingTrials * 18)
      (afterGrind transcript blindNonce) hafterBlind
      (by omega) (fun point hpoint _ => hscalar point hpoint)
    change sampleNonzero rightOracle veilSamplingTrials
        (afterGrind transcript blindNonce) =
      sampleNonzero leftOracle veilSamplingTrials
        (afterGrind transcript blindNonce) at hblind
    rw [hblind]
    split
    · rfl
    · rename_i blindChallenge afterBlindChallenge hblindSample
      have hafterBlindChallenge : isFiatShamirPoint afterBlindChallenge :=
        sampleScalarUntil_some_isFiatShamir nonzero leftOracle
          veilSamplingTrials (afterGrind transcript blindNonce) hafterBlind
          blindChallenge afterBlindChallenge hblindSample
      have halpha := sampleScalarUntil_oracle_congr_fiat_bounded notZeroOrOne
        leftOracle rightOracle veilSamplingTrials
        (afterBlindChallenge.length + veilSamplingTrials * 18)
        afterBlindChallenge hafterBlindChallenge (by omega)
        (fun point hpoint _ => hscalar point hpoint)
      change sampleNotZeroOrOne rightOracle veilSamplingTrials
          afterBlindChallenge =
        sampleNotZeroOrOne leftOracle veilSamplingTrials
          afterBlindChallenge at halpha
      rw [halpha]
      split
      · rfl
      · rename_i multiplicationAlpha afterAlpha halphaSample
        have hafterAlpha : isFiatShamirPoint afterAlpha :=
          sampleScalarUntil_some_isFiatShamir notZeroOrOne leftOracle
            veilSamplingTrials afterBlindChallenge hafterBlindChallenge
            multiplicationAlpha afterAlpha halphaSample
        have houterChallenge := sampleScalarUntil_oracle_congr_fiat_bounded
          nonzero leftOracle rightOracle veilSamplingTrials
          (afterAlpha.length + veilSamplingTrials * 18) afterAlpha hafterAlpha
          (by omega) (fun point hpoint _ => hscalar point hpoint)
        change sampleNonzero rightOracle veilSamplingTrials afterAlpha =
          sampleNonzero leftOracle veilSamplingTrials afterAlpha at houterChallenge
        rw [houterChallenge]
        split
        · rfl
        · rename_i outerChallenge afterOuterChallenge houterSample
          have hafterOuterChallenge : isFiatShamirPoint afterOuterChallenge :=
            sampleScalarUntil_some_isFiatShamir nonzero leftOracle
              veilSamplingTrials afterAlpha hafterAlpha outerChallenge
              afterOuterChallenge houterSample
          rw [sampleUniquePositions_oracle_congr_fiat_bounded
            (rustLowPosition (m shape - 11)) (outerL0QueryCount shape)
            leftOracle rightOracle veilSamplingTrials
            (afterOuterChallenge.length + veilSamplingTrials * 18)
            afterOuterChallenge hafterOuterChallenge (by omega)
            (fun point hpoint _ => hscalar point hpoint)]
          split
          · rfl
          · rename_i outerSet afterOuterPositions houterPositions
            have hafterOuterPositions : isFiatShamirPoint afterOuterPositions :=
              collectUnique_some_isFiatShamir
                (rustLowPosition (m shape - 11)) (outerL0QueryCount shape)
                leftOracle veilSamplingTrials afterOuterChallenge
                hafterOuterChallenge ∅ outerSet afterOuterPositions
                (by simpa [sampleUniquePositions] using houterPositions)
            rw [sampleUniquePositions_oracle_congr_fiat_bounded
              (rustLowPosition 13) veilQueryCount leftOracle rightOracle
              veilSamplingTrials
              (afterOuterPositions.length + veilSamplingTrials * 18)
              afterOuterPositions hafterOuterPositions (by omega)
              (fun point hpoint _ => hscalar point hpoint)]
            split
            · rfl
            · rename_i linearSet afterLinearPositions hlinearPositions
              have hafterLinearPositions :
                  isFiatShamirPoint afterLinearPositions :=
                collectUnique_some_isFiatShamir (rustLowPosition 13)
                  veilQueryCount leftOracle veilSamplingTrials
                  afterOuterPositions hafterOuterPositions ∅ linearSet
                  afterLinearPositions
                  (by simpa [sampleUniquePositions] using hlinearPositions)
              have hlinearRho := sampleScalarUntil_oracle_congr_fiat_bounded
                nonzero leftOracle rightOracle veilSamplingTrials
                (afterLinearPositions.length + veilSamplingTrials * 18)
                afterLinearPositions hafterLinearPositions (by omega)
                (fun point hpoint _ => hscalar point hpoint)
              change sampleNonzero rightOracle veilSamplingTrials
                  afterLinearPositions =
                sampleNonzero leftOracle veilSamplingTrials
                  afterLinearPositions at hlinearRho
              rw [hlinearRho]
              split
              · rfl
              · rename_i linearRho afterLinearRho hlinearRhoSample
                have hafterLinearRho : isFiatShamirPoint afterLinearRho :=
                  sampleScalarUntil_some_isFiatShamir nonzero leftOracle
                    veilSamplingTrials afterLinearPositions
                    hafterLinearPositions linearRho afterLinearRho
                    hlinearRhoSample
                rw [sampleUniquePositions_oracle_congr_fiat_bounded
                  (rustLowPosition 11) veilQueryCount leftOracle rightOracle
                  veilSamplingTrials
                  (afterLinearRho.length + veilSamplingTrials * 18)
                  afterLinearRho hafterLinearRho (by omega)
                  (fun point hpoint _ => hscalar point hpoint)]
                split
                · rfl
                · rename_i hadamardSet afterHadamardPositions
                    hhadamardPositions
                  have hafterHadamardPositions :
                      isFiatShamirPoint afterHadamardPositions :=
                    collectUnique_some_isFiatShamir (rustLowPosition 11)
                      veilQueryCount leftOracle veilSamplingTrials
                      afterLinearRho hafterLinearRho ∅ hadamardSet
                      afterHadamardPositions
                      (by simpa [sampleUniquePositions] using
                        hhadamardPositions)
                  have hhadamardRho :=
                    sampleScalarUntil_oracle_congr_fiat_bounded nonzero
                      leftOracle rightOracle veilSamplingTrials
                      (afterHadamardPositions.length +
                        veilSamplingTrials * 18)
                      afterHadamardPositions hafterHadamardPositions (by omega)
                      (fun point hpoint _ => hscalar point hpoint)
                  change sampleNonzero rightOracle veilSamplingTrials
                      afterHadamardPositions =
                    sampleNonzero leftOracle veilSamplingTrials
                      afterHadamardPositions at hhadamardRho
                  rw [hhadamardRho]
                  split
                  · rfl
                  · rename_i hadamardRho afterHadamardRho
                      hhadamardRhoSample
                    have hafterHadamardRho :
                        isFiatShamirPoint afterHadamardRho :=
                      sampleScalarUntil_some_isFiatShamir nonzero leftOracle
                        veilSamplingTrials afterHadamardPositions
                        hafterHadamardPositions hadamardRho afterHadamardRho
                        hhadamardRhoSample
                    have hproduct :=
                      sampleScalarUntil_oracle_congr_fiat_bounded nonzero
                        leftOracle rightOracle veilSamplingTrials
                        (afterHadamardRho.length + veilSamplingTrials * 18)
                        afterHadamardRho hafterHadamardRho (by omega)
                        (fun point hpoint _ => hscalar point hpoint)
                    change sampleNonzero rightOracle veilSamplingTrials
                        afterHadamardRho =
                      sampleNonzero leftOracle veilSamplingTrials
                        afterHadamardRho at hproduct
                    rw [hproduct]
                    split
                    · rfl
                    · rename_i productCoefficient afterProduct
                        hproductSample
                      have hafterProduct : isFiatShamirPoint afterProduct :=
                        sampleScalarUntil_some_isFiatShamir nonzero leftOracle
                          veilSamplingTrials afterHadamardRho
                          hafterHadamardRho productCoefficient afterProduct
                          hproductSample
                      rw [grindLigeritoSites_oracle_congr leftOracle
                        rightOracle maxLigeritoSites afterProduct hafterProduct
                        hscalar hpow]

/-- The certificate-bearing production tail is exactly preserved whenever
the coupled oracle agrees on the actual Fiat--Shamir and PoW domains. -/
theorem sampleProductionTail_oracle_congr
    (shape : BatchShape)
    (leftOracle rightOracle : List Byte → OracleBlock)
    (equalityPoint : VeiledFlock.ProductionEqualitySampler.EqualitySample
      (m shape - kSkip - 7))
    (transcript : List Byte) (hfiat : isFiatShamirPoint transcript)
    (hscalar : ∀ point, isFiatShamirPoint point →
      rightOracle point = leftOracle point)
    (hpow : ∀ state nonce,
      rightOracle (encodePowPoint state nonce) =
        leftOracle (encodePowPoint state nonce)) :
    sampleProductionTail shape rightOracle equalityPoint transcript =
      sampleProductionTail shape leftOracle equalityPoint transcript := by
  unfold sampleProductionTail
  rw [sampleProductionTailRaw_oracle_congr shape leftOracle rightOracle
    transcript hfiat hscalar hpow]

/-! ## Explicit operational good event for the complete production view -/

/-- The empty-audit initial state used by both concrete security experiments.
The coupled executions may start with different tables, but neither starts
with a hidden prior query or programming event. -/
def initialSharedOracleState {maxPointLength : ℕ}
    (table : BoundedBytes maxPointLength → OracleBlock) :
    SharedOracleState maxPointLength :=
  { table := table, events := [] }

/-- The exact adaptive pre-proof history generated against a table. -/
def productionPreHistory
    {AdversaryCoins FinalState : Type*} {shape : BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape) maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (coins : AdversaryCoins)
    (table : BoundedBytes maxPointLength → OracleBlock) :
    List (BoundedBytes maxPointLength × OracleBlock) :=
  runQueryValues
    (fun round history => adversary.preQuery round statement coins history)
    table (List.ofFn id) []

/-- The exact proof-dependent adaptive post-proof history generated against a
table, after fixing the complete visible pre-proof history. -/
def productionPostHistory
    {AdversaryCoins FinalState : Type*} {shape : BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape) maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (proof : Option (FormalVeilFlockProof shape (ProductionRest shape)))
    (coins : AdversaryCoins)
    (preHistory : List (BoundedBytes maxPointLength × OracleBlock))
    (table : BoundedBytes maxPointLength → OracleBlock) :
    List (BoundedBytes maxPointLength × OracleBlock) :=
  runQueryValues
    (fun round history => adversary.postQuery round statement proof coins
      preHistory history)
    table (List.ofFn id) []

/-- No adversarial call in `history` is one of the actual points at which the
simulator will program the shared oracle.  This is the concrete
`BadPrequery` complement used by the coupling. -/
def AvoidsProductionProgramPoints {maxPointLength sites : ℕ}
    (points : Fin sites → BoundedBytes maxPointLength)
    (history : List (BoundedBytes maxPointLength × OracleBlock)) : Prop :=
  ∀ call ∈ history, ∀ site, call.1 ≠ points site

/-- One reached adversarial history avoids every salted leaf coordinate whose
answer is exchanged by the concrete three-tree Merkle transport, on both the
honest-witness and public-representative sides. -/
def AvoidsProductionMerkleTransport
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (coins : ProductionCoins shape)
    (history : List (BoundedBytes maxPointLength × OracleBlock)) : Prop :=
  ∀ call ∈ history,
    (∀ index,
      unboundBytes call.1 ≠
        familyLeafPoint (productionTreeGeometry shape geometryCoins)
          (productionTreeMaterial shape geometryCoins causalSecret baseMessage
            publicPositions weights context answers rest left) coins index) ∧
    (∀ index,
      unboundBytes call.1 ≠
        familyLeafPoint (productionTreeGeometry shape geometryCoins)
          (productionTreeMaterial shape geometryCoins causalSecret baseMessage
            publicPositions weights context answers rest right)
          (productionProtocolCoinEquiv shape causalSecret baseMessage
            publicPositions weights context left right answers rest coins)
          index)

/-- The proof assembled from the successful concrete real trace. -/
noncomputable def productionTraceProof
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ} (shape : BatchShape) (fallback : OracleBlock)
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
    (table : BoundedBytes maxPointLength → OracleBlock)
    (trace : ProductionExecutionTrace shape) :
    FormalVeilFlockProof shape (ProductionRest shape) :=
  productionProofOfTrace shape causalSecret baseMessage publicPositions weights
    context witness coins (answerBounded fallback table) trace

/-- The explicit operational `Good` event for one concrete successful
production coupling fiber.  Its fields are only success/freshness facts about
actual executions and actual serialized oracle points; it contains no
real/simulator equality or coupling premise. -/
structure ProductionGood
    {PublicCoord W AdversaryCoins FinalState : Type*} [Fintype PublicCoord]
    {preQueries postQueries : ℕ}
    (shape : BatchShape) (maxStartLength : ℕ) (fallback : OracleBlock)
    (r1csDigest : List Byte)
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
    (input : ProductionCouplingInput shape maxStartLength) : Prop
    where
  startBound :
      let moved := productionMerkleCoinOracleEquivAt shape input.1
        causalSecret baseMessage publicPositions weights context witness
        (publicRepresentative statement) trace.answers trace.tail.rest houter
        hlinear hhadamard input
      (VeiledFlock.ProductionZerocheckSchedule.start shape
        trace.equalityPoint.2.2
        (VeiledFlock.ProductionCausalMaskTranscript.transcript shape
          causalSecret trace.answers
          (publicRepresentative statement, moved.1.outer.1,
            moved.1.outer.2.1) moved.1.outer.2.2)).length ≤ maxStartLength
  traceSuccess :
    productionRealTrace shape fallback r1csDigest causalSecret completion
      baseMessage statement witness input.1 input.2 = some trace
  preMerkleFresh :
    AvoidsProductionMerkleTransport shape input.1 causalSecret baseMessage
      publicPositions weights context witness (publicRepresentative statement)
      trace.answers trace.tail.rest input.1
      (productionPreHistory adversary statement adversaryCoins input.2)
  preProgrammingFresh :
    let moved := productionMerkleCoinOracleEquivAt shape input.1
      causalSecret baseMessage publicPositions weights context witness
      (publicRepresentative statement) trace.answers trace.tail.rest houter
      hlinear hhadamard input
    let points := productionSimulatorProgramPoints shape maxStartLength
      causalSecret trace.equalityPoint.2.2 (publicRepresentative statement)
      moved.1 trace.answers startBound
    AvoidsProductionProgramPoints points
      (productionPreHistory adversary statement adversaryCoins input.2)
  postMerkleFresh :
    AvoidsProductionMerkleTransport shape input.1 causalSecret baseMessage
      publicPositions weights context witness (publicRepresentative statement)
      trace.answers trace.tail.rest input.1
      (productionPostHistory adversary statement
        (some (productionTraceProof shape fallback causalSecret baseMessage
          publicPositions weights context witness input.1 input.2 trace))
        adversaryCoins
        (productionPreHistory adversary statement adversaryCoins input.2)
        input.2)
  programmingSucceeds :
    let moved := productionMerkleCoinOracleEquivAt shape input.1
      causalSecret baseMessage publicPositions weights context witness
      (publicRepresentative statement) trace.answers trace.tail.rest houter
      hlinear hhadamard input
    let coupled := productionCoupledInputAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context witness
      (publicRepresentative statement) trace houter hlinear hhadamard input
      startBound
    let preState :=
      (runPreQueries adversary statement adversaryCoins
        (initialSharedOracleState coupled.2)).2
    let schedule := zerocheckSimulatedByteSchedule shape causalSecret
      trace.equalityPoint.2.2 (publicRepresentative statement) coupled.1
      trace.answers
    (programSharedByteSchedule schedule trace.answers preState).1 = .ok ()

/-- The concrete three-tree transport cannot change any answer actually
reached by an adversarial history satisfying the serialized-leaf freshness
part of `ProductionGood`. -/
theorem productionMerkleTransport_agrees_on_safe_history
    {PublicCoord W : Type*} [Fintype PublicCoord]
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
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
    (left right : W)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ProductionCoins shape ×
      (BoundedBytes maxPointLength → OracleBlock))
    (history : List (BoundedBytes maxPointLength × OracleBlock))
    (hsafe : AvoidsProductionMerkleTransport shape geometryCoins causalSecret
      baseMessage publicPositions weights context left right answers rest
      input.1 history) :
    let moved := productionMerkleCoinOracleEquivAt shape geometryCoins
      causalSecret baseMessage publicPositions weights context left right
      answers rest houter hlinear hhadamard input
    ∀ call ∈ history, moved.2 call.1 = input.2 call.1 := by
  dsimp only
  intro call hcall
  have hsafeCall := hsafe call hcall
  have hbound : (unboundBytes call.1).length ≤ maxPointLength := by
    rcases call.1 with ⟨length, bytes⟩
    simp only [unboundBytes, List.Vector.toList_length]
    exact Nat.le_of_lt_succ length.isLt
  have hrebound : boundBytes (unboundBytes call.1) hbound = call.1 := by
    apply unboundBytes_injective
    simp
  have hoff := productionMerkleCoinOracleEquivAt_answer_off shape
    geometryCoins causalSecret baseMessage publicPositions weights context
    left right answers rest houter hlinear hhadamard fallback input
    (unboundBytes call.1) hbound hsafeCall.1 hsafeCall.2
  dsimp only at hoff
  simp only [answerBounded, dif_pos hbound] at hoff
  simpa only [hrebound] using hoff

/-- Programming only Fiat--Shamir points cannot alter a production Merkle
root: every leaf and internal-node input is byte-domain separated from every
programmed point. -/
theorem productionMerkleRoot_program_fiat
    {maxPointLength sites : ℕ}
    (fallback : OracleBlock)
    (points : Fin sites → BoundedBytes maxPointLength)
    (hinjective : Injective points)
    (hpointsFiat : ∀ site, isFiatShamirPoint (unboundBytes (points site)))
    (oracle : BoundedBytes maxPointLength → OracleBlock)
    (answers : Fin sites → OracleBlock)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : Word64) (depth : ℕ)
    (salts : Fin (2 ^ depth) → NumericNonce)
    (payload : Fin (2 ^ depth) → List Byte) :
    VeiledFlock.ProductionMerkleTree.productionMerkleRoot
        (answerBounded fallback
          (OracleProgramming.program points hinjective oracle answers))
        channel treeDepth treeNonce leafLength depth salts payload =
      VeiledFlock.ProductionMerkleTree.productionMerkleRoot
        (answerBounded fallback oracle)
        channel treeDepth treeNonce leafLength depth salts payload := by
  unfold VeiledFlock.ProductionMerkleTree.productionMerkleRoot
  apply VeiledFlock.ProductionMerkleTree.merkleRoot_congr
  · intro level index left right
    let point := VeiledFlock.ProductionMerkleTree.productionNodePoint channel
      treeDepth treeNonce level index left right
    by_cases hfit : point.length ≤ maxPointLength
    · rw [answerBounded_of_le fallback _ point hfit,
        answerBounded_of_le fallback oracle point hfit]
      apply OracleProgramming.program_off
      rintro ⟨site, heq⟩
      have hunbound := congrArg unboundBytes heq
      simp only [unbound_boundBytes] at hunbound
      exact fiatShamir_ne_merkle (hpointsFiat site) .node channel treeDepth
        treeNonce (BitVec.ofNat 64 64) level (BitVec.ofNat 64 index.val)
        (VeiledFlock.ProductionMerkleTree.oracleBlockBytes left ++
          VeiledFlock.ProductionMerkleTree.oracleBlockBytes right) (by
            simpa [point,
              VeiledFlock.ProductionMerkleTree.productionNodePoint,
              VeiledFlock.ProductionMerkleTree.productionNodeQuery,
              encodeMerkleQuery] using hunbound)
    · have hfit' : ¬140 ≤ maxPointLength := by
        simpa [point] using hfit
      simp [answerBounded, hfit']
  · intro index
    let point := VeiledFlock.ProductionMerkleTree.productionLeafPoint channel
      treeDepth treeNonce leafLength depth index (salts index) (payload index)
    by_cases hfit : point.length ≤ maxPointLength
    · rw [answerBounded_of_le fallback _ point hfit,
        answerBounded_of_le fallback oracle point hfit]
      apply OracleProgramming.program_off
      rintro ⟨site, heq⟩
      have hunbound := congrArg unboundBytes heq
      simp only [unbound_boundBytes] at hunbound
      exact fiatShamir_ne_merkle (hpointsFiat site) .leaf channel treeDepth
        treeNonce leafLength (BitVec.ofNat 32 depth)
        (BitVec.ofNat 64 index.val)
        (nonceBytes (numericNonceBytes (salts index)) ++ payload index) (by
          simpa [point,
            VeiledFlock.ProductionMerkleTree.productionLeafPoint,
            VeiledFlock.ProductionMerkleTree.productionLeafQuery,
            encodeMerkleQuery] using hunbound)
    · have hfit' : ¬108 + (payload index).length ≤ maxPointLength := by
        simpa [point] using hfit
      simp [answerBounded, hfit']

/-- Programming the future causal FLOCK Fiat--Shamir points does not change
the already-computed outer or VEIL-linear Merkle commitments.  Combined with
the concrete three-tree witness transport, the simulator therefore computes
exactly the commitments recorded in the successful real trace. -/
theorem productionCoupledInputAt_commitments
    {PublicCoord W : Type*} [Fintype PublicCoord]
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
        (publicStatement shape publicPositions baseMessage))
    (statement : ProductionStatement shape) (left right : W)
    (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
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
    (facts : ProductionTraceFacts shape fallback r1csDigest causalSecret
      completion baseMessage statement left input.1 input.2 trace) :
    let coupled := productionCoupledInputAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context left right trace houter
      hlinear hhadamard input hstart
    let oracle := answerBounded fallback coupled.2
    outerRoot shape baseMessage right coupled.1 oracle =
        trace.outerCommitment ∧
      linearRoot shape coupled.1 oracle = trace.linearCommitment := by
  dsimp only
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let points := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart
  let hinjective := productionSimulatorProgramPoints_injective shape
    maxStartLength causalSecret trace.equalityPoint.2.2 right moved.1
    trace.answers hstart
  let coupled := productionCoupledInputAt shape maxStartLength causalSecret
    baseMessage publicPositions weights context left right trace houter hlinear
    hhadamard input hstart
  have hcoupledCoins : coupled.1 = withSimulatedAnswers shape moved.1
      trace.answers := by rfl
  have hcoupledTable : coupled.2 = OracleProgramming.program points hinjective
      moved.2 moved.1.simulatedAnswers := by rfl
  have houterRoot := productionMerkleCoinOracleEquivAt_roots shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard hnodes fallback input
    (.outer)
  have hlinearRoot := productionMerkleCoinOracleEquivAt_roots shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard hnodes fallback input
    (.veilLinear)
  have houterRoot' : outerRoot shape baseMessage right moved.1
      (answerBounded fallback moved.2) = trace.outerCommitment := by
    dsimp only at houterRoot
    change outerRoot shape baseMessage right moved.1
      (answerBounded fallback moved.2) =
      outerRoot shape baseMessage left input.1
        (answerBounded fallback input.2) at houterRoot
    rw [facts.outerCommitment] at houterRoot
    exact houterRoot
  have hlinearRoot' : linearRoot shape moved.1
      (answerBounded fallback moved.2) = trace.linearCommitment := by
    dsimp only at hlinearRoot
    change linearRoot shape moved.1 (answerBounded fallback moved.2) =
      linearRoot shape input.1 (answerBounded fallback input.2) at hlinearRoot
    rw [facts.linearCommitment] at hlinearRoot
    exact hlinearRoot
  let realPrelude := preEqualityTranscript
    (productionStatementDigest statement) r1csDigest input.1.proofNonce
    input.1.treeNonces.outer input.1.treeNonces.veilLinear
    input.1.treeNonces.veilHadamard trace.outerCommitment
    trace.linearCommitment
  have hpreludeFiat : isFiatShamirPoint realPrelude :=
    preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _
  have htraceFiat : isFiatShamirPoint trace.equalityPoint.2.2 :=
    sampleEqualityPointPrefix_some_isFiatShamir
      (answerBounded fallback input.2) (m shape - kSkip - 7)
      veilSamplingTrials realPrelude hpreludeFiat trace.equalityPoint
      facts.equalityPoint
  have hpointsFiat : ∀ site, isFiatShamirPoint
      (unboundBytes (points site)) := by
    intro site
    simpa only [points, productionSimulatorProgramPoints,
      unbound_boundBytes] using
      (simulatedZerocheck_tracePoint_isFiatShamir shape causalSecret
        trace.equalityPoint.2.2 right moved.1 trace.answers htraceFiat site)
  let simCoins := withSimulatedAnswers shape moved.1 trace.answers
  have houterProgram : outerRoot shape baseMessage right simCoins
      (answerBounded fallback
        (OracleProgramming.program points hinjective moved.2
          moved.1.simulatedAnswers)) =
      outerRoot shape baseMessage right simCoins
        (answerBounded fallback moved.2) := by
    exact productionMerkleRoot_program_fiat fallback points hinjective
      hpointsFiat moved.2 moved.1.simulatedAnswers ⟨0, by decide⟩
      ⟨0, by decide⟩ simCoins.treeNonces.outer
      (BitVec.ofNat 64 (16 * (2 * outerLaneCount))) (m shape - 11)
      simCoins.outerSalts (outerRowPayload shape baseMessage right simCoins)
  have hlinearProgram : linearRoot shape simCoins
      (answerBounded fallback
        (OracleProgramming.program points hinjective moved.2
          moved.1.simulatedAnswers)) =
      linearRoot shape simCoins (answerBounded fallback moved.2) := by
    exact productionMerkleRoot_program_fiat fallback points hinjective
      hpointsFiat moved.2 moved.1.simulatedAnswers ⟨6, by decide⟩
      ⟨0, by decide⟩ simCoins.treeNonces.veilLinear
      (BitVec.ofNat 64 32) 13 simCoins.linearSalts
      (linearRowPayload shape simCoins)
  have houterSim : outerRoot shape baseMessage right simCoins
      (answerBounded fallback moved.2) = trace.outerCommitment := by
    have hsame : outerRoot shape baseMessage right simCoins
        (answerBounded fallback moved.2) =
        outerRoot shape baseMessage right moved.1
          (answerBounded fallback moved.2) := by rfl
    rw [hsame]
    exact houterRoot'
  have hlinearSim : linearRoot shape simCoins
      (answerBounded fallback moved.2) = trace.linearCommitment := by
    have hsame : linearRoot shape simCoins
        (answerBounded fallback moved.2) =
        linearRoot shape moved.1 (answerBounded fallback moved.2) := by rfl
    rw [hsame]
    exact hlinearRoot'
  rw [hcoupledCoins, hcoupledTable]
  constructor
  · exact houterProgram.trans houterSim
  · exact hlinearProgram.trans hlinearSim

/-- The coupled simulator input selects exactly the successful production
equality sample.  The proof combines three-tree root transport, byte-domain
separation of the future programmed points, and the exact retry-prefix law. -/
theorem productionCoupledInputAt_equalityPoint
    {PublicCoord W : Type*} [Fintype PublicCoord]
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
        (publicStatement shape publicPositions baseMessage))
    (statement : ProductionStatement shape) (left right : W)
    (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
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
    (facts : ProductionTraceFacts shape fallback r1csDigest causalSecret
      completion baseMessage statement left input.1 input.2 trace) :
    let coupled := productionCoupledInputAt shape maxStartLength causalSecret
      baseMessage publicPositions weights context left right trace houter
      hlinear hhadamard input hstart
    let oracle := answerBounded fallback coupled.2
    let outerCommitment := outerRoot shape baseMessage right coupled.1 oracle
    let linearCommitment := linearRoot shape coupled.1 oracle
    let prelude := preEqualityTranscript (productionStatementDigest statement)
      r1csDigest coupled.1.proofNonce coupled.1.treeNonces.outer
      coupled.1.treeNonces.veilLinear coupled.1.treeNonces.veilHadamard
      outerCommitment linearCommitment
    sampleEqualityPointPrefix oracle (m shape - kSkip - 7)
      veilSamplingTrials prelude = some trace.equalityPoint := by
  dsimp only
  let moved := productionMerkleCoinOracleEquivAt shape input.1 causalSecret
    baseMessage publicPositions weights context left right trace.answers
    trace.tail.rest houter hlinear hhadamard input
  let points := productionSimulatorProgramPoints shape maxStartLength
    causalSecret trace.equalityPoint.2.2 right moved.1 trace.answers hstart
  let hinjective := productionSimulatorProgramPoints_injective shape
    maxStartLength causalSecret trace.equalityPoint.2.2 right moved.1
    trace.answers hstart
  let coupled := productionCoupledInputAt shape maxStartLength causalSecret
    baseMessage publicPositions weights context left right trace houter hlinear
    hhadamard input hstart
  have hcoupledCoins : coupled.1 = withSimulatedAnswers shape moved.1
      trace.answers := by rfl
  have hcoupledTable : coupled.2 = OracleProgramming.program points hinjective
      moved.2 moved.1.simulatedAnswers := by rfl
  have houterRoot := productionMerkleCoinOracleEquivAt_roots shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard hnodes fallback input
    (.outer)
  have hlinearRoot := productionMerkleCoinOracleEquivAt_roots shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard hnodes fallback input
    (.veilLinear)
  have houterRoot' : outerRoot shape baseMessage right moved.1
      (answerBounded fallback moved.2) =
      outerRoot shape baseMessage left input.1
        (answerBounded fallback input.2) := by
    dsimp only at houterRoot
    change outerRoot shape baseMessage right moved.1
      (answerBounded fallback moved.2) =
      outerRoot shape baseMessage left input.1
        (answerBounded fallback input.2) at houterRoot
    exact houterRoot
  have hlinearRoot' : linearRoot shape moved.1
      (answerBounded fallback moved.2) =
      linearRoot shape input.1 (answerBounded fallback input.2) := by
    dsimp only at hlinearRoot
    change linearRoot shape moved.1 (answerBounded fallback moved.2) =
      linearRoot shape input.1 (answerBounded fallback input.2) at hlinearRoot
    exact hlinearRoot
  rw [facts.outerCommitment] at houterRoot'
  rw [facts.linearCommitment] at hlinearRoot'
  let realPrelude := preEqualityTranscript
    (productionStatementDigest statement) r1csDigest input.1.proofNonce
    input.1.treeNonces.outer input.1.treeNonces.veilLinear
    input.1.treeNonces.veilHadamard trace.outerCommitment
    trace.linearCommitment
  have hpreludeFiat : isFiatShamirPoint realPrelude :=
    preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _
  have hmovedSample : sampleEqualityPointPrefix
      (answerBounded fallback moved.2) (m shape - kSkip - 7)
      veilSamplingTrials realPrelude = some trace.equalityPoint := by
    rw [sampleEqualityPointPrefix_oracle_congr_fiat_bounded
      (answerBounded fallback input.2) (answerBounded fallback moved.2)
      (m shape - kSkip - 7) veilSamplingTrials
      (realPrelude.length + 106 +
        veilSamplingTrials * (10 + 16 * (m shape - kSkip - 7)) + 18)
      realPrelude hpreludeFiat (by omega)]
    · exact facts.equalityPoint
    · intro point hfiat _
      exact productionMerkleCoinOracleEquivAt_answer_fiat_all shape input.1
        causalSecret baseMessage publicPositions weights context left right
        trace.answers trace.tail.rest houter hlinear hhadamard fallback input
        point hfiat
  have hprogramOff : ∀ point, point.length < trace.equalityPoint.2.2.length →
      answerBounded fallback coupled.2 point =
        answerBounded fallback moved.2 point := by
    intro point hlength
    by_cases hfit : point.length ≤ ProductionMaxPointLength shape maxStartLength
    · rw [answerBounded_of_le fallback coupled.2 point hfit,
        answerBounded_of_le fallback moved.2 point hfit, hcoupledTable]
      apply OracleProgramming.program_off
      rintro ⟨site, heq⟩
      have hunbound := congrArg unboundBytes heq
      have hlong := simulatedZerocheck_tracePoint_longer shape causalSecret
        trace.equalityPoint.2.2 right moved.1 trace.answers site
      simp only [points, productionSimulatorProgramPoints,
        unbound_boundBytes] at hunbound
      rw [hunbound] at hlong
      omega
    · simp [answerBounded, hfit]
  have hmovedCoins := productionMerkleCoinOracleEquivAt_coins shape input.1
    causalSecret baseMessage publicPositions weights context left right
    trace.answers trace.tail.rest houter hlinear hhadamard input
  have htraceFiat : isFiatShamirPoint trace.equalityPoint.2.2 :=
    sampleEqualityPointPrefix_some_isFiatShamir
      (answerBounded fallback input.2) (m shape - kSkip - 7)
      veilSamplingTrials realPrelude hpreludeFiat trace.equalityPoint
      facts.equalityPoint
  have hpointsFiat : ∀ site, isFiatShamirPoint
      (unboundBytes (points site)) := by
    intro site
    simpa only [points, productionSimulatorProgramPoints,
      unbound_boundBytes] using
      (simulatedZerocheck_tracePoint_isFiatShamir shape causalSecret
        trace.equalityPoint.2.2 right moved.1 trace.answers htraceFiat site)
  let simCoins := withSimulatedAnswers shape moved.1 trace.answers
  have houterProgram : outerRoot shape baseMessage right simCoins
      (answerBounded fallback
        (OracleProgramming.program points hinjective moved.2
          moved.1.simulatedAnswers)) =
      outerRoot shape baseMessage right simCoins
        (answerBounded fallback moved.2) := by
    exact productionMerkleRoot_program_fiat fallback points hinjective
      hpointsFiat moved.2 moved.1.simulatedAnswers ⟨0, by decide⟩
      ⟨0, by decide⟩ simCoins.treeNonces.outer
      (BitVec.ofNat 64 (16 * (2 * outerLaneCount))) (m shape - 11)
      simCoins.outerSalts (outerRowPayload shape baseMessage right simCoins)
  have hlinearProgram : linearRoot shape simCoins
      (answerBounded fallback
        (OracleProgramming.program points hinjective moved.2
          moved.1.simulatedAnswers)) =
      linearRoot shape simCoins (answerBounded fallback moved.2) := by
    exact productionMerkleRoot_program_fiat fallback points hinjective
      hpointsFiat moved.2 moved.1.simulatedAnswers ⟨6, by decide⟩
      ⟨0, by decide⟩ simCoins.treeNonces.veilLinear
      (BitVec.ofNat 64 32) 13 simCoins.linearSalts
      (linearRowPayload shape simCoins)
  have houterSim : outerRoot shape baseMessage right simCoins
      (answerBounded fallback moved.2) = trace.outerCommitment := by
    have hsame : outerRoot shape baseMessage right simCoins
        (answerBounded fallback moved.2) =
        outerRoot shape baseMessage right moved.1
          (answerBounded fallback moved.2) := by rfl
    rw [hsame]
    exact houterRoot'
  have hlinearSim : linearRoot shape simCoins
      (answerBounded fallback moved.2) = trace.linearCommitment := by
    have hsame : linearRoot shape simCoins
        (answerBounded fallback moved.2) =
        linearRoot shape moved.1 (answerBounded fallback moved.2) := by rfl
    rw [hsame]
    exact hlinearRoot'
  have hmovedProofNonce : moved.1.proofNonce = input.1.proofNonce := by
    rw [hmovedCoins]
    rfl
  have hmovedTreeNonces : moved.1.treeNonces = input.1.treeNonces := by
    rw [hmovedCoins]
    rfl
  rw [hcoupledCoins, hcoupledTable]
  change sampleEqualityPointPrefix
      (answerBounded fallback
        (OracleProgramming.program points hinjective moved.2
          moved.1.simulatedAnswers))
      (m shape - kSkip - 7) veilSamplingTrials _ = _
  rw [houterProgram, hlinearProgram, houterSim, hlinearSim]
  simp only [withSimulatedAnswers_proofNonce,
    withSimulatedAnswers_treeNonces]
  rw [hmovedProofNonce, hmovedTreeNonces]
  exact sampleEqualityPointPrefix_eq_of_agrees_below_success
    (answerBounded fallback moved.2) (answerBounded fallback coupled.2)
    (m shape - kSkip - 7) veilSamplingTrials realPrelude trace.equalityPoint
    (by cases shape <;> decide) hmovedSample hprogramOff

end VeiledFlock.ProductionNizkCoupling

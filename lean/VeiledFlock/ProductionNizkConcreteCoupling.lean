import VeiledFlock.ProductionNizkCompleteViewCoupling
import VeiledFlock.ProductionPublicRepresentative

/-!
# Complete-view coupling with the concrete public representative

This specialization removes the representative and its projection equality
from the external API of the complete production coupling.  The only
relation-side premise is that the packed witness has the public digest
projection carried by `ProductionStatement`.
-/

namespace VeiledFlock.ProductionNizkConcreteCoupling

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPublicRepresentative

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem production_real_sim_equal_on_good_concrete
    {AdversaryCoins FinalState : Type} {preQueries postQueries : ℕ}
    (shape : BatchShape) (maxStartLength : ℕ)
    (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret
      (W := Witness shape) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord shape → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape (Witness shape)
        (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape
          (publicPositions shape) (baseMessage shape)))
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape (ProductionRest shape)
        (ProductionMaxPointLength shape maxStartLength)
        preQueries postQueries)
    (statement : ProductionStatement shape) (witness : Witness shape)
    (hvalid : PublicProjectionValid shape statement witness)
    (adversaryCoins : AdversaryCoins) (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤ ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤ ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (input : ProductionCouplingInput shape maxStartLength)
    (hgood : ProductionGood shape maxStartLength fallback r1csDigest
      causalSecret completion (baseMessage shape) (publicPositions shape)
      weights context (publicRepresentative shape) adversary statement witness
      adversaryCoins trace houter hlinear hhadamard input) :
    let coupled := productionCoupledInputOnGood shape maxStartLength fallback
      r1csDigest causalSecret completion (baseMessage shape)
      (publicPositions shape) weights context (publicRepresentative shape)
      adversary statement witness adversaryCoins trace houter hlinear
      hhadamard input hgood
    (productionRealView shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context adversary
      statement witness input.1 adversaryCoins
      (initialSharedOracleState input.2)).1 =
    (productionSimulatedView shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context
      (publicRepresentative shape) adversary statement coupled.1
      adversaryCoins (initialSharedOracleState coupled.2)).1 := by
  exact production_real_sim_equal_on_good shape maxStartLength fallback
    r1csDigest causalSecret completion (baseMessage shape)
    (publicPositions shape) weights context (publicRepresentative shape)
    adversary statement witness
    (witness_projection_eq_publicRepresentative shape statement witness hvalid)
    adversaryCoins trace houter hlinear hhadamard hnodes input hgood

end VeiledFlock.ProductionNizkConcreteCoupling

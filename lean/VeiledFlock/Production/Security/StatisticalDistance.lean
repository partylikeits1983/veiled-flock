import VeiledFlock.Algebra.EndToEnd
import VeiledFlock.Production.Security.OperationalGlobalProbability
import VeiledFlock.Production.Security.SuccessfulCoupling

/-! # Statistical distance of the complete production views

This file connects the concrete successful coupling permutation to the single
operational bad-event ledger.  Both experiments are functions of the exact
operational tape: production coins, one shared random-oracle table, and the
adaptive adversary's private coins.
-/

namespace VeiledFlock.ProductionStatisticalDistance

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.EndToEnd
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkConcreteCoupling
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalGlobalProbability
open VeiledFlock.ProductionOperationalGood
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingOperationalProbability
open VeiledFlock.ProductionSuccessfulCoupling

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
variable (adversary : ProductionAdversary
  (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
  shape (ProductionRest shape)
    (ProductionMaxPointLength shape maxStartLength)
    preQueries postQueries)
variable (statement : ProductionStatement shape) (witness : Witness shape)

abbrev CompleteView := ProductionView
  (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
  shape (ProductionRest shape)
    (ProductionMaxPointLength shape maxStartLength)

/-- The complete real experiment as a deterministic function of its uniform
operational tape. -/
noncomputable def productionRealExperiment
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    CompleteView (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape maxStartLength :=
  (productionRealView shape fallback r1csDigest causalSecret completion
    (baseMessage shape) (publicPositions shape) weights context adversary
    statement witness tape.1 tape.2.2
    (initialSharedOracleState tape.2.1)).1

/-- The complete witness-free simulated experiment on the same operational
sample space. -/
noncomputable def productionSimulatedExperiment
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    CompleteView (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape maxStartLength :=
  (productionSimulatedView shape fallback r1csDigest causalSecret completion
    (baseMessage shape) (publicPositions shape) weights context
    (publicRepresentative shape) adversary statement tape.1 tape.2.2
    (initialSharedOracleState tape.2.1)).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem real_eq_simulated_after_coinEquiv_of_globalGood
    (hvalid : PublicProjectionValid shape statement witness)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (hmax : productionStartLengthBound shape statement r1csDigest ≤
      maxStartLength)
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins)
    (hgood : GlobalGood shape maxStartLength fallback r1csDigest causalSecret
      completion weights context adversary statement witness houter hlinear
      hhadamard tape) :
    productionRealExperiment shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness tape =
      productionSimulatedExperiment shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement
        (productionCoinEquiv (AdversaryCoins := AdversaryCoins) shape
          maxStartLength fallback r1csDigest causalSecret completion weights
          context statement witness hvalid houter hlinear hhadamard hnodes hmax
          tape) := by
  classical
  rcases globalGood_implies_productionGood shape maxStartLength fallback
    r1csDigest causalSecret completion weights context adversary statement
    witness houter hlinear hhadamard tape hgood with
    ⟨trace, htrace, hproductionGood⟩
  have hsuccess : SuccessfulTape shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness tape := ⟨trace, htrace⟩
  let successfulTape : {tape : ProductionLedgerTape shape maxStartLength
      AdversaryCoins // SuccessfulTape shape maxStartLength fallback r1csDigest
        causalSecret completion statement witness tape} := ⟨tape, hsuccess⟩
  let selectedTrace := successfulTrace shape maxStartLength fallback r1csDigest
    causalSecret completion statement witness successfulTape
  have hselected : selectedTrace = trace := by
    apply Option.some.inj
    exact (successfulTrace_spec shape maxStartLength fallback r1csDigest
      causalSecret completion statement witness successfulTape).symm.trans htrace
  subst trace
  let coupled := productionCoupledInputOnGood shape maxStartLength fallback
    r1csDigest causalSecret completion (baseMessage shape)
    (publicPositions shape) weights context (publicRepresentative shape)
    adversary statement witness tape.2.2 selectedTrace houter hlinear hhadamard
    (couplingInput shape maxStartLength tape) hproductionGood
  have hcoupledView := production_real_sim_equal_on_good_concrete shape
    maxStartLength fallback r1csDigest causalSecret completion weights context
    adversary statement witness hvalid tape.2.2 selectedTrace houter hlinear hhadamard
    hnodes (couplingInput shape maxStartLength tape) hproductionGood
  have hsuccessfulInput :
      successfulCouplingInput (AdversaryCoins := AdversaryCoins) shape
          maxStartLength fallback r1csDigest causalSecret completion weights
          context statement witness houter hlinear hhadamard hmax successfulTape =
        coupled := by
    unfold successfulCouplingInput coupled productionCoupledInputOnGood
    rfl
  rw [productionCoinEquiv_apply_success (AdversaryCoins := AdversaryCoins)
    shape maxStartLength fallback r1csDigest causalSecret completion weights
    context statement witness hvalid houter hlinear hhadamard hnodes hmax tape
    hsuccess]
  change
    (productionRealView shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context adversary
      statement witness tape.1 tape.2.2
      (initialSharedOracleState tape.2.1)).1 = _
  change
    (productionRealView shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context adversary
      statement witness (couplingInput shape maxStartLength tape).1 tape.2.2
      (initialSharedOracleState
        (couplingInput shape maxStartLength tape).2)).1 = _
  change
    (productionRealView shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context adversary
      statement witness (couplingInput shape maxStartLength tape).1 tape.2.2
      (initialSharedOracleState
        (couplingInput shape maxStartLength tape).2)).1 =
    (productionSimulatedView shape fallback r1csDigest causalSecret completion
      (baseMessage shape) (publicPositions shape) weights context
      (publicRepresentative shape) adversary statement
      (successfulCouplingInput (AdversaryCoins := AdversaryCoins) shape
        maxStartLength fallback r1csDigest causalSecret completion weights
        context statement witness houter hlinear hhadamard hmax
        successfulTape).1 tape.2.2
      (initialSharedOracleState
        (successfulCouplingInput (AdversaryCoins := AdversaryCoins) shape
          maxStartLength fallback r1csDigest causalSecret completion weights
          context statement witness houter hlinear hhadamard hmax
          successfulTape).2)).1
  rw [hsuccessfulInput]
  exact hcoupledView

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
/-- Unconditional complete-view statistical distance, with every failure
charged to the explicit operational ledger.  No good-event, coupling, or
probability premise appears in the statement. -/
theorem veil_flock_statistical_distance_le_operationalFailureBound
    [Nonempty AdversaryCoins]
    (hvalid : PublicProjectionValid shape statement witness)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤
      ProductionMaxPointLength shape maxStartLength)
    (hlinear : 108 + 32 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hhadamard : 108 + 64 ≤
      ProductionMaxPointLength shape maxStartLength)
    (hnodes : 140 ≤ ProductionMaxPointLength shape maxStartLength)
    (hmax : productionStartLengthBound shape statement r1csDigest ≤
      maxStartLength)
    (hbudget : OperationalSamplingBudget shape maxStartLength r1csDigest
      statement) :
    finiteSupportTV
        (productionRealExperiment shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement witness)
        (productionSimulatedExperiment shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement) ≤
      operationalFailureBound shape preQueries postQueries := by
  classical
  let real := productionRealExperiment shape maxStartLength fallback r1csDigest
    causalSecret completion weights context adversary statement witness
  let simulated := productionSimulatedExperiment shape maxStartLength fallback
    r1csDigest causalSecret completion weights context adversary statement
  let equiv := productionCoinEquiv (AdversaryCoins := AdversaryCoins) shape
    maxStartLength fallback r1csDigest causalSecret completion weights context
    statement witness hvalid houter hlinear hhadamard hnodes hmax
  let bad := operationalGlobalBadTapeSet shape maxStartLength fallback
    r1csDigest causalSecret completion weights context adversary statement
    witness
  have hsame : ∀ tape, tape ∉ bad → real tape = (simulated ∘ equiv) tape := by
    intro tape hnotBad
    have hglobal : GlobalGood shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement witness
        houter hlinear hhadamard tape := by
      by_contra hnotGood
      exact hnotBad
        (not_globalGood_implies_mem_operationalGlobalBadTapeSet shape
          maxStartLength fallback r1csDigest causalSecret completion weights
          context adversary statement witness houter hlinear hhadamard hmax tape
          hnotGood)
    exact real_eq_simulated_after_coinEquiv_of_globalGood
      (AdversaryCoins := AdversaryCoins) shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
      witness hvalid houter hlinear hhadamard hnodes hmax tape hglobal
  have hcoupling : finiteSupportTV real (simulated ∘ equiv) ≤
      (bad.card : ℚ) /
        Fintype.card
          (ProductionLedgerTape shape maxStartLength AdversaryCoins) :=
    finiteSupportTV_le_badProbability real (simulated ∘ equiv) bad hsame
  have hreparameterize :
      finiteSupportTV real (simulated ∘ equiv) =
        finiteSupportTV real simulated :=
    finiteSupportTV_reparameterize_right equiv real simulated
  rw [hreparameterize] at hcoupling
  exact hcoupling.trans (by
    simpa only [bad] using
      operationalGlobalBad_probability_le shape maxStartLength fallback
        r1csDigest causalSecret completion weights context adversary statement
        witness houter hlinear hhadamard hbudget hnodes)

end

end VeiledFlock.ProductionStatisticalDistance

import VeiledFlock.Production.Security.ConcreteFailureBound

/-!
# Formal statistical zero knowledge of the production protocol

This file contains the final security-definition layer for the formal
VEIL--FLOCK protocol in the classical programmable-random-oracle model.  It
does not model QROM access and it does not make an information-theoretic claim
about an instantiated hash function.
-/

namespace VeiledFlock.ProductionFormalZK

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
open VeiledFlock.ProductionConcreteFailureBound
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOperationalGood
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionPublicRepresentative
open VeiledFlock.ProductionSamplingOperationalProbability
open VeiledFlock.ProductionStatisticalDistance

section Distance

variable {AdversaryCoins FinalState : Type} [Fintype AdversaryCoins]
  [Nonempty AdversaryCoins]
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

/-- The unconditional statistical-distance theorem for the complete
production adversary view.  Its premises are only witness validity, concrete
serialization/schedule bounds, and the reviewed adaptive-query envelope.
There is no good-event, coupling, equality, or probability premise. -/
theorem veil_flock_statistical_distance_lt_two_pow_neg_126
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
      statement)
    (hqueries : preQueries + postQueries ≤ 2 ^ 64) :
    finiteSupportTV
        (productionRealExperiment shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement witness)
        (productionSimulatedExperiment shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement) <
      1 / (2 : ℚ) ^ 126 := by
  exact (veil_flock_statistical_distance_le_operationalFailureBound
    shape maxStartLength fallback r1csDigest causalSecret completion weights
    context adversary statement witness hvalid houter hlinear hhadamard hnodes
    hmax hbudget).trans_lt
      (operationalFailureBound_lt_two_pow_neg_126 shape preQueries postQueries
        hqueries)

end Distance

/-! ## Explicit simulator cost semantics

The formal protocol uses mathematical finite-field values, so Lean code
generation is not the security model.  Instead we give the simulator an
explicit algebraic/pROM machine cost.  One unit is one primitive byte/field
operation, one random-oracle action, or one black-box adversary step.  Every
bounded loop in the concrete simulator is charged at its public maximum.
This is the usual oracle-machine interpretation: an admissible adversary's
own internal running time is separate, while each invocation is charged here.
-/

/-- Every causally distinct stage executed by `productionSimulatedView`. -/
inductive ProductionSimulatorStage where
  | adversaryPreQueries
  | publicRepresentative
  | outerMerkle
  | linearMerkle
  | equalityAndFiatShamir
  | programmableOracle
  | flockVeilAlgebra
  | rejectionAndGrinding
  | hadamardMerkle
  | serialization
  | adversaryPostQueries
  deriving DecidableEq, Fintype

/-- A conservative size-independent coefficient for each concrete stage.
The three Merkle coefficients count all leaves and internal nodes; the
sampling coefficients use the complete fixed production slot allocation.
The algebra coefficient charges a dense polynomial amount of field work for
the fixed registered shape. -/
def productionSimulatorStageWeight (shape : BatchShape) :
    ProductionSimulatorStage → ℕ
  | .adversaryPreQueries => 1
  | .publicRepresentative => 2 * instanceCount shape + 1
  | .outerMerkle => 2 ^ ((m shape - 11) + 1)
  | .linearMerkle => 2 ^ (13 + 1)
  | .equalityAndFiatShamir =>
      VeiledFlock.ProductionSamplingLayout.productionSamplingSlots + 1
  | .programmableOracle => programmedPoints shape + 1
  | .flockVeilAlgebra => 2 ^ (2 * m shape + 16)
  | .rejectionAndGrinding =>
      VeiledFlock.ProductionSamplingLayout.productionSamplingSlots + 1
  | .hadamardMerkle => 2 ^ (11 + 1)
  | .serialization => 1
  | .adversaryPostQueries => 1

/-- The complete charged stage trace.  Multiplication by `(n+1)^2` covers
linear scans, transcript copying, and field/byte work at public size `n`. -/
def productionSimulatorCostTrace (shape : BatchShape) (n : ℕ) :
    List (ProductionSimulatorStage × ℕ) :=
  [.adversaryPreQueries, .publicRepresentative, .outerMerkle, .linearMerkle,
    .equalityAndFiatShamir, .programmableOracle, .flockVeilAlgebra,
    .rejectionAndGrinding, .hadamardMerkle, .serialization,
    .adversaryPostQueries].map fun stage ↦
      (stage, productionSimulatorStageWeight shape stage * (n + 1) ^ 2)

/-- Worst-case cost of the exact concrete simulator in the declared
algebraic/pROM machine model. -/
def productionSimulatorCost (shape : BatchShape) (n : ℕ) : ℕ :=
  (productionSimulatorCostTrace shape n).map Prod.snd |>.sum

def productionSimulatorCostCoefficient (shape : BatchShape) : ℕ :=
  [.adversaryPreQueries, .publicRepresentative, .outerMerkle, .linearMerkle,
    .equalityAndFiatShamir, .programmableOracle, .flockVeilAlgebra,
    .rejectionAndGrinding, .hadamardMerkle, .serialization,
    .adversaryPostQueries].map
      (productionSimulatorStageWeight shape) |>.sum

theorem productionSimulatorCost_eq (shape : BatchShape) (n : ℕ) :
    productionSimulatorCost shape n =
      productionSimulatorCostCoefficient shape * (n + 1) ^ 2 := by
  simp [productionSimulatorCost, productionSimulatorCostTrace,
    productionSimulatorCostCoefficient]
  ring

/-- Standard explicit polynomial-growth predicate. -/
def PolynomiallyBounded (cost : ℕ → ℕ) : Prop :=
  ∃ coefficient degree : ℕ, ∀ n,
    cost n ≤ coefficient * (n + 1) ^ degree

theorem productionSimulatorCost_polynomiallyBounded (shape : BatchShape) :
    PolynomiallyBounded (productionSimulatorCost shape) := by
  refine ⟨productionSimulatorCostCoefficient shape, 2, ?_⟩
  intro n
  rw [productionSimulatorCost_eq]

/-- A semantic algorithm paired with a pathwise cost.  `run` below is the
actual witness-free `productionSimulatedExperiment`, not an abstract
simulator parameter. -/
structure CostedAlgorithm (Input Output : Type) where
  run : Input → Output
  cost : Input → ℕ

/-- Exact expectation over the uniform finite operational tape. -/
noncomputable def uniformExpectedCost {Input Output : Type}
    [Fintype Input] (algorithm : CostedAlgorithm Input Output) : ℚ :=
  (∑ input : Input, (algorithm.cost input : ℚ)) / Fintype.card Input

/-- Accounting certificate for the complete simulator in the declared
algebraic/pROM cost model.

The `run` field is tied to the simulator and the adaptive query history is
bounded on the actual output. The machine-cost half records the stage-cost
function supplied by the model; Lean does not derive that cost by evaluating the
body of `run`. -/
structure SimulatorEfficiencyCertificate {Input Output : Type}
    [Fintype Input] (algorithm : CostedAlgorithm Input Output)
    (simulator : Input → Output)
    (publicSize queryBound : ℕ) (costFamily : ℕ → ℕ)
    (queryCount : Output → ℕ) : Prop where
  implementsSimulator : ∀ input, algorithm.run input = simulator input
  pathwiseCost : ∀ input, algorithm.cost input ≤ costFamily publicSize
  expectedCost : uniformExpectedCost algorithm ≤ costFamily publicSize
  pathwiseQueries : ∀ input, queryCount (algorithm.run input) ≤ queryBound
  polynomialCost : PolynomiallyBounded costFamily

section Efficiency

set_option maxHeartbeats 2000000

variable {AdversaryCoins FinalState : Type} [Fintype AdversaryCoins]
  [Nonempty AdversaryCoins]
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
variable (statement : ProductionStatement shape)

abbrev SimulatorInput :=
  ProductionLedgerTape shape maxStartLength AdversaryCoins

abbrev SimulatorOutput := ProductionView
  (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
  shape (ProductionRest shape)
    (ProductionMaxPointLength shape maxStartLength)

/-- The exact witness-free production simulator equipped with the stage cost
declared by the production pROM accounting model. The type of `run` has no
witness argument. -/
noncomputable def costedProductionSimulator :
    CostedAlgorithm
      (SimulatorInput (AdversaryCoins := AdversaryCoins) shape maxStartLength)
      (SimulatorOutput (AdversaryCoins := AdversaryCoins)
        (FinalState := FinalState) shape maxStartLength) where
  run := productionSimulatedExperiment shape maxStartLength fallback r1csDigest
    causalSecret completion weights context adversary statement
  cost := fun _ ↦ productionSimulatorCost shape
    (ProductionMaxPointLength shape maxStartLength + preQueries + postQueries)

omit [Fintype AdversaryCoins] [Nonempty AdversaryCoins] in
@[simp] theorem costedProductionSimulator_run
    (tape : SimulatorInput (AdversaryCoins := AdversaryCoins)
      shape maxStartLength) :
    (costedProductionSimulator shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement).run tape =
      productionSimulatedExperiment shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement tape := rfl

/-- The declared deterministic worst-case stage cost immediately bounds expected
cost over the same uniform operational tape used by the ZK theorem. -/
theorem costedProductionSimulator_expectedCost_le :
    uniformExpectedCost
        (costedProductionSimulator shape maxStartLength fallback r1csDigest
          causalSecret completion weights context adversary statement) ≤
      productionSimulatorCost shape
        (ProductionMaxPointLength shape maxStartLength + preQueries +
          postQueries) := by
  classical
  simp [uniformExpectedCost, costedProductionSimulator]

/-- Complete simulator accounting theorem in the explicit algebraic/pROM cost
model. Bounded rejection and first-success grinding are charged at their full
public caps in `productionSimulatorCost`; this is a polynomial bound for the
declared model cost, not a Lean evaluator-derived step count for `run`. -/
theorem productionSimulator_expected_polytime :
    SimulatorEfficiencyCertificate
      (costedProductionSimulator shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement)
      (productionSimulatedExperiment shape maxStartLength fallback r1csDigest
        causalSecret completion weights context adversary statement)
      (ProductionMaxPointLength shape maxStartLength + preQueries + postQueries)
      (preQueries + postQueries)
      (productionSimulatorCost shape)
      (fun view ↦ view.oracleView.queries.length) := by
  refine {
    implementsSimulator := ?_
    pathwiseCost := ?_
    expectedCost := costedProductionSimulator_expectedCost_le
      shape maxStartLength fallback r1csDigest causalSecret completion weights
      context adversary statement
    pathwiseQueries := ?_
    polynomialCost := productionSimulatorCost_polynomiallyBounded shape }
  · intro tape
    exact costedProductionSimulator_run shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement tape
  · intro tape
    exact le_rfl
  · intro tape
    exact productionSimulatedView_query_length_le shape fallback r1csDigest
      causalSecret completion (baseMessage shape) (publicPositions shape)
      weights context (publicRepresentative shape) adversary statement tape.1
      tape.2.2 (initialSharedOracleState tape.2.1)

end Efficiency

/-! ## The security predicate and concrete production theorem -/

/-- Statistical zero knowledge for uniform finite-tape experiments. The
simulator's type is structurally witness-free. The predicate quantifies over
every statement, valid witness, and admissible adversary and also carries the
declared simulator accounting certificate for that same simulator/adversary
pair.

The production instantiation below supplies complete adaptive classical-pROM
views; this definition neither models quantum oracle access nor an
instantiated deterministic hash function. -/
def StatisticalZeroKnowledge
    {Statement Witness Adversary Tape View : Type}
    [Fintype Tape] [Nonempty Tape] [DecidableEq View]
    (relation : Statement → Witness → Prop)
    (realExperiment : Statement → Witness → Adversary → Tape → View)
    (simulator : Statement → Adversary → Tape → View)
    (admissible : Statement → Adversary → Prop)
    (simulatorEfficient : Statement → Adversary → Prop)
    (epsilon : ℚ) : Prop :=
  (∀ statement adversary,
      admissible statement adversary →
        simulatorEfficient statement adversary) ∧
  ∀ statement witness adversary,
    relation statement witness →
    admissible statement adversary →
    finiteSupportTV
        (realExperiment statement witness adversary)
        (simulator statement adversary) < epsilon

/-- The formal production relation includes statement shape validity and the
exact public projection of the committed packed witness. -/
def veilFlockRelation (shape : BatchShape)
    (statement : ProductionStatement shape) (witness : Witness shape) : Prop :=
  StatementWellFormed shape statement ∧
    PublicProjectionValid shape statement witness

/-- All legitimate public conditions under which the reviewed production
bound applies.  No good event, probability bound, simulator correctness,
coupling, or real/simulator equality appears here. -/
structure ReviewedProductionEnvelope (shape : BatchShape)
    (maxStartLength preQueries postQueries : ℕ)
    (r1csDigest : List Byte) (statement : ProductionStatement shape) : Prop where
  outerEncodingFits : 108 + 16 * (2 * outerLaneCount) ≤
    ProductionMaxPointLength shape maxStartLength
  linearEncodingFits : 108 + 32 ≤
    ProductionMaxPointLength shape maxStartLength
  hadamardEncodingFits : 108 + 64 ≤
    ProductionMaxPointLength shape maxStartLength
  merkleNodeEncodingFits : 140 ≤
    ProductionMaxPointLength shape maxStartLength
  startTranscriptFits :
    productionStartLengthBound shape statement r1csDigest ≤ maxStartLength
  samplingScheduleFits :
    OperationalSamplingBudget shape maxStartLength r1csDigest statement
  adaptiveQueryEnvelope : preQueries + postQueries ≤ 2 ^ 64

section FinalTheorem

set_option maxHeartbeats 3000000

variable {AdversaryCoins FinalState : Type} [Fintype AdversaryCoins]
  [Nonempty AdversaryCoins]
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

abbrev FormalProductionAdversary := ProductionAdversary
  (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
  shape (ProductionRest shape)
    (ProductionMaxPointLength shape maxStartLength)
    preQueries postQueries

/-- Concrete real-experiment family used by the final predicate. -/
noncomputable def productionRealExperimentFamily
    (statement : ProductionStatement shape) (witness : Witness shape)
    (adversary : FormalProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      (preQueries := preQueries) (postQueries := postQueries)
      shape maxStartLength) :
    ProductionLedgerTape shape maxStartLength AdversaryCoins →
      ProductionView (AdversaryCoins := AdversaryCoins)
        (FinalState := FinalState) shape (ProductionRest shape)
          (ProductionMaxPointLength shape maxStartLength) :=
  productionRealExperiment shape maxStartLength fallback r1csDigest causalSecret
    completion weights context adversary statement witness

/-- Concrete simulator family used by the final predicate.  Its signature
contains a statement and adversary but no witness. -/
noncomputable def productionSimulatorFamily
    (statement : ProductionStatement shape)
    (adversary : FormalProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      (preQueries := preQueries) (postQueries := postQueries)
      shape maxStartLength) :
    ProductionLedgerTape shape maxStartLength AdversaryCoins →
      ProductionView (AdversaryCoins := AdversaryCoins)
        (FinalState := FinalState) shape (ProductionRest shape)
          (ProductionMaxPointLength shape maxStartLength) :=
  productionSimulatedExperiment shape maxStartLength fallback r1csDigest
    causalSecret completion weights context adversary statement

/-- Declared simulator accounting property supplied to the ZK definition. -/
def productionSimulatorEfficient
    (statement : ProductionStatement shape)
    (adversary : FormalProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      (preQueries := preQueries) (postQueries := postQueries)
      shape maxStartLength) : Prop :=
  SimulatorEfficiencyCertificate
    (costedProductionSimulator shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement)
    (productionSimulatedExperiment shape maxStartLength fallback r1csDigest
      causalSecret completion weights context adversary statement)
    (ProductionMaxPointLength shape maxStartLength + preQueries + postQueries)
    (preQueries + postQueries)
    (productionSimulatorCost shape)
    (fun view ↦ view.oracleView.queries.length)

/-- Final formal-protocol statistical-ZK theorem. It proves the actual
`StatisticalZeroKnowledge` predicate for the complete adaptive adversary view,
the concrete witness-free simulator, the declared simulator accounting model,
and the reviewed `2^-126` classical programmable-random-oracle envelope. -/
theorem veil_flock_statistical_zk_126 :
    StatisticalZeroKnowledge
      (Tape := ProductionLedgerTape shape maxStartLength AdversaryCoins)
      (View := ProductionView (AdversaryCoins := AdversaryCoins)
        (FinalState := FinalState) shape (ProductionRest shape)
          (ProductionMaxPointLength shape maxStartLength))
      (veilFlockRelation shape)
      (productionRealExperimentFamily shape maxStartLength fallback r1csDigest
        causalSecret completion weights context (preQueries := preQueries)
        (postQueries := postQueries))
      (productionSimulatorFamily shape maxStartLength fallback r1csDigest
        causalSecret completion weights context (preQueries := preQueries)
        (postQueries := postQueries))
      (fun statement _ ↦ ReviewedProductionEnvelope shape maxStartLength
        preQueries postQueries r1csDigest statement)
      (productionSimulatorEfficient shape maxStartLength fallback r1csDigest
        causalSecret completion weights context (preQueries := preQueries)
        (postQueries := postQueries))
      (1 / (2 : ℚ) ^ 126) := by
  constructor
  · intro statement adversary _henvelope
    exact productionSimulator_expected_polytime shape maxStartLength fallback
      r1csDigest causalSecret completion weights context adversary statement
  · intro statement witness adversary hrelation henvelope
    exact veil_flock_statistical_distance_lt_two_pow_neg_126 shape
      maxStartLength fallback r1csDigest causalSecret completion weights context
      adversary statement witness hrelation.2 henvelope.outerEncodingFits
      henvelope.linearEncodingFits henvelope.hadamardEncodingFits
      henvelope.merkleNodeEncodingFits henvelope.startTranscriptFits
      henvelope.samplingScheduleFits henvelope.adaptiveQueryEnvelope

end FinalTheorem

end VeiledFlock.ProductionFormalZK

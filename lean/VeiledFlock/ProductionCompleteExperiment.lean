import VeiledFlock.OptionalPairedInterleaved

/-!
# Complete real and simulated VEIL--FLOCK experiments

This module fixes the top-level shape of the ZK comparison.  Both executions
use one shared adaptive random-oracle table.  Bounded early-stopping sites use
an independent dummy tape only after the corresponding production query has
become inactive; dummy answers are not part of the adversary view.

The `OracleView` rendered by an instantiation must contain the adversary's
query/answer transcript (including pre-, inter-stage, and post-proof queries).
Consequently equality of `VeilFlockAdversaryView` is equality of the complete
joint view, not merely equality of serialized proof bytes.
-/

namespace VeiledFlock.ProductionCompleteExperiment

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.OptionalAdaptiveOracle
open VeiledFlock.OptionalPairedInterleaved

variable {Statement Witness RelationCoins AdversaryCoins State Prior Point
  Outcome Transcript ProofBytes OracleView : Type*}
variable [Fintype RelationCoins] [DecidableEq RelationCoins]
variable [Nonempty RelationCoins]
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- The exact object whose distributions are compared. `proofBytes` is the
canonical public proof serialization, while `oracleView` includes every
oracle interaction visible to the adversary and its final state. -/
structure VeilFlockAdversaryView where
  statement : Statement
  adversaryRandomness : AdversaryCoins
  transcript : Transcript
  proofBytes : ProofBytes
  oracleView : OracleView

/-- Visible fields rendered from the common post-transport protocol state. -/
structure RenderedView where
  adversaryRandomness : AdversaryCoins
  transcript : Transcript
  proofBytes : ProofBytes
  oracleView : OracleView

abbrev ExperimentCoins (sites : ℕ) :=
  OptionalPairedInterleaved.Coins RelationCoins Point Outcome sites

/-- The one joint algebraic/oracle reparameterization used by the final
coupling.  In particular this is not a tuple of independent per-component
simulator maps. -/
noncomputable def experimentCoinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites →
      RelationCoins ≃ RelationCoins)
    (realFixed simulatedFixed : RelationCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (realSchedule simulatedSchedule : RelationCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (hreal : ∀ coins answers,
      Injective (protectedTracePoints (realFixed coins)
        (realSchedule coins) answers))
    (hsimulated : ∀ coins answers,
      Injective (protectedTracePoints (simulatedFixed coins)
        (simulatedSchedule coins) answers)) :
    ExperimentCoins (RelationCoins := RelationCoins)
      (Point := Point) (Outcome := Outcome) sites ≃
    ExperimentCoins (RelationCoins := RelationCoins)
      (Point := Point) (Outcome := Outcome) sites :=
  OptionalPairedInterleaved.coinEquiv answerEquiv realFixed simulatedFixed
    realSchedule simulatedSchedule hreal hsimulated

/-- Complete production-side experiment. The state builder receives the
witness, but its oracle access is exclusively the one shared table inside
`ExperimentCoins`. -/
noncomputable def veilFlockRealExperiment {sites : ℕ}
    (statement : Statement) (witness : Witness)
    (realState : Statement → Witness → RelationCoins →
      History (Outcome := Outcome) sites → State)
    (fixedPoints : RelationCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (schedule : RelationCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (render : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites →
        RenderedView (AdversaryCoins := AdversaryCoins)
          (Transcript := Transcript) (ProofBytes := ProofBytes)
          (OracleView := OracleView)) :
    ExperimentCoins (RelationCoins := RelationCoins)
      (Point := Point) (Outcome := Outcome) sites →
      VeilFlockAdversaryView (Statement := Statement)
        (AdversaryCoins := AdversaryCoins) (Transcript := Transcript)
        (ProofBytes := ProofBytes) (OracleView := OracleView) :=
  OptionalPairedInterleaved.machine (realState statement witness) fixedPoints
    schedule
    (fun state protectedAnswers answers =>
      let visible := render state protectedAnswers answers
      { statement := statement
        adversaryRandomness := visible.adversaryRandomness
        transcript := visible.transcript
        proofBytes := visible.proofBytes
        oracleView := visible.oracleView })

/-- One complete public simulator. Its API contains no witness argument. It
uses the same shared adaptive programmable oracle as the real experiment. -/
noncomputable def veilFlockSimulator {sites : ℕ}
    (statement : Statement)
    (simulatedState : Statement → RelationCoins →
      History (Outcome := Outcome) sites → State)
    (fixedPoints : RelationCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (schedule : RelationCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (render : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites →
        RenderedView (AdversaryCoins := AdversaryCoins)
          (Transcript := Transcript) (ProofBytes := ProofBytes)
          (OracleView := OracleView)) :
    ExperimentCoins (RelationCoins := RelationCoins)
      (Point := Point) (Outcome := Outcome) sites →
      VeilFlockAdversaryView (Statement := Statement)
        (AdversaryCoins := AdversaryCoins) (Transcript := Transcript)
        (ProofBytes := ProofBytes) (OracleView := OracleView) :=
  OptionalPairedInterleaved.machine (simulatedState statement) fixedPoints
    schedule
    (fun state protectedAnswers answers =>
      let visible := render state protectedAnswers answers
      { statement := statement
        adversaryRandomness := visible.adversaryRandomness
        transcript := visible.transcript
        proofBytes := visible.proofBytes
        oracleView := visible.oracleView })

/-- Witness independence is structural: varying a witness cannot change the
simulator invocation because no witness is present in its type or arguments. -/
theorem simulator_witness_independent {sites : ℕ}
    (statement : Statement)
    (simulatedState : Statement → RelationCoins →
      History (Outcome := Outcome) sites → State)
    (fixedPoints : RelationCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (schedule : RelationCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (render : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites →
        RenderedView (AdversaryCoins := AdversaryCoins)
          (Transcript := Transcript) (ProofBytes := ProofBytes)
          (OracleView := OracleView))
    (input : ExperimentCoins (RelationCoins := RelationCoins)
      (Point := Point) (Outcome := Outcome) sites)
    (left right : Witness) :
    (fun _ : Witness => veilFlockSimulator statement simulatedState
      fixedPoints schedule render input) left =
    (fun _ : Witness => veilFlockSimulator statement simulatedState
      fixedPoints schedule render input) right := rfl

/-- Pointwise equality of the complete joint views under the single concrete
coin transport.  A final production instantiation obtains the injectivity
premises from freshness (`Good`); `render` ensures that this equality includes
proof bytes and the complete adaptive oracle interaction, not just individual
protocol components. -/
theorem real_sim_equal_on_good {sites : ℕ}
    (relation : Statement → Witness → Prop)
    (statement : Statement) (witness : Witness)
    (hrelation : relation statement witness)
    (realState : Statement → Witness → RelationCoins →
      History (Outcome := Outcome) sites → State)
    (simulatedState : Statement → RelationCoins →
      History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites →
      RelationCoins ≃ RelationCoins)
    (hstate : ∀ coins answers,
      realState statement witness coins answers =
        simulatedState statement (answerEquiv answers coins) answers)
    (realFixed simulatedFixed : RelationCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (realSchedule simulatedSchedule : RelationCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (hreal : ∀ coins answers,
      Injective (protectedTracePoints (realFixed coins)
        (realSchedule coins) answers))
    (hsimulated : ∀ coins answers,
      Injective (protectedTracePoints (simulatedFixed coins)
        (simulatedSchedule coins) answers))
    (render : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites →
        RenderedView (AdversaryCoins := AdversaryCoins)
          (Transcript := Transcript) (ProofBytes := ProofBytes)
          (OracleView := OracleView))
    (input : ExperimentCoins (RelationCoins := RelationCoins)
      (Point := Point) (Outcome := Outcome) sites) :
    veilFlockRealExperiment statement witness realState realFixed
        realSchedule render input =
      veilFlockSimulator statement simulatedState simulatedFixed
        simulatedSchedule render
        (experimentCoinEquiv answerEquiv realFixed simulatedFixed
          realSchedule simulatedSchedule hreal hsimulated input) := by
  have _hvalid := hrelation
  unfold veilFlockRealExperiment veilFlockSimulator experimentCoinEquiv
  let continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites →
        VeilFlockAdversaryView (Statement := Statement)
          (AdversaryCoins := AdversaryCoins) (Transcript := Transcript)
          (ProofBytes := ProofBytes) (OracleView := OracleView) :=
    fun state protectedAnswers answers =>
      let visible := render state protectedAnswers answers
      { statement := statement
        adversaryRandomness := visible.adversaryRandomness
        transcript := visible.transcript
        proofBytes := visible.proofBytes
        oracleView := visible.oracleView }
  change
    OptionalPairedInterleaved.machine (realState statement witness)
        realFixed realSchedule continueWith input =
      OptionalPairedInterleaved.machine (simulatedState statement)
        simulatedFixed simulatedSchedule continueWith
        (OptionalPairedInterleaved.coinEquiv answerEquiv realFixed
          simulatedFixed realSchedule simulatedSchedule hreal hsimulated input)
  exact OptionalPairedInterleaved.machine_transport
    (leftState := realState statement witness)
    (rightState := simulatedState statement)
    (answerEquiv := answerEquiv) (hstate := hstate)
    (leftFixed := realFixed) (rightFixed := simulatedFixed)
    (leftSchedule := realSchedule) (rightSchedule := simulatedSchedule)
    (hleft := hreal) (hright := hsimulated)
    (continueWith := continueWith) input

/-- Exact joint-distribution theorem for the complete real and simulator
views. An instantiation supplies the already-proved production algebraic
transport and byte-schedule freshness; `render` then exposes proof bytes and
the entire adversary oracle view together. -/
theorem complete_real_simulator_exact {sites : ℕ}
    (relation : Statement → Witness → Prop)
    (statement : Statement) (witness : Witness)
    (hrelation : relation statement witness)
    (realState : Statement → Witness → RelationCoins →
      History (Outcome := Outcome) sites → State)
    (simulatedState : Statement → RelationCoins →
      History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites →
      RelationCoins ≃ RelationCoins)
    (hstate : ∀ coins answers,
      realState statement witness coins answers =
        simulatedState statement (answerEquiv answers coins) answers)
    (realFixed simulatedFixed : RelationCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (realSchedule simulatedSchedule : RelationCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (hreal : ∀ coins answers,
      Injective (protectedTracePoints (realFixed coins)
        (realSchedule coins) answers))
    (hsimulated : ∀ coins answers,
      Injective (protectedTracePoints (simulatedFixed coins)
        (simulatedSchedule coins) answers))
    (render : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites →
        RenderedView (AdversaryCoins := AdversaryCoins)
          (Transcript := Transcript) (ProofBytes := ProofBytes)
          (OracleView := OracleView)) :
    (PMF.uniformOfFintype
      (ExperimentCoins (RelationCoins := RelationCoins)
        (Point := Point) (Outcome := Outcome) sites)).map
      (veilFlockRealExperiment statement witness realState
        realFixed realSchedule render) =
    (PMF.uniformOfFintype
      (ExperimentCoins (RelationCoins := RelationCoins)
        (Point := Point) (Outcome := Outcome) sites)).map
      (veilFlockSimulator statement simulatedState
        simulatedFixed simulatedSchedule render) := by
  have _hvalid := hrelation
  unfold veilFlockRealExperiment veilFlockSimulator
  let continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites →
        VeilFlockAdversaryView (Statement := Statement)
          (AdversaryCoins := AdversaryCoins) (Transcript := Transcript)
          (ProofBytes := ProofBytes) (OracleView := OracleView) :=
    fun state protectedAnswers answers =>
      let visible := render state protectedAnswers answers
      { statement := statement
        adversaryRandomness := visible.adversaryRandomness
        transcript := visible.transcript
        proofBytes := visible.proofBytes
        oracleView := visible.oracleView }
  change
    (PMF.uniformOfFintype
      (ExperimentCoins (RelationCoins := RelationCoins)
        (Point := Point) (Outcome := Outcome) sites)).map
        (OptionalPairedInterleaved.machine (realState statement witness)
          realFixed realSchedule continueWith) =
      (PMF.uniformOfFintype
        (ExperimentCoins (RelationCoins := RelationCoins)
          (Point := Point) (Outcome := Outcome) sites)).map
        (OptionalPairedInterleaved.machine (simulatedState statement)
          simulatedFixed simulatedSchedule continueWith)
  exact OptionalPairedInterleaved.simulator_exact
    (leftState := realState statement witness)
    (rightState := simulatedState statement)
    (answerEquiv := answerEquiv)
    (hstate := hstate)
    (leftFixed := realFixed) (rightFixed := simulatedFixed)
    (leftSchedule := realSchedule) (rightSchedule := simulatedSchedule)
    (hleft := hreal) (hright := hsimulated)
    (continueWith := continueWith)

end VeiledFlock.ProductionCompleteExperiment

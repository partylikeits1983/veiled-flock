import VeiledFlock.Oracle.AdaptiveOracleProgramming
import VeiledFlock.Core.Probability

/-!
# Operational adaptive programmer for answer-dependent algebraic state

After the coupled Fiat--Shamir hybrid, the public simulator's algebraic state
is a function of the desired challenge vector.  This module splits the random
oracle inside each fixed simulator-coin fiber and reconstructs it by adaptive
programming.  The resulting oracle is pointwise the original table under the
split equivalence, so arbitrary post-proof oracle interaction is preserved.
-/

namespace VeiledFlock.DependentProtocolSimulator

open VeiledFlock.AdaptiveOracleProgramming

variable {AlgCoins State Point Outcome View : Type*}
variable [Fintype AlgCoins] [Nonempty AlgCoins]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

abbrev SimulatorCoins (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome)) :=
  Σ coins : AlgCoins,
    AdaptiveOracleProgramming.SimulatorCoins
      (sites := sites) (schedule coins)

noncomputable instance simulatorCoinsNonempty (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome)) :
    Nonempty (SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites schedule) := by
  let coins : AlgCoins := Classical.choice inferInstance
  exact ⟨⟨coins, Classical.choice inferInstance⟩⟩

/-- The operational simulator coin space is finite whenever the algebraic
coins and finite random-oracle domain are finite.  The fibers vary with the
answer-dependent schedule, hence this instance is declared noncomputably. -/
noncomputable instance simulatorCoinsFintype (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome)) :
    Fintype (SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites schedule) := by
  classical
  unfold SimulatorCoins AdaptiveOracleProgramming.SimulatorCoins
  infer_instance

/-- Fiberwise exact split of the unchanged random oracle. -/
noncomputable def splitCoinEquiv (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ coins (answers : History (Outcome := Outcome) sites),
      Function.Injective (tracePoints (schedule coins) answers)) :
    (AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) ≃
      SimulatorCoins (Point := Point) (Outcome := Outcome) sites schedule :=
  (Equiv.sigmaEquivProd AlgCoins
      (Oracle (Point := Point) (Outcome := Outcome))).symm |>.trans
    (Equiv.sigmaCongrRight fun coins ↦
      splitAdaptive (sites := sites) (schedule coins) (hinjective coins))

omit [Fintype AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
@[simp]
theorem splitCoinEquiv_apply (sites : ℕ)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ coins (answers : History (Outcome := Outcome) sites),
      Function.Injective (tracePoints (schedule coins) answers))
    (coins : AlgCoins) (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    splitCoinEquiv sites schedule hinjective (coins, oracle) =
      ⟨coins, splitAdaptive (sites := sites) (schedule coins)
        (hinjective coins) oracle⟩ := rfl

def oracleMachine (sites : ℕ)
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) : View :=
  let answers := run (schedule input.1) input.2 sites
  continueWith (state input.1 answers) input.2 answers

noncomputable def programmedMachine (sites : ℕ)
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ coins (answers : History (Outcome := Outcome) sites),
      Function.Injective (tracePoints (schedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : SimulatorCoins (Point := Point) (Outcome := Outcome)
      sites schedule) : View :=
  continueWith (state input.1 input.2.1)
    (simulatedOracle (schedule input.1) (hinjective input.1) input.2)
    input.2.1

omit [Fintype AlgCoins] [Nonempty AlgCoins] [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome] in
/-- Pointwise equivalence of the clairvoyant view and the executable adaptive
programmer. -/
theorem machine_transport (sites : ℕ)
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ coins (answers : History (Outcome := Outcome) sites),
      Function.Injective (tracePoints (schedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : AlgCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    oracleMachine sites state schedule continueWith input =
      programmedMachine sites state schedule hinjective continueWith
        (splitCoinEquiv sites schedule hinjective input) := by
  rcases input with ⟨coins, oracle⟩
  simp only [oracleMachine, programmedMachine, splitCoinEquiv_apply]
  let split := splitAdaptive (sites := sites) (schedule coins)
    (hinjective coins)
  have horacle : simulatedOracle (schedule coins) (hinjective coins)
      (split oracle) = oracle := by
    exact split.symm_apply_apply oracle
  have hanswers : (split oracle).1 = run (schedule coins) oracle sites := rfl
  rw [horacle, hanswers]

omit [DecidableEq Outcome] in
/-- Exact distributional equivalence of look-ahead sampling and straightline
adaptive oracle programming. -/
theorem programmed_exact (sites : ℕ)
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (schedule : AlgCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ coins (answers : History (Outcome := Outcome) sites),
      Function.Injective (tracePoints (schedule coins) answers))
    (continueWith : State →
      Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (AlgCoins × Oracle (Point := Point) (Outcome := Outcome))).map
        (oracleMachine sites state schedule continueWith) =
      (PMF.uniformOfFintype
        (SimulatorCoins (Point := Point) (Outcome := Outcome)
          sites schedule)).map
          (programmedMachine sites state schedule hinjective continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (splitCoinEquiv sites schedule hinjective)
  exact machine_transport sites state schedule hinjective continueWith

end VeiledFlock.DependentProtocolSimulator

import VeiledFlock.ConcreteSecurityBound
import VeiledFlock.ProductionCompleteExperiment
import VeiledFlock.ProductionGlobalGood

/-!
# Statistical distance from the explicit production coupling

This module is the probability-theoretic end of the end-to-end proof.  It
does not hide the remaining protocol obligation: callers must supply the
single pointwise theorem saying that the *complete* transported real view and
the witness-free simulated view are equal whenever `ProductionGlobalGood.Good`
holds.  Once that production coupling is instantiated, every probability
and arithmetic obligation is discharged here.

The result is statistical ZK in a finite classical programmable-random-oracle
experiment.  It is not a QROM theorem and does not assert information-
theoretic security of the SHA-256 function used by the Rust instantiation.
-/

namespace VeiledFlock.ProductionStatisticalZK

open VeiledFlock.ConcreteRandomTape
open VeiledFlock.EndToEnd
open VeiledFlock.ProductionGlobalGood
open VeiledFlock.SecurityLedger

variable {Core View Statement Witness : Type 0}
variable [Fintype Core] [DecidableEq Core] [Nonempty Core]
variable [Fintype View] [DecidableEq View]

/-- Coupling inequality specialized to the one explicit global production
event.  Equality is equality of `View`; an end-to-end instantiation chooses
`View = VeilFlockAdversaryView`, which includes proof bytes and the adaptive
oracle interaction. -/
theorem coupling_distance_le_global_bad
    (parameters : Parameters)
    (challengePrequery :
      ComponentEvent parameters (Tape parameters Core) .challengePrequery)
    (hiddenMerkleInput :
      ComponentEvent parameters (Tape parameters Core) .hiddenMerkleInput)
    (real simulated : Tape parameters Core → View)
    (coinEquiv : Tape parameters Core ≃ Tape parameters Core)
    (hgood : ∀ tape,
      Good parameters challengePrequery hiddenMerkleInput tape →
        real (coinEquiv tape) = simulated tape) :
    uniformTV real simulated ≤
      ((globalBad parameters challengePrequery hiddenMerkleInput).card : ℚ) /
        Fintype.card (Tape parameters Core) := by
  apply e2e_zk_of_coin_bijection real simulated coinEquiv
    (globalBad parameters challengePrequery hiddenMerkleInput)
  intro tape htape
  exact hgood tape
    ((good_iff_not_mem_globalBad parameters challengePrequery
      hiddenMerkleInput tape).2 htape)

/-- Symbolic, query-dependent statistical-ZK bound.  `zkBound parameters`
retains the proof count, programming-point count, adversarial query cap,
protocol query cap, nonce lengths, rejection limits, and grinding limits from
the concrete security ledger. -/
theorem veil_flock_statistical_zk_bound_of_good_coupling
    (relation : Statement → Witness → Prop)
    (statement : Statement) (witness : Witness)
    (hvalid : relation statement witness)
    (parameters : Parameters)
    (challengePrequery :
      ComponentEvent parameters (Tape parameters Core) .challengePrequery)
    (hiddenMerkleInput :
      ComponentEvent parameters (Tape parameters Core) .hiddenMerkleInput)
    (real simulated : Tape parameters Core → View)
    (coinEquiv : Tape parameters Core ≃ Tape parameters Core)
    (hgood : ∀ tape,
      Good parameters challengePrequery hiddenMerkleInput tape →
        real (coinEquiv tape) = simulated tape) :
    uniformTV real simulated ≤ zkBound parameters := by
  have _hvalid := hvalid
  exact (coupling_distance_le_global_bad parameters challengePrequery
    hiddenMerkleInput real simulated coinEquiv hgood).trans
      (global_bad_probability_le parameters challengePrequery hiddenMerkleInput)

/-- The explicit production bad-event probability is below `2^-126` for the
reviewed deployment envelope. -/
theorem global_failure_lt_two_pow_neg_126
    (challengePrequery : ComponentEvent
      ConcreteSecurityBound.reviewedParameters
      (Tape ConcreteSecurityBound.reviewedParameters Core)
      .challengePrequery)
    (hiddenMerkleInput : ComponentEvent
      ConcreteSecurityBound.reviewedParameters
      (Tape ConcreteSecurityBound.reviewedParameters Core)
      .hiddenMerkleInput) :
    ((globalBad ConcreteSecurityBound.reviewedParameters challengePrequery
        hiddenMerkleInput).card : ℚ) /
        Fintype.card (Tape ConcreteSecurityBound.reviewedParameters Core) <
      1 / (2 : ℚ) ^ 126 := by
  exact (global_bad_probability_le ConcreteSecurityBound.reviewedParameters
    challengePrequery hiddenMerkleInput).trans_lt
      ConcreteSecurityBound.reviewed_zkBound_lt_two_pow_neg_126

/-- Concrete statistical distance after the complete production equality-on-
`Good` theorem has been supplied.  This deliberately retains that premise in
its name and statement; the final no-gap theorem must discharge it from the
actual protocol state machine rather than silently assuming it. -/
theorem veil_flock_statistical_zk_126_of_good_coupling
    (relation : Statement → Witness → Prop)
    (statement : Statement) (witness : Witness)
    (hvalid : relation statement witness)
    (challengePrequery : ComponentEvent
      ConcreteSecurityBound.reviewedParameters
      (Tape ConcreteSecurityBound.reviewedParameters Core)
      .challengePrequery)
    (hiddenMerkleInput : ComponentEvent
      ConcreteSecurityBound.reviewedParameters
      (Tape ConcreteSecurityBound.reviewedParameters Core)
      .hiddenMerkleInput)
    (real simulated :
      Tape ConcreteSecurityBound.reviewedParameters Core → View)
    (coinEquiv :
      Tape ConcreteSecurityBound.reviewedParameters Core ≃
        Tape ConcreteSecurityBound.reviewedParameters Core)
    (hgood : ∀ tape,
      Good ConcreteSecurityBound.reviewedParameters challengePrequery
          hiddenMerkleInput tape →
        real (coinEquiv tape) = simulated tape) :
    uniformTV real simulated < 1 / (2 : ℚ) ^ 126 := by
  exact (veil_flock_statistical_zk_bound_of_good_coupling relation statement
    witness hvalid ConcreteSecurityBound.reviewedParameters challengePrequery
    hiddenMerkleInput real simulated coinEquiv hgood).trans_lt
      ConcreteSecurityBound.reviewed_zkBound_lt_two_pow_neg_126

end VeiledFlock.ProductionStatisticalZK

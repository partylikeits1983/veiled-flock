import VeiledFlock.ProductionChallengeSampler
import VeiledFlock.ProductionGrinding

/-!
# Joint production laws for bounded sampling and grinding

The verifier does not merely consume the accepted field element or a valid
PoW nonce. Rejected scalar draws are reabsorbed into the transcript and the
grinder returns the first successful counter. These theorems therefore compare
the complete observable result, including the updated transcript, rather than
only the accepted-value marginal.
-/

namespace VeiledFlock.ProductionSamplingJoint

open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrinding

/-- Exact real/simulator equality for a bounded scalar-rejection call. The
returned transcript contains every rejected draw, so this is equality of the
accepted value, retry count, rejected-prefix effects, and abort result jointly.
-/
theorem rejection_real_sim_equal_on_success
    (good : GhashField → Prop) [DecidablePred good]
    (realOracle simulatedOracle : List Byte → OracleBlock)
    (trials maxLength : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + trials * 18 ≤ maxLength)
    (horacle : ∀ point, isFiatShamirPoint point →
      point.length ≤ maxLength →
        simulatedOracle point = realOracle point) :
    sampleScalarUntil good simulatedOracle trials transcript =
      sampleScalarUntil good realOracle trials transcript := by
  exact sampleScalarUntil_oracle_congr_fiat_bounded good realOracle
    simulatedOracle trials maxLength transcript hfiat hbudget horacle

/-- The complete visible effect of a successful bounded grind. The nonce is
the canonical first successful counter and is then absorbed with the exact
tagged-byte framing; failure remains `none`. -/
noncomputable def grindVisible (good : OracleBlock → Prop)
    [DecidablePred good] (oracle : List Byte → OracleBlock)
    (state : Nonce256) (trials : ℕ) (transcript : List Byte) :
    Option (Word64 × List Byte) :=
  (grindPowBounded good oracle state trials).map fun nonce =>
    (nonce, afterGrind transcript nonce)

/-- Exact real/simulator equality of the first-success nonce, updated
transcript, and abort result. This rules out replacing production grinding by
an arbitrary valid nonce. -/
theorem grinding_real_sim_equal_on_success
    (good : OracleBlock → Prop) [DecidablePred good]
    (realOracle simulatedOracle : List Byte → OracleBlock)
    (state : Nonce256) (trials : ℕ) (transcript : List Byte)
    (horacle : ∀ candidate, candidate < trials →
      simulatedOracle
          (encodePowPoint state (BitVec.ofNat 64 candidate)) =
        realOracle
          (encodePowPoint state (BitVec.ofNat 64 candidate))) :
    grindVisible good simulatedOracle state trials transcript =
      grindVisible good realOracle state trials transcript := by
  unfold grindVisible
  rw [grindPowBounded_oracle_congr good realOracle simulatedOracle state
    trials horacle]

end VeiledFlock.ProductionSamplingJoint

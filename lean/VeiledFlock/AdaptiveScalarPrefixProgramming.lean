import VeiledFlock.AdaptiveOracleProgramming
import VeiledFlock.ScalarPrefixProgramming

/-!
# Adaptive scalar-prefix programming

The executable simulator chooses one 128-bit field element, reads the honest
256-bit random-oracle block at the reached point, overwrites its low half, and
retains its high half.  This module lifts the block-level equivalence through
an adaptive schedule.  The old low halves become independent discarded coins;
the resulting desired 256-bit blocks and untouched oracle complement are
exactly the ordinary adaptive-programmer coin space.
-/

namespace VeiledFlock.AdaptiveScalarPrefixProgramming

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.OracleProgramming
open VeiledFlock.ScalarPrefixProgramming

variable {Point View : Type*}
variable [Fintype Point] [DecidableEq Point]

/-- Simulator coins in the form used by Rust: selected field elements,
pre-programming oracle blocks at the reached sites, and the oracle table away
from the resulting programmed trace. -/
abbrev ScalarSimulatorCoins (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock)) :=
  Σ raw : ScalarAnswers sites × BlockAnswers sites,
    Unprogrammed
      (tracePoints schedule (answerCoinEquiv sites raw).1) → OracleBlock

noncomputable instance scalarSimulatorCoinsNonempty (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock)) :
    Nonempty (ScalarSimulatorCoins (Point := Point) sites schedule) := by
  classical
  infer_instance

noncomputable instance scalarSimulatorCoinsFintype (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock)) :
    Fintype (ScalarSimulatorCoins (Point := Point) sites schedule) := by
  classical
  unfold ScalarSimulatorCoins
  infer_instance

private noncomputable def reassociateEquiv (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock)) :
    (Σ pair : BlockAnswers sites × DiscardedPrefixes sites,
      Unprogrammed (tracePoints schedule pair.1) → OracleBlock) ≃
      (SimulatorCoins (sites := sites) schedule ×
        DiscardedPrefixes sites) :=
  (Equiv.sigmaCongr
      (Equiv.sigmaEquivProd (BlockAnswers sites)
        (DiscardedPrefixes sites)).symm
      (fun _ ↦ Equiv.refl _)).trans
    ((Equiv.sigmaAssoc (fun answers (_ : DiscardedPrefixes sites) ↦
        Unprogrammed (tracePoints schedule answers) → OracleBlock)).trans
      ((Equiv.sigmaCongrRight fun answers ↦
          (Equiv.sigmaEquivProd (DiscardedPrefixes sites)
              (Unprogrammed (tracePoints schedule answers) → OracleBlock)).trans
            (Equiv.prodComm _ _)).trans
        (Equiv.sigmaProdDistrib
          (fun answers ↦
            Unprogrammed (tracePoints schedule answers) → OracleBlock)
          (DiscardedPrefixes sites)).symm))

/-- Exact reparameterization from scalar-prefix programming coins to full
uniform programmed blocks plus unused old low halves. -/
noncomputable def coinEquiv (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock)) :
    ScalarSimulatorCoins (Point := Point) sites schedule ≃
      (SimulatorCoins (sites := sites) schedule ×
        DiscardedPrefixes sites) :=
  (Equiv.sigmaCongr (answerCoinEquiv sites) (fun _ ↦ Equiv.refl _)).trans
    (reassociateEquiv sites schedule)

/-- Reconstruct the oracle after low-half programming. -/
noncomputable def scalarProgrammedOracle (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock))
    (hinjective : ∀ answers : BlockAnswers sites,
      Function.Injective (tracePoints schedule answers))
    (coins : ScalarSimulatorCoins (Point := Point) sites schedule) :
    AdaptiveOracleProgramming.Oracle
      (Point := Point) (Outcome := OracleBlock) :=
  simulatedOracle schedule hinjective
    ⟨(answerCoinEquiv sites coins.1).1, coins.2⟩

/-- The reached programmed block has the simulator-selected low scalar. -/
theorem scalarProgrammedOracle_decodes (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock))
    (hinjective : ∀ answers : BlockAnswers sites,
      Function.Injective (tracePoints schedule answers))
    (coins : ScalarSimulatorCoins (Point := Point) sites schedule)
    (site : Fin sites) :
    VeiledFlock.Field128Serialization.encodeGhashFieldEquiv.symm
        (oracleBlockSplit
          (scalarProgrammedOracle sites schedule hinjective coins
            (tracePoint schedule (answerCoinEquiv sites coins.1).1 site))).1 =
      coins.1.1 site := by
  rw [scalarProgrammedOracle, simulatedOracle_at]
  exact programmedBlock_decodes sites coins.1 site

/-- The reached programmed block preserves the high half of the original
site block supplied in the scalar simulator coins. -/
theorem scalarProgrammedOracle_preservesHighHalf (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock))
    (hinjective : ∀ answers : BlockAnswers sites,
      Function.Injective (tracePoints schedule answers))
    (coins : ScalarSimulatorCoins (Point := Point) sites schedule)
    (site : Fin sites) :
    (oracleBlockSplit
      (scalarProgrammedOracle sites schedule hinjective coins
        (tracePoint schedule (answerCoinEquiv sites coins.1).1 site))).2 =
      (oracleBlockSplit (coins.1.2 site)).2 := by
  rw [scalarProgrammedOracle, simulatedOracle_at]
  exact programmedBlock_preservesHighHalf sites coins.1 site

/-- Any view of the programmed answer vector and its untouched complement has
the same distribution under Rust-style scalar-prefix coins as under uniform
full-block adaptive-programmer coins. -/
theorem simulator_exact (sites : ℕ)
    (schedule : Schedule (Point := Point) (Outcome := OracleBlock))
    (view : SimulatorCoins (sites := sites) schedule → View) :
    (PMF.uniformOfFintype
      (ScalarSimulatorCoins (Point := Point) sites schedule)).map
        (fun coins ↦ view (coinEquiv sites schedule coins).1) =
      (PMF.uniformOfFintype
        (SimulatorCoins (sites := sites) schedule)).map view := by
  calc
    _ = (PMF.uniformOfFintype
          (SimulatorCoins (sites := sites) schedule ×
            DiscardedPrefixes sites)).map
          (fun coins ↦ view coins.1) := by
        apply VeiledFlock.Probability.uniform_map_eq_of_equiv
          (coinEquiv sites schedule)
        intro coins
        rfl
    _ = _ := VeiledFlock.Probability.uniform_map_ignore_right view

end VeiledFlock.AdaptiveScalarPrefixProgramming

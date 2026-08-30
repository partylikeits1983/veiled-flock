import VeiledFlock.Oracle.AdaptiveOracleProgramming
import VeiledFlock.Core.Probability

/-!
# Coin transport plus witness-dependent adaptive oracle traces

The honest and simulated executions need not query the random oracle at the
same hidden points: salted Merkle leaves contain different private payloads,
and Fiat--Shamir points contain the resulting transcript.  This module
composes an arbitrary public-state coin equivalence with exact adaptive trace
retargeting.  The visible state and complete oracle-answer transcript are
preserved pointwise.
-/

namespace VeiledFlock.AdaptiveTraceStateMachine

open Function
open VeiledFlock.AdaptiveOracleProgramming

variable {StateCoins State Point Outcome View : Type*}
variable [Fintype StateCoins] [DecidableEq StateCoins] [Nonempty StateCoins]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

private def swapCoinsOracle :
    (StateCoins × Oracle (Point := Point) (Outcome := Outcome)) ≃
      (Oracle (Point := Point) (Outcome := Outcome) × StateCoins) :=
  ⟨fun coins => (coins.2, coins.1), fun coins => (coins.2, coins.1),
    fun _ => rfl, fun _ => rfl⟩

/-- First retarget the oracle trace in the original state-coin fiber, then
translate the state coins. -/
noncomputable def retargetedCoinEquiv {sites : ℕ}
    (coinEquiv : StateCoins ≃ StateCoins)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (rightSchedule coins) answers)) :
    (StateCoins × Oracle (Point := Point) (Outcome := Outcome)) ≃
      (StateCoins × Oracle (Point := Point) (Outcome := Outcome)) :=
  (VeiledFlock.Probability.fiberwiseEquiv swapCoinsOracle
    (fun coins => retargetAdaptive (leftSchedule coins)
      (rightSchedule (coinEquiv coins)) (hleft coins)
      (hright (coinEquiv coins)))).trans
    (Equiv.prodCongr coinEquiv (Equiv.refl _))

theorem retargetedCoinEquiv_state {sites : ℕ}
    (coinEquiv : StateCoins ≃ StateCoins)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (rightSchedule coins) answers))
    (coins : StateCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    (retargetedCoinEquiv coinEquiv leftSchedule rightSchedule hleft hright
      coins).1 = coinEquiv coins.1 := by
  let fiber := VeiledFlock.Probability.fiberwiseEquiv swapCoinsOracle
    (fun stateCoins => retargetAdaptive (leftSchedule stateCoins)
      (rightSchedule (coinEquiv stateCoins)) (hleft stateCoins)
      (hright (coinEquiv stateCoins)))
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapCoinsOracle
    (fun stateCoins => retargetAdaptive (leftSchedule stateCoins)
      (rightSchedule (coinEquiv stateCoins)) (hleft stateCoins)
      (hright (coinEquiv stateCoins))) coins
  have hstate : (fiber coins).1 = coins.1 := congrArg Prod.snd hsplit
  change coinEquiv (fiber coins).1 = coinEquiv coins.1
  rw [hstate]

theorem retargetedCoinEquiv_answers {sites : ℕ}
    (coinEquiv : StateCoins ≃ StateCoins)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (rightSchedule coins) answers))
    (coins : StateCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    run (rightSchedule
        (retargetedCoinEquiv coinEquiv leftSchedule rightSchedule hleft hright
          coins).1)
      (retargetedCoinEquiv coinEquiv leftSchedule rightSchedule hleft hright
        coins).2 sites =
      run (leftSchedule coins.1) coins.2 sites := by
  let fiber := VeiledFlock.Probability.fiberwiseEquiv swapCoinsOracle
    (fun stateCoins => retargetAdaptive (leftSchedule stateCoins)
      (rightSchedule (coinEquiv stateCoins)) (hleft stateCoins)
      (hright (coinEquiv stateCoins)))
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapCoinsOracle
    (fun stateCoins => retargetAdaptive (leftSchedule stateCoins)
      (rightSchedule (coinEquiv stateCoins)) (hleft stateCoins)
      (hright (coinEquiv stateCoins))) coins
  have hstate : (fiber coins).1 = coins.1 := congrArg Prod.snd hsplit
  have horacle : (fiber coins).2 =
      retargetAdaptive (leftSchedule coins.1)
        (rightSchedule (coinEquiv coins.1)) (hleft coins.1)
        (hright (coinEquiv coins.1)) coins.2 := congrArg Prod.fst hsplit
  have hretargetedOracle :
      (retargetedCoinEquiv coinEquiv leftSchedule rightSchedule hleft hright
        coins).2 =
        retargetAdaptive (leftSchedule coins.1)
          (rightSchedule (coinEquiv coins.1)) (hleft coins.1)
          (hright (coinEquiv coins.1)) coins.2 := by
    change (fiber coins).2 = _
    exact horacle
  rw [retargetedCoinEquiv_state coinEquiv leftSchedule rightSchedule hleft
    hright, hretargetedOracle]
  exact run_retargetAdaptive (leftSchedule coins.1)
    (rightSchedule (coinEquiv coins.1)) (hleft coins.1)
    (hright (coinEquiv coins.1)) coins.2

noncomputable def machine {sites : ℕ}
    (state : StateCoins → State)
    (schedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State → History (Outcome := Outcome) sites → View)
    (coins : StateCoins × Oracle (Point := Point) (Outcome := Outcome)) : View :=
  continueWith (state coins.1) (run (schedule coins.1) coins.2 sites)

/-- Pointwise preservation of the visible state and the complete adaptive
oracle-answer trace. -/
theorem machine_transport {sites : ℕ}
    (leftState rightState : StateCoins → State)
    (coinEquiv : StateCoins ≃ StateCoins)
    (hstate : ∀ coins, leftState coins = rightState (coinEquiv coins))
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (rightSchedule coins) answers))
    (continueWith : State → History (Outcome := Outcome) sites → View)
    (coins : StateCoins × Oracle (Point := Point) (Outcome := Outcome)) :
    machine leftState leftSchedule continueWith coins =
      machine rightState rightSchedule continueWith
        (retargetedCoinEquiv coinEquiv leftSchedule rightSchedule hleft hright
          coins) := by
  simp only [machine]
  have hanswers := retargetedCoinEquiv_answers coinEquiv leftSchedule
    rightSchedule hleft hright coins
  rw [retargetedCoinEquiv_state coinEquiv leftSchedule rightSchedule hleft
    hright] at hanswers
  rw [retargetedCoinEquiv_state coinEquiv leftSchedule rightSchedule hleft
      hright,
    hstate, hanswers]

/-- Exact distributional equality for a production state translation followed
by arbitrary witness-dependent, causal random-oracle work. -/
theorem simulator_exact {sites : ℕ}
    (leftState rightState : StateCoins → State)
    (coinEquiv : StateCoins ≃ StateCoins)
    (hstate : ∀ coins, leftState coins = rightState (coinEquiv coins))
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (rightSchedule coins) answers))
    (continueWith : State → History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (StateCoins × Oracle (Point := Point) (Outcome := Outcome))).map
        (machine leftState leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (StateCoins × Oracle (Point := Point) (Outcome := Outcome))).map
          (machine rightState rightSchedule continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (retargetedCoinEquiv coinEquiv leftSchedule rightSchedule hleft hright)
  exact machine_transport leftState rightState coinEquiv hstate leftSchedule
    rightSchedule hleft hright continueWith

end VeiledFlock.AdaptiveTraceStateMachine

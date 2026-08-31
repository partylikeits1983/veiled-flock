import VeiledFlock.Oracle.ProtectedAdaptiveOracle

/-!
# State transport with protected adversary oracle answers

This composes an algebraic coin bijection with protected adaptive oracle
retargeting.  The full view contains the visible algebraic state, every
earlier adversary oracle answer, and every subsequent protocol oracle answer.
-/

namespace VeiledFlock.ProtectedAdaptiveStateMachine

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ProtectedAdaptiveOracle

variable {StateCoins State Prior Point Outcome View : Type*}
variable [Fintype StateCoins] [DecidableEq StateCoins] [Nonempty StateCoins]
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

private def swapCoinsOracle :
    (StateCoins × RandomOracle (Point := Point) (Outcome := Outcome)) ≃
      (RandomOracle (Point := Point) (Outcome := Outcome) × StateCoins) :=
  ⟨fun coins => (coins.2, coins.1), fun coins => (coins.2, coins.1),
    fun _ => rfl, fun _ => rfl⟩

/-- Retarget the oracle inside each original state-coin fiber, then transport
the algebraic state coins.  The fixed query family is included in both sides
of every oracle split. -/
noncomputable def coinEquiv {sites : ℕ}
    (stateEquiv : StateCoins ≃ StateCoins)
    (fixedPoints : StateCoins → Prior → Point)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points (fixedPoints coins) (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points (fixedPoints coins) (rightSchedule (stateEquiv coins))
          answers)) :
    (StateCoins × RandomOracle (Point := Point) (Outcome := Outcome)) ≃
      (StateCoins × RandomOracle (Point := Point) (Outcome := Outcome)) :=
  (VeiledFlock.Probability.fiberwiseEquiv swapCoinsOracle
    (fun coins => retarget (fixedPoints coins) (leftSchedule coins)
      (rightSchedule (stateEquiv coins)) (hleft coins) (hright coins))).trans
    (Equiv.prodCongr stateEquiv (Equiv.refl _))

omit [Nonempty StateCoins] [Nonempty Outcome] in
omit [Fintype StateCoins] [DecidableEq StateCoins] [Fintype Outcome] [DecidableEq Outcome] in
theorem coinEquiv_state {sites : ℕ}
    (stateEquiv : StateCoins ≃ StateCoins)
    (fixedPoints : StateCoins → Prior → Point)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points (fixedPoints coins) (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points (fixedPoints coins) (rightSchedule (stateEquiv coins))
          answers))
    (coins : StateCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) :
    (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft hright
      coins).1 = stateEquiv coins.1 := by
  let fiber := VeiledFlock.Probability.fiberwiseEquiv swapCoinsOracle
    (fun stateCoins => retarget (fixedPoints stateCoins)
      (leftSchedule stateCoins) (rightSchedule (stateEquiv stateCoins))
      (hleft stateCoins) (hright stateCoins))
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapCoinsOracle
    (fun stateCoins => retarget (fixedPoints stateCoins)
      (leftSchedule stateCoins) (rightSchedule (stateEquiv stateCoins))
      (hleft stateCoins) (hright stateCoins)) coins
  have hstate : (fiber coins).1 = coins.1 := congrArg Prod.snd hsplit
  change stateEquiv (fiber coins).1 = stateEquiv coins.1
  rw [hstate]

omit [Nonempty StateCoins] [Nonempty Outcome] in
omit [Fintype StateCoins] [DecidableEq StateCoins] [Fintype Outcome] [DecidableEq Outcome] in
theorem coinEquiv_oracle {sites : ℕ}
    (stateEquiv : StateCoins ≃ StateCoins)
    (fixedPoints : StateCoins → Prior → Point)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points (fixedPoints coins) (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points (fixedPoints coins) (rightSchedule (stateEquiv coins))
          answers))
    (coins : StateCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) :
    (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft hright
      coins).2 =
      retarget (fixedPoints coins.1) (leftSchedule coins.1)
        (rightSchedule (stateEquiv coins.1)) (hleft coins.1)
        (hright coins.1) coins.2 := by
  let fiber := VeiledFlock.Probability.fiberwiseEquiv swapCoinsOracle
    (fun stateCoins => retarget (fixedPoints stateCoins)
      (leftSchedule stateCoins) (rightSchedule (stateEquiv stateCoins))
      (hleft stateCoins) (hright stateCoins))
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapCoinsOracle
    (fun stateCoins => retarget (fixedPoints stateCoins)
      (leftSchedule stateCoins) (rightSchedule (stateEquiv stateCoins))
      (hleft stateCoins) (hright stateCoins)) coins
  exact congrArg Prod.fst hsplit

omit [Nonempty StateCoins] [Nonempty Outcome] in
omit [Fintype StateCoins] [DecidableEq StateCoins] [Fintype Outcome] [DecidableEq Outcome] in
theorem coinEquiv_fixedAnswers {sites : ℕ}
    (stateEquiv : StateCoins ≃ StateCoins)
    (fixedPoints : StateCoins → Prior → Point)
    (hfixed : ∀ coins prior,
      fixedPoints (stateEquiv coins) prior = fixedPoints coins prior)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points (fixedPoints coins) (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points (fixedPoints coins) (rightSchedule (stateEquiv coins))
          answers))
    (coins : StateCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) (prior : Prior) :
    (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft hright
      coins).2
        (fixedPoints
          (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft
            hright coins).1 prior) =
      coins.2 (fixedPoints coins.1 prior) := by
  rw [coinEquiv_state]
  rw [hfixed, coinEquiv_oracle]
  exact retarget_protected (fixedPoints coins.1) (leftSchedule coins.1)
    (rightSchedule (stateEquiv coins.1)) (hleft coins.1) (hright coins.1)
    coins.2 prior

omit [Nonempty StateCoins] [Nonempty Outcome] in
omit [Fintype StateCoins] [DecidableEq StateCoins] [Fintype Outcome] [DecidableEq Outcome] in
theorem coinEquiv_protocolAnswers {sites : ℕ}
    (stateEquiv : StateCoins ≃ StateCoins)
    (fixedPoints : StateCoins → Prior → Point)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points (fixedPoints coins) (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points (fixedPoints coins) (rightSchedule (stateEquiv coins))
          answers))
    (coins : StateCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) :
    run (rightSchedule
        (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft
          hright coins).1)
      (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft
        hright coins).2 sites =
      run (leftSchedule coins.1) coins.2 sites := by
  rw [coinEquiv_state, coinEquiv_oracle]
  exact retarget_answers (fixedPoints coins.1) (leftSchedule coins.1)
    (rightSchedule (stateEquiv coins.1)) (hleft coins.1) (hright coins.1)
    coins.2

noncomputable def machine {sites : ℕ}
    (state : StateCoins → State)
    (fixedPoints : StateCoins → Prior → Point)
    (schedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (coins : StateCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) : View :=
  continueWith (state coins.1)
    (fun prior => coins.2 (fixedPoints coins.1 prior))
    (run (schedule coins.1) coins.2 sites)

omit [Nonempty StateCoins] [Nonempty Outcome] in
/-- Pointwise equality of the complete algebraic, adversary-prefix, and
protocol-answer view. -/
theorem machine_transport {sites : ℕ}
    (leftState rightState : StateCoins → State)
    (stateEquiv : StateCoins ≃ StateCoins)
    (hstate : ∀ coins, leftState coins = rightState (stateEquiv coins))
    (fixedPoints : StateCoins → Prior → Point)
    (hfixed : ∀ coins prior,
      fixedPoints (stateEquiv coins) prior = fixedPoints coins prior)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points (fixedPoints coins) (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points (fixedPoints coins) (rightSchedule (stateEquiv coins))
          answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (coins : StateCoins ×
      RandomOracle (Point := Point) (Outcome := Outcome)) :
    machine leftState fixedPoints leftSchedule continueWith coins =
      machine rightState fixedPoints rightSchedule continueWith
        (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft
          hright coins) := by
  simp only [machine]
  rw [coinEquiv_state, ← hstate]
  have hfixedAnswers := coinEquiv_fixedAnswers stateEquiv fixedPoints hfixed
    leftSchedule rightSchedule hleft hright coins
  have hprotocol := coinEquiv_protocolAnswers stateEquiv fixedPoints
    leftSchedule rightSchedule hleft hright coins
  rw [coinEquiv_state] at hfixedAnswers hprotocol
  rw [hprotocol]
  apply congrArg (fun fixedAnswers =>
    continueWith (leftState coins.1) fixedAnswers
      (run (leftSchedule coins.1) coins.2 sites))
  funext prior
  exact (hfixedAnswers prior).symm

/-- Exact distributional equality on the good event, including the complete
earlier classical adversary view. -/
theorem simulator_exact {sites : ℕ}
    (leftState rightState : StateCoins → State)
    (stateEquiv : StateCoins ≃ StateCoins)
    (hstate : ∀ coins, leftState coins = rightState (stateEquiv coins))
    (fixedPoints : StateCoins → Prior → Point)
    (hfixed : ∀ coins prior,
      fixedPoints (stateEquiv coins) prior = fixedPoints coins prior)
    (leftSchedule rightSchedule : StateCoins →
      Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective (points (fixedPoints coins) (leftSchedule coins) answers))
    (hright : ∀ coins (answers : History (Outcome := Outcome) sites),
      Injective
        (points (fixedPoints coins) (rightSchedule (stateEquiv coins))
          answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (StateCoins ×
        RandomOracle (Point := Point) (Outcome := Outcome))).map
        (machine leftState fixedPoints leftSchedule continueWith) =
      (PMF.uniformOfFintype
        (StateCoins ×
          RandomOracle (Point := Point) (Outcome := Outcome))).map
        (machine rightState fixedPoints rightSchedule continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv stateEquiv fixedPoints leftSchedule rightSchedule hleft hright)
  exact machine_transport leftState rightState stateEquiv hstate fixedPoints
    hfixed leftSchedule rightSchedule hleft hright continueWith

end VeiledFlock.ProtectedAdaptiveStateMachine

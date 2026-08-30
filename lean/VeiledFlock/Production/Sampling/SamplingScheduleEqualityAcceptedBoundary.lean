import VeiledFlock.Production.Sampling.SamplingScheduleEqualityBoundary

/-! # Equality boundaries after the first accepting attempt -/

namespace VeiledFlock.ProductionSamplingScheduleEqualityAcceptedBoundary

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleEqualityBoundary
open VeiledFlock.ProductionSamplingScheduleEqualityGrowth
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawControlUntil_after_first_equality_live_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape) :
    let first := firstEqualityAccepted shape answers hgood
    let result := rawControlUntil shape causalSecret completion witness coins
      prelude answers (equalityOffset + (first + 1) * 6)
        (equalityBoundary_fits (first + 1) (by
          exact (firstEqualityAccepted_lt shape answers hgood)))
    result.status = .live ∧ result.equalityPoint.isSome = true := by
  dsimp only
  let first := firstEqualityAccepted shape answers hgood
  have hfirst : first < rejectionTrials :=
    firstEqualityAccepted_lt shape answers hgood
  have hbefore := rawControlUntil_equality_boundary_live_none shape
    causalSecret completion witness coins prelude answers hgood first (by rfl)
  rcases firstEqualityAccepted_spec shape answers hgood with
    ⟨_, haccepts⟩
  have hlocal := equalityAttempt_live_some_of_accepted shape first
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (equalityOffset + first * 6)
        (equalityBoundary_fits first hfirst.le))
    (equalityAttemptAnswers answers ⟨first, hfirst⟩)
    hbefore.1 hbefore.2.1 hbefore.2.2 haccepts
  have hstep := rawControlUntil_equality_boundary_step shape causalSecret
    completion witness coins prelude answers first hfirst hlocal.1
  rw [hstep]
  exact hlocal

set_option maxRecDepth 10000 in
theorem rawControlUntil_equality_boundary_after_first_eq
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (extra : ℕ)
    (hcap : firstEqualityAccepted shape answers hgood + 1 + extra ≤
      rejectionTrials) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (equalityOffset +
          (firstEqualityAccepted shape answers hgood + 1 + extra) * 6)
        (equalityBoundary_fits
          (firstEqualityAccepted shape answers hgood + 1 + extra) hcap) =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        (equalityOffset +
          (firstEqualityAccepted shape answers hgood + 1) * 6)
        (equalityBoundary_fits
          (firstEqualityAccepted shape answers hgood + 1)
            (firstEqualityAccepted_lt shape answers hgood)) := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      let attempt := firstEqualityAccepted shape answers hgood + 1 + extra
      have hattempt : attempt < rejectionTrials := by
        dsimp only [attempt]
        omega
      have hprevCap : attempt ≤ rejectionTrials := hattempt.le
      have ih' := ih hprevCap
      have haccepted := rawControlUntil_after_first_equality_live_some shape
        causalSecret completion witness coins prelude answers hgood
      let previous := rawControlUntil shape causalSecret completion witness coins
        prelude answers (equalityOffset + attempt * 6)
          (equalityBoundary_fits attempt hprevCap)
      have hpreviousEq : previous =
          rawControlUntil shape causalSecret completion witness coins prelude
            answers
            (equalityOffset +
              (firstEqualityAccepted shape answers hgood + 1) * 6)
            (equalityBoundary_fits
              (firstEqualityAccepted shape answers hgood + 1)
                (firstEqualityAccepted_lt shape answers hgood)) := by
        exact ih'
      have hpreviousStatus : previous.status = .live := by
        rw [hpreviousEq]
        exact haccepted.1
      have hpreviousSome : previous.equalityPoint.isSome = true := by
        rw [hpreviousEq]
        exact haccepted.2
      have hlocalEq :
          iterateFrom (equalityStep shape) (equalityOffset + attempt * 6) 6
              previous (equalityAttemptAnswers answers ⟨attempt, hattempt⟩) =
            previous :=
        equalityAttempt_eq_of_some shape attempt previous _ hpreviousSome
      have hlocalStatus :
          (iterateFrom (equalityStep shape) (equalityOffset + attempt * 6) 6
            previous
            (equalityAttemptAnswers answers ⟨attempt, hattempt⟩)).status =
              .live := by
        rw [hlocalEq]
        exact hpreviousStatus
      have hstep := rawControlUntil_equality_boundary_step shape causalSecret
        completion witness coins prelude answers attempt hattempt hlocalStatus
      change rawControlUntil shape causalSecret completion witness coins prelude
        answers (equalityOffset + (attempt + 1) * 6) _ = _
      rw [hstep, hlocalEq, hpreviousEq]

end VeiledFlock.ProductionSamplingScheduleEqualityAcceptedBoundary

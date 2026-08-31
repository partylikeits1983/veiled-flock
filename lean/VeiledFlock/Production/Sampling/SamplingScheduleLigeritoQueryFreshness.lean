import VeiledFlock.Production.Sampling.SamplingScheduleLigeritoSegment

/-! # Fiat--Shamir freshness across production Ligerito sites -/

namespace VeiledFlock.ProductionSamplingScheduleLigeritoQueryFreshness

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingScheduleLigeritoSegment
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole

set_option maxRecDepth 10000 in
theorem fiat_query_not_in_ligerito_grinding
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (round : Fin productionSamplingSlots)
    (control : Control shape) (point : List Byte)
    (hfiat : isFiatShamirPoint point)
    (hquery : rawQuery shape causalSecret completion witness coins round
      control = some point)
    (hlower : ligeritoSiteStart site + 1 ≤ round.val)
    (hupper : round.val < ligeritoSiteStart site + ligeritoSiteWidth) : False := by
  let trial := round.val - (ligeritoSiteStart site + 1)
  have hroundEq : round.val = ligeritoSiteStart site + 1 + trial := by
    dsimp only [trial]
    omega
  have htrial : trial < maxLigeritoTrials := by
    unfold ligeritoSiteWidth at hupper
    omega
  have hwithin := (ligerito_trial_offset site trial htrial).1
  have hwithin' :
      (round.val - ligeritoOffset) % ligeritoSiteWidth = 1 + trial := by
    rw [hroundEq]
    exact hwithin
  have hwithinNe :
      (round.val - ligeritoOffset) % ligeritoSiteWidth ≠ 0 := by
    rw [hwithin']
    omega
  have hligeritoLower : ligeritoOffset ≤ round.val := by
    unfold ligeritoSiteStart at hlower
    omega
  have hskip : ¬round.val < equalitySkipBlocks := by
    have : equalitySkipBlocks ≤ ligeritoOffset := by decide
    omega
  have hequality : ¬round.val < zerocheckOffset := by
    have : zerocheckOffset ≤ ligeritoOffset := by decide
    omega
  have hzero : ¬round.val < blindStateOffset := by
    have : blindStateOffset ≤ ligeritoOffset := by decide
    omega
  have hblindState : ¬round.val < blindGrindingOffset := by
    have : blindGrindingOffset ≤ ligeritoOffset := by decide
    omega
  have hblindGrind : ¬round.val < blindChallengeOffset := by
    have : blindChallengeOffset ≤ ligeritoOffset := by decide
    omega
  have hblind : ¬round.val < multiplicationAlphaOffset := by
    have : multiplicationAlphaOffset ≤ ligeritoOffset := by decide
    omega
  have halpha : ¬round.val < outerChallengeOffset := by
    have : outerChallengeOffset ≤ ligeritoOffset := by decide
    omega
  have houterChallenge : ¬round.val < outerPositionsOffset := by
    have : outerPositionsOffset ≤ ligeritoOffset := by decide
    omega
  have houterPositions : ¬round.val < linearPositionsOffset := by
    have : linearPositionsOffset ≤ ligeritoOffset := by decide
    omega
  have hlinearPositions : ¬round.val < linearRhoOffset := by
    have : linearRhoOffset ≤ ligeritoOffset := by decide
    omega
  have hlinearRho : ¬round.val < hadamardPositionsOffset := by
    have : hadamardPositionsOffset ≤ ligeritoOffset := by decide
    omega
  have hhadamardPositions : ¬round.val < hadamardRhoOffset := by
    have : hadamardRhoOffset ≤ ligeritoOffset := by decide
    omega
  have hhadamardRho : ¬round.val < productCoefficientOffset := by
    have : productCoefficientOffset ≤ ligeritoOffset := by decide
    omega
  have hproduct : ¬round.val < ligeritoOffset := by omega
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hdone : control.stageDone
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho,
      hproduct, round.isLt, hwithinNe, hdone] at hquery
  · cases hpow : control.powState with
    | none =>
        simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
          hblindGrind, hblind, halpha, houterChallenge, houterPositions,
          hlinearPositions, hlinearRho, hhadamardPositions,
          hhadamardRho, hproduct, round.isLt, hwithinNe, hdone, hpow]
          at hquery
    | some state =>
        simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
          hblindGrind, hblind, halpha, houterChallenge, houterPositions,
          hlinearPositions, hlinearRho, hhadamardPositions,
          hhadamardRho, hproduct, round.isLt, hwithinNe, hdone, hpow]
          at hquery
        subst point
        exact fiatShamir_ne_pow hfiat state _ rfl

set_option maxRecDepth 10000 in
theorem ligerito_state_fiat_query_length_strict
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (site : Fin maxLigeritoSites) (right : Fin productionSamplingSlots)
    (hlt : ligeritoSiteStart site < right.val)
    (leftPoint rightPoint : List Byte)
    (hleftFiat : isFiatShamirPoint leftPoint)
    (hrightFiat : isFiatShamirPoint rightPoint)
    (hleft : rawQuery shape causalSecret completion witness coins
      (ligeritoSiteStart site)
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site)
          (Nat.le_trans (Nat.le_add_right _ _) (ligeritoSite_window_fits site))) =
        some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  have hrightAfter :
      ligeritoSiteStart site + ligeritoSiteWidth ≤ right.val := by
    by_contra hnot
    exact fiat_query_not_in_ligerito_grinding shape causalSecret completion
      witness coins site right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le)
      rightPoint hrightFiat hright (by omega) (by omega)
  have hleftStatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site)
          (Nat.le_trans (Nat.le_add_right _ _) (ligeritoSite_window_fits site))).status =
        .live := by
    generalize hcontrol : rawControlUntil shape causalSecret completion witness
      coins prelude answers (ligeritoSiteStart site)
        (Nat.le_trans (Nat.le_add_right _ _)
          (ligeritoSite_window_fits site)) = control at hleft ⊢
    cases hstatus : control.status with
    | live => rfl
    | abort => simp [rawQuery, hstatus] at hleft
    | success => simp [rawQuery, hstatus] at hleft
    | collision => simp [rawQuery, hstatus] at hleft
  have hbound :
      (rawControlUntil shape causalSecret completion witness coins prelude
          answers (ligeritoSiteStart site)
            (Nat.le_trans (Nat.le_add_right _ _)
              (ligeritoSite_window_fits site))).transcript.length + 17 ≤
        (ligeritoSegmentResult shape causalSecret completion witness coins site
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (ligeritoSiteStart site)
              (Nat.le_trans (Nat.le_add_right _ _)
                (ligeritoSite_window_fits site))) answers).transcript.length :=
    ligeritoSegmentResult_add_seventeen shape causalSecret completion witness
      coins site
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site)
          (Nat.le_trans (Nat.le_add_right _ _) (ligeritoSite_window_fits site)))
      answers hleftStatus
      (exists_ligeritoGrinding_answer_of_not_globalBad shape answers hgood site)
  have hlength := rawControlUntil_ligerito_length_eq_segment shape causalSecret
    completion witness coins prelude answers site
  have hmono := rawControlUntil_transcript_length_mono shape causalSecret
    completion witness coins prelude answers
    (ligeritoSiteStart site + ligeritoSiteWidth) right.val hrightAfter
    right.isLt.le
  have hleftLength := rawQuery_afterZerocheck_fiat_length_le shape causalSecret
    completion witness coins (ligeritoSiteStart site)
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (ligeritoSiteStart site)
        (Nat.le_trans (Nat.le_add_right _ _) (ligeritoSite_window_fits site)))
    leftPoint (by
      have : blindStateOffset ≤ ligeritoOffset := by decide
      unfold ligeritoSiteStart
      omega) hleftFiat hleft
  have hrightLength := rawQuery_afterZerocheck_fiat_length_ge shape causalSecret
    completion witness coins right
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      right right.isLt.le) rightPoint (by
        have : blindStateOffset ≤ ligeritoOffset := by decide
        unfold ligeritoSiteStart at hlt
        omega) hrightFiat hright
  omega

end VeiledFlock.ProductionSamplingScheduleLigeritoQueryFreshness

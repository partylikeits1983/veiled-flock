import VeiledFlock.ProductionSamplingScheduleLigeritoQueryFreshness

/-! # PoW-state projections of the literal production schedule -/

namespace VeiledFlock.ProductionSamplingSchedulePowState

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingLayoutBounds
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleLigeritoSegment
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawStep_blindGrinding_powState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (round : ℕ)
    (control : Control shape) (answer : OracleBlock)
    (hlower : blindGrindingOffset ≤ round)
    (hupper : round < blindChallengeOffset) :
    (rawStep shape causalSecret completion witness coins round control
      answer).powState = control.powState := by
  have hskip : ¬round < equalitySkipBlocks := by
    have : equalitySkipBlocks ≤ blindGrindingOffset := by decide
    omega
  have hequality : ¬round < zerocheckOffset := by
    have : zerocheckOffset ≤ blindGrindingOffset := by decide
    omega
  have hzero : ¬round < blindStateOffset := by
    have : blindStateOffset ≤ blindGrindingOffset := by decide
    omega
  have hstate : ¬round < blindGrindingOffset := by omega
  by_cases hstatus : control.status != .live
  · simp [rawStep, hstatus]
  · simp only [rawStep, hstatus, Bool.false_eq_true, ↓reduceIte, hskip,
      ↓reduceDIte, hequality, hzero, hstate, hupper]
    by_cases hdone : control.stageDone
    · simp [blindGrindingStep, hdone]
    · by_cases hgood : blindGrindingGood answer
      · simp [blindGrindingStep, hdone, hgood]
      · by_cases hcap : round - blindGrindingOffset + 1 = maxBlindTrials
        <;> simp [blindGrindingStep, hdone, hgood, hcap]

theorem iterateFrom_blindGrinding_powState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (rounds : ℕ)
    (hrounds : rounds ≤ maxBlindTrials) (control : Control shape)
    (answers : Fin rounds → OracleBlock) :
    (iterateFrom (rawStep shape causalSecret completion witness coins)
      blindGrindingOffset rounds control answers).powState = control.powState := by
  induction rounds with
  | zero => simp [iterateFrom, iterateList]
  | succ rounds ih =>
      rw [iterateFrom_succ_last,
        rawStep_blindGrinding_powState shape causalSecret completion witness
          coins (blindGrindingOffset + rounds) _ _ (by omega) (by
            rw [blindChallengeOffset_eq_grinding_end]
            omega),
        ih (hrounds := by omega)]

set_option maxRecDepth 10000 in
theorem rawControlUntil_blind_powState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (round : ℕ)
    (hlower : blindGrindingOffset ≤ round)
    (hupper : round ≤ blindChallengeOffset)
    (hstateLive :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots).status = .live) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      round (hupper.trans blindChallengeOffset_le_slots)).powState =
      some (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩) := by
  have hstate := rawControlUntil_succ shape causalSecret completion witness coins
    prelude answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩
  have hstart :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindGrindingOffset blindGrindingOffset_le_slots).powState =
        some (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩) := by
    have hpow := congrArg (fun control ↦ control.powState) hstate
    have hstep := rawStep_blindState shape causalSecret completion witness coins
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers blindStateOffset blindStateOffset_le_slots)
      (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩) hstateLive
    calc
      _ = (rawStep shape causalSecret completion witness coins blindStateOffset
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindStateOffset blindStateOffset_le_slots)
          (answers ⟨blindStateOffset, blindStateOffset_lt_slots⟩)).powState := by
            simpa only [blindGrindingOffset_eq_state_succ] using hpow
      _ = _ := by rw [hstep]
  have hfit : blindGrindingOffset + (round - blindGrindingOffset) ≤
      productionSamplingSlots := by
    rw [Nat.add_sub_of_le hlower]
    exact hupper.trans blindChallengeOffset_le_slots
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers blindGrindingOffset (round - blindGrindingOffset) hfit
  have hiter := iterateFrom_blindGrinding_powState shape causalSecret completion
    witness coins (round - blindGrindingOffset) (by
      rw [blindChallengeOffset_eq_grinding_end] at hupper
      omega)
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      blindGrindingOffset (Nat.le_trans (Nat.le_add_right _ _) hfit))
    (window blindGrindingOffset (round - blindGrindingOffset) hfit answers)
  have haddPow := congrArg (fun control ↦ control.powState) hadd
  have haddPow' :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers round (hupper.trans blindChallengeOffset_le_slots)).powState =
      (iterateFrom (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset (round - blindGrindingOffset)
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindGrindingOffset
            (Nat.le_trans (Nat.le_add_right _ _) hfit))
        (window blindGrindingOffset (round - blindGrindingOffset) hfit
          answers)).powState := by
    simpa only [Nat.add_sub_of_le hlower] using haddPow
  rw [haddPow', hiter]
  exact hstart

set_option maxRecDepth 10000 in
theorem rawStep_ligeritoGrinding_powState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials) (control : Control shape)
    (answer : OracleBlock) :
    (rawStep shape causalSecret completion witness coins
      (ligeritoSiteStart site + 1 + trial) control answer).powState =
      control.powState := by
  by_cases hstatus : control.status != .live
  · simp [rawStep, hstatus]
  · have hlive : control.status = .live := by
      cases h : control.status <;> simp [h] at hstatus ⊢
    rw [rawStep_ligeritoTrial shape causalSecret completion witness coins site
      trial htrial control answer hlive]
    unfold ligeritoStep
    have hoff := ligerito_trial_offset site trial htrial
    have htrialsPositive : maxLigeritoTrials ≠ 0 := by decide
    dsimp only
    rw [hoff.1, hoff.2]
    by_cases hdone : control.stageDone
    · simp [hdone]
    · by_cases hgood :
          VeiledFlock.ProductionGrindingProjection.rustLeadingZeroBitsAtLeast
            maxLigeritoBits (by decide) answer
      · by_cases hlast : site.val + 1 = maxLigeritoSites
        <;> simp [hdone, hgood, hlast]
      · by_cases hcap : 1 + trial = maxLigeritoTrials
        <;> simp [hdone, hgood, hcap, htrialsPositive]

theorem iterateFrom_ligeritoGrinding_powState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (rounds : ℕ)
    (hrounds : rounds ≤ maxLigeritoTrials) (control : Control shape)
    (answers : Fin rounds → OracleBlock) :
    (iterateFrom (rawStep shape causalSecret completion witness coins)
      (ligeritoSiteStart site + 1) rounds control answers).powState =
      control.powState := by
  induction rounds with
  | zero => simp [iterateFrom, iterateList]
  | succ rounds ih =>
      rw [iterateFrom_succ_last,
        rawStep_ligeritoGrinding_powState shape causalSecret completion witness
          coins site rounds (by omega),
        ih (hrounds := by omega)]

set_option maxRecDepth 10000 in
theorem rawControlUntil_ligerito_powState
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (site : Fin maxLigeritoSites) (round : ℕ)
    (hlower : ligeritoSiteStart site + 1 ≤ round)
    (hupper : round ≤ ligeritoSiteStart site + ligeritoSiteWidth)
    (hstateLive :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site)
          (ligeritoSiteStart_lt_slots site).le).status = .live) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      round (hupper.trans (ligeritoSite_window_fits site))).powState =
      some (answers ⟨ligeritoSiteStart site, ligeritoSiteStart_lt_slots site⟩) := by
  have hstate := rawControlUntil_succ shape causalSecret completion witness coins
    prelude answers
      ⟨ligeritoSiteStart site, ligeritoSiteStart_lt_slots site⟩
  have hstart :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (ligeritoSiteStart site + 1) (by
          exact hlower.trans (hupper.trans (ligeritoSite_window_fits site)))).powState =
        some (answers ⟨ligeritoSiteStart site,
          ligeritoSiteStart_lt_slots site⟩) := by
    have hpow := congrArg (fun control ↦ control.powState) hstate
    have hstep := rawStep_ligeritoStart shape causalSecret completion witness
      coins site
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site)
          (ligeritoSiteStart_lt_slots site).le)
      (answers ⟨ligeritoSiteStart site, ligeritoSiteStart_lt_slots site⟩)
      hstateLive
    calc
      _ = (rawStep shape causalSecret completion witness coins
          (ligeritoSiteStart site)
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (ligeritoSiteStart site)
              (ligeritoSiteStart_lt_slots site).le)
          (answers ⟨ligeritoSiteStart site,
            ligeritoSiteStart_lt_slots site⟩)).powState := by
              simpa only using hpow
      _ = _ := by rw [hstep, ligeritoStep_at_start]
  have hfit : (ligeritoSiteStart site + 1) +
      (round - (ligeritoSiteStart site + 1)) ≤ productionSamplingSlots := by
    rw [Nat.add_sub_of_le hlower]
    exact hupper.trans (ligeritoSite_window_fits site)
  have hadd := rawControlUntil_add shape causalSecret completion witness coins
    prelude answers (ligeritoSiteStart site + 1)
      (round - (ligeritoSiteStart site + 1)) hfit
  have hiter := iterateFrom_ligeritoGrinding_powState shape causalSecret
    completion witness coins site (round - (ligeritoSiteStart site + 1)) (by
      unfold ligeritoSiteWidth at hupper
      omega)
    (rawControlUntil shape causalSecret completion witness coins prelude answers
      (ligeritoSiteStart site + 1)
        (Nat.le_trans (Nat.le_add_right _ _) hfit))
    (window (ligeritoSiteStart site + 1)
      (round - (ligeritoSiteStart site + 1)) hfit answers)
  have haddPow := congrArg (fun control ↦ control.powState) hadd
  have haddPow' :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers round (hupper.trans (ligeritoSite_window_fits site))).powState =
      (iterateFrom (rawStep shape causalSecret completion witness coins)
        (ligeritoSiteStart site + 1)
        (round - (ligeritoSiteStart site + 1))
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (ligeritoSiteStart site + 1)
            (Nat.le_trans (Nat.le_add_right _ _) hfit))
        (window (ligeritoSiteStart site + 1)
          (round - (ligeritoSiteStart site + 1)) hfit answers)).powState := by
    simpa only [Nat.add_sub_of_le hlower] using haddPow
  rw [haddPow', hiter]
  exact hstart

end VeiledFlock.ProductionSamplingSchedulePowState

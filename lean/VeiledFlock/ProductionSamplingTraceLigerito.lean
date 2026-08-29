import VeiledFlock.ProductionSamplingTraceBlind
import VeiledFlock.ProductionSamplingScheduleWholeSuccess

/-! # First-success Ligerito-site grinding refinement -/

namespace VeiledFlock.ProductionSamplingTraceLigerito

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingTraceEquality
open VeiledFlock.ProductionSamplingTraceScalar
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.ProductionSamplingScheduleWhole

theorem ligeritoPrefix_le_slots (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial ≤ maxLigeritoTrials) :
    ligeritoSiteStart site + 1 + trial ≤ productionSamplingSlots := by
  have hfit := ligeritoGrinding_window_fits site
  unfold ligeritoSiteStart at ⊢
  omega

theorem ligeritoTrial_lt_slots (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials) :
    ligeritoSiteStart site + 1 + trial < productionSamplingSlots := by
  have hfit := ligeritoGrinding_window_fits site
  unfold ligeritoSiteStart at ⊢
  omega

theorem ligeritoTrialOffset_lt_slots (site : Fin maxLigeritoSites)
    (trial remaining : ℕ) (hcap : trial + remaining ≤ maxLigeritoTrials)
    (offset : Fin remaining) :
    ligeritoSiteStart site + 1 + trial + offset.val <
      productionSamplingSlots := by
  have hfit := ligeritoGrinding_window_fits site
  unfold ligeritoSiteStart at ⊢
  omega

theorem ligeritoSiteEnd_le_slots (site : Fin maxLigeritoSites) :
    ligeritoSiteStart site + ligeritoSiteWidth ≤ productionSamplingSlots := by
  simpa only [ligeritoSiteStart, ligeritoSiteWidth, Nat.add_assoc] using
    ligeritoGrinding_window_fits site

set_option maxRecDepth 10000 in
theorem rawQuery_ligerito_start
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (control : Control shape)
    (hstatus : control.status = .live) :
    rawQuery shape causalSecret completion witness coins
        (ligeritoSiteStart site) control =
      some (scalarPoint control.transcript) := by
  have hlig : ligeritoSiteStart site < productionSamplingSlots := by
    unfold ligeritoSiteStart productionSamplingSlots ligeritoWidth
    have hwidth : 0 < ligeritoSiteWidth := by
      unfold ligeritoSiteWidth
      omega
    nlinarith [site.isLt]
  have hbefore : ligeritoOffset ≤ ligeritoSiteStart site := by
    unfold ligeritoSiteStart
    omega
  unfold rawQuery
  rw [if_neg (by simp [hstatus])]
  simp only [
    dif_neg (not_before_ligerito (by decide : equalitySkipBlocks ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : zerocheckOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindStateOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindGrindingOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : multiplicationAlphaOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : productCoefficientOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_lt_of_ge hbefore), dif_pos hlig]
  rw [(ligerito_start_offset site).1]
  simp

set_option maxRecDepth 10000 in
theorem rawQuery_ligerito_trial
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials)
    (control : Control shape) (state : Nonce256)
    (hstatus : control.status = .live)
    (hactive : control.stageDone = false)
    (hstate : control.powState = some state) :
    rawQuery shape causalSecret completion witness coins
        (ligeritoSiteStart site + 1 + trial) control =
      some (encodePowPoint state (BitVec.ofNat 64 trial)) := by
  have hlig : ligeritoSiteStart site + 1 + trial <
      productionSamplingSlots := by
    unfold ligeritoSiteStart productionSamplingSlots ligeritoWidth
    unfold ligeritoSiteWidth
    nlinarith [site.isLt]
  have hbefore : ligeritoOffset ≤ ligeritoSiteStart site + 1 + trial := by
    unfold ligeritoSiteStart
    omega
  unfold rawQuery
  rw [if_neg (by simp [hstatus])]
  simp only [
    dif_neg (not_before_ligerito (by decide : equalitySkipBlocks ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : zerocheckOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindStateOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindGrindingOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : blindChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : multiplicationAlphaOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerChallengeOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : outerPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : linearRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardPositionsOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : hadamardRhoOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_before_ligerito (by decide : productCoefficientOffset ≤ ligeritoOffset) hbefore),
    dif_neg (not_lt_of_ge hbefore), dif_pos hlig]
  have hoff := ligerito_trial_offset site trial htrial
  rw [hoff.1]
  have hpositive : 1 + trial ≠ 0 := by omega
  simp [hpositive, hactive, hstate]

set_option maxRecDepth 10000 in
theorem rawControlUntil_ligerito_stable_of_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (site : Fin maxLigeritoSites)
    (trial remaining : ℕ) (hsum : trial + remaining = maxLigeritoTrials)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site + 1 + trial) (by
          exact ligeritoPrefix_le_slots site trial (by omega))).status =
        ligeritoSiteTerminalStatus site)
    (hdone :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site + 1 + trial) (by
          exact ligeritoPrefix_le_slots site trial (by omega))).stageDone = true) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (ligeritoSiteStart site + ligeritoSiteWidth) (by
          exact ligeritoSiteEnd_le_slots site) =
      rawControlUntil shape causalSecret completion witness coins prelude answers
        (ligeritoSiteStart site + 1 + trial) (by
          exact ligeritoPrefix_le_slots site trial (by omega)) := by
  induction remaining generalizing trial with
  | zero =>
      have htrial : trial = maxLigeritoTrials := by omega
      subst trial
      congr 1 <;> simp [ligeritoSiteWidth]
  | succ remaining ih =>
      have htrial : trial < maxLigeritoTrials := by omega
      let round : Fin productionSamplingSlots :=
        ⟨ligeritoSiteStart site + 1 + trial, by
          exact ligeritoTrial_lt_slots site trial htrial⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (ligeritoSiteStart site + 1 + trial) round.isLt.le
      have hstatus' : current.status = ligeritoSiteTerminalStatus site := hstatus
      have hdone' : current.stageDone = true := hdone
      have hsucc := rawControlUntil_succ shape causalSecret completion witness
        coins prelude answers round
      have hstep := rawStep_ligeritoTrial_preserves_terminal shape causalSecret
        completion witness coins site trial htrial current (answers round)
        hstatus' hdone'
      rw [hstep] at hsucc
      let next := rawControlUntil shape causalSecret completion witness coins
        prelude answers (ligeritoSiteStart site + 1 + (trial + 1)) (by
          exact ligeritoPrefix_le_slots site (trial + 1) (by omega))
      have hnext : next = current := by
        simpa only [next, current, round, Nat.add_assoc] using hsucc
      have hnextStatus : next.status = ligeritoSiteTerminalStatus site := by
        rw [hnext]
        exact hstatus'
      have hnextDone : next.stageDone = true := by rw [hnext]; exact hdone'
      rw [ih (trial + 1) (by omega) hnextStatus hnextDone]
      exact hnext

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem grindFrom_ligerito_site_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (site : Fin maxLigeritoSites) (state : Nonce256)
    (trial remaining : ℕ) (hcap : trial + remaining ≤ maxLigeritoTrials)
    (hstatus :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site + 1 + trial) (by
          exact ligeritoPrefix_le_slots site trial (by omega))).status = .live)
    (hactive :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site + 1 + trial) (by
          exact ligeritoPrefix_le_slots site trial (by omega))).stageDone = false)
    (hstate :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site + 1 + trial) (by
          exact ligeritoPrefix_le_slots site trial (by omega))).powState = some state)
    (hexists : ∃ offset : Fin remaining,
      rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (answers ⟨ligeritoSiteStart site + 1 + trial + offset.val, by
          exact ligeritoTrialOffset_lt_slots site trial remaining hcap offset⟩)) :
    ∃ nonce,
      grindFrom (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide))
          oracle state trial remaining = some nonce ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site + ligeritoSiteWidth) (by
          exact ligeritoSiteEnd_le_slots site)).transcript =
        afterGrind
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (ligeritoSiteStart site + 1 + trial) (by
              exact ligeritoPrefix_le_slots site trial (by omega))).transcript nonce := by
  induction remaining generalizing trial with
  | zero => simp at hexists
  | succ remaining ih =>
      have htrial : trial < maxLigeritoTrials := by
        rcases hexists with ⟨offset, _⟩
        omega
      let round : Fin productionSamplingSlots :=
        ⟨ligeritoSiteStart site + 1 + trial, by
          exact ligeritoTrial_lt_slots site trial htrial⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (ligeritoSiteStart site + 1 + trial) round.isLt.le
      have hstatus' : current.status = .live := hstatus
      have hactive' : current.stageDone = false := hactive
      have hstate' : current.powState = some state := hstate
      have hquery : rawQuery shape causalSecret completion witness coins round
          current = some (encodePowPoint state (BitVec.ofNat 64 trial)) := by
        simpa only [round, current] using rawQuery_ligerito_trial shape
          causalSecret completion witness coins site trial htrial current state
          hstatus' hactive' hstate'
      have horacle : oracle (encodePowPoint state (BitVec.ofNat 64 trial)) =
          answers round := (hagrees round _ hquery).symm
      by_cases hgood : rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
          (answers round)
      · let nonce : Word64 := BitVec.ofNat 64 trial
        have hgrind : grindFrom
            (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)) oracle state trial
            (remaining + 1) = some nonce := by
          simp only [grindFrom, nonce]
          rw [horacle]
          simp [hgood]
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers round
        have hstep := rawStep_ligeritoTrial shape causalSecret completion witness
          coins site trial htrial current (answers round) hstatus'
        rw [hstep] at hsucc
        let next := rawControlUntil shape causalSecret completion witness coins
          prelude answers (ligeritoSiteStart site + 1 + (trial + 1)) (by
            exact ligeritoPrefix_le_slots site (trial + 1) (by omega))
        have hsucc' : next = ligeritoStep
            (ligeritoSiteStart site + 1 + trial) current (answers round) := by
          simpa only [next, round, Nat.add_assoc] using hsucc
        have hterminal := ligeritoStep_trial_good site trial htrial current
          (answers round) hstatus' hactive' hgood
        have hnextStatus : next.status = ligeritoSiteTerminalStatus site := by
          rw [hsucc']
          exact hterminal.1
        have hnextDone : next.stageDone = true := by rw [hsucc']; exact hterminal.2
        have hnextTranscript : next.transcript =
            afterGrind current.transcript nonce := by
          rw [hsucc']
          have hoff := ligerito_trial_offset site trial htrial
          unfold ligeritoStep
          dsimp only
          rw [hoff.1, hoff.2]
          simp [hactive', show rustLeadingZeroBitsAtLeast maxLigeritoBits
            (by decide) (answers round) from hgood, nonce]
          split <;> rfl
        have hstable := rawControlUntil_ligerito_stable_of_done shape
          causalSecret completion witness coins prelude answers site (trial + 1)
          (maxLigeritoTrials - (trial + 1)) (by omega) hnextStatus hnextDone
        refine ⟨nonce, hgrind, ?_⟩
        rw [congrArg Control.transcript hstable]
        exact hnextTranscript
      · have hremainingPos : 0 < remaining := by
          by_contra hzero
          have hremainingZero : remaining = 0 := by omega
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetZero : offset.val = 0 := by omega
          exact hgood (by simpa [round, hoffsetZero] using hoffset)
        have hsucc := rawControlUntil_succ shape causalSecret completion witness
          coins prelude answers round
        have hstep := rawStep_ligeritoTrial shape causalSecret completion witness
          coins site trial htrial current (answers round) hstatus'
        rw [hstep] at hsucc
        let next := rawControlUntil shape causalSecret completion witness coins
          prelude answers (ligeritoSiteStart site + 1 + (trial + 1)) (by
            exact ligeritoPrefix_le_slots site (trial + 1) (by omega))
        have hsucc' : next = ligeritoStep
            (ligeritoSiteStart site + 1 + trial) current (answers round) := by
          simpa only [next, round, Nat.add_assoc] using hsucc
        have hnotCap : trial + 1 ≠ maxLigeritoTrials := by
          rcases hexists with ⟨offset, hoffset⟩
          by_contra heq
          have hremainingZero : remaining = 0 := by omega
          have hoffsetZero : offset.val = 0 := by omega
          exact hgood (by simpa [round, hoffsetZero] using hoffset)
        have hbad := ligeritoStep_trial_bad_before_cap site trial (by omega)
          current (answers round) hstatus' hactive' hgood
        have hnextStatus : next.status = .live := by rw [hsucc']; exact hbad.1
        have hnextActive : next.stageDone = false := by rw [hsucc']; exact hbad.2
        have hnextState : next.powState = some state := by
          rw [hsucc']
          have hoff := ligerito_trial_offset site trial htrial
          unfold ligeritoStep
          dsimp only
          rw [hoff.1, hoff.2]
          simp [hactive', show ¬rustLeadingZeroBitsAtLeast maxLigeritoBits
            (by decide) (answers round) from hgood, hnotCap, hstate']
          split <;> rfl
        have hnextTranscript : next.transcript = current.transcript := by
          rw [hsucc']
          have hoff := ligerito_trial_offset site trial htrial
          unfold ligeritoStep
          dsimp only
          rw [hoff.1, hoff.2]
          simp [hactive', show ¬rustLeadingZeroBitsAtLeast maxLigeritoBits
            (by decide) (answers round) from hgood, hnotCap]
          split <;> rfl
        have hnextExists : ∃ offset : Fin remaining,
            rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
              (answers ⟨ligeritoSiteStart site + 1 + (trial + 1) +
                  offset.val, by
                    exact ligeritoTrialOffset_lt_slots site (trial + 1)
                      remaining (by omega) offset⟩) := by
          rcases hexists with ⟨offset, hoffset⟩
          have hoffsetPos : 0 < offset.val := by
            by_contra hzero
            have hoffsetZero : offset.val = 0 := by omega
            exact hgood (by simpa [round, hoffsetZero] using hoffset)
          let prior : Fin remaining := ⟨offset.val - 1, by omega⟩
          refine ⟨prior, ?_⟩
          have hindex :
              (⟨ligeritoSiteStart site + 1 + (trial + 1) + prior.val, by
                exact ligeritoTrialOffset_lt_slots site (trial + 1)
                  remaining (by omega) prior⟩ :
                  Fin productionSamplingSlots) =
              ⟨ligeritoSiteStart site + 1 + trial + offset.val, by
                exact ligeritoTrialOffset_lt_slots site trial (remaining + 1)
                  hcap offset⟩ := by
            apply Fin.ext
            dsimp only [prior]
            omega
          rw [hindex]
          exact hoffset
        rcases ih (trial + 1) (by omega) hnextStatus hnextActive hnextState
            hnextExists with ⟨nonce, hgrind, htranscript⟩
        refine ⟨nonce, ?_, ?_⟩
        · simp only [grindFrom]
          rw [horacle]
          simp [hgood]
          exact hgrind
        · rw [← hnextTranscript]
          exact htranscript

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem grindLigeritoSites_from_index_some
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (oracle : List Byte → OracleBlock)
    (hagrees : RawAnswersOracleAgreement shape causalSecret completion witness
      coins prelude answers oracle)
    (hstart : (rawControlUntil shape causalSecret completion witness coins
      prelude answers ligeritoOffset (by decide)).status = .live)
    (hgrind : ∀ site : Fin maxLigeritoSites,
      ∃ trial : Fin maxLigeritoTrials,
        rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
          (window (ligeritoSiteStart site + 1) maxLigeritoTrials
            (ligeritoGrinding_window_fits site) answers trial))
    (siteIndex remaining : ℕ)
    (hsum : siteIndex + remaining = maxLigeritoSites)
    (transcript : List Byte)
    (htranscript :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoOffset + siteIndex * ligeritoSiteWidth) (by
          unfold productionSamplingSlots ligeritoWidth
          have hwidth : 0 < ligeritoSiteWidth := by
            unfold ligeritoSiteWidth
            omega
          nlinarith)).transcript = transcript) :
    ∃ nonces finalTranscript,
      grindLigeritoSites oracle remaining transcript =
          some (nonces, finalTranscript) ∧
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers productionSamplingSlots (by rfl)).transcript = finalTranscript := by
  induction remaining generalizing siteIndex transcript with
  | zero =>
      have hindex : siteIndex = maxLigeritoSites := by omega
      subst siteIndex
      refine ⟨[], transcript, ?_, ?_⟩
      · simp [grindLigeritoSites]
      · simpa [productionSamplingSlots, ligeritoWidth] using htranscript
  | succ remaining ih =>
      have hsiteLt : siteIndex < maxLigeritoSites := by omega
      let site : Fin maxLigeritoSites := ⟨siteIndex, hsiteLt⟩
      let current := rawControlUntil shape causalSecret completion witness coins
        prelude answers (ligeritoSiteStart site) (by
          exact Nat.le_trans (Nat.le_add_right _ _)
            (ligeritoSiteEnd_le_slots site))
      have hprefix := rawControlUntil_ligerito_prefix_status shape causalSecret
        completion witness coins prelude answers hstart hgrind siteIndex (by omega)
      have hstatus : current.status = .live := by
        simpa [current, site, ligeritoSiteStart,
          show siteIndex ≠ maxLigeritoSites by omega] using hprefix
      have hcurrentTranscript : current.transcript = transcript := by
        simpa only [current, site, ligeritoSiteStart] using htranscript
      let startRound : Fin productionSamplingSlots :=
        ⟨ligeritoSiteStart site, by
          have hfit := ligeritoSiteEnd_le_slots site
          have hwidth : 0 < ligeritoSiteWidth := by
            unfold ligeritoSiteWidth
            omega
          omega⟩
      have hquery : rawQuery shape causalSecret completion witness coins
          startRound current = some (scalarPoint current.transcript) := by
        simpa only [startRound] using rawQuery_ligerito_start shape causalSecret
          completion witness coins site current hstatus
      have horacleCurrent : oracle (scalarPoint current.transcript) =
          answers startRound := (hagrees startRound _ hquery).symm
      have horacleTranscript : oracle (scalarPoint transcript) =
          answers startRound := by
        rw [← hcurrentTranscript]
        exact horacleCurrent
      have hsucc := rawControlUntil_succ shape causalSecret completion witness
        coins prelude answers startRound
      have hstep := rawStep_ligeritoStart shape causalSecret completion witness
        coins site current (answers startRound) hstatus
      rw [hstep, ligeritoStep_at_start] at hsucc
      let withState := rawControlUntil shape causalSecret completion witness coins
        prelude answers (ligeritoSiteStart site + 1) (by
          exact ligeritoPrefix_le_slots site 0 (by omega))
      have hwithState : withState =
          { current with
            powState := some (answers startRound)
            stageDone := false
            stageBlocks := [] } := by
        simpa only [withState, startRound] using hsucc
      have hwithStatus : withState.status = .live := by
        rw [hwithState]
        exact hstatus
      have hwithDone : withState.stageDone = false := by simp [hwithState]
      have hwithPow : withState.powState = some (answers startRound) := by
        simp [hwithState]
      have hexists : ∃ offset : Fin maxLigeritoTrials,
          rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
            (answers ⟨ligeritoSiteStart site + 1 + offset.val, by
              exact ligeritoTrialOffset_lt_slots site 0 maxLigeritoTrials
                (by omega) offset⟩) := by
        rcases hgrind site with ⟨trial, htrial⟩
        refine ⟨trial, ?_⟩
        simpa [FixedWindowProbability.window] using htrial
      have hsiteResult := grindFrom_ligerito_site_some shape causalSecret
        completion witness coins prelude answers oracle hagrees site
        (answers startRound) 0 maxLigeritoTrials (by omega) hwithStatus
        (by simpa only [withState] using hwithDone)
        (by simpa only [withState] using hwithPow) hexists
      rcases hsiteResult with ⟨nonce, hnonce, hsiteTranscript⟩
      have hnonce' : grindPowBounded
          (rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)) oracle
          (answers startRound) maxLigeritoTrials = some nonce := by
        simpa only [grindPowBounded] using hnonce
      have hnextTranscript :
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (ligeritoOffset + (siteIndex + 1) * ligeritoSiteWidth) (by
              simpa [site, ligeritoSiteStart, Nat.add_mul, Nat.add_assoc] using
                ligeritoSiteEnd_le_slots site)).transcript =
            afterGrind transcript nonce := by
        have hsiteTranscript' := hsiteTranscript
        have hwithTranscript :
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers (ligeritoSiteStart site + 1 + 0) (by
                exact ligeritoPrefix_le_slots site 0 (by omega))).transcript =
              current.transcript := by
          have hprojection := congrArg Control.transcript hwithState
          simpa only [withState, Nat.add_zero] using hprojection
        rw [hwithTranscript, hcurrentTranscript] at hsiteTranscript'
        have htransport := rawControlUntil_round_eq shape causalSecret
          completion witness coins prelude answers
          (left := ligeritoOffset + (siteIndex + 1) * ligeritoSiteWidth)
          (right := ligeritoSiteStart site + ligeritoSiteWidth)
          (by
            simpa [site, ligeritoSiteStart, Nat.add_mul, Nat.add_assoc] using
              ligeritoSiteEnd_le_slots site)
          (ligeritoSiteEnd_le_slots site)
          (by simp [site, ligeritoSiteStart, Nat.add_mul, Nat.add_assoc])
        exact (congrArg Control.transcript htransport).trans hsiteTranscript'
      rcases ih (siteIndex + 1) (by omega) (afterGrind transcript nonce)
          hnextTranscript with ⟨nonces, finalTranscript, hrest, hfinal⟩
      refine ⟨nonce :: nonces, finalTranscript, ?_, hfinal⟩
      simp only [grindLigeritoSites]
      rw [horacleTranscript, hnonce']
      simp [hrest]

end VeiledFlock.ProductionSamplingTraceLigerito

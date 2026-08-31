import VeiledFlock.Production.Sampling.SamplingSchedulePowRange

/-! # Concrete origins of production PoW oracle queries -/

namespace VeiledFlock.ProductionSamplingSchedulePowOrigin

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleLigeritoSegment
open VeiledFlock.ProductionSamplingSchedulePowRange
open VeiledFlock.ProductionSamplingSchedulePowState
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionSamplingScheduleWhole

structure ProductionPowOrigin where
  site : Fin powStateCount
  nonce : ℕ
  nonce_lt : nonce < 2 ^ 64

def ProductionPowOrigin.round (origin : ProductionPowOrigin) : ℕ :=
  if origin.site.val = 0 then blindGrindingOffset + origin.nonce
  else ligeritoOffset + (origin.site.val - 1) * ligeritoSiteWidth + 1 +
    origin.nonce

def ProductionPowOrigin.point (answers : SamplingAnswerTape)
    (origin : ProductionPowOrigin) : List Byte :=
  encodePowPoint (answers (powStateIndex origin.site))
    (BitVec.ofNat 64 origin.nonce)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_blind_pow_origin
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (round : Fin productionSamplingSlots) (point : List Byte)
    (hlower : blindGrindingOffset ≤ round.val)
    (hupper : round.val < blindChallengeOffset)
    (hquery : rawQuery shape causalSecret completion witness coins round
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers round round.isLt.le) = some point) :
    ∃ origin : ProductionPowOrigin,
      round.val = origin.round ∧ point = origin.point answers := by
  have hequality := rawControlUntil_equality_live_some shape causalSecret
    completion witness coins prelude answers
    (equality_accepted_of_not_globalBad shape answers hgood)
  have hzero := rawControlUntil_zerocheck_live_some shape causalSecret completion
    witness coins prelude answers hequality
  have hpowState := rawControlUntil_blind_powState shape causalSecret completion
    witness coins prelude answers round.val hlower hupper.le hzero.1
  let control := rawControlUntil shape causalSecret completion witness coins
    prelude answers round round.isLt.le
  change rawQuery shape causalSecret completion witness coins round control =
    some point at hquery
  have hstatus : control.status = .live := by
    by_contra hnot
    have hne : control.status != .live := by
      cases h : control.status <;> simp [h] at hnot ⊢
    simp [rawQuery, hne] at hquery
  have hskip : ¬ round.val < equalitySkipBlocks := by
    have : equalitySkipBlocks ≤ blindGrindingOffset := by decide
    omega
  have heq : ¬ round.val < zerocheckOffset := by
    have : zerocheckOffset ≤ blindGrindingOffset := by decide
    omega
  have hz : ¬ round.val < blindStateOffset := by
    have : blindStateOffset ≤ blindGrindingOffset := by decide
    omega
  have hstate : ¬ round.val < blindGrindingOffset := by omega
  have hpowState' : control.powState =
      some (answers ⟨blindStateOffset,
        VeiledFlock.ProductionSamplingLayoutBounds.blindStateOffset_lt_slots⟩) := by
    dsimp only [control]
    exact hpowState
  have hpoint : point = encodePowPoint
      (answers ⟨blindStateOffset,
        VeiledFlock.ProductionSamplingLayoutBounds.blindStateOffset_lt_slots⟩)
      (BitVec.ofNat 64 (round.val - blindGrindingOffset)) := by
    simp [rawQuery, hstatus, hskip, heq, hz, hstate, hupper, hpowState']
      at hquery
    exact hquery.2.symm
  let origin : ProductionPowOrigin :=
    { site := ⟨0, by unfold powStateCount; omega⟩
      nonce := round.val - blindGrindingOffset
      nonce_lt := by
        have htrials : round.val - blindGrindingOffset < maxBlindTrials := by
          rw [show blindChallengeOffset = blindGrindingOffset + maxBlindTrials
            by rfl] at hupper
          omega
        exact htrials.trans (by decide) }
  refine ⟨origin, ?_, ?_⟩
  · simp [ProductionPowOrigin.round, origin]
    omega
  · rw [hpoint]
    unfold ProductionPowOrigin.point
    apply congrArg₂ encodePowPoint
    · apply congrArg answers
      apply Fin.ext
      simp [origin, powStateIndex]
    · rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_ligerito_pow_origin
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (round : Fin productionSamplingSlots) (point : List Byte)
    (hlower : ligeritoOffset ≤ round.val)
    (hwithin : (round.val - ligeritoOffset) % ligeritoSiteWidth ≠ 0)
    (hquery : rawQuery shape causalSecret completion witness coins round
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers round round.isLt.le) = some point) :
    ∃ origin : ProductionPowOrigin,
      round.val = origin.round ∧ point = origin.point answers := by
  let offset := round.val - ligeritoOffset
  let siteNat := offset / ligeritoSiteWidth
  let within := offset % ligeritoSiteWidth
  have hwidth : 0 < ligeritoSiteWidth := by
    unfold ligeritoSiteWidth
    omega
  have hoffsetLt : offset < maxLigeritoSites * ligeritoSiteWidth := by
    have := round.isLt
    unfold productionSamplingSlots ligeritoWidth at this
    dsimp only [offset]
    omega
  have hsiteNat : siteNat < maxLigeritoSites := by
    dsimp only [siteNat]
    exact (Nat.div_lt_iff_lt_mul hwidth).2 (by
      simpa only [Nat.mul_comm] using hoffsetLt)
  let site : Fin maxLigeritoSites := ⟨siteNat, hsiteNat⟩
  have hoffset : offset = site.val * ligeritoSiteWidth + within := by
    dsimp only [site, siteNat, within]
    simpa only [Nat.add_comm, Nat.mul_comm] using
      (Nat.mod_add_div offset ligeritoSiteWidth).symm
  have hwithinPositive : 0 < within := by
    exact Nat.pos_of_ne_zero (by
      dsimp only [within]
      exact hwithin)
  have hwithinUpper : within < ligeritoSiteWidth := by
    dsimp only [within]
    exact Nat.mod_lt _ hwidth
  have hroundSite :
      round.val = ligeritoSiteStart site + 1 + (within - 1) := by
    have hroundOffset : round.val = ligeritoOffset + offset := by
      dsimp only [offset]
      omega
    unfold ligeritoSiteStart
    omega
  have htrial : within - 1 < maxLigeritoTrials := by
    unfold ligeritoSiteWidth at hwithinUpper
    omega
  have hstart := rawControlUntil_ligerito_live_of_not_globalBad shape
    causalSecret completion witness coins prelude answers hgood
  have hprefix := rawControlUntil_ligerito_prefix_status shape causalSecret
    completion witness coins prelude answers hstart
    (exists_ligeritoGrinding_answer_of_not_globalBad shape answers hgood)
    site.val site.isLt.le
  have hsiteLive :
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers (ligeritoSiteStart site)
          (ligeritoSiteStart_lt_slots site).le).status = .live := by
    unfold ligeritoSiteStart
    simpa [show site.val ≠ maxLigeritoSites by omega] using hprefix
  have hpowState := rawControlUntil_ligerito_powState shape causalSecret
    completion witness coins prelude answers site round.val (by omega)
    (by rw [hroundSite]; unfold ligeritoSiteWidth; omega) hsiteLive
  let control := rawControlUntil shape causalSecret completion witness coins
    prelude answers round round.isLt.le
  change rawQuery shape causalSecret completion witness coins round control =
    some point at hquery
  have hstatus : control.status = .live := by
    by_contra hnot
    have hne : control.status != .live := by
      cases h : control.status <;> simp [h] at hnot ⊢
    simp [rawQuery, hne] at hquery
  have hskip : ¬ round.val < equalitySkipBlocks :=
    not_lt_of_ge ((by decide : equalitySkipBlocks ≤ ligeritoOffset).trans hlower)
  have hequality : ¬ round.val < zerocheckOffset :=
    not_lt_of_ge ((by decide : zerocheckOffset ≤ ligeritoOffset).trans hlower)
  have hzero : ¬ round.val < blindStateOffset :=
    not_lt_of_ge ((by decide : blindStateOffset ≤ ligeritoOffset).trans hlower)
  have hblindState : ¬ round.val < blindGrindingOffset :=
    not_lt_of_ge ((by decide : blindGrindingOffset ≤ ligeritoOffset).trans
      hlower)
  have hblindGrind : ¬ round.val < blindChallengeOffset :=
    not_lt_of_ge ((by decide : blindChallengeOffset ≤ ligeritoOffset).trans
      hlower)
  have hblind : ¬ round.val < multiplicationAlphaOffset :=
    not_lt_of_ge
      ((by decide : multiplicationAlphaOffset ≤ ligeritoOffset).trans hlower)
  have halpha : ¬ round.val < outerChallengeOffset :=
    not_lt_of_ge ((by decide : outerChallengeOffset ≤ ligeritoOffset).trans
      hlower)
  have houterChallenge : ¬ round.val < outerPositionsOffset :=
    not_lt_of_ge ((by decide : outerPositionsOffset ≤ ligeritoOffset).trans
      hlower)
  have houterPositions : ¬ round.val < linearPositionsOffset :=
    not_lt_of_ge ((by decide : linearPositionsOffset ≤ ligeritoOffset).trans
      hlower)
  have hlinearPositions : ¬ round.val < linearRhoOffset :=
    not_lt_of_ge ((by decide : linearRhoOffset ≤ ligeritoOffset).trans hlower)
  have hlinearRho : ¬ round.val < hadamardPositionsOffset :=
    not_lt_of_ge
      ((by decide : hadamardPositionsOffset ≤ ligeritoOffset).trans hlower)
  have hhadamardPositions : ¬ round.val < hadamardRhoOffset :=
    not_lt_of_ge ((by decide : hadamardRhoOffset ≤ ligeritoOffset).trans
      hlower)
  have hhadamardRho : ¬ round.val < productCoefficientOffset :=
    not_lt_of_ge
      ((by decide : productCoefficientOffset ≤ ligeritoOffset).trans hlower)
  have hproduct : ¬ round.val < ligeritoOffset := not_lt_of_ge hlower
  have hpowState' : control.powState =
      some (answers ⟨ligeritoSiteStart site, ligeritoSiteStart_lt_slots site⟩) := by
    dsimp only [control]
    exact hpowState
  have hpoint : point = encodePowPoint
      (answers ⟨ligeritoSiteStart site, ligeritoSiteStart_lt_slots site⟩)
      (BitVec.ofNat 64 (within - 1)) := by
    simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState, hblindGrind,
      hblind, halpha, houterChallenge, houterPositions, hlinearPositions,
      hlinearRho, hhadamardPositions, hhadamardRho, hproduct,
      hwithin, hpowState'] at hquery
    exact hquery.2.symm
  let origin : ProductionPowOrigin :=
    { site := ⟨site.val + 1, by unfold powStateCount; omega⟩
      nonce := within - 1
      nonce_lt := htrial.trans (by decide) }
  refine ⟨origin, ?_, ?_⟩
  · simp [ProductionPowOrigin.round, origin]
    rw [hroundSite]
    unfold ligeritoSiteStart
    omega
  · rw [hpoint]
    unfold ProductionPowOrigin.point
    apply congrArg₂ encodePowPoint
    · apply congrArg answers
      apply Fin.ext
      simp [origin, powStateIndex, ligeritoSiteStart]
    · rfl

theorem rawQuery_pow_origin
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (round : Fin productionSamplingSlots) (point : List Byte)
    (hquery : rawQuery shape causalSecret completion witness coins round
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers round round.isLt.le) = some point)
    (hnotFiat : ¬ isFiatShamirPoint point) :
    ∃ origin : ProductionPowOrigin,
      round.val = origin.round ∧ point = origin.point answers := by
  rcases rawQuery_nonFiat_range shape causalSecret completion witness coins
    prelude hprelude answers round point hquery hnotFiat with hblind | hligerito
  · exact rawQuery_blind_pow_origin shape causalSecret completion witness coins
      prelude answers hgood round point hblind.1 hblind.2 hquery
  · exact rawQuery_ligerito_pow_origin shape causalSecret completion witness
      coins prelude answers hgood round point hligerito.1 hligerito.2 hquery

end VeiledFlock.ProductionSamplingSchedulePowOrigin

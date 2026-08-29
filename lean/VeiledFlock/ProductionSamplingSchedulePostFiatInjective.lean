import VeiledFlock.ProductionSamplingSchedulePowState

/-! # Pairwise separation of post-zerocheck Fiat--Shamir inputs -/

namespace VeiledFlock.ProductionSamplingSchedulePostFiatInjective

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindQueryFreshness
open VeiledFlock.ProductionSamplingScheduleLigeritoQueryFreshness
open VeiledFlock.ProductionSamplingScheduleLigeritoSegment
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleQueryFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem post_fiat_query_length_strict
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (left right : Fin productionSamplingSlots)
    (hleftLower : blindStateOffset ≤ left.val)
    (hlt : left.val < right.val) (leftPoint rightPoint : List Byte)
    (hleftFiat : isFiatShamirPoint leftPoint)
    (hrightFiat : isFiatShamirPoint rightPoint)
    (hleft : rawQuery shape causalSecret completion witness coins left
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers left left.isLt.le) = some leftPoint)
    (hright : rawQuery shape causalSecret completion witness coins right
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers right right.isLt.le) = some rightPoint) :
    leftPoint.length < rightPoint.length := by
  by_cases hstate : isPowStateRound left.val
  · rcases hstate with hblind | hligerito
    · have hleft' : rawQuery shape causalSecret completion witness coins
          blindStateOffset
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindStateOffset
              VeiledFlock.ProductionSamplingLayoutBounds.blindStateOffset_le_slots) =
            some leftPoint := by
        simpa only [hblind] using hleft
      exact blind_state_fiat_query_length_strict shape causalSecret completion
        witness coins prelude answers hgood right (by omega) leftPoint rightPoint
        hleftFiat hrightFiat hleft' hright
    · let offset := left.val - ligeritoOffset
      let siteNat := offset / ligeritoSiteWidth
      have hwidth : 0 < ligeritoSiteWidth := by
        unfold ligeritoSiteWidth
        omega
      have hoffsetLt : offset < maxLigeritoSites * ligeritoSiteWidth := by
        have hleftSlots := left.isLt
        unfold productionSamplingSlots ligeritoWidth at hleftSlots
        dsimp only [offset]
        omega
      have hsiteNat : siteNat < maxLigeritoSites := by
        dsimp only [siteNat]
        exact (Nat.div_lt_iff_lt_mul hwidth).2 (by
          simpa only [Nat.mul_comm] using hoffsetLt)
      let site : Fin maxLigeritoSites := ⟨siteNat, hsiteNat⟩
      have hoffset :
          offset = site.val * ligeritoSiteWidth := by
        have hdiv := Nat.mod_add_div offset ligeritoSiteWidth
        dsimp only [site, siteNat]
        rw [hligerito.2] at hdiv
        simpa only [Nat.zero_add, Nat.mul_comm] using hdiv.symm
      have hleftEq : left.val = ligeritoSiteStart site := by
        unfold ligeritoSiteStart
        dsimp only [offset] at hoffset
        omega
      have hleft' : rawQuery shape causalSecret completion witness coins
          (ligeritoSiteStart site)
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers (ligeritoSiteStart site)
              (Nat.le_trans (Nat.le_add_right _ _)
                (ligeritoSite_window_fits site))) = some leftPoint := by
        simpa only [hleftEq] using hleft
      exact ligerito_state_fiat_query_length_strict shape causalSecret
        completion witness coins prelude answers hgood site right (by omega)
        leftPoint rightPoint hleftFiat hrightFiat hleft' hright
  · exact regular_post_fiat_query_length_strict shape causalSecret completion
      witness coins prelude answers left right hleftLower hstate hlt leftPoint
      rightPoint hleftFiat hrightFiat hleft hright

end VeiledFlock.ProductionSamplingSchedulePostFiatInjective

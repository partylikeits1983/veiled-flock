import VeiledFlock.Production.Sampling.SamplingScheduleLigeritoGrowth

/-! # Opaque production Ligerito-site segment -/

namespace VeiledFlock.ProductionSamplingScheduleLigeritoSegment

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleLigeritoGrowth
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem ligeritoSite_window_fits (site : Fin maxLigeritoSites) :
    ligeritoSiteStart site + ligeritoSiteWidth ≤ productionSamplingSlots := by
  simpa only [ligeritoSiteStart, ligeritoSiteWidth, Nat.add_assoc] using
    ProductionSamplingScheduleSemantics.ligeritoGrinding_window_fits site

theorem ligeritoSiteStart_lt_slots (site : Fin maxLigeritoSites) :
    ligeritoSiteStart site < productionSamplingSlots := by
  have hfit := ligeritoSite_window_fits site
  have hpositive : 0 < ligeritoSiteWidth := by
    unfold ligeritoSiteWidth
    omega
  omega

noncomputable def ligeritoSegmentResult
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (before : Control shape)
    (answers : SamplingAnswerTape) : Control shape :=
  iterateFrom (rawStep shape causalSecret completion witness coins)
    (ligeritoSiteStart site) ligeritoSiteWidth before
    (window (ligeritoSiteStart site) ligeritoSiteWidth
      (ligeritoSite_window_fits site) answers)

set_option maxRecDepth 10000 in
theorem ligeritoSegmentResult_add_seventeen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (before : Control shape)
    (answers : SamplingAnswerTape)
    (hstatus : before.status = .live)
    (hexists : ∃ trial : Fin maxLigeritoTrials,
      ligeritoGrindingGood shape site.val
        (window (ligeritoSiteStart site + 1) maxLigeritoTrials
          (ProductionSamplingScheduleSemantics.ligeritoGrinding_window_fits site)
          answers trial)) :
    before.transcript.length + 17 ≤
      (ligeritoSegmentResult shape causalSecret completion witness coins site
        before answers).transcript.length := by
  unfold ligeritoSegmentResult
  let step := rawStep shape causalSecret completion witness coins
  let siteAnswers := window (ligeritoSiteStart site) (1 + maxLigeritoTrials)
    (ligeritoSite_window_fits site) answers
  change before.transcript.length + 17 ≤
    (iterateFrom step (ligeritoSiteStart site) (1 + maxLigeritoTrials)
      before siteAnswers).transcript.length
  rw [iterateFrom_add]
  have hstate : siteAnswers (Fin.castAdd maxLigeritoTrials ⟨0, by omega⟩) =
      answers ⟨ligeritoSiteStart site, ligeritoSiteStart_lt_slots site⟩ := rfl
  have htail : (fun index : Fin maxLigeritoTrials ↦
      siteAnswers (Fin.natAdd 1 index)) =
      window (ligeritoSiteStart site + 1) maxLigeritoTrials
        (ProductionSamplingScheduleSemantics.ligeritoGrinding_window_fits site)
        answers := by
    funext index
    apply congrArg answers
    apply Fin.ext
    simp
    omega
  have hone : iterateFrom step (ligeritoSiteStart site) 1 before
      (fun index ↦ siteAnswers (Fin.castAdd maxLigeritoTrials index)) =
      step (ligeritoSiteStart site) before
        (answers ⟨ligeritoSiteStart site, ligeritoSiteStart_lt_slots site⟩) := by
    rw [show (fun index : Fin 1 ↦
        siteAnswers (Fin.castAdd maxLigeritoTrials index)) =
        fun _ ↦ answers ⟨ligeritoSiteStart site,
          ligeritoSiteStart_lt_slots site⟩ by
      funext index
      fin_cases index
      exact hstate]
    simp [iterateFrom, iterateList]
  rw [hone, htail]
  exact rawLigeritoSite_add_seventeen shape causalSecret completion witness coins
    site before (answers ⟨ligeritoSiteStart site,
      ligeritoSiteStart_lt_slots site⟩)
    (window (ligeritoSiteStart site + 1) maxLigeritoTrials
      (ProductionSamplingScheduleSemantics.ligeritoGrinding_window_fits site)
      answers) hstatus hexists

set_option maxRecDepth 10000 in
theorem rawControlUntil_ligerito_eq_segment
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (site : Fin maxLigeritoSites) :
    rawControlUntil shape causalSecret completion witness coins prelude answers
        (ligeritoSiteStart site + ligeritoSiteWidth)
        (ligeritoSite_window_fits site) =
      ligeritoSegmentResult shape causalSecret completion witness coins site
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (ligeritoSiteStart site)
          (Nat.le_trans (Nat.le_add_right _ _) (ligeritoSite_window_fits site)))
        answers := by
  exact rawControlUntil_add shape causalSecret completion witness coins prelude
    answers (ligeritoSiteStart site) ligeritoSiteWidth
      (ligeritoSite_window_fits site)

theorem rawControlUntil_ligerito_length_eq_segment
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (site : Fin maxLigeritoSites) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        (ligeritoSiteStart site + ligeritoSiteWidth)
        (ligeritoSite_window_fits site)).transcript.length =
      (ligeritoSegmentResult shape causalSecret completion witness coins site
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers (ligeritoSiteStart site)
          (Nat.le_trans (Nat.le_add_right _ _) (ligeritoSite_window_fits site)))
        answers).transcript.length := by
  exact congrArg (fun result ↦ result.transcript.length)
    (rawControlUntil_ligerito_eq_segment shape causalSecret completion witness
      coins prelude answers site)

end VeiledFlock.ProductionSamplingScheduleLigeritoSegment

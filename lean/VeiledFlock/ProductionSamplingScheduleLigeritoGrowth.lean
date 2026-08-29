import VeiledFlock.ProductionSamplingScheduleBlindQueryFreshness

/-! # Transcript growth inside a production Ligerito grinding site -/

namespace VeiledFlock.ProductionSamplingScheduleLigeritoGrowth

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionGrindingProjection
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem ligeritoStep_trial_good_transcript_length_eq
    {shape : BatchShape} (site : Fin maxLigeritoSites) (trial : ℕ)
    (htrial : trial < maxLigeritoTrials) (control : Control shape)
    (answer : OracleBlock) (hdone : control.stageDone = false)
    (hgood : rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide) answer) :
    (ligeritoStep (ligeritoSiteStart site + 1 + trial) control answer).transcript.length =
      control.transcript.length + 17 := by
  have hoff := ligerito_trial_offset site trial htrial
  unfold ligeritoStep
  dsimp only
  rw [hoff.1, hoff.2]
  have hpositive : 1 + trial ≠ 0 := by omega
  simp [hdone, hgood]
  split <;> simp [VeiledFlock.ProductionGrinding.afterGrind_length]

theorem iterateFrom_rawStep_transcript_length_mono
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (start rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock) :
    control.transcript.length ≤
      (iterateFrom (rawStep shape causalSecret completion witness coins)
        start rounds control answers).transcript.length := by
  induction rounds with
  | zero => simp [iterateFrom, iterateList]
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      exact (ih (fun index ↦ answers index.castSucc)).trans
        (rawStep_transcript_length_mono shape causalSecret completion witness
          coins _ _ _)

theorem rawLigeritoGrinding_add_seventeen_of_exists
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (rounds : ℕ)
    (control : Control shape) (answers : Fin rounds → OracleBlock)
    (hrounds : rounds ≤ maxLigeritoTrials)
    (hstatus : control.status = .live)
    (hdone : control.stageDone = false)
    (hexists : ∃ trial : Fin rounds,
      rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (answers trial)) :
    control.transcript.length + 17 ≤
      (iterateFrom (rawStep shape causalSecret completion witness coins)
        (ligeritoSiteStart site + 1) rounds control answers).transcript.length := by
  induction rounds with
  | zero => simp at hexists
  | succ rounds ih =>
      rw [iterateFrom_succ_last]
      let prefixAnswers : Fin rounds → OracleBlock :=
        fun index ↦ answers index.castSucc
      let prior := iterateFrom
        (rawStep shape causalSecret completion witness coins)
        (ligeritoSiteStart site + 1) rounds control prefixAnswers
      by_cases hearlier : ∃ trial : Fin rounds,
          rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
            (prefixAnswers trial)
      · have hprefix := ih (answers := prefixAnswers) (hrounds := by omega)
          (hexists := hearlier)
        exact hprefix.trans
          (rawStep_transcript_length_mono shape causalSecret completion witness
            coins _ _ _)
      · have hallbad : ∀ trial : Fin rounds,
            ¬rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
              (prefixAnswers trial) := by
          simpa only [not_exists] using hearlier
        have hprefix := rawLigeritoFailures_live shape causalSecret completion
          witness coins site rounds control prefixAnswers (by omega) hstatus
          hdone hallbad
        have hlast : rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
            (answers (Fin.last rounds)) := by
          rcases hexists with ⟨trial, htrial⟩
          rcases Fin.eq_castSucc_or_eq_last trial with ⟨priorTrial, rfl⟩ | rfl
          · exact False.elim ((hallbad priorTrial) htrial)
          · exact htrial
        have hstep := rawStep_ligeritoTrial shape causalSecret completion witness
          coins site rounds (by omega) prior (answers (Fin.last rounds))
          hprefix.1
        have hmono : control.transcript.length ≤ prior.transcript.length := by
          dsimp only [prior, prefixAnswers]
          exact iterateFrom_rawStep_transcript_length_mono shape causalSecret
            completion witness coins (ligeritoSiteStart site + 1) rounds control
            (fun index ↦ answers index.castSucc)
        have hlength := ligeritoStep_trial_good_transcript_length_eq site rounds
          (by omega) prior (answers (Fin.last rounds)) hprefix.2 hlast
        rw [hstep, hlength]
        omega

theorem rawLigeritoSite_add_seventeen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape)
    (site : Fin maxLigeritoSites) (control : Control shape)
    (stateAnswer : OracleBlock)
    (answers : Fin maxLigeritoTrials → OracleBlock)
    (hstatus : control.status = .live)
    (hexists : ∃ trial : Fin maxLigeritoTrials,
      rustLeadingZeroBitsAtLeast maxLigeritoBits (by decide)
        (answers trial)) :
    control.transcript.length + 17 ≤
      (iterateFrom (rawStep shape causalSecret completion witness coins)
        (ligeritoSiteStart site + 1) maxLigeritoTrials
        (rawStep shape causalSecret completion witness coins
          (ligeritoSiteStart site) control stateAnswer) answers).transcript.length := by
  have hstate := rawStep_ligeritoStart shape causalSecret completion witness coins
    site control stateAnswer hstatus
  rw [hstate, ligeritoStep_at_start]
  exact rawLigeritoGrinding_add_seventeen_of_exists shape causalSecret
    completion witness coins site maxLigeritoTrials
    { control with
      powState := some stateAnswer
      stageDone := false
      stageBlocks := [] }
    answers (by rfl) (by simpa using hstatus) (by simp) hexists

end VeiledFlock.ProductionSamplingScheduleLigeritoGrowth

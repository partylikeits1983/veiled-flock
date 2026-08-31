import VeiledFlock.Production.Sampling.SamplingScheduleWhole

/-!
# Blind-grinding prefix semantics

This bridge keeps the production ordering explicit: one PoW-state block is
absorbed first, followed by the bounded first-success grinding window.
-/

namespace VeiledFlock.ProductionSamplingScheduleWhole

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.FixedWindowProbability
open VeiledFlock.Framing
open VeiledFlock.Grinding
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionGrinding
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics

set_option maxRecDepth 10000 in
theorem rawControlUntil_blind_live_done
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape)
    (hbefore : (rawControlUntil shape causalSecret completion witness coins
      prelude answers blindStateOffset (by decide)).status = .live)
    (hexists : ∃ trial : Fin maxBlindTrials,
      blindGrindingGood shape
        (window blindGrindingOffset maxBlindTrials (by decide) answers trial)) :
    let result := rawControlUntil shape causalSecret completion witness coins
      prelude answers blindChallengeOffset (by decide)
    result.status = .live ∧ result.stageDone = true := by
  dsimp only
  have hstate :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset (by decide) =
        rawStep shape causalSecret completion witness coins blindStateOffset
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindStateOffset (by decide))
          (answers ⟨blindStateOffset, by decide⟩) := by
    have hadd := rawControlUntil_add shape causalSecret completion witness coins
      prelude answers blindStateOffset blindStateWidth (by decide)
    change rawControlUntil shape causalSecret completion witness coins prelude
      answers (blindStateOffset + blindStateWidth) _ = _
    calc
      _ = iterateFrom (rawStep shape causalSecret completion witness coins)
          blindStateOffset blindStateWidth
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindStateOffset _)
          (window blindStateOffset blindStateWidth (by decide) answers) := hadd
      _ = rawStep shape causalSecret completion witness coins blindStateOffset
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindStateOffset _)
          (answers ⟨blindStateOffset, by decide⟩) := by
        simp [blindStateWidth, iterateFrom, iterateList, window]
  have hlocal :
      let withState := rawStep shape causalSecret completion witness coins
        blindStateOffset
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindStateOffset (by decide))
        (answers ⟨blindStateOffset, by decide⟩)
      let result := iterateFrom
        (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset maxBlindTrials withState
        (window blindGrindingOffset maxBlindTrials (by decide) answers)
      result.status = .live ∧ result.stageDone = true :=
    rawBlindGrinding_live_done shape causalSecret completion witness coins
      _ (answers ⟨blindStateOffset, by decide⟩)
      (window blindGrindingOffset maxBlindTrials (by decide) answers)
      hbefore hexists
  have hwindow :
      let result := iterateFrom
        (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset maxBlindTrials
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers blindGrindingOffset (by decide))
        (window blindGrindingOffset maxBlindTrials (by decide) answers)
      result.status = .live ∧ result.stageDone = true := by
    rw [hstate]
    exact hlocal
  have hfinal :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindChallengeOffset (by decide) =
        iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset maxBlindTrials
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindGrindingOffset (by decide))
          (window blindGrindingOffset maxBlindTrials (by decide) answers) := by
    change rawControlUntil shape causalSecret completion witness coins prelude
      answers (blindGrindingOffset + blindGrindingWidth) _ = _
    exact rawControlUntil_add shape causalSecret completion witness coins prelude
      answers blindGrindingOffset maxBlindTrials (by decide)
  constructor
  · exact (congrArg Control.status hfinal).trans hwindow.1
  · exact (congrArg Control.stageDone hfinal).trans hwindow.2

end VeiledFlock.ProductionSamplingScheduleWhole

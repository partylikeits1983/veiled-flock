import VeiledFlock.Production.Sampling.SamplingScheduleBlindFreshness

/-! # Transport blind-grinding growth through `rawControlUntil` -/

namespace VeiledFlock.ProductionSamplingScheduleBlindControlFreshness

open VeiledFlock.AdaptiveOracleProgramming
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
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleBlindFreshness
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem rawControlUntil_add_transcript_le
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (start rounds increment : ℕ)
    (hfit : start + rounds ≤ productionSamplingSlots)
    (hlocal :
      (rawControlUntil shape causalSecret completion witness coins prelude
          answers start (Nat.le_trans (Nat.le_add_right start rounds) hfit)).transcript.length +
          increment ≤
        (iterateFrom (rawStep shape causalSecret completion witness coins) start
          rounds
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers start (Nat.le_trans (Nat.le_add_right start rounds) hfit))
          (window start rounds hfit answers)).transcript.length) :
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        start (Nat.le_trans (Nat.le_add_right start rounds) hfit)).transcript.length +
        increment ≤
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        (start + rounds) hfit).transcript.length := by
  calc
    _ ≤ (iterateFrom (rawStep shape causalSecret completion witness coins) start
        rounds
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers start (Nat.le_trans (Nat.le_add_right start rounds) hfit))
        (window start rounds hfit answers)).transcript.length := hlocal
    _ = _ := congrArg (fun result ↦ result.transcript.length)
      (rawControlUntil_add shape causalSecret completion witness coins prelude
        answers start rounds hfit).symm

/-
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000 in
theorem rawControlUntil_blind_add_seventeen
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
    (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindStateOffset (by decide)).transcript.length + 17 ≤
      (rawControlUntil shape causalSecret completion witness coins prelude answers
        blindChallengeOffset (by decide)).transcript.length := by
  let before := rawControlUntil shape causalSecret completion witness coins
    prelude answers blindStateOffset (by decide)
  let withState := rawStep shape causalSecret completion witness coins
    blindStateOffset before (answers ⟨blindStateOffset, by decide⟩)
  have hstate :
      rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset (by decide) = withState := by
    have hs := rawControlUntil_succ shape causalSecret completion witness coins
      prelude answers ⟨blindStateOffset, by decide⟩
    simpa [blindGrindingOffset, blindStateWidth] using hs
  have hwithEq : withState =
      { before with
        powState := some (answers ⟨blindStateOffset, by decide⟩)
        stageDone := false
        stageBlocks := [] } := by
    exact rawStep_blindState shape causalSecret completion witness coins before
      (answers ⟨blindStateOffset, by decide⟩) hbefore
  have htranscript : withState.transcript = before.transcript := by simp [hwithEq]
  let grindAnswers := window blindGrindingOffset maxBlindTrials (by decide) answers
  have hraw := rawBlindGrinding_add_seventeen shape causalSecret completion
    witness coins before (answers ⟨blindStateOffset, by decide⟩) grindAnswers
    hbefore hexists
  have hstateLength := congrArg (fun result ↦ result.transcript.length) hstate
  have hwithLength : withState.transcript.length = before.transcript.length :=
    congrArg List.length htranscript
  have hiterate := congrArg
    (fun initial ↦
      (iterateFrom (rawStep shape causalSecret completion witness coins)
        blindGrindingOffset maxBlindTrials initial grindAnswers).transcript.length)
    hstate
  have hlocal :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
          blindGrindingOffset (by decide)).transcript.length + 17 ≤
        (iterateFrom (rawStep shape causalSecret completion witness coins)
          blindGrindingOffset maxBlindTrials
          (rawControlUntil shape causalSecret completion witness coins prelude
            answers blindGrindingOffset (by decide)) grindAnswers).transcript.length := by
    omega
  have hsegment := rawControlUntil_add_transcript_le shape causalSecret
    completion witness coins prelude answers blindGrindingOffset maxBlindTrials
    17 (by decide) hlocal
  have hendLength :
      (rawControlUntil shape causalSecret completion witness coins prelude answers
          (blindGrindingOffset + maxBlindTrials) (by decide)).transcript.length =
        (rawControlUntil shape causalSecret completion witness coins prelude answers
          blindChallengeOffset (by decide)).transcript.length := by rfl
  change before.transcript.length + 17 ≤ _
  omega
-/

end VeiledFlock.ProductionSamplingScheduleBlindControlFreshness

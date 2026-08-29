import VeiledFlock.ProductionSamplingScheduleFiatInjective

/-! # Non-Fiat production queries occur only in grinding windows -/

namespace VeiledFlock.ProductionSamplingSchedulePowRange

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleAudit
open VeiledFlock.ProductionSamplingScheduleClassification
open VeiledFlock.ProductionSamplingScheduleFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics
open VeiledFlock.ProductionTranscriptFraming

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem rawQuery_nonFiat_range
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude) (answers : SamplingAnswerTape)
    (round : Fin productionSamplingSlots) (point : List Byte)
    (hquery : rawQuery shape causalSecret completion witness coins round
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers round round.isLt.le) = some point)
    (hnotFiat : ¬ isFiatShamirPoint point) :
    (blindGrindingOffset ≤ round.val ∧ round.val < blindChallengeOffset) ∨
      (ligeritoOffset ≤ round.val ∧
        (round.val - ligeritoOffset) % ligeritoSiteWidth ≠ 0) := by
  let control := rawControlUntil shape causalSecret completion witness coins
    prelude answers round round.isLt.le
  change rawQuery shape causalSecret completion witness coins round control =
    some point at hquery
  have hcontrolFiat := rawControlUntil_fiat shape causalSecret completion witness
    coins prelude hprelude answers round round.isLt.le
  by_cases hstatus : control.status != .live
  · simp [rawQuery, hstatus] at hquery
  by_cases hskip : round.val < equalitySkipBlocks
  · simp [rawQuery, hstatus, hskip] at hquery
    subst point
    exact False.elim (hnotFiat (slicePoint_isFiatShamir hcontrolFiat _ _))
  by_cases hequality : round.val < zerocheckOffset
  · let offset := round.val - equalityOffset
    let counter := offset % equalityAttemptBlocks
    by_cases hsome : control.equalityPoint.isSome
    · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome]
        at hquery
    by_cases hcounter : counter < equalityBlockCount shape
    · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome,
        hcounter] at hquery
      subst point
      exact False.elim (hnotFiat (slicePoint_isFiatShamir hcontrolFiat _ _))
    · simp [rawQuery, hstatus, hskip, hequality, offset, counter, hsome,
        hcounter] at hquery
  by_cases hzero : round.val < blindStateOffset
  · let offset := round.val - zerocheckOffset
    cases heq : control.equalityPoint with
    | none =>
        simp [rawQuery, hstatus, hskip, hequality, hzero, offset, heq] at hquery
    | some equalityPoint =>
        by_cases hsite : offset < programmedPoints shape
        · simp [rawQuery, hstatus, hskip, hequality, hzero, offset, heq,
            hsite] at hquery
          subst point
          exact False.elim (hnotFiat
            (zerocheckRealByteSchedule_isFiatShamir shape causalSecret
              completion control.transcript hcontrolFiat witness coins offset
              (historyFromList control.zerocheckAnswers offset)))
        · simp [rawQuery, hstatus, hskip, hequality, hzero, offset, heq,
            hsite] at hquery
  by_cases hblindState : round.val < blindGrindingOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState] at hquery
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases hblindGrind : round.val < blindChallengeOffset
  · exact Or.inl ⟨by omega, hblindGrind⟩
  by_cases hblind : round.val < multiplicationAlphaOffset
  · have hpoint := nonzeroStageQuery_some blindChallengeOffset round.val
      control point (by simpa [rawQuery, hstatus, hskip, hequality, hzero,
        hblindState, hblindGrind, hblind] using hquery)
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases halpha : round.val < outerChallengeOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.2.symm
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases houterChallenge : round.val < outerPositionsOffset
  · have hpoint := nonzeroStageQuery_some outerChallengeOffset round.val
      control point (by simpa [rawQuery, hstatus, hskip, hequality, hzero,
        hblindState, hblindGrind, hblind, halpha, houterChallenge] using hquery)
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases houterPositions : round.val < linearPositionsOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.symm
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases hlinearPositions : round.val < linearRhoOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.symm
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases hlinearRho : round.val < hadamardPositionsOffset
  · have hpoint := nonzeroStageQuery_some linearRhoOffset round.val control
      point (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho] using hquery)
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases hhadamardPositions : round.val < hadamardRhoOffset
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions] at hquery
    have hpoint : point = scalarPoint control.transcript := hquery.2.symm
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases hhadamardRho : round.val < productCoefficientOffset
  · have hpoint := nonzeroStageQuery_some hadamardRhoOffset round.val control
      point (by simpa [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
        hblindGrind, hblind, halpha, houterChallenge, houterPositions,
        hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho] using
        hquery)
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  by_cases hproduct : round.val < ligeritoOffset
  · have hpoint := nonzeroStageQuery_some productCoefficientOffset round.val
      control point (by simpa [rawQuery, hstatus, hskip, hequality, hzero,
        hblindState, hblindGrind, hblind, halpha, houterChallenge,
        houterPositions, hlinearPositions, hlinearRho, hhadamardPositions,
        hhadamardRho, hproduct] using hquery)
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  let within := (round.val - ligeritoOffset) % ligeritoSiteWidth
  by_cases hstate : within = 0
  · simp [rawQuery, hstatus, hskip, hequality, hzero, hblindState,
      hblindGrind, hblind, halpha, houterChallenge, houterPositions,
      hlinearPositions, hlinearRho, hhadamardPositions, hhadamardRho, hproduct,
      within, hstate] at hquery
    subst point
    exact False.elim (hnotFiat (scalarPoint_isFiatShamir hcontrolFiat))
  · exact Or.inr ⟨by omega, hstate⟩

end VeiledFlock.ProductionSamplingSchedulePowRange

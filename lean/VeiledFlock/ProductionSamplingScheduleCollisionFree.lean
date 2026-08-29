import VeiledFlock.ProductionSamplingScheduleInjective

/-!
# Collision freedom of the operational production schedule

The operational optional schedule records previously queried byte strings and
fails closed on a duplicate.  The literal production schedule is pairwise
injective outside the explicit sampling ledger.  This file connects those two
facts: duplicate suppression is therefore observationally inert on every good
answer tape.
-/

namespace VeiledFlock.ProductionSamplingScheduleCollisionFree

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleInjective
open VeiledFlock.ProductionSamplingSchedulePostFreshness
open VeiledFlock.ProductionSamplingScheduleSemantics

noncomputable def scheduledControlUntil
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (answers : SamplingAnswerTape) (rounds : ℕ)
    (hrounds : rounds ≤ productionSamplingSlots) : ScheduledControl shape :=
  scheduledControlAfter shape causalSecret completion witness coins prelude
    (fun index : Fin rounds ↦
      answers ⟨index.val, index.isLt.trans_le hrounds⟩)

set_option maxRecDepth 10000 in
theorem scheduledControlUntil_raw_and_seen
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (rounds : ℕ) (hrounds : rounds ≤ productionSamplingSlots) :
    let scheduled := scheduledControlUntil shape causalSecret completion witness
      coins prelude answers rounds hrounds
    scheduled.raw =
        rawControlUntil shape causalSecret completion witness coins prelude
          answers rounds hrounds ∧
      ∀ point, point ∈ scheduled.seen ↔
        ∃ site : Fin rounds,
          rawQuery shape causalSecret completion witness coins site.val
            (rawControlUntil shape causalSecret completion witness coins prelude
              answers site.val
                (site.isLt.le.trans hrounds)) = some point := by
  induction rounds with
  | zero =>
      simp [scheduledControlUntil, scheduledControlAfter,
        initialScheduledControl, rawControlUntil, iterateFrom, iterateList]
  | succ rounds ih =>
      have hround : rounds < productionSamplingSlots := by omega
      let current : Fin productionSamplingSlots := ⟨rounds, hround⟩
      let before := scheduledControlUntil shape causalSecret completion witness
        coins prelude answers rounds (Nat.le_of_lt hround)
      have ih' := ih (Nat.le_of_lt hround)
      dsimp only at ih'
      rcases ih' with ⟨hraw, hseen⟩
      have hsucc :
          rawControlUntil shape causalSecret completion witness coins prelude
              answers (rounds + 1) hrounds =
            rawStep shape causalSecret completion witness coins rounds
              (rawControlUntil shape causalSecret completion witness coins
                prelude answers rounds (Nat.le_of_lt hround))
              (answers current) := by
        simpa [current] using rawControlUntil_succ shape causalSecret completion
          witness coins prelude answers current
      have hscheduledSucc :
          scheduledControlUntil shape causalSecret completion witness coins
              prelude answers (rounds + 1) hrounds =
            scheduledStep shape causalSecret completion witness coins rounds
              before (answers current) := by
        simp only [scheduledControlUntil, scheduledControlAfter]
        congr 2
      have hrawBefore : before.raw =
          rawControlUntil shape causalSecret completion witness coins prelude
            answers rounds (Nat.le_of_lt hround) := by
        exact hraw
      generalize hquery : rawQuery shape causalSecret completion witness coins
          rounds (rawControlUntil shape causalSecret completion witness coins
            prelude answers rounds (Nat.le_of_lt hround)) = query
      cases query with
      | none =>
          have hqueryBefore : rawQuery shape causalSecret completion witness coins
              rounds before.raw = none := by rw [hrawBefore]; exact hquery
          constructor
          · rw [hscheduledSucc, hsucc]
            unfold scheduledStep
            rw [hqueryBefore]
            simp only
            rw [hrawBefore]
          · intro point
            rw [hscheduledSucc]
            simp only [scheduledStep, hqueryBefore]
            rw [hseen]
            constructor
            · rintro ⟨site, hsite⟩
              exact ⟨⟨site.val, by omega⟩, by simpa using hsite⟩
            · rintro ⟨site, hsite⟩
              by_cases hlast : site.val = rounds
              · have hlastQuery : rawQuery shape causalSecret completion
                    witness coins rounds
                      (rawControlUntil shape causalSecret completion witness
                        coins prelude answers rounds (Nat.le_of_lt hround)) =
                      some point := by
                    simpa [hlast] using hsite
                rw [hquery] at hlastQuery
                simp at hlastQuery
              · exact ⟨⟨site.val, by omega⟩, by simpa using hsite⟩
      | some point =>
          have hqueryBefore : rawQuery shape causalSecret completion witness coins
              rounds before.raw = some point := by rw [hrawBefore]; exact hquery
          have hfresh : point ∉ before.seen := by
            intro hmem
            rw [hseen] at hmem
            rcases hmem with ⟨site, hsite⟩
            exact rawQuery_complete_injective shape causalSecret completion
              witness coins prelude hprelude answers hgood
              ⟨site.val, site.isLt.trans hround⟩ current site.isLt point point
              (by simpa using hsite) (by simpa [current] using hquery) rfl
          constructor
          · rw [hscheduledSucc, hsucc]
            unfold scheduledStep
            rw [hqueryBefore]
            simp only
            rw [if_neg hfresh]
            simp only
            rw [hrawBefore]
          · intro candidate
            rw [hscheduledSucc]
            simp only [scheduledStep, hqueryBefore, hfresh, if_false]
            rw [Finset.mem_insert, hseen]
            constructor
            · rintro (rfl | ⟨site, hsite⟩)
              · exact ⟨⟨rounds, by omega⟩, by simpa using hquery⟩
              · exact ⟨⟨site.val, by omega⟩, by simpa using hsite⟩
            · rintro ⟨site, hsite⟩
              by_cases hlast : site.val = rounds
              · have hcandidate : candidate = point := by
                  have hlastQuery : rawQuery shape causalSecret completion
                      witness coins rounds
                        (rawControlUntil shape causalSecret completion witness
                          coins prelude answers rounds
                            (Nat.le_of_lt hround)) = some candidate := by
                    simpa [hlast] using hsite
                  exact Option.some.inj (hlastQuery.symm.trans hquery)
                exact Or.inl hcandidate
              · exact Or.inr ⟨⟨site.val, by omega⟩, by simpa using hsite⟩

theorem scheduledControlUntil_raw_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (rounds : ℕ) (hrounds : rounds ≤ productionSamplingSlots) :
    (scheduledControlUntil shape causalSecret completion witness coins prelude
      answers rounds hrounds).raw =
      rawControlUntil shape causalSecret completion witness coins prelude
        answers rounds hrounds :=
  (scheduledControlUntil_raw_and_seen shape causalSecret completion witness
    coins prelude hprelude answers hgood rounds hrounds).1

theorem freshSchedule_eq_rawQuery_of_not_globalBad
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (witness : W) (coins : ProductionCoins shape) (prelude : List Byte)
    (hprelude : isFiatShamirPoint prelude)
    (answers : SamplingAnswerTape) (hgood : answers ∉ globalBad shape)
    (site : Fin productionSamplingSlots) :
    freshSchedule shape causalSecret completion witness coins prelude site
        (priorAnswers answers site) =
      rawQuery shape causalSecret completion witness coins site
        (rawControlUntil shape causalSecret completion witness coins prelude
          answers site site.isLt.le) := by
  classical
  have hall := scheduledControlUntil_raw_and_seen shape causalSecret completion
    witness coins prelude hprelude answers hgood site.val site.isLt.le
  rcases hall with ⟨hraw, hseen⟩
  have hschedule : scheduledControlAfter shape causalSecret completion witness
      coins prelude (priorAnswers answers site) =
        scheduledControlUntil shape causalSecret completion witness coins prelude
          answers site.val site.isLt.le := by
    rfl
  rw [freshSchedule, hschedule, hraw]
  generalize hquery : rawQuery shape causalSecret completion witness coins site
      (rawControlUntil shape causalSecret completion witness coins prelude
        answers site site.isLt.le) = query
  cases query with
  | none => rfl
  | some point =>
      have hfresh : point ∉
          (scheduledControlUntil shape causalSecret completion witness coins
            prelude answers site.val site.isLt.le).seen := by
        intro hmem
        rw [hseen] at hmem
        rcases hmem with ⟨left, hleft⟩
        exact rawQuery_complete_injective shape causalSecret completion witness
          coins prelude hprelude answers hgood
          ⟨left.val, left.isLt.trans site.isLt⟩ site left.isLt point point
          (by simpa using hleft) hquery rfl
      simp [hfresh]

end VeiledFlock.ProductionSamplingScheduleCollisionFree

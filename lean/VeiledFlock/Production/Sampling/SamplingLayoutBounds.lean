import VeiledFlock.Production.Sampling.SamplingLayout

/-! # Named bounds for fixed production sampling offsets -/

namespace VeiledFlock.ProductionSamplingLayoutBounds

open VeiledFlock.Grinding
open VeiledFlock.ProductionSamplingLayout

theorem blindStateOffset_lt_slots :
    blindStateOffset < productionSamplingSlots := by
  rw [productionSamplingSlots_eq]
  decide

theorem blindStateOffset_le_slots :
    blindStateOffset ≤ productionSamplingSlots :=
  blindStateOffset_lt_slots.le

theorem blindGrindingOffset_le_slots :
    blindGrindingOffset ≤ productionSamplingSlots := by
  rw [productionSamplingSlots_eq]
  decide

theorem blindChallengeOffset_le_slots :
    blindChallengeOffset ≤ productionSamplingSlots := by
  rw [productionSamplingSlots_eq]
  decide

theorem blindGrinding_window_fits :
    blindGrindingOffset + maxBlindTrials ≤ productionSamplingSlots := by
  rw [productionSamplingSlots_eq]
  decide

theorem blindGrindingOffset_eq_state_succ :
    blindGrindingOffset = blindStateOffset + 1 := by decide

theorem blindChallengeOffset_eq_grinding_end :
    blindChallengeOffset = blindGrindingOffset + maxBlindTrials := rfl

end VeiledFlock.ProductionSamplingLayoutBounds

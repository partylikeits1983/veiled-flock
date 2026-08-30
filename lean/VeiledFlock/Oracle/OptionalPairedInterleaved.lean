import VeiledFlock.Oracle.OptionalAdaptiveOracle
import VeiledFlock.Oracle.PairedInterleavedFiatShamir

/-!
# Paired algebraic/oracle transport for early-stopping schedules

This is the distributional wrapper connecting optional bounded Rust traces to
the paired interleaved simulator theorem.  The public random oracle remains a
table on real byte points; inactive coordinates are an independent dummy tape
and therefore cannot change shared-oracle state.
-/

namespace VeiledFlock.OptionalPairedInterleaved

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.OptionalAdaptiveOracle

variable {AlgCoins State Prior Point Outcome View : Type*}
variable [Fintype AlgCoins] [DecidableEq AlgCoins] [Nonempty AlgCoins]
variable [Finite Prior]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

abbrev Coins (AlgCoins Point Outcome : Type*) (sites : ℕ) :=
  AlgCoins × ((Point → Outcome) × (Fin (sites + 1) → Outcome))

/-- Reassociate the actual shared-oracle plus dummy-tape coins as the table
on the compiled sum universe used by the generic theorem. -/
def compiledInputEquiv (sites : ℕ) :
    Coins AlgCoins Point Outcome sites ≃
      AlgCoins × (CompiledPoint Point sites → Outcome) :=
  (Equiv.refl AlgCoins).prodCongr
    (oracleDummyEquiv (Point := Point) (Outcome := Outcome) sites)

/-- The concrete coin transport for an optional production schedule.  It
first compiles the shared-oracle/dummy pair to one sum-indexed table, applies
the paired algebraic/oracle retargeting, and then splits the table back into
the same public-oracle and private-dummy coordinates. -/
noncomputable def coinEquiv {sites : ℕ}
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (hleft : ∀ coins answers,
      Injective
        (protectedTracePoints (leftFixed coins)
          (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective
        (protectedTracePoints (rightFixed coins)
          (rightSchedule coins) answers)) :
    Coins AlgCoins Point Outcome sites ≃ Coins AlgCoins Point Outcome sites :=
  ((compiledInputEquiv sites).trans
    (VeiledFlock.PairedInterleavedFiatShamir.coinEquiv answerEquiv
      (fun coins answers prior =>
        Sum.inl (leftFixed coins answers prior))
      (fun coins answers prior =>
        Sum.inl (rightFixed coins answers prior))
      (fun coins => compile (leftSchedule coins))
      (fun coins => compile (rightSchedule coins))
      hleft hright)).trans
    (compiledInputEquiv sites).symm

/-- Actual optional-schedule machine, expressed through its semantics-
preserving compiled schedule. -/
noncomputable def machine {sites : ℕ}
    (state : AlgCoins → History (Outcome := Outcome) sites → State)
    (fixedPoints : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (schedule : AlgCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : Coins AlgCoins Point Outcome sites) : View :=
  VeiledFlock.PairedInterleavedFiatShamir.machine state
    (fun coins answers prior => Sum.inl (fixedPoints coins answers prior))
    (fun coins => compile (schedule coins)) continueWith
    (compiledInputEquiv sites input)

/-- Exact pointwise transport for the complete optional execution.  The
view may contain the serialized proof, every adaptive oracle query/answer,
and the adversary's final state, so this theorem is joint rather than
component-wise. -/
theorem machine_transport {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (hleft : ∀ coins answers,
      Injective
        (protectedTracePoints (leftFixed coins)
          (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective
        (protectedTracePoints (rightFixed coins)
          (rightSchedule coins) answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View)
    (input : Coins AlgCoins Point Outcome sites) :
    machine leftState leftFixed leftSchedule continueWith input =
      machine rightState rightFixed rightSchedule continueWith
        (coinEquiv answerEquiv leftFixed rightFixed leftSchedule
          rightSchedule hleft hright input) := by
  unfold machine coinEquiv
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
    (VeiledFlock.PairedInterleavedFiatShamir.machine_transport
      leftState rightState answerEquiv hstate
      (fun coins answers prior => Sum.inl (leftFixed coins answers prior))
      (fun coins answers prior => Sum.inl (rightFixed coins answers prior))
      (fun coins => compile (leftSchedule coins))
      (fun coins => compile (rightSchedule coins))
      hleft hright continueWith (compiledInputEquiv sites input))

/-- Uniform real and simulator views remain exactly equal for a bounded
early-stopping trace.  The two injectivity premises include the protected
shared-oracle family and the compiled active/dummy schedule. -/
theorem simulator_exact {sites : ℕ}
    (leftState rightState :
      AlgCoins → History (Outcome := Outcome) sites → State)
    (answerEquiv : History (Outcome := Outcome) sites → AlgCoins ≃ AlgCoins)
    (hstate : ∀ coins answers,
      leftState coins answers =
        rightState (answerEquiv answers coins) answers)
    (leftFixed rightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → Point)
    (leftSchedule rightSchedule : AlgCoins →
      OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (hleft : ∀ coins answers,
      Injective
        (protectedTracePoints (leftFixed coins) (leftSchedule coins) answers))
    (hright : ∀ coins answers,
      Injective
        (protectedTracePoints (rightFixed coins)
          (rightSchedule coins) answers))
    (continueWith : State → (Prior → Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype (Coins AlgCoins Point Outcome sites)).map
        (machine leftState leftFixed leftSchedule continueWith) =
      (PMF.uniformOfFintype (Coins AlgCoins Point Outcome sites)).map
        (machine rightState rightFixed rightSchedule continueWith) := by
  let compiledLeftFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → CompiledPoint Point sites :=
    fun coins answers prior => Sum.inl (leftFixed coins answers prior)
  let compiledRightFixed : AlgCoins →
      History (Outcome := Outcome) sites → Prior → CompiledPoint Point sites :=
    fun coins answers prior => Sum.inl (rightFixed coins answers prior)
  let compiledLeftSchedule : AlgCoins →
      Schedule (Point := CompiledPoint Point sites) (Outcome := Outcome) :=
    fun coins => compile (leftSchedule coins)
  let compiledRightSchedule : AlgCoins →
      Schedule (Point := CompiledPoint Point sites) (Outcome := Outcome) :=
    fun coins => compile (rightSchedule coins)
  have hcompiled :
      (PMF.uniformOfFintype
        (AlgCoins × (CompiledPoint Point sites → Outcome))).map
          (VeiledFlock.PairedInterleavedFiatShamir.machine leftState
            compiledLeftFixed compiledLeftSchedule continueWith) =
        (PMF.uniformOfFintype
          (AlgCoins × (CompiledPoint Point sites → Outcome))).map
          (VeiledFlock.PairedInterleavedFiatShamir.machine rightState
            compiledRightFixed compiledRightSchedule continueWith) := by
    apply VeiledFlock.PairedInterleavedFiatShamir.simulator_exact
      leftState rightState answerEquiv hstate compiledLeftFixed
      compiledRightFixed compiledLeftSchedule compiledRightSchedule
    · intro coins answers
      exact hleft coins answers
    · intro coins answers
      exact hright coins answers
  calc
    (PMF.uniformOfFintype (Coins AlgCoins Point Outcome sites)).map
          (machine leftState leftFixed leftSchedule continueWith) =
        (PMF.uniformOfFintype
          (AlgCoins × (CompiledPoint Point sites → Outcome))).map
          (VeiledFlock.PairedInterleavedFiatShamir.machine leftState
            compiledLeftFixed compiledLeftSchedule continueWith) := by
      apply VeiledFlock.Probability.uniform_map_eq_of_equiv
        (compiledInputEquiv sites)
      intro input
      rfl
    _ = (PMF.uniformOfFintype
          (AlgCoins × (CompiledPoint Point sites → Outcome))).map
          (VeiledFlock.PairedInterleavedFiatShamir.machine rightState
            compiledRightFixed compiledRightSchedule continueWith) := hcompiled
    _ = (PMF.uniformOfFintype (Coins AlgCoins Point Outcome sites)).map
          (machine rightState rightFixed rightSchedule continueWith) := by
      symm
      apply VeiledFlock.Probability.uniform_map_eq_of_equiv
        (compiledInputEquiv sites)
      intro input
      rfl

end VeiledFlock.OptionalPairedInterleaved

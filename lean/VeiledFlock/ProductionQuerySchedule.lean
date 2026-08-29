import VeiledFlock.AdaptiveOracleProgramming
import VeiledFlock.ProductionFraming

/-!
# Production query schedules

The adaptive-oracle proof operates on a finite point type.  This module lifts
the exact Rust query encoder into that model: any causal schedule of logical
Fiat--Shamir, Merkle, and PoW queries with a public byte-length cap becomes a
schedule over finite bounded byte strings.  Injectivity of the logical query
trace is sufficient because the production encoding itself is injective.
-/

namespace VeiledFlock.ProductionQuerySchedule

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.Framing
open VeiledFlock.ProductionFraming

variable {Outcome : Type*}

def boundedSchedule (maxLength : ℕ)
    (next : Schedule (Point := ProductionQuery) (Outcome := Outcome))
    (hbound : ∀ rounds history,
      (encodeProductionQuery (next rounds history)).length ≤ maxLength) :
    Schedule (Point := BoundedBytes maxLength) (Outcome := Outcome) :=
  fun rounds history =>
    boundBytes (encodeProductionQuery (next rounds history))
      (hbound rounds history)

@[simp]
theorem unbound_boundedSchedule (maxLength : ℕ)
    (next : Schedule (Point := ProductionQuery) (Outcome := Outcome))
    (hbound : ∀ rounds history,
      (encodeProductionQuery (next rounds history)).length ≤ maxLength)
    (rounds : ℕ) (history : History (Outcome := Outcome) rounds) :
    unboundBytes (boundedSchedule maxLength next hbound rounds history) =
      encodeProductionQuery (next rounds history) := rfl

theorem unbound_tracePoint_boundedSchedule {sites maxLength : ℕ}
    (next : Schedule (Point := ProductionQuery) (Outcome := Outcome))
    (hbound : ∀ rounds history,
      (encodeProductionQuery (next rounds history)).length ≤ maxLength)
    (answers : History (Outcome := Outcome) sites) (site : Fin sites) :
    unboundBytes
        (tracePoint (boundedSchedule maxLength next hbound) answers site) =
      encodeProductionQuery (tracePoint next answers site) := rfl

/-- Concrete-byte injectivity follows entirely from logical query-site
injectivity; there is no additional collision premise at the serialization
boundary. -/
theorem tracePoints_boundedSchedule_injective {sites maxLength : ℕ}
    (next : Schedule (Point := ProductionQuery) (Outcome := Outcome))
    (hbound : ∀ rounds history,
      (encodeProductionQuery (next rounds history)).length ≤ maxLength)
    (answers : History (Outcome := Outcome) sites)
    (hinjective : Injective (tracePoints next answers)) :
    Injective
      (tracePoints (boundedSchedule maxLength next hbound) answers) := by
  intro left right heq
  have hunbound := congrArg unboundBytes heq
  change
    unboundBytes
        (tracePoint (boundedSchedule maxLength next hbound) answers left) =
      unboundBytes
        (tracePoint (boundedSchedule maxLength next hbound) answers right)
      at hunbound
  rw [unbound_tracePoint_boundedSchedule,
    unbound_tracePoint_boundedSchedule] at hunbound
  exact hinjective (encodeProductionQuery_injective hunbound)

end VeiledFlock.ProductionQuerySchedule

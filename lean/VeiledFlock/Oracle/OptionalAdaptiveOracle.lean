import VeiledFlock.Oracle.AdaptiveOracleProgramming

/-!
# Bounded causal schedules with inactive coordinates

Fail-closed rejection and grinding loops have a public maximum number of
attempts but stop querying the random oracle after the first success.  Padding
such a trace with ordinary oracle queries would change the shared oracle
table.  Instead, an inactive coordinate consumes a private dummy outcome.

The compiler below embeds real queries in the left side of a sum and each
inactive coordinate in its own right-side point.  A function on that sum is
exactly a shared random oracle paired with an independent dummy tape.  This
lets all bounded Rust loops use the existing adaptive-oracle equivalences
without pretending that post-success queries occurred.
-/

namespace VeiledFlock.OptionalAdaptiveOracle

open Function
open VeiledFlock.AdaptiveOracleProgramming

variable {Point Outcome : Type*}
variable [Fintype Point] [DecidableEq Point]

/-- A public-cap schedule either issues one real oracle query or marks the
coordinate inactive, based only on the preceding answer history. -/
abbrev OptionalSchedule (sites : ℕ) :=
  ∀ round : Fin sites, History (Outcome := Outcome) round → Option Point

/-- One extra unreachable dummy coordinate makes the compiled schedule total
for natural rounds beyond its public cap. -/
abbrev CompiledPoint (Point : Type*) (sites : ℕ) :=
  Point ⊕ Fin (sites + 1)

def compile {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites) :
    Schedule (Point := CompiledPoint Point sites) (Outcome := Outcome) :=
  fun rounds history =>
    if hround : rounds < sites then
      match next ⟨rounds, hround⟩ history with
      | some point => Sum.inl point
      | none => Sum.inr ⟨rounds, Nat.lt_succ_of_lt hround⟩
    else
      Sum.inr ⟨sites, Nat.lt_succ_self sites⟩

theorem tracePoint_compile {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites) (site : Fin sites) :
    tracePoint (compile next) answers site =
      match next site (priorAnswers answers site) with
      | some point => Sum.inl point
      | none => Sum.inr site.castSucc := by
  simp only [tracePoint, compile, site.isLt, ↓reduceDIte]
  generalize next site (priorAnswers answers site) = result
  cases result with
  | none =>
      congr 1
  | some point => rfl

/-- The real oracle table and the private inactive-coordinate tape are exactly
one table on the compiled sum universe. -/
def oracleDummyEquiv (sites : ℕ) :
    ((Point → Outcome) × (Fin (sites + 1) → Outcome)) ≃
      (CompiledPoint Point sites → Outcome) :=
  (Equiv.sumArrowEquivProdArrow Point (Fin (sites + 1)) Outcome).symm

@[simp]
theorem oracleDummyEquiv_real (sites : ℕ)
    (oracle : Point → Outcome) (dummy : Fin (sites + 1) → Outcome)
    (point : Point) :
    oracleDummyEquiv sites (oracle, dummy) (Sum.inl point) = oracle point := by
  exact Equiv.sumArrowEquivProdArrow_symm_apply_inl oracle dummy point

@[simp]
theorem oracleDummyEquiv_dummy (sites : ℕ)
    (oracle : Point → Outcome) (dummy : Fin (sites + 1) → Outcome)
    (site : Fin (sites + 1)) :
    oracleDummyEquiv sites (oracle, dummy) (Sum.inr site) = dummy site := by
  exact Equiv.sumArrowEquivProdArrow_symm_apply_inr oracle dummy site

/-- Run exactly the public number of optional coordinates.  Inactive suffix
answers come from the private tape and cannot mutate the shared oracle. -/
def run {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (oracle : Point → Outcome) (dummy : Fin (sites + 1) → Outcome) :
    History (Outcome := Outcome) sites :=
  AdaptiveOracleProgramming.run (compile next)
    (oracleDummyEquiv sites (oracle, dummy)) sites

/-- Real points reached by a proposed complete answer vector are distinct.
Inactive coordinates need no premise because their compiled dummy names are
the coordinate indices themselves. -/
def ActiveInjective {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites) : Prop :=
  ∀ left right leftPoint rightPoint,
    next left (priorAnswers answers left) = some leftPoint →
    next right (priorAnswers answers right) = some rightPoint →
    leftPoint = rightPoint → left = right

/-- An optional schedule with distinct active points compiles to an injective
ordinary adaptive trace. -/
theorem tracePoints_compile_injective {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites)
    (hinjective : ActiveInjective next answers) :
    Injective (tracePoints (compile next) answers) := by
  intro left right heq
  change
    tracePoint (compile next) answers left =
      tracePoint (compile next) answers right at heq
  rw [tracePoint_compile, tracePoint_compile] at heq
  generalize hleft : next left (priorAnswers answers left) = leftResult at heq
  generalize hright : next right (priorAnswers answers right) = rightResult at heq
  cases leftResult with
  | none =>
      cases rightResult with
      | none =>
          simp only at heq
          have hsite : left.castSucc = right.castSucc := Sum.inr.inj heq
          exact Fin.castSucc_injective _ hsite
      | some rightPoint => simp at heq
  | some leftPoint =>
      cases rightResult with
      | none => simp at heq
      | some rightPoint =>
          simp only at heq
          exact hinjective left right leftPoint rightPoint hleft hright
            (Sum.inl.inj heq)

/-- Answer-dependent protected points followed by the compiled optional
trace.  Protected points always live in the shared-oracle namespace. -/
def protectedTracePoints {Prior : Type*} {sites : ℕ}
    (fixed : History (Outcome := Outcome) sites → Prior → Point)
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites) :
    Prior ⊕ Fin sites → CompiledPoint Point sites
  | .inl prior => Sum.inl (fixed answers prior)
  | .inr site => tracePoint (compile next) answers site

/-- Protected points and every active optional query are mutually fresh. -/
def ProtectedActiveFresh {Prior : Type*} {sites : ℕ}
    (fixed : History (Outcome := Outcome) sites → Prior → Point)
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites) : Prop :=
  ∀ prior site point,
    next site (priorAnswers answers site) = some point →
      fixed answers prior ≠ point

/-- Fixed-point injectivity, active trace injectivity, and mutual freshness
imply injectivity of the complete protected optional family. -/
theorem protectedTracePoints_injective {Prior : Type*} {sites : ℕ}
    (fixed : History (Outcome := Outcome) sites → Prior → Point)
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites)
    (hfixed : Injective (fixed answers))
    (hactive : ActiveInjective next answers)
    (hfresh : ProtectedActiveFresh fixed next answers) :
    Injective (protectedTracePoints fixed next answers) := by
  intro left right heq
  cases left with
  | inl leftPrior =>
      cases right with
      | inl rightPrior =>
          apply congrArg Sum.inl
          exact hfixed (Sum.inl.inj heq)
      | inr rightSite =>
          exfalso
          change Sum.inl (fixed answers leftPrior) =
            tracePoint (compile next) answers rightSite at heq
          rw [tracePoint_compile] at heq
          generalize hresult :
            next rightSite (priorAnswers answers rightSite) = result at heq
          cases result with
          | none => simp at heq
          | some point =>
              exfalso
              exact hfresh leftPrior rightSite point hresult
                (Sum.inl.inj heq)
  | inr leftSite =>
      cases right with
      | inl rightPrior =>
          exfalso
          change tracePoint (compile next) answers leftSite =
            Sum.inl (fixed answers rightPrior) at heq
          rw [tracePoint_compile] at heq
          generalize hresult :
            next leftSite (priorAnswers answers leftSite) = result at heq
          cases result with
          | none => simp at heq
          | some point =>
              exfalso
              exact hfresh rightPrior leftSite point hresult
                (Sum.inl.inj heq.symm)
      | inr rightSite =>
          apply congrArg Sum.inr
          apply (tracePoints_compile_injective next answers hactive)
          change tracePoint (compile next) answers leftSite =
            tracePoint (compile next) answers rightSite
          exact heq

/-- Activity-pattern preservation states that real and simulated executions
issue a shared-oracle query at exactly the same bounded coordinates.  It is
the refinement condition needed to ensure the coupling never exchanges a
real oracle coordinate with a private dummy coordinate. -/
def SameActivity {sites : ℕ}
    (left right : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites) : Prop :=
  ∀ site,
    (left site (priorAnswers answers site)).isSome =
      (right site (priorAnswers answers site)).isSome

theorem compile_sameActivity {sites : ℕ}
    (left right : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (answers : History (Outcome := Outcome) sites)
    (hactivity : SameActivity left right answers) (site : Fin sites) :
    (∃ point, tracePoint (compile left) answers site = Sum.inl point) ↔
      (∃ point, tracePoint (compile right) answers site = Sum.inl point) := by
  rw [tracePoint_compile, tracePoint_compile]
  specialize hactivity site
  generalize hleft : left site (priorAnswers answers site) = leftResult at hactivity
  generalize hright : right site (priorAnswers answers site) = rightResult at hactivity
  cases leftResult <;> cases rightResult <;> simp_all

/-! ## Exact probability of an optional adaptive trace -/

/-- Shared-oracle/dummy-tape inputs whose realized optional answer history
belongs to `bad`.  Inactive coordinates are private uniform padding and never
touch the shared oracle. -/
noncomputable def optionalBadInputs [Fintype Outcome] [DecidableEq Outcome]
    {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (bad : Finset (History (Outcome := Outcome) sites)) :
    Finset ((Point → Outcome) × (Fin (sites + 1) → Outcome)) :=
  Finset.univ.filter fun input => run next input.1 input.2 ∈ bad

@[simp]
theorem mem_optionalBadInputs_iff [Fintype Outcome] [DecidableEq Outcome]
    {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (bad : Finset (History (Outcome := Outcome) sites))
    (input : (Point → Outcome) × (Fin (sites + 1) → Outcome)) :
    input ∈ optionalBadInputs next bad ↔ run next input.1 input.2 ∈ bad := by
  simp [optionalBadInputs]

/-- A uniformly random shared oracle paired with a uniformly random private
inactive tape produces an exactly uniform fixed-length answer history. -/
theorem optionalBadInputs_probability_eq [Fintype Outcome]
    [DecidableEq Outcome] [Nonempty Outcome] {sites : ℕ}
    (next : OptionalSchedule (Point := Point) (Outcome := Outcome) sites)
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      ActiveInjective next answers)
    (bad : Finset (History (Outcome := Outcome) sites)) :
    ((optionalBadInputs next bad).card : ℚ) /
        Fintype.card ((Point → Outcome) × (Fin (sites + 1) → Outcome)) =
      (bad.card : ℚ) /
        Fintype.card (History (Outcome := Outcome) sites) := by
  classical
  let equiv := oracleDummyEquiv (Point := Point) (Outcome := Outcome) sites
  have hcard : (optionalBadInputs next bad).card =
      (adaptiveBadOracles (compile next) bad).card := by
    apply Finset.card_equiv equiv
    intro input
    rw [mem_optionalBadInputs_iff, mem_adaptiveBadOracles_iff]
    rfl
  rw [hcard]
  rw [show Fintype.card
      ((Point → Outcome) × (Fin (sites + 1) → Outcome)) =
        Fintype.card (CompiledPoint Point sites → Outcome) by
      exact Fintype.card_congr equiv]
  exact adaptiveBadOracles_probability_eq (compile next)
    (fun answers => tracePoints_compile_injective next answers
      (hinjective answers)) bad

end VeiledFlock.OptionalAdaptiveOracle

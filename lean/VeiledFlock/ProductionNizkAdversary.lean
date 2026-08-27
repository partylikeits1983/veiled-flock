import Mathlib.Control.Monad.Basic
import VeiledFlock.AdaptiveOracleProgramming
import VeiledFlock.ConcreteOracle
import VeiledFlock.ProductionAdaptiveAdversary
import VeiledFlock.ProductionBoundedOracle
import VeiledFlock.ProductionFraming
import VeiledFlock.ProductionNizkProof

/-!
# Adaptive malicious-verifier interface for the production NIZK

`VeilFlockProof` is noninteractive: no proof component is released while the
prover is constructing it.  A malicious verifier may nevertheless query the
classical random oracle before requesting the proof and may continue querying
after it receives the complete proof.  Both phases below use the very same
oracle table as the prover or simulator.

The adversary's private computation is represented extensionally by its
random tape together with the complete preceding query/answer history.  This
is equivalent to carrying an explicit deterministic state, while avoiding a
second state whose relation to the visible history would itself need a
refinement theorem.
-/

namespace VeiledFlock.ProductionNizkAdversary

open VeiledFlock.ConcreteOracle
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.Framing
open VeiledFlock.ProductionAdaptiveAdversary
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionNizkProof

/-- Audit identity for every user of the one production random oracle.  The
tag is metadata in the formal execution log, not a second domain or oracle. -/
inductive OracleCaller
  | adversaryPreProof
  | flockZerocheck
  | flockLincheck
  | flockPcs
  | veilCommitment
  | veilConstraint
  | merkle
  | fiatShamir
  | rejection
  | grinding
  | simulatorProgramming
  | adversaryPostProof
  deriving DecidableEq, Fintype

/-- One query made against the shared table. -/
structure OracleCall (maxPointLength : ℕ) where
  caller : OracleCaller
  point : BoundedBytes maxPointLength
  answer : OracleBlock

/-- One simulator programming operation.  Programming events are retained in
the execution audit but are not directly exposed to the adversary.  Their
effect remains observable through subsequent answers from the same table. -/
structure OracleProgramming (maxPointLength : ℕ) where
  point : BoundedBytes maxPointLength
  previous : OracleBlock
  programmed : OracleBlock

/-- Complete internal audit event of the single oracle state. -/
inductive OracleEvent (maxPointLength : ℕ)
  | query (call : OracleCall maxPointLength)
  | program (programming : OracleProgramming maxPointLength)

/-- The sole random-oracle state used by every production component and by
the malicious verifier.  `table` is the finite classical random function;
`events` records its exact causal use. -/
structure SharedOracleState (maxPointLength : ℕ) where
  table : BoundedBytes maxPointLength → OracleBlock
  events : List (OracleEvent maxPointLength)

abbrev SharedOracleM (maxPointLength : ℕ) :=
  StateM (SharedOracleState maxPointLength)

/-- Read the one shared table and append the query to the causal audit. -/
def queryShared {maxPointLength : ℕ} (caller : OracleCaller)
    (point : BoundedBytes maxPointLength) :
    SharedOracleM maxPointLength OracleBlock := fun state =>
  let answer := state.table point
  (answer,
    { state with events := state.events ++
        [.query { caller := caller, point := point, answer := answer }] })

/-- Byte-list adapter used by the production implementations.  In-budget
points read the sole finite table; an out-of-budget point fails closed to the
experiment's explicit fallback rather than consulting a second oracle. -/
def querySharedBytes {maxPointLength : ℕ} (fallback : OracleBlock)
    (caller : OracleCaller) (point : List Byte) :
    SharedOracleM maxPointLength OracleBlock :=
  if hpoint : point.length ≤ maxPointLength then
    queryShared caller (boundBytes point hpoint)
  else
    pure fallback

@[simp]
theorem querySharedBytes_value {maxPointLength : ℕ}
    (fallback : OracleBlock) (caller : OracleCaller) (point : List Byte)
    (state : SharedOracleState maxPointLength) :
    (querySharedBytes fallback caller point state).1 =
      answerBounded fallback state.table point := by
  by_cases hpoint : point.length ≤ maxPointLength
  · simp [querySharedBytes, answerBounded, hpoint, queryShared]
  · simp only [querySharedBytes, answerBounded, dif_neg hpoint]
    rfl

@[simp]
theorem querySharedBytes_table {maxPointLength : ℕ}
    (fallback : OracleBlock) (caller : OracleCaller) (point : List Byte)
    (state : SharedOracleState maxPointLength) :
    (querySharedBytes fallback caller point state).2.table = state.table := by
  by_cases hpoint : point.length ≤ maxPointLength
  · simp [querySharedBytes, hpoint, queryShared]
  · simp only [querySharedBytes, dif_neg hpoint]
    rfl

/-- Whether a point has already been queried by any participant. -/
def wasQueried {maxPointLength : ℕ}
    (state : SharedOracleState maxPointLength)
    (point : BoundedBytes maxPointLength) : Prop :=
  ∃ call, OracleEvent.query call ∈ state.events ∧ call.point = point

/-- Whether the simulator has already programmed a point. -/
def wasProgrammed {maxPointLength : ℕ}
    (state : SharedOracleState maxPointLength)
    (point : BoundedBytes maxPointLength) : Prop :=
  ∃ programming, OracleEvent.program programming ∈ state.events ∧
    programming.point = point

/-- A programming conflict is precisely an attempted change to an answer at a
point that has already been queried. -/
def ProgramConflict {maxPointLength : ℕ}
    (state : SharedOracleState maxPointLength)
    (point : BoundedBytes maxPointLength) (answer : OracleBlock) : Prop :=
  (wasQueried state point ∨ wasProgrammed state point) ∧
    state.table point ≠ answer

/-- Program the shared table, failing without mutation if a previously
observed answer would change. -/
noncomputable def programShared {maxPointLength : ℕ}
    (point : BoundedBytes maxPointLength) (answer : OracleBlock) :
    SharedOracleM maxPointLength (Except Unit Unit) := by
  classical
  intro state
  if _hconflict : ProgramConflict state point answer then
    exact (.error (), state)
  else
    let previous := state.table point
    exact (.ok (),
        { table := Function.update state.table point answer
          events := state.events ++
          [.program ⟨point, previous, answer⟩] })

/-- Byte-list adapter for simulator programming.  Out-of-budget points are
reported as conflicts and leave the unique shared table unchanged. -/
noncomputable def programSharedBytes {maxPointLength : ℕ}
    (point : List Byte) (answer : OracleBlock) :
    SharedOracleM maxPointLength (Except Unit Unit) :=
  if hpoint : point.length ≤ maxPointLength then
    programShared (boundBytes point hpoint) answer
  else
    pure (.error ())

/-- Run a causal Fiat--Shamir schedule against the shared table.  The next
point is computed only from the answers to earlier points, exactly as in
`AdaptiveOracleProgramming.Schedule`. -/
def runSharedSchedule {maxPointLength : ℕ} (caller : OracleCaller)
    (schedule : Schedule (Point := BoundedBytes maxPointLength)
      (Outcome := OracleBlock)) :
    (sites : ℕ) → SharedOracleM maxPointLength
      (History (Outcome := OracleBlock) sites)
  | 0 => pure Fin.elim0
  | sites + 1 => do
      let prior ← runSharedSchedule caller schedule sites
      let answer ← queryShared caller (schedule sites prior)
      pure (Fin.lastCases answer prior)

/-- Run an unbounded byte-level causal schedule through the bounded shared
oracle adapter.  This is the direct execution form of the production
`FsChallenger` transcript schedule. -/
def runSharedByteSchedule {maxPointLength : ℕ} (fallback : OracleBlock)
    (caller : OracleCaller)
    (schedule : Schedule (Point := List Byte) (Outcome := OracleBlock)) :
    (sites : ℕ) → SharedOracleM maxPointLength
      (History (Outcome := OracleBlock) sites)
  | 0 => pure Fin.elim0
  | sites + 1 => do
      let prior ← runSharedByteSchedule fallback caller schedule sites
      let answer ← querySharedBytes fallback caller (schedule sites prior)
      pure (Fin.lastCases answer prior)

/-- Honest schedule queries only append audit events; the unique oracle table
is unchanged. -/
theorem runSharedByteSchedule_table {maxPointLength sites : ℕ}
    (fallback : OracleBlock) (caller : OracleCaller)
    (schedule : Schedule (Point := List Byte) (Outcome := OracleBlock))
    (state : SharedOracleState maxPointLength) :
    ((runSharedByteSchedule fallback caller schedule sites) state).2.table =
      state.table := by
  induction sites with
  | zero => rfl
  | succ sites ih =>
      let prior :=
        (runSharedByteSchedule fallback caller schedule sites) state
      change
        (querySharedBytes fallback caller (schedule sites prior.1)
          prior.2).2.table = state.table
      rw [querySharedBytes_table]
      exact ih

/-- The value returned by the stateful honest schedule is exactly the pure
adaptive-oracle run against the bounded view of that same table. -/
theorem runSharedByteSchedule_value {maxPointLength sites : ℕ}
    (fallback : OracleBlock) (caller : OracleCaller)
    (schedule : Schedule (Point := List Byte) (Outcome := OracleBlock))
    (state : SharedOracleState maxPointLength) :
    ((runSharedByteSchedule fallback caller schedule sites) state).1 =
      AdaptiveOracleProgramming.run schedule
        (answerBounded fallback state.table) sites := by
  induction sites with
  | zero => rfl
  | succ sites ih =>
      change
        (let priorResult :
              History (Outcome := OracleBlock) sites ×
                SharedOracleState maxPointLength :=
            (runSharedByteSchedule fallback caller schedule sites) state
         let answerResult : OracleBlock × SharedOracleState maxPointLength :=
            querySharedBytes fallback caller
              (schedule sites priorResult.1) priorResult.2
         fun i : Fin (sites + 1) =>
            @Fin.lastCases sites (fun _ => OracleBlock)
              answerResult.1 priorResult.1 i) =
        (let prior := AdaptiveOracleProgramming.run schedule
            (answerBounded fallback state.table) sites
         let answer := answerBounded fallback state.table
            (schedule sites prior)
         fun i : Fin (sites + 1) =>
            @Fin.lastCases sites (fun _ => OracleBlock) answer prior i)
      dsimp only
      rw [querySharedBytes_value, runSharedByteSchedule_table, ih]

/-- Install the simulator-selected answers at every point of one causal
schedule.  Each point is derived from the already selected prefix, and every
write targets the same table later read by the adversary. -/
noncomputable def programSharedSchedule {maxPointLength sites : ℕ}
    (schedule : Schedule (Point := BoundedBytes maxPointLength)
      (Outcome := OracleBlock))
    (answers : History (Outcome := OracleBlock) sites) :
    SharedOracleM maxPointLength (Except Unit Unit) := by
  classical
  let points := List.ofFn fun site => tracePoint schedule answers site
  let targets := List.ofFn answers
  exact (points.zip targets).foldlM
    (fun result entry => match result with
      | .error conflict => pure (.error conflict)
      | .ok () => programShared entry.1 entry.2)
    (.ok ())

/-- Program a concrete list of byte-point/answer entries in order, stopping at
the first conflict. -/
noncomputable def programSharedByteEntries {maxPointLength : ℕ} :
    List (List Byte × OracleBlock) →
      SharedOracleM maxPointLength (Except Unit Unit)
  | [] => pure (.ok ())
  | entry :: entries => fun state =>
      let result := programSharedBytes entry.1 entry.2 state
      match result.1 with
      | .error conflict => (.error conflict, result.2)
      | .ok () => programSharedByteEntries entries result.2

/-- A successful byte-level programming step performs exactly one bounded
functional update. -/
theorem programSharedBytes_table_of_ok {maxPointLength : ℕ}
    (point : List Byte) (answer : OracleBlock)
    (state : SharedOracleState maxPointLength)
    (hok : (programSharedBytes point answer state).1 = .ok ()) :
    ∃ hpoint : point.length ≤ maxPointLength,
      (programSharedBytes point answer state).2.table =
        Function.update state.table (boundBytes point hpoint) answer := by
  by_cases hpoint : point.length ≤ maxPointLength
  · simp only [programSharedBytes, dif_pos hpoint] at hok ⊢
    refine ⟨hpoint, ?_⟩
    unfold programShared at hok ⊢
    by_cases hconflict : ProgramConflict state (boundBytes point hpoint) answer
    · simp only [dif_pos hconflict] at hok
      contradiction
    · simp only [dif_neg hconflict]
  · simp only [programSharedBytes, dif_neg hpoint] at hok
    contradiction

/-- If an ordered programming run succeeds, and its entries contain exactly
the locations where the initial table may differ from a target table, then
the final shared table is that target.  No freshness is assumed here: success
already records that no conflicting observed write occurred. -/
theorem programSharedByteEntries_restores {maxPointLength : ℕ}
    (entries : List (List Byte × OracleBlock))
    (target : BoundedBytes maxPointLength → OracleBlock)
    (state : SharedOracleState maxPointLength)
    (hfits : ∀ entry ∈ entries, entry.1.length ≤ maxPointLength)
    (htarget : ∀ entry ∈ entries,
      ∀ hfit : entry.1.length ≤ maxPointLength,
        target (boundBytes entry.1 hfit) = entry.2)
    (hoff : ∀ point,
      (∀ entry ∈ entries,
        ∀ hfit : entry.1.length ≤ maxPointLength,
          point ≠ boundBytes entry.1 hfit) →
      state.table point = target point)
    (hok : (programSharedByteEntries entries state).1 = .ok ()) :
    (programSharedByteEntries entries state).2.table = target := by
  induction entries generalizing state with
  | nil =>
      apply funext
      intro point
      exact hoff point (by simp)
  | cons entry entries ih =>
      simp only [programSharedByteEntries] at hok ⊢
      generalize hhead : programSharedBytes entry.1 entry.2 state = headResult
        at hok ⊢
      cases headResult with
      | mk result nextState =>
          cases result with
          | error conflict =>
              simp only [hhead] at hok
              contradiction
          | ok _unit =>
              simp only [hhead] at hok ⊢
              have hheadOk :
                  (programSharedBytes entry.1 entry.2 state).1 = .ok () := by
                rw [hhead]
              have hheadTable := programSharedBytes_table_of_ok
                entry.1 entry.2 state hheadOk
              obtain ⟨hentryFits, htable⟩ := hheadTable
              have hnextTable : nextState.table =
                  Function.update state.table
                    (boundBytes entry.1 hentryFits) entry.2 := by
                rw [← htable, hhead]
              apply ih nextState
              · intro current hmem
                exact hfits current (by simp [hmem])
              · intro current hmem hfit
                exact htarget current (by simp [hmem]) hfit
              · intro point hoffTail
                rw [hnextTable]
                by_cases heq : point = boundBytes entry.1 hentryFits
                · subst point
                  simp only [Function.update_self]
                  exact (htarget entry (by simp) hentryFits).symm
                · simp only [Function.update, heq]
                  apply hoff point
                  intro current hmem
                  rcases List.mem_cons.mp hmem with he | hmem
                  · subst current
                    intro hfit
                    simpa only [Subsingleton.elim hfit hentryFits] using heq
                  · intro hfit
                    exact hoffTail current hmem hfit
              · exact hok

theorem zip_ofFn {n : ℕ} {A B : Type*} (left : Fin n → A)
    (right : Fin n → B) :
    (List.ofFn left).zip (List.ofFn right) =
      List.ofFn (fun site ↦ (left site, right site)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.zip_cons_cons, List.cons.injEq, true_and]
      exact ih (fun site ↦ left site.succ) (fun site ↦ right site.succ)

/-- Program an exact causal byte schedule through the same bounded adapter. -/
noncomputable def programSharedByteSchedule {maxPointLength sites : ℕ}
    (schedule : Schedule (Point := List Byte) (Outcome := OracleBlock))
    (answers : History (Outcome := OracleBlock) sites) :
    SharedOracleM maxPointLength (Except Unit Unit) :=
  let points := List.ofFn fun site => tracePoint schedule answers site
  let targets := List.ofFn answers
  programSharedByteEntries (points.zip targets)

/-- Successful programming of a complete causal schedule restores any target
table which already agrees off the scheduled points and contains the selected
answer at every scheduled point. -/
theorem programSharedByteSchedule_restores {maxPointLength sites : ℕ}
    (schedule : Schedule (Point := List Byte) (Outcome := OracleBlock))
    (answers : History (Outcome := OracleBlock) sites)
    (target : BoundedBytes maxPointLength → OracleBlock)
    (state : SharedOracleState maxPointLength)
    (hfits : ∀ site, (tracePoint schedule answers site).length ≤
      maxPointLength)
    (htarget : ∀ site,
      target (boundBytes (tracePoint schedule answers site) (hfits site)) =
        answers site)
    (hoff : ∀ point,
      (∀ site, point ≠
        boundBytes (tracePoint schedule answers site) (hfits site)) →
      state.table point = target point)
    (hok : (programSharedByteSchedule schedule answers state).1 = .ok ()) :
    (programSharedByteSchedule schedule answers state).2.table = target := by
  let entries := List.ofFn fun site ↦
    (tracePoint schedule answers site, answers site)
  have hschedule :
      @programSharedByteSchedule maxPointLength sites schedule answers =
        @programSharedByteEntries maxPointLength entries := by
    simp only [programSharedByteSchedule, entries, zip_ofFn]
  rw [hschedule] at hok ⊢
  apply programSharedByteEntries_restores entries target state
  · intro entry hmem
    rw [List.mem_ofFn] at hmem
    obtain ⟨site, hsite⟩ := hmem
    rw [← hsite]
    exact hfits site
  · intro entry hmem hfit
    rw [List.mem_ofFn] at hmem
    obtain ⟨site, hsite⟩ := hmem
    subst entry
    simpa only [Subsingleton.elim hfit (hfits site)] using htarget site
  · intro point hoffEntries
    apply hoff point
    intro site heq
    exact hoffEntries (tracePoint schedule answers site, answers site)
      (by rw [List.mem_ofFn]; exact ⟨site, rfl⟩)
      (hfits site) (by simpa only using heq)
  · exact hok

/-- Query/answer pairs visible to one adversarial phase. -/
def adversaryCalls {maxPointLength : ℕ} (caller : OracleCaller)
    (events : List (OracleEvent maxPointLength)) :
    List (BoundedBytes maxPointLength × OracleBlock) :=
  events.filterMap fun event => match event with
    | .query call =>
        if call.caller = caller then some (call.point, call.answer) else none
    | .program _ => none

variable {AdversaryCoins FinalState Rest : Type*}

/-- The complete information available to the malicious verifier in one
production NIZK execution.  `proof` is an `Option` so fail-closed rejection or
grinding aborts remain visible.  It is the conservative complete formal
protocol proof, not proof bytes alone. -/
structure ProductionView (shape : ConcreteParameters.BatchShape)
    (Rest : Type*) (maxPointLength : ℕ) where
  statement : ProductionStatement shape
  adversaryRandomness : AdversaryCoins
  proof : Option (FormalVeilFlockProof shape Rest)
  oracleView : OracleView (Point := BoundedBytes maxPointLength)
    (Outcome := OracleBlock) (FinalState := FinalState)

/-- A bounded adaptive malicious verifier for a noninteractive proof.  It may
query before the proof and, after receiving the complete proof, issue later
queries depending on the proof and on every previous oracle response.

No witness occurs in this interface.  Randomized/private adversarial state is
represented by `AdversaryCoins`; arbitrary deterministic state evolution is
captured by dependence on the complete query/answer histories. -/
structure ProductionAdversary (shape : ConcreteParameters.BatchShape)
    (Rest : Type*) (maxPointLength preQueries postQueries : ℕ)
    where
  preQuery : Fin preQueries → ProductionStatement shape → AdversaryCoins →
    List (BoundedBytes maxPointLength × OracleBlock) →
      Option (BoundedBytes maxPointLength)
  postQuery : Fin postQueries → ProductionStatement shape →
    Option (FormalVeilFlockProof shape Rest) →
    AdversaryCoins →
    List (BoundedBytes maxPointLength × OracleBlock) →
    List (BoundedBytes maxPointLength × OracleBlock) →
      Option (BoundedBytes maxPointLength)
  finish : ProductionStatement shape → Option (FormalVeilFlockProof shape Rest) →
    AdversaryCoins →
    List (BoundedBytes maxPointLength × OracleBlock) →
    List (BoundedBytes maxPointLength × OracleBlock) → FinalState

private def runQueryList {maxPointLength sites : ℕ}
    (caller : OracleCaller)
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength)) :
    List (Fin sites) →
      List (BoundedBytes maxPointLength × OracleBlock) →
        SharedOracleM maxPointLength
          (List (BoundedBytes maxPointLength × OracleBlock))
  | [], history => pure history
  | round :: rounds, history => do
      match nextQuery round history with
      | none => runQueryList caller nextQuery rounds history
      | some point =>
          let answer ← queryShared caller point
          runQueryList caller nextQuery rounds
            (history ++ [(point, answer)])

/-- Pure value-level semantics of one optional adaptive query phase. -/
def runQueryValues {maxPointLength sites : ℕ}
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (table : BoundedBytes maxPointLength → OracleBlock) :
    List (Fin sites) →
      List (BoundedBytes maxPointLength × OracleBlock) →
        List (BoundedBytes maxPointLength × OracleBlock)
  | [], history => history
  | round :: rounds, history =>
      match nextQuery round history with
      | none => runQueryValues nextQuery table rounds history
      | some point => runQueryValues nextQuery table rounds
          (history ++ [(point, table point)])

theorem runQueryList_value {maxPointLength sites : ℕ}
    (caller : OracleCaller)
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (rounds : List (Fin sites))
    (history : List (BoundedBytes maxPointLength × OracleBlock))
    (state : SharedOracleState maxPointLength) :
    (runQueryList caller nextQuery rounds history state).1 =
      runQueryValues nextQuery state.table rounds history := by
  induction rounds generalizing history state with
  | nil => rfl
  | cons round rounds ih =>
      rw [runQueryList, runQueryValues]
      cases hquery : nextQuery round history with
      | none =>
          simp only [hquery]
          exact ih history state
      | some point =>
          simp only [hquery, queryShared]
          exact ih (history ++ [(point, state.table point)]) _

theorem runQueryList_table {maxPointLength sites : ℕ}
    (caller : OracleCaller)
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (rounds : List (Fin sites))
    (history : List (BoundedBytes maxPointLength × OracleBlock))
    (state : SharedOracleState maxPointLength) :
    (runQueryList caller nextQuery rounds history state).2.table =
      state.table := by
  induction rounds generalizing history state with
  | nil => rfl
  | cons round rounds ih =>
      rw [runQueryList]
      cases hquery : nextQuery round history with
      | none =>
          simp only [hquery]
          exact ih history state
      | some point =>
          simp only [hquery, queryShared]
          exact ih (history ++ [(point, state.table point)]) _

theorem runQueryValues_prefix {maxPointLength sites : ℕ}
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (table : BoundedBytes maxPointLength → OracleBlock)
    (rounds : List (Fin sites))
    (history : List (BoundedBytes maxPointLength × OracleBlock)) :
    history <+: runQueryValues nextQuery table rounds history := by
  induction rounds generalizing history with
  | nil => exact List.prefix_refl _
  | cons round rounds ih =>
      simp only [runQueryValues]
      split
      · exact ih history
      · exact (List.prefix_append history _).trans
          (ih (history ++ [(_, table _)]))

/-- Adaptive query histories are identical when the two tables agree at every
point actually reached by the left execution. -/
theorem runQueryValues_eq_of_agrees_on_result {maxPointLength sites : ℕ}
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (left right : BoundedBytes maxPointLength → OracleBlock)
    (rounds : List (Fin sites))
    (history : List (BoundedBytes maxPointLength × OracleBlock))
    (hagrees : ∀ call ∈ runQueryValues nextQuery left rounds history,
      right call.1 = left call.1) :
    runQueryValues nextQuery right rounds history =
      runQueryValues nextQuery left rounds history := by
  induction rounds generalizing history with
  | nil => rfl
  | cons round rounds ih =>
      rw [runQueryValues, runQueryValues]
      cases hquery : nextQuery round history with
      | none =>
        simp only [runQueryValues, hquery] at hagrees
        simp only [hquery]
        exact ih history hagrees
      | some point =>
        simp only [runQueryValues, hquery] at hagrees
        simp only [hquery]
        have hmem : (point, left point) ∈
            runQueryValues nextQuery left rounds
              (history ++ [(point, left point)]) :=
          (runQueryValues_prefix nextQuery left rounds
            (history ++ [(point, left point)])).mem (by simp)
        have hanswer := hagrees (point, left point) hmem
        rw [hanswer]
        exact ih (history ++ [(point, left point)]) hagrees

/-- Execute every allowed adaptive pre-proof query against the shared table. -/
def runPreQueries {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (coins : AdversaryCoins) :
    SharedOracleM maxPointLength
      (List (BoundedBytes maxPointLength × OracleBlock)) :=
  runQueryList .adversaryPreProof
    (fun round history => adversary.preQuery round statement coins history)
    (List.ofFn id) []

@[simp]
theorem runPreQueries_value {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (coins : AdversaryCoins)
    (state : SharedOracleState maxPointLength) :
    (runPreQueries adversary statement coins state).1 =
      runQueryValues
        (fun round history => adversary.preQuery round statement coins history)
        state.table (List.ofFn id) [] := by
  exact runQueryList_value .adversaryPreProof _ _ _ state

@[simp]
theorem runPreQueries_table {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (coins : AdversaryCoins)
    (state : SharedOracleState maxPointLength) :
    (runPreQueries adversary statement coins state).2.table = state.table := by
  exact runQueryList_table .adversaryPreProof _ _ _ state

/-- Execute every allowed adaptive post-proof query against the same table. -/
def runPostQueries {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (proof : Option (FormalVeilFlockProof shape Rest)) (coins : AdversaryCoins)
    (preHistory :
      List (BoundedBytes maxPointLength × OracleBlock)) :
    SharedOracleM maxPointLength
      (List (BoundedBytes maxPointLength × OracleBlock)) :=
  runQueryList .adversaryPostProof
    (fun round history => adversary.postQuery round statement proof coins
      preHistory history)
    (List.ofFn id) []

@[simp]
theorem runPostQueries_value {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (proof : Option (FormalVeilFlockProof shape Rest))
    (coins : AdversaryCoins)
    (preHistory : List (BoundedBytes maxPointLength × OracleBlock))
    (state : SharedOracleState maxPointLength) :
    (runPostQueries adversary statement proof coins preHistory state).1 =
      runQueryValues
        (fun round history => adversary.postQuery round statement proof coins
          preHistory history)
        state.table (List.ofFn id) [] := by
  exact runQueryList_value .adversaryPostProof _ _ _ state

@[simp]
theorem runPostQueries_table {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (proof : Option (FormalVeilFlockProof shape Rest))
    (coins : AdversaryCoins)
    (preHistory : List (BoundedBytes maxPointLength × OracleBlock))
    (state : SharedOracleState maxPointLength) :
    (runPostQueries adversary statement proof coins preHistory state).2.table =
      state.table := by
  exact runQueryList_table .adversaryPostProof _ _ _ state

/-- Connect the two adversarial query phases to the existing exact
`OracleView`: it contains every actual adversarial query/answer pair and the
adversary's final state/output. -/
def finishOracleView {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (proof : Option (FormalVeilFlockProof shape Rest)) (coins : AdversaryCoins)
    (preHistory postHistory :
      List (BoundedBytes maxPointLength × OracleBlock)) :
    OracleView (Point := BoundedBytes maxPointLength)
      (Outcome := OracleBlock) (FinalState := FinalState) where
  queries := preHistory ++ postHistory
  finalState := adversary.finish statement proof coins preHistory postHistory

@[simp]
theorem finishOracleView_queries {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape)
    (proof : Option (FormalVeilFlockProof shape Rest)) (coins : AdversaryCoins)
    (preHistory postHistory :
      List (BoundedBytes maxPointLength × OracleBlock)) :
    (finishOracleView adversary statement proof coins preHistory
      postHistory).queries = preHistory ++ postHistory := rfl

end VeiledFlock.ProductionNizkAdversary

import Mathlib.Control.Monad.Basic
import VeiledFlock.Oracle.AdaptiveOracleProgramming
import VeiledFlock.Concrete.ConcreteOracle
import VeiledFlock.Production.Nizk.AdaptiveAdversary
import VeiledFlock.Production.Nizk.BoundedOracle
import VeiledFlock.Production.Core.Framing
import VeiledFlock.Production.Nizk.NizkProof

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

/-- A fitted point which has neither been queried nor programmed can always
be programmed.  No assumption about its current hidden table value is needed. -/
theorem programSharedBytes_ok_of_fresh {maxPointLength : ℕ}
    (point : List Byte) (answer : OracleBlock)
    (state : SharedOracleState maxPointLength)
    (hfit : point.length ≤ maxPointLength)
    (hquery : ¬ wasQueried state (boundBytes point hfit))
    (hprogram : ¬ wasProgrammed state (boundBytes point hfit)) :
    (programSharedBytes point answer state).1 = .ok () := by
  simp only [programSharedBytes, dif_pos hfit]
  unfold programShared
  have hconflict :
      ¬ ProgramConflict state (boundBytes point hfit) answer := by
    simp [ProgramConflict, hquery, hprogram]
  simp only [dif_neg hconflict]

/-- Successful fresh programming adds no query event. -/
theorem wasQueried_programSharedBytes_of_fresh {maxPointLength : ℕ}
    (point : List Byte) (answer : OracleBlock)
    (state : SharedOracleState maxPointLength)
    (hfit : point.length ≤ maxPointLength)
    (hquery : ¬ wasQueried state (boundBytes point hfit))
    (hprogram : ¬ wasProgrammed state (boundBytes point hfit))
    (other : BoundedBytes maxPointLength) :
    wasQueried (programSharedBytes point answer state).2 other ↔
      wasQueried state other := by
  simp only [programSharedBytes, dif_pos hfit]
  unfold programShared
  have hconflict :
      ¬ ProgramConflict state (boundBytes point hfit) answer := by
    simp [ProgramConflict, hquery, hprogram]
  simp only [dif_neg hconflict]
  simp [wasQueried]

/-- Successful fresh programming records exactly the newly programmed point
in addition to any earlier programming events. -/
theorem wasProgrammed_programSharedBytes_of_fresh {maxPointLength : ℕ}
    (point : List Byte) (answer : OracleBlock)
    (state : SharedOracleState maxPointLength)
    (hfit : point.length ≤ maxPointLength)
    (hquery : ¬ wasQueried state (boundBytes point hfit))
    (hprogram : ¬ wasProgrammed state (boundBytes point hfit))
    (other : BoundedBytes maxPointLength) :
    wasProgrammed (programSharedBytes point answer state).2 other ↔
      wasProgrammed state other ∨ other = boundBytes point hfit := by
  simp only [programSharedBytes, dif_pos hfit]
  unfold programShared
  have hconflict :
      ¬ ProgramConflict state (boundBytes point hfit) answer := by
    simp [ProgramConflict, hquery, hprogram]
  simp only [dif_neg hconflict]
  simp [wasProgrammed, eq_comm]

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

/-- An ordered list of distinct, fitted byte points programs successfully
when every point is fresh in the initial state. -/
theorem programSharedByteEntries_ok_of_fresh {maxPointLength : ℕ}
    (entries : List (List Byte × OracleBlock))
    (state : SharedOracleState maxPointLength)
    (hfits : ∀ entry ∈ entries, entry.1.length ≤ maxPointLength)
    (hnodup : (entries.map Prod.fst).Nodup)
    (hqueries : ∀ entry ∈ entries,
      ∀ hfit : entry.1.length ≤ maxPointLength,
        ¬ wasQueried state (boundBytes entry.1 hfit))
    (hprograms : ∀ entry ∈ entries,
      ∀ hfit : entry.1.length ≤ maxPointLength,
        ¬ wasProgrammed state (boundBytes entry.1 hfit)) :
    (programSharedByteEntries entries state).1 = .ok () := by
  classical
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries ih =>
      have hentryMem : entry ∈ entry :: entries := by simp
      let hentryFit := hfits entry hentryMem
      have hentryQuery :
          ¬ wasQueried state (boundBytes entry.1 hentryFit) := by
        exact hqueries entry hentryMem hentryFit
      have hentryProgram :
          ¬ wasProgrammed state (boundBytes entry.1 hentryFit) := by
        exact hprograms entry hentryMem hentryFit
      have hhead := programSharedBytes_ok_of_fresh entry.1 entry.2 state
        hentryFit hentryQuery hentryProgram
      have hnodupParts := List.nodup_cons.mp hnodup
      have htailFits : ∀ current ∈ entries,
          current.1.length ≤ maxPointLength := by
        intro current hmem
        exact hfits current (by simp [hmem])
      have htailQueries : ∀ current ∈ entries,
          ∀ hcurrentFit : current.1.length ≤ maxPointLength,
            ¬ wasQueried (programSharedBytes entry.1 entry.2 state).2
              (boundBytes current.1 hcurrentFit) := by
        intro current hmem hcurrentFit
        rw [wasQueried_programSharedBytes_of_fresh entry.1 entry.2 state
          hentryFit hentryQuery hentryProgram]
        exact hqueries current (by simp [hmem]) hcurrentFit
      have htailPrograms : ∀ current ∈ entries,
          ∀ hcurrentFit : current.1.length ≤ maxPointLength,
            ¬ wasProgrammed (programSharedBytes entry.1 entry.2 state).2
              (boundBytes current.1 hcurrentFit) := by
        intro current hmem hcurrentFit
        rw [wasProgrammed_programSharedBytes_of_fresh entry.1 entry.2 state
          hentryFit hentryQuery hentryProgram]
        push Not
        constructor
        · exact hprograms current (by simp [hmem]) hcurrentFit
        · intro heq
          have hunbound := congrArg unboundBytes heq
          simp only [unbound_boundBytes] at hunbound
          apply hnodupParts.1
          exact List.mem_map.mpr ⟨current, hmem, hunbound⟩
      simp only [programSharedByteEntries]
      rw [hhead]
      exact ih (programSharedBytes entry.1 entry.2 state).2 htailFits
        hnodupParts.2 htailQueries htailPrograms

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
              simp only  at hok
              contradiction
          | ok _unit =>
              simp only  at hok ⊢
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

/-- A fitted injective causal schedule succeeds whenever none of its realized
points occurs in the state's prior query or programming audit. -/
theorem programSharedByteSchedule_ok_of_fresh {maxPointLength sites : ℕ}
    (schedule : Schedule (Point := List Byte) (Outcome := OracleBlock))
    (answers : History (Outcome := OracleBlock) sites)
    (state : SharedOracleState maxPointLength)
    (hfits : ∀ site, (tracePoint schedule answers site).length ≤
      maxPointLength)
    (hinjective : Function.Injective
      (fun site => tracePoint schedule answers site))
    (hqueries : ∀ site,
      ¬ wasQueried state
        (boundBytes (tracePoint schedule answers site) (hfits site)))
    (hprograms : ∀ site,
      ¬ wasProgrammed state
        (boundBytes (tracePoint schedule answers site) (hfits site))) :
    (programSharedByteSchedule schedule answers state).1 = .ok () := by
  let entries := List.ofFn fun site =>
    (tracePoint schedule answers site, answers site)
  have hschedule :
      @programSharedByteSchedule maxPointLength sites schedule answers =
        @programSharedByteEntries maxPointLength entries := by
    simp only [programSharedByteSchedule, entries, zip_ofFn]
  rw [hschedule]
  apply programSharedByteEntries_ok_of_fresh entries state
  · intro entry hmem
    rw [List.mem_ofFn] at hmem
    obtain ⟨site, hsite⟩ := hmem
    rw [← hsite]
    exact hfits site
  · have hmap : entries.map Prod.fst =
        List.ofFn (fun site => tracePoint schedule answers site) := by
      simp [entries, List.map_ofFn, Function.comp_def]
    rw [hmap]
    exact List.nodup_ofFn.mpr hinjective
  · intro entry hmem hfit
    rw [List.mem_ofFn] at hmem
    obtain ⟨site, hsite⟩ := hmem
    subst entry
    simpa only [Subsingleton.elim hfit (hfits site)] using hqueries site
  · intro entry hmem hfit
    rw [List.mem_ofFn] at hmem
    obtain ⟨site, hsite⟩ := hmem
    subst entry
    simpa only [Subsingleton.elim hfit (hfits site)] using hprograms site

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

/-- Equality of complete views is decidable in the finite production model.
The classical instance avoids burdening the adversary API with implementation
instances for its private randomness and final-state types. -/
noncomputable instance productionViewDecidableEq
    (shape : ConcreteParameters.BatchShape) (Rest : Type*)
    (maxPointLength : ℕ) :
    DecidableEq (ProductionView (AdversaryCoins := AdversaryCoins)
      (FinalState := FinalState) shape Rest maxPointLength) :=
  Classical.decEq _

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
          simp only
          exact ih history state
      | some point =>
          simp only
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
          simp only
          exact ih history state
      | some point =>
          simp only
          exact ih (history ++ [(point, state.table point)]) _

/-- Audit events corresponding exactly to a visible query/answer history. -/
def queryEvents {maxPointLength : ℕ} (caller : OracleCaller)
    (history : List (BoundedBytes maxPointLength × OracleBlock)) :
    List (OracleEvent maxPointLength) :=
  history.map fun call => .query {
    caller := caller
    point := call.1
    answer := call.2
  }

private theorem runQueryList_events_eq_queryEvents
    {maxPointLength sites : ℕ} (caller : OracleCaller)
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (rounds : List (Fin sites))
    (history : List (BoundedBytes maxPointLength × OracleBlock))
    (state : SharedOracleState maxPointLength)
    (hstate : state.events = queryEvents caller history) :
    (runQueryList caller nextQuery rounds history state).2.events =
      queryEvents caller
        (runQueryList caller nextQuery rounds history state).1 := by
  induction rounds generalizing history state with
  | nil =>
      change state.events = queryEvents caller history
      exact hstate
  | cons round rounds ih =>
      rw [runQueryList]
      cases hquery : nextQuery round history with
      | none =>
          simp only
          exact ih history state hstate
      | some point =>
          simp only
          apply ih
          simp [ queryEvents, hstate]

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

/-- An optional adaptive phase emits at most one visible query/answer pair
per scheduled round. -/
theorem runQueryValues_length_le {maxPointLength sites : ℕ}
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (table : BoundedBytes maxPointLength → OracleBlock)
    (rounds : List (Fin sites))
    (history : List (BoundedBytes maxPointLength × OracleBlock)) :
    (runQueryValues nextQuery table rounds history).length ≤
      history.length + rounds.length := by
  induction rounds generalizing history with
  | nil => simp [runQueryValues]
  | cons round rounds ih =>
      rw [runQueryValues]
      cases hquery : nextQuery round history with
      | none =>
        have htail := ih history
        simp only [ List.length_cons]
        omega
      | some point =>
        have htail := ih (history ++ [(point, table point)])
        simp only [List.length_append, List.length_singleton] at htail
        simp only [ List.length_cons]
        omega

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
        simp only
        exact ih history hagrees
      | some point =>
        simp only [runQueryValues, hquery] at hagrees
        simp only
        have hmem : (point, left point) ∈
            runQueryValues nextQuery left rounds
              (history ++ [(point, left point)]) :=
          (runQueryValues_prefix nextQuery left rounds
            (history ++ [(point, left point)])).mem (by simp)
        have hanswer := hagrees (point, left point) hmem
        rw [hanswer]
        exact ih (history ++ [(point, left point)]) hagrees

/-! ## Identical-until-hidden-query transport -/

/-- A visible adaptive query history reaches one member of a protected point
family.  This predicate records the selected query point, not merely the
answer, so it is suitable for first-hit random-oracle arguments. -/
def QueryHistoryHits {Index Point Outcome : Type*}
    (points : Index → Point) (history : List (Point × Outcome)) : Prop :=
  ∃ call ∈ history, ∃ index, call.1 = points index

theorem queryHistoryHits_of_prefix {Index Point Outcome : Type*}
    (points : Index → Point) {head history : List (Point × Outcome)}
    (hprefix : head <+: history) (hhit : QueryHistoryHits points head) :
    QueryHistoryHits points history := by
  rcases hhit with ⟨call, hcall, index, hpoint⟩
  exact ⟨call, hprefix.mem hcall, index, hpoint⟩

/-- Complement-fixing oracle transport preserves an adaptive execution up to
its first query in either moved family.  Consequently, if the left execution
eventually queries the left family, then either it first reaches the right
family or the transported execution reaches the left family.  These are the
two independently countable events in the averaged hidden-salt proof.

Unlike a final-history extensionality lemma, this statement handles the case
where the two oracle answers differ at the first protected query: membership
of that query is recorded before either continuation can diverge. -/
theorem runQueryValues_hit_transport
    {Index : Type*} {maxPointLength sites : ℕ}
    (nextQuery : Fin sites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (leftPoints rightPoints : Index → BoundedBytes maxPointLength)
    (leftTable rightTable : BoundedBytes maxPointLength → OracleBlock)
    (rounds : List (Fin sites))
    (history : List (BoundedBytes maxPointLength × OracleBlock))
    (hleftHistory : ¬ QueryHistoryHits leftPoints history)
    (hrightHistory : ¬ QueryHistoryHits rightPoints history)
    (hagreesOff : ∀ point,
      (∀ index, point ≠ leftPoints index) →
      (∀ index, point ≠ rightPoints index) →
      rightTable point = leftTable point)
    (hhit : QueryHistoryHits leftPoints
      (runQueryValues nextQuery leftTable rounds history)) :
    QueryHistoryHits rightPoints
        (runQueryValues nextQuery leftTable rounds history) ∨
      QueryHistoryHits leftPoints
        (runQueryValues nextQuery rightTable rounds history) := by
  induction rounds generalizing history with
  | nil =>
      simp only [runQueryValues] at hhit
      exact False.elim (hleftHistory hhit)
  | cons round rounds ih =>
      simp only [runQueryValues] at hhit ⊢
      cases hquery : nextQuery round history with
      | none =>
          simp only [hquery] at hhit ⊢
          exact ih history hleftHistory hrightHistory hhit
      | some point =>
          simp only [hquery] at hhit ⊢
          by_cases hrightPoint : ∃ index, point = rightPoints index
          · left
            obtain ⟨index, hpoint⟩ := hrightPoint
            apply queryHistoryHits_of_prefix rightPoints
              (runQueryValues_prefix nextQuery leftTable rounds
                (history ++ [(point, leftTable point)]))
            exact ⟨(point, leftTable point), by simp, index, hpoint⟩
          · by_cases hleftPoint : ∃ index, point = leftPoints index
            · right
              obtain ⟨index, hpoint⟩ := hleftPoint
              apply queryHistoryHits_of_prefix leftPoints
                (runQueryValues_prefix nextQuery rightTable rounds
                  (history ++ [(point, rightTable point)]))
              exact ⟨(point, rightTable point), by simp, index, hpoint⟩
            · have hrightOff : ∀ index, point ≠ rightPoints index := by
                intro index heq
                exact hrightPoint ⟨index, heq⟩
              have hleftOff : ∀ index, point ≠ leftPoints index := by
                intro index heq
                exact hleftPoint ⟨index, heq⟩
              have hanswer : rightTable point = leftTable point :=
                hagreesOff point hleftOff hrightOff
              rw [hanswer]
              apply ih (history ++ [(point, leftTable point)])
              · intro hbad
                rcases hbad with ⟨call, hcall, index, hcallPoint⟩
                rw [List.mem_append, List.mem_singleton] at hcall
                rcases hcall with hprior | rfl
                · exact hleftHistory ⟨call, hprior, index, hcallPoint⟩
                · exact hleftOff index hcallPoint
              · intro hbad
                rcases hbad with ⟨call, hcall, index, hcallPoint⟩
                rw [List.mem_append, List.mem_singleton] at hcall
                rcases hcall with hprior | rfl
                · exact hrightHistory ⟨call, hprior, index, hcallPoint⟩
                · exact hrightOff index hcallPoint
              · exact hhit

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

/-- Starting from the experiment's empty audit, the pre-proof phase records
exactly its visible query history and no hidden programming events. -/
theorem runPreQueries_events {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (coins : AdversaryCoins)
    (table : BoundedBytes maxPointLength → OracleBlock) :
    (runPreQueries adversary statement coins
      { table := table, events := [] }).2.events =
      queryEvents .adversaryPreProof
        (runPreQueries adversary statement coins
          { table := table, events := [] }).1 := by
  exact runQueryList_events_eq_queryEvents .adversaryPreProof _ _ _ _ rfl

theorem runPreQueries_not_wasProgrammed
    {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (coins : AdversaryCoins)
    (table : BoundedBytes maxPointLength → OracleBlock)
    (point : BoundedBytes maxPointLength) :
    ¬ wasProgrammed
      (runPreQueries adversary statement coins
        { table := table, events := [] }).2 point := by
  rintro ⟨programming, hmem, _⟩
  rw [runPreQueries_events adversary statement coins table] at hmem
  rcases List.mem_map.mp hmem with ⟨call, _, hevent⟩
  contradiction

theorem runPreQueries_wasQueried_mem
    {shape : ConcreteParameters.BatchShape}
    {maxPointLength preQueries postQueries : ℕ}
    (adversary : ProductionAdversary
      (AdversaryCoins := AdversaryCoins) (FinalState := FinalState)
      shape Rest maxPointLength preQueries postQueries)
    (statement : ProductionStatement shape) (coins : AdversaryCoins)
    (table : BoundedBytes maxPointLength → OracleBlock)
    (point : BoundedBytes maxPointLength)
    (hquery : wasQueried
      (runPreQueries adversary statement coins
        { table := table, events := [] }).2 point) :
    ∃ call ∈
      (runPreQueries adversary statement coins
        { table := table, events := [] }).1,
      call.1 = point := by
  rcases hquery with ⟨call, hmem, hpoint⟩
  rw [runPreQueries_events adversary statement coins table] at hmem
  rcases List.mem_map.mp hmem with ⟨visible, hvisible, hevent⟩
  cases hevent
  exact ⟨visible, hvisible, hpoint⟩

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

/-! ## Two-phase adaptive query schedules -/

theorem queryHistoryHits_append_iff {Index Point Outcome : Type*}
    (points : Index → Point) (left right : List (Point × Outcome)) :
    QueryHistoryHits points (left ++ right) ↔
      QueryHistoryHits points left ∨ QueryHistoryHits points right := by
  simp only [QueryHistoryHits, List.mem_append]
  constructor
  · rintro ⟨call, hleft | hright, index, hpoint⟩
    · exact Or.inl ⟨call, hleft, index, hpoint⟩
    · exact Or.inr ⟨call, hright, index, hpoint⟩
  · rintro (⟨call, hcall, index, hpoint⟩ |
      ⟨call, hcall, index, hpoint⟩)
    · exact ⟨call, Or.inl hcall, index, hpoint⟩
    · exact ⟨call, Or.inr hcall, index, hpoint⟩

/-- Execute adaptive pre-proof queries, then post-proof queries whose query
function may depend on the complete pre-proof history. -/
def runTwoPhaseQueryValues {maxPointLength preSites postSites : ℕ}
    (preQuery : Fin preSites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (postQuery : List (BoundedBytes maxPointLength × OracleBlock) →
      Fin postSites → List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (table : BoundedBytes maxPointLength → OracleBlock) :
    List (BoundedBytes maxPointLength × OracleBlock) :=
  let pre := runQueryValues preQuery table (List.ofFn id) []
  pre ++ runQueryValues (postQuery pre) table (List.ofFn id) []

/-- The standard identical-until-bad reduction for the exact two-phase
adaptive schedule used by the production NIZK adversary. -/
theorem runTwoPhaseQueryValues_hit_transport
    {Index : Type*} {maxPointLength preSites postSites : ℕ}
    (preQuery : Fin preSites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (postQuery : List (BoundedBytes maxPointLength × OracleBlock) →
      Fin postSites → List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (leftPoints rightPoints : Index → BoundedBytes maxPointLength)
    (leftTable rightTable : BoundedBytes maxPointLength → OracleBlock)
    (hagreesOff : ∀ point,
      (∀ index, point ≠ leftPoints index) →
      (∀ index, point ≠ rightPoints index) →
      rightTable point = leftTable point)
    (hhit : QueryHistoryHits leftPoints
      (runTwoPhaseQueryValues preQuery postQuery leftTable)) :
    QueryHistoryHits rightPoints
        (runTwoPhaseQueryValues preQuery postQuery leftTable) ∨
      QueryHistoryHits leftPoints
        (runTwoPhaseQueryValues preQuery postQuery rightTable) := by
  let leftPre := runQueryValues preQuery leftTable (List.ofFn id) []
  let rightPre := runQueryValues preQuery rightTable (List.ofFn id) []
  let leftPost := runQueryValues (postQuery leftPre) leftTable
    (List.ofFn id) []
  simp only [runTwoPhaseQueryValues] at hhit ⊢
  rw [queryHistoryHits_append_iff] at hhit
  rcases hhit with hpreHit | hpostHit
  · have htransport := runQueryValues_hit_transport preQuery leftPoints
      rightPoints leftTable rightTable (List.ofFn id) []
      (by simp [QueryHistoryHits]) (by simp [QueryHistoryHits]) hagreesOff
      hpreHit
    rcases htransport with horiginal | hmoved
    · exact Or.inl ((queryHistoryHits_append_iff _ _ _).2 (Or.inl horiginal))
    · exact Or.inr ((queryHistoryHits_append_iff _ _ _).2 (Or.inl hmoved))
  · by_cases hleftPre : QueryHistoryHits leftPoints leftPre
    · have htransport := runQueryValues_hit_transport preQuery leftPoints
        rightPoints leftTable rightTable (List.ofFn id) []
        (by simp [QueryHistoryHits]) (by simp [QueryHistoryHits]) hagreesOff
        hleftPre
      rcases htransport with horiginal | hmoved
      · exact Or.inl ((queryHistoryHits_append_iff _ _ _).2
          (Or.inl horiginal))
      · exact Or.inr ((queryHistoryHits_append_iff _ _ _).2
          (Or.inl hmoved))
    · by_cases hrightPre : QueryHistoryHits rightPoints leftPre
      · exact Or.inl ((queryHistoryHits_append_iff _ _ _).2
          (Or.inl hrightPre))
      · have hpreEq : rightPre = leftPre := by
          exact runQueryValues_eq_of_agrees_on_result preQuery leftTable
            rightTable (List.ofFn id) [] (by
              intro call hcall
              apply hagreesOff call.1
              · intro index heq
                exact hleftPre ⟨call, hcall, index, heq⟩
              · intro index heq
                exact hrightPre ⟨call, hcall, index, heq⟩)
        have hpostTransport := runQueryValues_hit_transport
          (postQuery leftPre) leftPoints rightPoints leftTable rightTable
          (List.ofFn id) [] (by simp [QueryHistoryHits])
          (by simp [QueryHistoryHits]) hagreesOff hpostHit
        rcases hpostTransport with horiginal | hmoved
        · exact Or.inl ((queryHistoryHits_append_iff _ _ _).2
            (Or.inr horiginal))
        · right
          change QueryHistoryHits leftPoints
            (rightPre ++ runQueryValues (postQuery rightPre) rightTable
              (List.ofFn id) [])
          rw [hpreEq]
          exact (queryHistoryHits_append_iff _ _ _).2 (Or.inr hmoved)

/-- If the left two-phase execution never reaches either moved family, the
whole adaptive history is identical under the transported oracle. -/
theorem runTwoPhaseQueryValues_eq_of_avoids
    {Index : Type*} {maxPointLength preSites postSites : ℕ}
    (preQuery : Fin preSites →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (postQuery : List (BoundedBytes maxPointLength × OracleBlock) →
      Fin postSites → List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (leftPoints rightPoints : Index → BoundedBytes maxPointLength)
    (leftTable rightTable : BoundedBytes maxPointLength → OracleBlock)
    (hagreesOff : ∀ point,
      (∀ index, point ≠ leftPoints index) →
      (∀ index, point ≠ rightPoints index) →
      rightTable point = leftTable point)
    (hleft : ¬ QueryHistoryHits leftPoints
      (runTwoPhaseQueryValues preQuery postQuery leftTable))
    (hright : ¬ QueryHistoryHits rightPoints
      (runTwoPhaseQueryValues preQuery postQuery leftTable)) :
    runTwoPhaseQueryValues preQuery postQuery rightTable =
      runTwoPhaseQueryValues preQuery postQuery leftTable := by
  let leftPre := runQueryValues preQuery leftTable (List.ofFn id) []
  let rightPre := runQueryValues preQuery rightTable (List.ofFn id) []
  have hleftPre : ¬ QueryHistoryHits leftPoints leftPre := by
    intro hhit
    apply hleft
    exact queryHistoryHits_of_prefix leftPoints
      (List.prefix_append leftPre _) hhit
  have hrightPre : ¬ QueryHistoryHits rightPoints leftPre := by
    intro hhit
    apply hright
    exact queryHistoryHits_of_prefix rightPoints
      (List.prefix_append leftPre _) hhit
  have hpreEq : rightPre = leftPre := by
    exact runQueryValues_eq_of_agrees_on_result preQuery leftTable rightTable
      (List.ofFn id) [] (by
        intro call hcall
        apply hagreesOff call.1
        · intro index heq
          exact hleftPre ⟨call, hcall, index, heq⟩
        · intro index heq
          exact hrightPre ⟨call, hcall, index, heq⟩)
  have hleftPost : ¬ QueryHistoryHits leftPoints
      (runQueryValues (postQuery leftPre) leftTable (List.ofFn id) []) := by
    intro hhit
    apply hleft
    exact (queryHistoryHits_append_iff _ _ _).2 (Or.inr hhit)
  have hrightPost : ¬ QueryHistoryHits rightPoints
      (runQueryValues (postQuery leftPre) leftTable (List.ofFn id) []) := by
    intro hhit
    apply hright
    exact (queryHistoryHits_append_iff _ _ _).2 (Or.inr hhit)
  have hpostEq := runQueryValues_eq_of_agrees_on_result
    (postQuery leftPre) leftTable rightTable (List.ofFn id) [] (by
      intro call hcall
      apply hagreesOff call.1
      · intro index heq
        exact hleftPost ⟨call, hcall, index, heq⟩
      · intro index heq
        exact hrightPost ⟨call, hcall, index, heq⟩)
  simp only [runTwoPhaseQueryValues]
  change rightPre ++
      runQueryValues (postQuery rightPre) rightTable (List.ofFn id) [] =
    leftPre ++
      runQueryValues (postQuery leftPre) leftTable (List.ofFn id) []
  rw [hpreEq]
  exact congrArg (leftPre ++ ·) hpostEq

end VeiledFlock.ProductionNizkAdversary

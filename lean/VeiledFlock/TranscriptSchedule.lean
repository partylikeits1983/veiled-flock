import VeiledFlock.AdaptiveOracleProgramming
import VeiledFlock.Framing

/-!
# Append-only Fiat--Shamir programming schedule

The Rust challenger names a scalar squeeze by appending an eight-byte counter
to the complete absorbed transcript.  A sampled scalar reabsorbs sixteen
bytes; each simulated recursive round then observes two framed field elements
and absorbs the next scalar-squeeze tag.  Thus consecutive programmed points
grow by exactly 54 bytes and cannot coincide.

This module proves that byte-level fact independently of the field values and
round messages.  It is the distinct-programming-points premise required by the
exact adaptive-oracle simulator theorem.
-/

namespace VeiledFlock.TranscriptSchedule

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.Framing

variable {Outcome Message : Type*}

def counterZero : List Byte := List.replicate 8 0

@[simp]
theorem counterZero_length : counterZero.length = 8 := by
  simp [counterZero]

/-- Transcript prefix used for the next programmed point.  `step n history`
is everything absorbed after answer `n` and before programming answer `n+1`.
-/
def appendState (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte) :
    ∀ rounds, History (Outcome := Outcome) rounds → List Byte
  | 0, _ => start
  | rounds + 1, history =>
      appendState start step rounds (fun site => history site.castSucc) ++
        step rounds history

theorem appendState_length (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hstep : ∀ rounds history, (step rounds history).length = growth) :
    ∀ rounds history,
      (appendState start step rounds history).length =
        start.length + rounds * growth := by
  intro rounds
  induction rounds with
  | zero =>
      intro history
      simp [appendState]
  | succ rounds ih =>
      intro history
      simp [appendState, List.length_append, hstep, ih, Nat.succ_mul,
        Nat.add_assoc]

/-- Point schedule matching `OracleChallenger::squeeze_point(0)` for scalar
programming: append the zero counter to the current absorbed prefix. -/
def appendSchedule (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte) :
    Schedule (Point := List Byte) (Outcome := Outcome) :=
  fun rounds history => appendState start step rounds history ++ counterZero

/-- Every later transcript state retains the complete initial state as a byte
prefix, irrespective of the adaptive answer history. -/
theorem appendState_hasPrefix (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte) :
    ∀ rounds history,
      ∃ suffix, appendState start step rounds history = start ++ suffix := by
  intro rounds
  induction rounds with
  | zero =>
      intro history
      exact ⟨[], by simp [appendState]⟩
  | succ rounds ih =>
      intro history
      obtain ⟨suffix, hsuffix⟩ :=
        ih (fun site ↦ history site.castSucc)
      exact ⟨suffix ++ step rounds history, by
        simp only [appendState, hsuffix, List.append_assoc]⟩

/-- Every reachable append-only oracle point retains the complete initial
state as a byte prefix. -/
theorem tracePoint_appendSchedule_hasPrefix {sites : ℕ}
    (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (answers : History (Outcome := Outcome) sites) (site : Fin sites) :
    ∃ suffix,
      tracePoint (appendSchedule start step) answers site = start ++ suffix := by
  obtain ⟨suffix, hsuffix⟩ := appendState_hasPrefix start step site
    (priorAnswers answers site)
  exact ⟨suffix ++ counterZero, by
    simp only [tracePoint, appendSchedule, hsuffix, List.append_assoc]⟩

/-- Two append-only transcript states agree along one complete answer trace
when their initial bytes agree and every reached step emits the same bytes.
The premise is deliberately restricted to prefixes of `answers`; no
counterfactual-history equality is required. -/
theorem appendState_eq_of_traceSteps {sites : ℕ}
    (leftStart rightStart : List Byte)
    (leftStep rightStep : ∀ rounds,
      History (Outcome := Outcome) (rounds + 1) → List Byte)
    (answers : History (Outcome := Outcome) sites)
    (hstart : rightStart = leftStart)
    (hstep : ∀ rounds (hle : rounds + 1 ≤ sites),
      rightStep rounds (fun site ↦ answers (Fin.castLE hle site)) =
        leftStep rounds (fun site ↦ answers (Fin.castLE hle site))) :
    ∀ rounds (hle : rounds ≤ sites),
      appendState rightStart rightStep rounds
          (fun site ↦ answers (Fin.castLE hle site)) =
        appendState leftStart leftStep rounds
          (fun site ↦ answers (Fin.castLE hle site)) := by
  intro rounds
  induction rounds with
  | zero =>
      intro hle
      simpa only [appendState] using hstart
  | succ rounds ih =>
      intro hle
      have hprevious : rounds ≤ sites :=
        Nat.le_trans (Nat.le_succ rounds) hle
      have hhistory :
          (fun site : Fin rounds ↦
            answers (Fin.castLE hle site.castSucc)) =
          (fun site : Fin rounds ↦
            answers (Fin.castLE hprevious site)) := by
        funext site
        rfl
      simp only [appendState]
      rw [hhistory, ih hprevious, hstep rounds hle]

/-- Causal trace-point equality obtained from equality of precisely the
initial state and step messages reached along the proposed answer vector. -/
theorem tracePoint_appendSchedule_eq_of_traceSteps {sites : ℕ}
    (leftStart rightStart : List Byte)
    (leftStep rightStep : ∀ rounds,
      History (Outcome := Outcome) (rounds + 1) → List Byte)
    (answers : History (Outcome := Outcome) sites)
    (hstart : rightStart = leftStart)
    (hstep : ∀ rounds (hle : rounds + 1 ≤ sites),
      rightStep rounds (fun site ↦ answers (Fin.castLE hle site)) =
        leftStep rounds (fun site ↦ answers (Fin.castLE hle site)))
    (site : Fin sites) :
    tracePoint (appendSchedule rightStart rightStep) answers site =
    tracePoint (appendSchedule leftStart leftStep) answers site := by
  simp only [tracePoint, appendSchedule]
  have hhistory : priorAnswers answers site =
      (fun prior ↦ answers (Fin.castLE site.isLt.le prior)) := by
    funext prior
    rfl
  rw [hhistory]
  rw [appendState_eq_of_traceSteps leftStart rightStart leftStep rightStep
    answers hstart hstep site site.isLt.le]

theorem tracePoint_appendSchedule_length {sites : ℕ}
    (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hstep : ∀ rounds history, (step rounds history).length = growth)
    (answers : History (Outcome := Outcome) sites) (site : Fin sites) :
    (tracePoint (appendSchedule start step) answers site).length =
      start.length + site * growth + 8 := by
  simp only [tracePoint, appendSchedule, List.length_append, counterZero_length]
  rw [appendState_length start step growth hstep]

/-- Fixed positive growth makes the complete adaptive programming trace
pairwise distinct, for every possible answer history. -/
theorem tracePoints_appendSchedule_injective {sites : ℕ}
    (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hpositive : 0 < growth)
    (hstep : ∀ rounds history, (step rounds history).length = growth)
    (answers : History (Outcome := Outcome) sites) :
    Injective (tracePoints (appendSchedule start step) answers) := by
  intro left right heq
  have hlength := congrArg List.length heq
  change
    (tracePoint (appendSchedule start step) answers left).length =
      (tracePoint (appendSchedule start step) answers right).length at hlength
  rw [tracePoint_appendSchedule_length start step growth hstep,
    tracePoint_appendSchedule_length start step growth hstep] at hlength
  apply Fin.ext
  exact Nat.mul_right_cancel hpositive
    (Nat.add_left_cancel (Nat.add_right_cancel hlength))

/-- A finite oracle-point type large enough for every programmed point in a
`sites`-round append-only execution.  The one-past bound avoids special cases
when `sites = 0`. -/
def maxPointLength (sites : ℕ) (start : List Byte) (growth : ℕ) : ℕ :=
  start.length + sites * growth + 8

def maxPointLengthFromBound (sites maxStartLength growth : ℕ) : ℕ :=
  maxStartLength + sites * growth + 8

/-- Bounded schedule with one public upper bound shared by every possible
initial transcript.  This is needed when the initial transcript varies with
the simulated algebraic messages but the random oracle has one common finite
point type. -/
def boundedAppendScheduleFromBound (sites maxStartLength : ℕ)
    (start : List Byte) (hstart : start.length ≤ maxStartLength)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hstep : ∀ rounds history, (step rounds history).length = growth) :
    Schedule
      (Point := BoundedBytes
        (maxPointLengthFromBound sites maxStartLength growth))
      (Outcome := Outcome) :=
  fun rounds history =>
    if hround : rounds < sites then
      boundBytes (appendSchedule start step rounds history) (by
        have hmul : rounds * growth ≤ sites * growth :=
          Nat.mul_le_mul_right growth (Nat.le_of_lt hround)
        simp only [appendSchedule, List.length_append, counterZero_length,
          maxPointLengthFromBound]
        rw [appendState_length start step growth hstep]
        omega)
    else
      boundBytes [] (Nat.zero_le _)

theorem unbound_tracePoint_boundedAppendScheduleFromBound {sites maxStartLength : ℕ}
    (start : List Byte) (hstart : start.length ≤ maxStartLength)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hstep : ∀ rounds history, (step rounds history).length = growth)
    (answers : History (Outcome := Outcome) sites) (site : Fin sites) :
    unboundBytes
        (tracePoint
          (boundedAppendScheduleFromBound sites maxStartLength start hstart
            step growth hstep) answers site) =
      tracePoint (appendSchedule start step) answers site := by
  simp [tracePoint, boundedAppendScheduleFromBound, site.isLt]

theorem tracePoints_boundedAppendScheduleFromBound_injective
    {sites maxStartLength : ℕ}
    (start : List Byte) (hstart : start.length ≤ maxStartLength)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hpositive : 0 < growth)
    (hstep : ∀ rounds history, (step rounds history).length = growth)
    (answers : History (Outcome := Outcome) sites) :
    Injective
      (tracePoints
        (boundedAppendScheduleFromBound sites maxStartLength start hstart
          step growth hstep) answers) := by
  intro left right heq
  have hunbound := congrArg unboundBytes heq
  change
    unboundBytes
        (tracePoint
          (boundedAppendScheduleFromBound sites maxStartLength start hstart
            step growth hstep) answers left) =
      unboundBytes
        (tracePoint
          (boundedAppendScheduleFromBound sites maxStartLength start hstart
            step growth hstep) answers right) at hunbound
  rw [unbound_tracePoint_boundedAppendScheduleFromBound,
    unbound_tracePoint_boundedAppendScheduleFromBound] at hunbound
  exact tracePoints_appendSchedule_injective start step growth hpositive hstep
    answers hunbound

/-- Cap the otherwise unbounded schedule to the finite byte-string universe
needed by one protocol execution.  Rounds outside the registered execution
map to the empty point and are unreachable by `run ... sites`. -/
def boundedAppendSchedule (sites : ℕ) (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hstep : ∀ rounds history, (step rounds history).length = growth) :
    Schedule
      (Point := BoundedBytes (maxPointLength sites start growth))
      (Outcome := Outcome) :=
  fun rounds history =>
    if hround : rounds < sites then
      boundBytes (appendSchedule start step rounds history) (by
        have hmul : rounds * growth ≤ sites * growth :=
          Nat.mul_le_mul_right growth (Nat.le_of_lt hround)
        simp only [appendSchedule, List.length_append, counterZero_length,
          maxPointLength]
        rw [appendState_length start step growth hstep]
        omega)
    else
      boundBytes [] (Nat.zero_le _)

theorem unbound_tracePoint_boundedAppendSchedule {sites : ℕ}
    (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hstep : ∀ rounds history, (step rounds history).length = growth)
    (answers : History (Outcome := Outcome) sites) (site : Fin sites) :
    unboundBytes
        (tracePoint (boundedAppendSchedule sites start step growth hstep)
          answers site) =
      tracePoint (appendSchedule start step) answers site := by
  simp [tracePoint, boundedAppendSchedule, site.isLt]

/-- Finite-domain form used by the exact random-oracle table theorem. -/
theorem tracePoints_boundedAppendSchedule_injective {sites : ℕ}
    (start : List Byte)
    (step : ∀ rounds, History (Outcome := Outcome) (rounds + 1) → List Byte)
    (growth : ℕ) (hpositive : 0 < growth)
    (hstep : ∀ rounds history, (step rounds history).length = growth)
    (answers : History (Outcome := Outcome) sites) :
    Injective
      (tracePoints
        (boundedAppendSchedule sites start step growth hstep) answers) := by
  intro left right heq
  have hunbound := congrArg unboundBytes heq
  change
    unboundBytes
        (tracePoint (boundedAppendSchedule sites start step growth hstep)
          answers left) =
      unboundBytes
        (tracePoint (boundedAppendSchedule sites start step growth hstep)
          answers right) at hunbound
  rw [unbound_tracePoint_boundedAppendSchedule,
    unbound_tracePoint_boundedAppendSchedule] at hunbound
  exact tracePoints_appendSchedule_injective start step growth hpositive hstep
    answers hunbound

/-- Exact `observe_f128` encoding: operation tag, scalar-kind tag, then the
sixteen field bytes. -/
def observeScalar (encode : Message → List Byte) (message : Message) : List Byte :=
  [(3 : Byte), (1 : Byte)] ++ encode message

theorem observeScalar_length (encode : Message → List Byte)
    (hencode : ∀ message, (encode message).length = 16) (message : Message) :
    (observeScalar encode message).length = 18 := by
  simp [observeScalar, hencode]

/-- Bytes absorbed between two programmed scalar points in the simulated
zerocheck: the previous 16-byte challenge, two framed scalar messages, and the
two-byte tag for the next scalar squeeze. -/
def scalarRoundStep
    (consume : Outcome → List Byte)
    (encode : Message → List Byte)
    (first second : ∀ rounds,
      History (Outcome := Outcome) (rounds + 1) → Message)
    (rounds : ℕ) (history : History (Outcome := Outcome) (rounds + 1)) :
    List Byte :=
  consume (history (Fin.last rounds)) ++
    observeScalar encode (first rounds history) ++
    observeScalar encode (second rounds history) ++
    [(4 : Byte), (1 : Byte)]

theorem scalarRoundStep_length
    (consume : Outcome → List Byte) (hconsume : ∀ answer, (consume answer).length = 16)
    (encode : Message → List Byte) (hencode : ∀ message, (encode message).length = 16)
    (first second : ∀ rounds,
      History (Outcome := Outcome) (rounds + 1) → Message)
    (rounds : ℕ) (history : History (Outcome := Outcome) (rounds + 1)) :
    (scalarRoundStep consume encode first second rounds history).length = 54 := by
  simp [scalarRoundStep, hconsume, observeScalar_length encode hencode]

/-- Concrete distinctness theorem for all points programmed by the Rust
zerocheck simulator. -/
theorem scalarProgrammingPoints_injective {sites : ℕ}
    (start : List Byte)
    (consume : Outcome → List Byte) (hconsume : ∀ answer, (consume answer).length = 16)
    (encode : Message → List Byte) (hencode : ∀ message, (encode message).length = 16)
    (first second : ∀ rounds,
      History (Outcome := Outcome) (rounds + 1) → Message)
    (answers : History (Outcome := Outcome) sites) :
    Injective
      (tracePoints
        (appendSchedule start (scalarRoundStep consume encode first second))
        answers) :=
  tracePoints_appendSchedule_injective start
    (scalarRoundStep consume encode first second) 54 (by decide)
    (scalarRoundStep_length consume hconsume encode hencode first second) answers

/-- Concrete finite-domain schedule and injectivity fact for the Rust scalar
programming path. -/
theorem boundedScalarProgrammingPoints_injective {sites : ℕ}
    (start : List Byte)
    (consume : Outcome → List Byte) (hconsume : ∀ answer, (consume answer).length = 16)
    (encode : Message → List Byte) (hencode : ∀ message, (encode message).length = 16)
    (first second : ∀ rounds,
      History (Outcome := Outcome) (rounds + 1) → Message)
    (answers : History (Outcome := Outcome) sites) :
    Injective
      (tracePoints
        (boundedAppendSchedule sites start
          (scalarRoundStep consume encode first second) 54
          (scalarRoundStep_length consume hconsume encode hencode first second))
        answers) :=
  tracePoints_boundedAppendSchedule_injective start
    (scalarRoundStep consume encode first second) 54 (by decide)
    (scalarRoundStep_length consume hconsume encode hencode first second) answers

end VeiledFlock.TranscriptSchedule

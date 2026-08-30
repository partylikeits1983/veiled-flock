import VeiledFlock.Oracle.OracleProgramming
import VeiledFlock.Core.Probability

/-!
# Exact adaptive random-oracle programming

`OracleProgramming` proves exact reparameterization at a fixed family of
points.  Fiat--Shamir programming is adaptive: the point used in round `i`
depends on the answers from rounds `< i`.  This file closes that gap.

For a proposed vector of programmed answers, causality determines every
programming point from the preceding prefix.  When those points are distinct,
a random oracle is equivalent to that answer vector plus a random table on all
other points.  The equivalence below is exact; freshness with respect to
external queries is the separate bad event charged by the security ledger.
-/

namespace VeiledFlock.AdaptiveOracleProgramming

open Function
open VeiledFlock.OracleProgramming

variable {Point Outcome : Type*}
variable [Fintype Point] [DecidableEq Point]

abbrev Oracle := Point → Outcome
abbrev History (rounds : ℕ) := Fin rounds → Outcome

/-- A causal schedule names the next oracle point from prior answers only. -/
abbrev Schedule := ∀ rounds, History (Outcome := Outcome) rounds → Point

/-- Honest adaptive answers obtained from a complete oracle table. -/
def run (next : Schedule (Point := Point) (Outcome := Outcome))
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    ∀ rounds, History (Outcome := Outcome) rounds
  | 0 => Fin.elim0
  | rounds + 1 =>
      Fin.lastCases
        (oracle (next rounds (run next oracle rounds)))
        (run next oracle rounds)

omit [Fintype Point] [DecidableEq Point] in
@[simp]
theorem run_zero (next : Schedule (Point := Point) (Outcome := Outcome))
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    run next oracle 0 = Fin.elim0 := rfl

omit [Fintype Point] [DecidableEq Point] in
@[simp]
theorem run_succ_last (next : Schedule (Point := Point) (Outcome := Outcome))
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) (rounds : ℕ) :
    run next oracle (rounds + 1) (Fin.last rounds) =
      oracle (next rounds (run next oracle rounds)) := by
  simp [run]

omit [Fintype Point] [DecidableEq Point] in
@[simp]
theorem run_succ_castSucc
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (oracle : Oracle (Point := Point) (Outcome := Outcome))
    (rounds : ℕ) (site : Fin rounds) :
    run next oracle (rounds + 1) site.castSucc =
      run next oracle rounds site := by
  simp [run]

/-- Restrict a full proposed answer vector to the answers preceding `site`. -/
def priorAnswers {sites : ℕ} (answers : History (Outcome := Outcome) sites)
    (site : Fin sites) : History (Outcome := Outcome) site :=
  fun prior => answers ⟨prior, prior.isLt.trans site.isLt⟩

/-- The oracle point that a causal schedule reaches at `site` when its answers
are the proposed vector `answers`. -/
def tracePoint {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (answers : History (Outcome := Outcome) sites) (site : Fin sites) : Point :=
  next site (priorAnswers answers site)

def tracePoints {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (answers : History (Outcome := Outcome) sites) : Fin sites → Point :=
  tracePoint next answers

omit [Fintype Point] [DecidableEq Point] in
/-- Running for more rounds preserves every earlier answer. -/
theorem run_castLE
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (oracle : Oracle (Point := Point) (Outcome := Outcome))
    {small large : ℕ} (h : small ≤ large) (site : Fin small) :
    run next oracle large (Fin.castLE h site) = run next oracle small site := by
  induction large with
  | zero =>
      have hzero : small = 0 := by omega
      subst small
      exact Fin.elim0 site
  | succ large ih =>
      by_cases heq : small = large + 1
      · subst small
        rfl
      · have hsmall : small ≤ large := Nat.le_of_lt_succ
          (lt_of_le_of_ne h heq)
        have hcast : Fin.castLE h site =
            (Fin.castLE hsmall site).castSucc := by
          apply Fin.ext
          rfl
        rw [hcast, run_succ_castSucc, ih hsmall]

omit [Fintype Point] [DecidableEq Point] in
/-- The prefix of an honest run is the honest run of that shorter length. -/
theorem priorAnswers_run
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (oracle : Oracle (Point := Point) (Outcome := Outcome))
    {sites : ℕ} (site : Fin sites) :
    priorAnswers (run next oracle sites) site = run next oracle site := by
  funext prior
  exact run_castLE next oracle (Nat.le_of_lt site.isLt) prior

omit [Fintype Point] [DecidableEq Point] in
/-- At each adaptive trace point, the honest table contains the corresponding
honest answer. -/
theorem oracle_tracePoint_run
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (oracle : Oracle (Point := Point) (Outcome := Outcome))
    {sites : ℕ} (site : Fin sites) :
    oracle (tracePoint next (run next oracle sites) site) =
      run next oracle sites site := by
  rw [tracePoint, priorAnswers_run]
  have h := run_succ_last next oracle site
  rw [← h]
  exact (run_castLE next oracle (Nat.succ_le_of_lt site.isLt)
    (Fin.last site)).symm

/-- A classical adaptive query transcript depends only on the oracle values at
the points that the transcript actually reaches.  This is the causal
noninterference fact needed when a simulator changes an oracle table after an
adversary's prior queries: if none of those reached points changes, neither
the future query choices nor the observed answers change. -/
theorem run_eq_of_eq_on_trace
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (left right : Oracle (Point := Point) (Outcome := Outcome))
    {rounds : ℕ}
    (hagrees : ∀ site : Fin rounds,
      right (tracePoint next (run next left rounds) site) =
        left (tracePoint next (run next left rounds) site)) :
    run next right rounds = run next left rounds := by
  have hprefix : ∀ count (hle : count ≤ rounds),
      run next right count = run next left count := by
    intro count
    induction count with
    | zero =>
        intro _
        rfl
    | succ count ih =>
        intro hle
        have hprevious := ih (Nat.le_trans (Nat.le_succ count) hle)
        funext site
        refine Fin.lastCases ?_ (fun prior => ?_) site
        · rw [run_succ_last, run_succ_last, hprevious]
          let fullSite : Fin rounds :=
            ⟨count, Nat.lt_of_succ_le hle⟩
          have hagree := hagrees fullSite
          rw [tracePoint, priorAnswers_run] at hagree
          exact hagree
        · rw [run_succ_castSucc, run_succ_castSucc]
          exact congrFun hprevious prior
  exact hprefix rounds (le_refl rounds)

/-- Set-valued form of `run_eq_of_eq_on_trace`, convenient for freshness
ledger events. -/
theorem run_eq_of_agree_on_traceSet
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (left right : Oracle (Point := Point) (Outcome := Outcome))
    {rounds : ℕ}
    (hagrees : ∀ point,
      point ∈ Set.range (tracePoints next (run next left rounds)) →
        right point = left point) :
    run next right rounds = run next left rounds := by
  apply run_eq_of_eq_on_trace next left right
  intro site
  exact hagrees _ ⟨site, rfl⟩

/-- Independent simulator coins: all desired adaptive answers, together with
the oracle table restricted away from the points determined by those answers.
-/
abbrev SimulatorCoins {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome)) :=
  Σ answers : History (Outcome := Outcome) sites,
    Unprogrammed (tracePoints next answers) → Outcome

noncomputable instance simulatorCoinsNonempty [Nonempty Outcome] {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome)) :
    Nonempty (SimulatorCoins (sites := sites) next) := by
  let value : Outcome := Classical.choice inferInstance
  exact ⟨⟨fun _ => value, fun _ => value⟩⟩

/-- Reconstruct a complete oracle by installing the proposed answers and
retaining the supplied table everywhere else. -/
noncomputable def simulatedOracle {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    (coins : SimulatorCoins (sites := sites) next) :
    Oracle (Point := Point) (Outcome := Outcome) :=
  (splitOracle (tracePoints next coins.1) (hinjective coins.1)).symm
    (coins.1, coins.2)

@[simp]
theorem simulatedOracle_at {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    (coins : SimulatorCoins (sites := sites) next) (site : Fin sites) :
    simulatedOracle next hinjective coins (tracePoint next coins.1 site) =
      coins.1 site := by
  change
    ((splitOracle (tracePoints next coins.1) (hinjective coins.1)).symm
      (coins.1, coins.2)) (tracePoints next coins.1 site) = coins.1 site
  have h := splitOracle_programmed (tracePoints next coins.1)
    (hinjective coins.1)
    ((splitOracle (tracePoints next coins.1) (hinjective coins.1)).symm
      (coins.1, coins.2)) site
  rw [(splitOracle (tracePoints next coins.1)
    (hinjective coins.1)).apply_symm_apply] at h
  exact h.symm

@[simp]
theorem simulatedOracle_off {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    (coins : SimulatorCoins (sites := sites) next) (point : Point)
    (hoff : point ∉ Set.range (tracePoints next coins.1)) :
    simulatedOracle next hinjective coins point = coins.2 ⟨point, hoff⟩ := by
  change
    ((splitOracle (tracePoints next coins.1) (hinjective coins.1)).symm
      (coins.1, coins.2)) point = _
  let outside : Unprogrammed (tracePoints next coins.1) := ⟨point, hoff⟩
  have h := splitOracle_unprogrammed
    (tracePoints next coins.1) (hinjective coins.1)
    ((splitOracle (tracePoints next coins.1) (hinjective coins.1)).symm
      (coins.1, coins.2)) outside
  rw [(splitOracle (tracePoints next coins.1)
    (hinjective coins.1)).apply_symm_apply] at h
  exact h.symm

/-- Programming a causal, pairwise-distinct trace forces the whole adaptive
run to equal the proposed answer vector. -/
theorem run_simulatedOracle {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    (coins : SimulatorCoins (sites := sites) next) :
    run next (simulatedOracle next hinjective coins) sites = coins.1 := by
  let oracle := simulatedOracle next hinjective coins
  have hround : ∀ rounds (hle : rounds ≤ sites),
      run next oracle rounds = fun site => coins.1 (Fin.castLE hle site) := by
    intro rounds
    induction rounds with
    | zero =>
        intro hle
        funext site
        exact Fin.elim0 site
    | succ rounds ih =>
        intro hle
        funext site
        refine Fin.lastCases ?_ (fun prior => ?_) site
        · rw [run_succ_last]
          have hprev : run next oracle rounds =
              priorAnswers coins.1 ⟨rounds, Nat.lt_of_succ_le hle⟩ := by
            rw [ih (Nat.le_trans (Nat.le_succ rounds) hle)]
            funext prior
            rfl
          rw [hprev]
          change oracle (tracePoint next coins.1
              ⟨rounds, Nat.lt_of_succ_le hle⟩) = _
          rw [show Fin.castLE hle (Fin.last rounds) =
              ⟨rounds, Nat.lt_of_succ_le hle⟩ by
            apply Fin.ext
            rfl]
          exact simulatedOracle_at next hinjective coins _
        · rw [run_succ_castSucc, ih (Nat.le_trans (Nat.le_succ rounds) hle)]
          rfl
  simpa only [Fin.castLE_refl] using hround sites (le_refl sites)

/-! ## Retargeting a complete adaptive trace -/

/-- For every proposed answer vector, transport the untouched oracle table
from the complement of one causal trace to the complement of another.  The
answer vector itself is unchanged. -/
noncomputable def retargetSimulatorCoins {sites : ℕ}
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints right answers)) :
    SimulatorCoins (sites := sites) left ≃
      SimulatorCoins (sites := sites) right :=
  Equiv.sigmaCongrRight fun answers =>
    Equiv.arrowCongr
      (unprogrammedRename (tracePoints left answers)
        (tracePoints right answers) (hleft answers) (hright answers))
      (Equiv.refl Outcome)

@[simp]
theorem retargetSimulatorCoins_answers {sites : ℕ}
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints right answers))
    (coins : SimulatorCoins (sites := sites) left) :
    (retargetSimulatorCoins left right hleft hright coins).1 = coins.1 := rfl

/-- Operational freshness lemma.  Before programming, an online simulator
answers prior adversary queries from the off-trace table.  Installing the
adaptive Fiat--Shamir answers later leaves that complete causal prior
transcript unchanged whenever its reached points avoid the programmed trace.
-/
theorem priorRun_preserved_by_freshProgramming {sites priorRounds : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    (coins : SimulatorCoins (sites := sites) next)
    (priorNext : Schedule (Point := Point) (Outcome := Outcome))
    (before : Oracle (Point := Point) (Outcome := Outcome))
    (hbefore : ∀ point
      (hoff : point ∉ Set.range (tracePoints next coins.1)),
      before point = coins.2 ⟨point, hoff⟩)
    (hfresh : Set.range (tracePoints priorNext (run priorNext before priorRounds)) ∩
      Set.range (tracePoints next coins.1) = ∅) :
    run priorNext (simulatedOracle next hinjective coins) priorRounds =
      run priorNext before priorRounds := by
  apply run_eq_of_agree_on_traceSet priorNext before
    (simulatedOracle next hinjective coins)
  intro point hprior
  have hoff : point ∉ Set.range (tracePoints next coins.1) := by
    intro hprogrammed
    have : point ∈
        Set.range (tracePoints priorNext (run priorNext before priorRounds)) ∩
          Set.range (tracePoints next coins.1) := ⟨hprior, hprogrammed⟩
    rw [hfresh] at this
    exact this
  rw [simulatedOracle_off next hinjective coins point hoff,
    ← hbefore point hoff]

/-- Exact coin equivalence for an adaptive programmable random oracle. -/
noncomputable def splitAdaptive {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers)) :
    Oracle (Point := Point) (Outcome := Outcome) ≃
      SimulatorCoins (sites := sites) next where
  toFun oracle :=
    ⟨run next oracle sites,
      (splitOracle (tracePoints next (run next oracle sites))
        (hinjective (run next oracle sites)) oracle).2⟩
  invFun := simulatedOracle next hinjective
  left_inv oracle := by
    change
      (splitOracle (tracePoints next (run next oracle sites))
        (hinjective (run next oracle sites))).symm
          (run next oracle sites,
            (splitOracle (tracePoints next (run next oracle sites))
              (hinjective (run next oracle sites)) oracle).2) = oracle
    apply (splitOracle (tracePoints next (run next oracle sites))
      (hinjective (run next oracle sites))).injective
    rw [(splitOracle (tracePoints next (run next oracle sites))
      (hinjective (run next oracle sites))).apply_symm_apply]
    apply Prod.ext
    · funext site
      rw [splitOracle_programmed]
      exact (oracle_tracePoint_run next oracle site).symm
    · rfl
  right_inv coins := by
    rcases coins with ⟨answers, outside⟩
    let oracle := simulatedOracle next hinjective ⟨answers, outside⟩
    have hrun :
        run next oracle sites = answers :=
      run_simulatedOracle next hinjective ⟨answers, outside⟩
    change
      (⟨run next oracle sites,
        (splitOracle (tracePoints next (run next oracle sites))
          (hinjective (run next oracle sites)) oracle).2⟩ :
          SimulatorCoins (sites := sites) next) = ⟨answers, outside⟩
    calc
      _ = (⟨answers,
          (splitOracle (tracePoints next answers) (hinjective answers) oracle).2⟩ :
            SimulatorCoins (sites := sites) next) := by
        exact congrArg
          (fun proposed =>
            (⟨proposed,
              (splitOracle (tracePoints next proposed)
                (hinjective proposed) oracle).2⟩ :
              SimulatorCoins (sites := sites) next)) hrun
      _ = ⟨answers, outside⟩ := by
        have houtside :
            (splitOracle (tracePoints next answers) (hinjective answers) oracle).2 =
              outside := by
          dsimp [oracle, simulatedOracle]
          exact congrArg Prod.snd
            ((splitOracle (tracePoints next answers)
              (hinjective answers)).apply_symm_apply (answers, outside))
        exact congrArg
          (fun remaining =>
            (⟨answers, remaining⟩ :
              SimulatorCoins (sites := sites) next)) houtside

/-- Exact oracle-table permutation that makes the `right` causal schedule see
the same answer vector that the original table gave the `left` schedule. -/
noncomputable def retargetAdaptive {sites : ℕ}
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints right answers)) :
    Oracle (Point := Point) (Outcome := Outcome) ≃
      Oracle (Point := Point) (Outcome := Outcome) :=
  (splitAdaptive left hleft).trans
    ((retargetSimulatorCoins left right hleft hright).trans
      (splitAdaptive right hright).symm)

/-- Retargeting preserves the full causal answer transcript pointwise. -/
theorem run_retargetAdaptive {sites : ℕ}
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints right answers))
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    run right (retargetAdaptive left right hleft hright oracle) sites =
      run left oracle sites := by
  let leftCoins := splitAdaptive left hleft oracle
  let rightCoins := retargetSimulatorCoins left right hleft hright leftCoins
  change run right (simulatedOracle right hright rightCoins) sites =
    run left oracle sites
  calc
    run right (simulatedOracle right hright rightCoins) sites = rightCoins.1 :=
      run_simulatedOracle right hright rightCoins
    _ = leftCoins.1 := retargetSimulatorCoins_answers left right hleft hright _
    _ = run left oracle sites := rfl

/-- Any deterministic view of an adaptive answer transcript has exactly the
same distribution after retargeting the entire causal query schedule. -/
theorem adaptiveTraceReplacement_exact [Fintype Outcome] [Nonempty Outcome]
    {sites : ℕ}
    (left right : Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints left answers))
    (hright : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints right answers))
    {View : Type*}
    (continueWith : History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (Oracle (Point := Point) (Outcome := Outcome))).map
        (fun oracle => continueWith (run left oracle sites)) =
      (PMF.uniformOfFintype
        (Oracle (Point := Point) (Outcome := Outcome))).map
          (fun oracle => continueWith (run right oracle sites)) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (retargetAdaptive left right hleft hright)
  intro oracle
  exact congrArg continueWith
    (run_retargetAdaptive left right hleft hright oracle).symm

section FiberwiseRetarget

variable {Rest View : Type*}
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]

/-- Retarget a causal oracle schedule separately in every fixed public-state
fiber. -/
theorem fiberwiseAdaptiveTraceReplacement_exact {sites : ℕ}
    (left right : Rest → Schedule (Point := Point) (Outcome := Outcome))
    (hleft : ∀ rest (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (left rest) answers))
    (hright : ∀ rest (answers : History (Outcome := Outcome) sites),
      Injective (tracePoints (right rest) answers))
    (continueWith : Rest → History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (Rest × Oracle (Point := Point) (Outcome := Outcome))).map
        (fun coins => continueWith coins.1
          (run (left coins.1) coins.2 sites)) =
      (PMF.uniformOfFintype
        (Rest × Oracle (Point := Point) (Outcome := Outcome))).map
          (fun coins => continueWith coins.1
            (run (right coins.1) coins.2 sites)) := by
  let split :
      (Rest × Oracle (Point := Point) (Outcome := Outcome)) ≃
        (Oracle (Point := Point) (Outcome := Outcome) × Rest) :=
    ⟨fun coins => (coins.2, coins.1), fun coins => (coins.2, coins.1),
      fun _ => rfl, fun _ => rfl⟩
  let equiv := VeiledFlock.Probability.fiberwiseEquiv split
    (fun rest => retargetAdaptive (left rest) (right rest)
      (hleft rest) (hright rest))
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv equiv
  intro coins
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply split
    (fun rest => retargetAdaptive (left rest) (right rest)
      (hleft rest) (hright rest)) coins
  have hrest : (equiv coins).1 = coins.1 := congrArg Prod.snd hsplit
  have horacle : (equiv coins).2 =
      retargetAdaptive (left coins.1) (right coins.1)
        (hleft coins.1) (hright coins.1) coins.2 := congrArg Prod.fst hsplit
  rw [hrest, horacle]
  exact congrArg (continueWith coins.1)
    (run_retargetAdaptive (left coins.1) (right coins.1)
      (hleft coins.1) (hright coins.1) coins.2).symm

end FiberwiseRetarget

/-- The real adaptive random-oracle execution and the straightline simulator
have exactly the same output distribution.  No extractor is involved: this is
the distributional statement required for zero knowledge. -/
theorem adaptiveProgrammingSimulator_exact [Fintype Outcome]
    [DecidableEq Outcome] [Nonempty Outcome] {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    {View : Type*}
    (view : Oracle (Point := Point) (Outcome := Outcome) →
      History (Outcome := Outcome) sites → View) :
    (PMF.uniformOfFintype
      (Oracle (Point := Point) (Outcome := Outcome))).map
        (fun oracle => view oracle (run next oracle sites)) =
      (PMF.uniformOfFintype
        (SimulatorCoins (sites := sites) next)).map
        (fun coins => view (simulatedOracle next hinjective coins) coins.1) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (splitAdaptive next hinjective)
  intro oracle
  change view oracle (run next oracle sites) =
    view (simulatedOracle next hinjective ((splitAdaptive next hinjective) oracle))
      (run next oracle sites)
  have h := (splitAdaptive next hinjective).symm_apply_apply oracle
  change simulatedOracle next hinjective
    ((splitAdaptive next hinjective) oracle) = oracle at h
  rw [h]

/-! ## Uniform law of a fresh adaptive trace -/

/-- Choose one harmless reference answer vector.  It is used only to put the
answer-dependent complement of an injective trace into one fixed product
type; it is not part of the protocol or simulator. -/
noncomputable def referenceHistory [Nonempty Outcome] (sites : ℕ) :
    History (Outcome := Outcome) sites :=
  fun _ => Classical.choice inferInstance

/-- The adaptive split has answer-dependent complement fibers.  All those
fibers are nevertheless canonically equipotent: injective traces of the same
public length remove the same number of oracle points.  This equivalence
straightens the sigma type into a genuine product whose first coordinate is
the complete answer history. -/
noncomputable def simulatorCoinsProductEquiv [Nonempty Outcome] {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers)) :
    SimulatorCoins (sites := sites) next ≃
      History (Outcome := Outcome) sites ×
        (Unprogrammed
          (tracePoints next (referenceHistory (Outcome := Outcome) sites)) →
            Outcome) :=
  (Equiv.sigmaCongrRight fun answers =>
    Equiv.arrowCongr
      (unprogrammedRename (tracePoints next answers)
        (tracePoints next (referenceHistory (Outcome := Outcome) sites))
        (hinjective answers)
        (hinjective (referenceHistory (Outcome := Outcome) sites)))
      (Equiv.refl Outcome)).trans
    (Equiv.sigmaEquivProd _ _)

@[simp]
theorem simulatorCoinsProductEquiv_fst [Nonempty Outcome] {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    (coins : SimulatorCoins (sites := sites) next) :
    (simulatorCoinsProductEquiv next hinjective coins).1 = coins.1 := by
  rfl

/-- Answers returned by a uniformly random finite oracle along any causal,
pairwise-distinct adaptive query trace are exactly a uniform answer vector.
This is the probability bridge needed for the concrete rejection and grinding
failure ledger: adaptivity does not create correlations among fresh oracle
answers. -/
theorem uniform_run_eq_uniform_history [Fintype Outcome] [DecidableEq Outcome]
    [Nonempty Outcome] {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers)) :
    (PMF.uniformOfFintype
      (Oracle (Point := Point) (Outcome := Outcome))).map
        (fun oracle => run next oracle sites) =
      PMF.uniformOfFintype (History (Outcome := Outcome) sites) := by
  let productEquiv := simulatorCoinsProductEquiv next hinjective
  calc
    (PMF.uniformOfFintype
        (Oracle (Point := Point) (Outcome := Outcome))).map
          (fun oracle => run next oracle sites) =
      (PMF.uniformOfFintype
        (SimulatorCoins (sites := sites) next)).map Sigma.fst := by
        apply VeiledFlock.Probability.uniform_map_eq_of_equiv
          (splitAdaptive next hinjective)
        intro oracle
        rfl
    _ = (PMF.uniformOfFintype
          (History (Outcome := Outcome) sites ×
            (Unprogrammed
              (tracePoints next
                (referenceHistory (Outcome := Outcome) sites)) → Outcome))).map
          Prod.fst := by
        apply VeiledFlock.Probability.uniform_map_eq_of_equiv productEquiv
        intro coins
        exact (simulatorCoinsProductEquiv_fst next hinjective coins).symm
    _ = PMF.uniformOfFintype
          (History (Outcome := Outcome) sites) :=
      by
        rw [← PMF.map_id
          (PMF.uniformOfFintype (History (Outcome := Outcome) sites))]
        exact VeiledFlock.Probability.uniform_map_ignore_right
          (A := History (Outcome := Outcome) sites)
          (B := Unprogrammed
            (tracePoints next
              (referenceHistory (Outcome := Outcome) sites)) → Outcome)
          (view := id)

/-- Complete oracle tables whose realized adaptive answer vector lies in a
specified finite bad set. -/
noncomputable def adaptiveBadOracles [Fintype Outcome] [DecidableEq Outcome]
    {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (bad : Finset (History (Outcome := Outcome) sites)) :
    Finset (Oracle (Point := Point) (Outcome := Outcome)) :=
  Finset.univ.filter fun oracle => run next oracle sites ∈ bad

theorem mem_adaptiveBadOracles_iff [Fintype Outcome] [DecidableEq Outcome]
    {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (bad : Finset (History (Outcome := Outcome) sites))
    (oracle : Oracle (Point := Point) (Outcome := Outcome)) :
    oracle ∈ adaptiveBadOracles next bad ↔ run next oracle sites ∈ bad := by
  simp [adaptiveBadOracles]

/-- Exact finite probability of any event determined by a fresh injective
adaptive trace.  This is the cardinality form used by the operational ledger. -/
theorem adaptiveBadOracles_probability_eq [Fintype Outcome]
    [DecidableEq Outcome] [Nonempty Outcome] {sites : ℕ}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (hinjective : ∀ answers : History (Outcome := Outcome) sites,
      Injective (tracePoints next answers))
    (bad : Finset (History (Outcome := Outcome) sites)) :
    ((adaptiveBadOracles next bad).card : ℚ) /
        Fintype.card (Oracle (Point := Point) (Outcome := Outcome)) =
      (bad.card : ℚ) /
        Fintype.card (History (Outcome := Outcome) sites) := by
  classical
  let equiv := (splitAdaptive next hinjective).trans
    (simulatorCoinsProductEquiv next hinjective)
  let Rest :=
    Unprogrammed
      (tracePoints next (referenceHistory (Outcome := Outcome) sites)) →
        Outcome
  have hequivFst : ∀ oracle,
      (equiv oracle).1 = run next oracle sites := by
    intro oracle
    rfl
  have hcardBad : (adaptiveBadOracles next bad).card =
      (bad.product (Finset.univ : Finset Rest)).card := by
    refine Finset.card_equiv equiv fun oracle => ?_
    simp [adaptiveBadOracles, hequivFst oracle]
  have hcardProduct :
      (bad.product (Finset.univ : Finset Rest)).card =
        bad.card * Fintype.card Rest := by
    simp
  rw [hcardBad, hcardProduct]
  have hcard : Fintype.card
      (Oracle (Point := Point) (Outcome := Outcome)) =
      Fintype.card (History (Outcome := Outcome) sites) *
        Fintype.card Rest := by
    rw [Fintype.card_congr equiv, Fintype.card_prod]
  rw [hcard]
  norm_num only [Nat.cast_mul]
  have hrest : (Fintype.card Rest : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Rest ≠ 0)
  have hhistory :
      (Fintype.card (History (Outcome := Outcome) sites) : ℚ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (History (Outcome := Outcome) sites) ≠ 0)
  field_simp [hrest, hhistory]

end VeiledFlock.AdaptiveOracleProgramming

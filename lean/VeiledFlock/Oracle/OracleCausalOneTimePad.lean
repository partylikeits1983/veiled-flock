import VeiledFlock.Oracle.AdaptiveOneTimePad
import VeiledFlock.Oracle.AdaptiveOracleProgramming

/-!
# One-time pads causal in an external oracle history

The masked-message recurrence is causal in its own visible prefix.  A
Fiat--Shamir implementation has a second causality condition: the unmasked
message emitted at a cursor position may use only oracle answers already
sampled at that position.  This module makes that condition explicit and
proves that completing a reached oracle prefix with arbitrary future answers
cannot change the reached masked-message prefix.
-/

namespace VeiledFlock.OracleCausalOneTimePad

open VeiledFlock.AdaptiveOneTimePad

variable {F I W Outcome : Type*}
variable [AddCommGroup F]

abbrev OracleHistory (rounds : ℕ) := Fin rounds → Outcome

/-- `available round` is the number of external oracle answers available
before masked message `round` is emitted. -/
abbrev CausalSecret (available : ℕ → ℕ) :=
  W → ∀ round,
    History (F := F) (I := I) round →
    OracleHistory (Outcome := Outcome) (available round) →
    Message (F := F) (I := I)

/-- Number of external answers sufficient to evaluate an entire masked
prefix.  A prefix of length `n + 1` ends with message index `n`. -/
def prefixAvailable (available : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | rounds + 1 => available rounds

theorem prefixAvailable_le_current (available : ℕ → ℕ)
    (hmono : Monotone available) (rounds : ℕ) :
    prefixAvailable available rounds ≤ available rounds := by
  cases rounds with
  | zero => simp [prefixAvailable]
  | succ rounds =>
      exact hmono (Nat.le_succ rounds)

/-- Close an externally causal secret against one complete answer vector. -/
def closeSecret {sites : ℕ} (available : ℕ → ℕ)
    (havail : ∀ round, available round ≤ sites)
    (secret : CausalSecret (F := F) (I := I) (W := W)
      (Outcome := Outcome) available)
    (answers : OracleHistory (Outcome := Outcome) sites) :
    Secret (F := F) (I := I) (W := W) :=
  fun witness round history ↦
    secret witness round history
      (fun site ↦ answers (Fin.castLE (havail round) site))

omit [AddCommGroup F] in
theorem closeSecret_eq_of_prefix {sites round : ℕ}
    (available : ℕ → ℕ) (havail : ∀ n, available n ≤ sites)
    (secret : CausalSecret (F := F) (I := I) (W := W)
      (Outcome := Outcome) available)
    (left right : OracleHistory (Outcome := Outcome) sites)
    (heq : ∀ site : Fin (available round),
      left (Fin.castLE (havail round) site) =
        right (Fin.castLE (havail round) site))
    (witness : W) (history : History (F := F) (I := I) round) :
    closeSecret available havail secret left witness round history =
      closeSecret available havail secret right witness round history := by
  unfold closeSecret
  congr 2
  funext site
  exact heq site

/-- Arbitrary future completions do not affect a masked-message prefix when
the availability schedule is monotone. -/
theorem run_eq_of_answer_prefix {sites rounds : ℕ}
    (available : ℕ → ℕ) (havail : ∀ n, available n ≤ sites)
    (hmono : Monotone available)
    (secret : CausalSecret (F := F) (I := I) (W := W)
      (Outcome := Outcome) available)
    (left right : OracleHistory (Outcome := Outcome) sites)
    (heq : ∀ site : Fin (prefixAvailable available rounds),
      left (Fin.castLE
          (Nat.le_trans (prefixAvailable_le_current available hmono rounds)
            (havail rounds)) site) =
        right (Fin.castLE
          (Nat.le_trans (prefixAvailable_le_current available hmono rounds)
            (havail rounds)) site))
    (witness : W) (masks : Masks (F := F) (I := I) rounds) :
    run (closeSecret available havail secret left) witness rounds masks =
      run (closeSecret available havail secret right) witness rounds masks := by
  induction rounds with
  | zero =>
      funext site
      exact Fin.elim0 site
  | succ rounds ih =>
      have hprefix := prefixAvailable_le_current available hmono rounds
      have heqPrevious : ∀ site : Fin (prefixAvailable available rounds),
          left (Fin.castLE
              (Nat.le_trans hprefix (havail rounds)) site) =
            right (Fin.castLE
              (Nat.le_trans hprefix (havail rounds)) site) := by
        intro site
        have heqAt := heq (Fin.castLE hprefix site)
        exact heqAt
      have heqCurrent : ∀ site : Fin (available rounds),
          left (Fin.castLE (havail rounds) site) =
            right (Fin.castLE (havail rounds) site) := by
        simpa only [prefixAvailable] using heq
      have hprevious := ih heqPrevious
        (fun site ↦ masks site.castSucc)
      funext site
      refine Fin.lastCases ?_ (fun earlier ↦ ?_) site
      · rw [run_succ_last, run_succ_last, hprevious]
        rw [closeSecret_eq_of_prefix available havail secret left right
          heqCurrent]
      · rw [run_succ_castSucc, run_succ_castSucc]
        exact congrFun hprevious earlier

/-- A supplied completion operation agrees with the reached prefix by
contract. -/
structure Completion (Outcome : Type*) (sites : ℕ) where
  complete : ∀ rounds, rounds ≤ sites →
    OracleHistory (Outcome := Outcome) rounds →
      OracleHistory (Outcome := Outcome) sites
  apply_prefix : ∀ rounds (hle : rounds ≤ sites)
    (history : OracleHistory (Outcome := Outcome) rounds)
    (site : Fin rounds),
    complete rounds hle history (Fin.castLE hle site) = history site

theorem run_completion_eq {sites rounds reached : ℕ}
    (available : ℕ → ℕ) (havail : ∀ n, available n ≤ sites)
    (hmono : Monotone available)
    (secret : CausalSecret (F := F) (I := I) (W := W)
      (Outcome := Outcome) available)
    (completion : Completion Outcome sites)
    (hreached : reached ≤ sites)
    (havailable : prefixAvailable available rounds ≤ reached)
    (history : OracleHistory (Outcome := Outcome) reached)
    (answers : OracleHistory (Outcome := Outcome) sites)
    (hanswers : ∀ site : Fin reached,
      answers (Fin.castLE hreached site) = history site)
    (witness : W) (masks : Masks (F := F) (I := I) rounds) :
    run (closeSecret available havail secret
        (completion.complete reached hreached history))
        witness rounds masks =
      run (closeSecret available havail secret answers)
        witness rounds masks := by
  apply run_eq_of_answer_prefix available havail hmono secret
  intro site
  let reachedSite : Fin reached := Fin.castLE havailable site
  calc
    completion.complete reached hreached history
        (Fin.castLE
          (Nat.le_trans (prefixAvailable_le_current available hmono rounds)
            (havail rounds)) site) =
      completion.complete reached hreached history
        (Fin.castLE hreached reachedSite) := rfl
    _ = history reachedSite := completion.apply_prefix reached hreached
      history reachedSite
    _ = answers (Fin.castLE hreached reachedSite) :=
      (hanswers reachedSite).symm
    _ = answers
        (Fin.castLE
          (Nat.le_trans (prefixAvailable_le_current available hmono rounds)
            (havail rounds)) site) := rfl

/-- Coordinate form used by an append-only transcript serializer. -/
theorem run_at_completion_eq {sites total reached : ℕ}
    (available : ℕ → ℕ) (havail : ∀ n, available n ≤ sites)
    (hmono : Monotone available)
    (secret : CausalSecret (F := F) (I := I) (W := W)
      (Outcome := Outcome) available)
    (completion : Completion Outcome sites)
    (hreached : reached ≤ sites)
    (history : OracleHistory (Outcome := Outcome) reached)
    (answers : OracleHistory (Outcome := Outcome) sites)
    (hanswers : ∀ answerSite : Fin reached,
      answers (Fin.castLE hreached answerSite) = history answerSite)
    (witness : W) (masks : Masks (F := F) (I := I) total)
    (site : Fin total)
    (havailable : prefixAvailable available (site.val + 1) ≤ reached) :
    run (closeSecret available havail secret
        (completion.complete reached hreached history))
        witness total masks site =
      run (closeSecret available havail secret answers)
        witness total masks site := by
  have hsite : site.val + 1 ≤ total := Nat.succ_le_of_lt site.isLt
  let last : Fin (site.val + 1) := Fin.last site.val
  have hcast : Fin.castLE hsite last = site := by
    apply Fin.ext
    rfl
  have heq := run_completion_eq available havail hmono secret completion
    hreached havailable history answers hanswers witness
    (fun index : Fin (site.val + 1) ↦ masks (Fin.castLE hsite index))
  have hleft := run_castLE
    (closeSecret available havail secret
      (completion.complete reached hreached history))
    witness hsite masks last
  have hright := run_castLE
    (closeSecret available havail secret answers)
    witness hsite masks last
  rw [hcast] at hleft hright
  rw [hleft, hright]
  exact congrFun heq last

end VeiledFlock.OracleCausalOneTimePad

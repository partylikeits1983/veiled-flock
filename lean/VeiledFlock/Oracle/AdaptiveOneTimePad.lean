import VeiledFlock.Core.Probability

/-!
# Adaptive coordinate-wise one-time pads

VEIL--FLOCK alternates masked prover messages with Fiat--Shamir challenges.
Consequently a later unmasked message may depend on every earlier *masked*
message and on the random-oracle table.  A flat, challenge-fixed masking lemma
does not capture that dependency.

This module proves the stronger triangular statement.  At every round the
prover adds one fresh uniform message-sized pad.  For any witness and any
causal secret-message function, evaluation is a bijection from pads to the
complete visible transcript.  The inverse simply subtracts the causal secret
from each requested visible message.  Hence the transcript is perfectly
uniform, even when the causal function depends on arbitrary fixed external
state such as the complete random-oracle table.
-/

namespace VeiledFlock.AdaptiveOneTimePad

open Function

variable {F I W Rest FullView : Type*}
variable [AddCommGroup F]

abbrev Message := I → F
abbrev History (rounds : ℕ) := Fin rounds → Message (F := F) (I := I)
abbrev Masks (rounds : ℕ) := Fin rounds → Message (F := F) (I := I)

/-- The unmasked message at a round may depend on the entire visible prefix. -/
abbrev Secret :=
  W → ∀ rounds, History (F := F) (I := I) rounds → Message (F := F) (I := I)

/-- Restrict a full visible transcript to the messages preceding `site`. -/
def prior {rounds : ℕ} (transcript : History (F := F) (I := I) rounds)
    (site : Fin rounds) : History (F := F) (I := I) site :=
  fun earlier => transcript ⟨earlier, earlier.isLt.trans site.isLt⟩

/-- Evaluate the causal masked transcript. -/
def run (secret : Secret (F := F) (I := I) (W := W)) (witness : W) :
    ∀ rounds, Masks (F := F) (I := I) rounds →
      History (F := F) (I := I) rounds
  | 0, _ => Fin.elim0
  | rounds + 1, masks =>
      let previous := run secret witness rounds
        (fun site => masks site.castSucc)
      Fin.lastCases
        (masks (Fin.last rounds) + secret witness rounds previous)
        previous

@[simp]
theorem run_succ_last (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) (rounds : ℕ)
    (masks : Masks (F := F) (I := I) (rounds + 1)) :
    run secret witness (rounds + 1) masks (Fin.last rounds) =
      masks (Fin.last rounds) +
        secret witness rounds
          (run secret witness rounds (fun site => masks site.castSucc)) := by
  simp [run]

@[simp]
theorem run_succ_castSucc (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) (rounds : ℕ)
    (masks : Masks (F := F) (I := I) (rounds + 1)) (site : Fin rounds) :
    run secret witness (rounds + 1) masks site.castSucc =
      run secret witness rounds (fun earlier => masks earlier.castSucc) site := by
  simp [run]

theorem run_castLE (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) {small large : ℕ} (hle : small ≤ large)
    (masks : Masks (F := F) (I := I) large) (site : Fin small) :
    run secret witness large masks (Fin.castLE hle site) =
      run secret witness small
        (fun earlier => masks (Fin.castLE hle earlier)) site := by
  induction large with
  | zero =>
      have : small = 0 := by omega
      subst small
      exact Fin.elim0 site
  | succ large ih =>
      by_cases heq : small = large + 1
      · subst small
        rfl
      · have hsmall : small ≤ large := Nat.le_of_lt_succ
          (lt_of_le_of_ne hle heq)
        have hcast : Fin.castLE hle site =
            (Fin.castLE hsmall site).castSucc := by
          apply Fin.ext
          rfl
        rw [hcast, run_succ_castSucc, ih hsmall]
        rfl

theorem prior_run (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) {rounds : ℕ}
    (masks : Masks (F := F) (I := I) rounds) (site : Fin rounds) :
    prior (run secret witness rounds masks) site =
      run secret witness site
        (fun earlier => masks ⟨earlier, earlier.isLt.trans site.isLt⟩) := by
  funext earlier
  exact run_castLE secret witness (Nat.le_of_lt site.isLt) masks earlier

theorem run_at (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) {rounds : ℕ}
    (masks : Masks (F := F) (I := I) rounds) (site : Fin rounds) :
    run secret witness rounds masks site =
      masks site + secret witness site (prior (run secret witness rounds masks) site) := by
  let hle : site + 1 ≤ rounds := Nat.succ_le_of_lt site.isLt
  have hsite : Fin.castLE hle (Fin.last site) = site := by
    apply Fin.ext
    rfl
  have hlast := run_succ_last secret witness site
    (fun index : Fin (site + 1) =>
      masks (Fin.castLE hle index))
  have hvalue := run_castLE secret witness
    hle masks (Fin.last site)
  have hprefix :
      run secret witness site
          (fun earlier =>
            (fun index : Fin (site + 1) =>
              masks (Fin.castLE hle index))
              earlier.castSucc) =
        prior (run secret witness rounds masks) site := by
    rw [prior_run]
    rfl
  calc
    run secret witness rounds masks site =
        run secret witness rounds masks (Fin.castLE hle (Fin.last site)) := by
      rw [hsite]
    _ = run secret witness (site + 1)
        (fun index => masks (Fin.castLE hle index)) (Fin.last site) := hvalue
    _ = masks (Fin.castLE hle (Fin.last site)) +
        secret witness site
          (run secret witness site
            (fun earlier => masks (Fin.castLE hle earlier.castSucc))) := hlast
    _ = masks site +
        secret witness site (prior (run secret witness rounds masks) site) := by
      rw [hsite, hprefix]

/-- Recover the unique pad vector that realizes a requested transcript. -/
def recover (secret : Secret (F := F) (I := I) (W := W)) (witness : W)
    {rounds : ℕ} (transcript : History (F := F) (I := I) rounds) :
    Masks (F := F) (I := I) rounds :=
  fun site => transcript site - secret witness site (prior transcript site)

theorem recover_run (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) {rounds : ℕ}
    (masks : Masks (F := F) (I := I) rounds) :
    recover secret witness (run secret witness rounds masks) = masks := by
  funext site
  rw [recover, run_at]
  abel

theorem run_recover (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) {rounds : ℕ}
    (transcript : History (F := F) (I := I) rounds) :
    run secret witness rounds (recover secret witness transcript) = transcript := by
  induction rounds with
  | zero =>
      funext site
      exact Fin.elim0 site
  | succ rounds ih =>
      funext site
      refine Fin.lastCases ?_ (fun earlier => ?_) site
      · rw [run_succ_last]
        have hprevious :
            run secret witness rounds
                (fun earlier =>
                  recover secret witness transcript earlier.castSucc) =
              prior transcript (Fin.last rounds) := by
          change run secret witness rounds
              (recover secret witness (prior transcript (Fin.last rounds))) = _
          exact ih (prior transcript (Fin.last rounds))
        rw [hprevious]
        simp only [recover]
        change transcript (Fin.last rounds) -
            secret witness rounds (prior transcript (Fin.last rounds)) +
              secret witness rounds (prior transcript (Fin.last rounds)) =
          transcript (Fin.last rounds)
        abel
      · rw [run_succ_castSucc]
        change run secret witness rounds
            (recover secret witness (prior transcript (Fin.last rounds))) earlier = _
        rw [ih (prior transcript (Fin.last rounds))]
        rfl

/-- For every witness, causal masking is an explicit bijection from fresh
pads to the full visible transcript. -/
def transcriptEquiv (secret : Secret (F := F) (I := I) (W := W))
    (witness : W) (rounds : ℕ) :
    Masks (F := F) (I := I) rounds ≃ History (F := F) (I := I) rounds where
  toFun := run secret witness rounds
  invFun := recover secret witness
  left_inv := recover_run secret witness
  right_inv := run_recover secret witness

/-- Translate pads between two witnesses while preserving every visible
message, even though later secret messages depend on the visible prefix. -/
def witnessCoinEquiv
    (secret : Secret (F := F) (I := I) (W := W))
    (left right : W) (rounds : ℕ) :
    Masks (F := F) (I := I) rounds ≃ Masks (F := F) (I := I) rounds :=
  (transcriptEquiv secret left rounds).trans
    (transcriptEquiv secret right rounds).symm

theorem run_witnessCoinEquiv
    (secret : Secret (F := F) (I := I) (W := W))
    (left right : W) (rounds : ℕ)
    (masks : Masks (F := F) (I := I) rounds) :
    run secret right rounds (witnessCoinEquiv secret left right rounds masks) =
      run secret left rounds masks := by
  exact (transcriptEquiv secret right rounds).apply_symm_apply
    (run secret left rounds masks)

section Distribution

variable [Fintype F] [DecidableEq F] [Fintype I]
variable [Fintype (I → F)]

/-- Perfect adaptive transcript privacy. -/
theorem transcript_witness_independent
    (secret : Secret (F := F) (I := I) (W := W))
    (left right : W) (rounds : ℕ) :
    (PMF.uniformOfFintype (Masks (F := F) (I := I) rounds)).map
        (run secret left rounds) =
      (PMF.uniformOfFintype (Masks (F := F) (I := I) rounds)).map
        (run secret right rounds) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (witnessCoinEquiv secret left right rounds)
  intro masks
  exact (run_witnessCoinEquiv secret left right rounds masks).symm

/-- External state is carried through unchanged.  In particular, `Rest` may
contain the entire random-oracle table and adversary coins, and `secret` may
depend on it.  The resulting arbitrary full view remains witness independent. -/
theorem fullView_witness_independent
    [Fintype Rest] [Nonempty Rest]
    (secret : Rest → Secret (F := F) (I := I) (W := W))
    (left right : W) (rounds : ℕ)
    (continueWith : Rest → History (F := F) (I := I) rounds → FullView) :
    (PMF.uniformOfFintype
      (Masks (F := F) (I := I) rounds × Rest)).map
        (fun coins => continueWith coins.2
          (run (secret coins.2) left rounds coins.1)) =
      (PMF.uniformOfFintype
        (Masks (F := F) (I := I) rounds × Rest)).map
          (fun coins => continueWith coins.2
            (run (secret coins.2) right rounds coins.1)) := by
  let split :
      (Masks (F := F) (I := I) rounds × Rest) ≃
        (Masks (F := F) (I := I) rounds × Rest) := Equiv.refl _
  let equiv := VeiledFlock.Probability.fiberwiseEquiv split
    (fun rest => witnessCoinEquiv (secret rest) left right rounds)
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv equiv
  intro coins
  simp only [equiv, split, VeiledFlock.Probability.fiberwiseEquiv_split_apply,
    Equiv.refl_apply]
  exact congrArg (continueWith coins.2)
    (run_witnessCoinEquiv (secret coins.2) left right rounds coins.1).symm

end Distribution

end VeiledFlock.AdaptiveOneTimePad

import VeiledFlock.Algebra.JointPcs
import VeiledFlock.Oracle.AdaptiveOneTimePad
import VeiledFlock.Algebra.Field128Ghash

/-!
# Outer PCS blinding with a causal masked prefix

The outer commitment contains a witness-bearing message and an independent
full-support PCS blinder. The nonzero fold challenge is sampled only after a
causal, one-time-padded prefix which may itself contain masked evaluations of
both values. This module reparameterizes the blinder and the complete mask
tape together by factoring them through the invariant pair
`(visible history, folded PCS message)`.
-/

namespace VeiledFlock.ProductionOuterPcs

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.Field128Ghash
open VeiledFlock.JointPcs

variable {K I P W Public Rest : Type*}
variable {rounds : ℕ}

abbrev Blind := I → GhashField
abbrev State := W × Blind (I := I)
abbrev PcsMasks := Masks (F := GhashField) (I := K) rounds
abbrev PreCoins := Blind (I := I) × PcsMasks (K := K) (rounds := rounds)
abbrev Prefix := History (F := GhashField) (I := K) rounds

/-- The PCS-visible data after the fold: the entire folded vector and every
public-direct blinder functional. Revealing the complete folded vector is a
conservative abstraction of all recursive Ligerito post-processing. -/
abbrev OuterView := Blind (I := I) × (P → GhashField)

/-- Factor the witness-specific blinder/mask tape through the two values that
must remain fixed when changing witnesses. -/
noncomputable def stateEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (witness : W) (rest : Rest) : Equiv
      (PreCoins (K := K) (I := I) (rounds := rounds))
      (Prefix (K := K) (rounds := rounds) × Blind (I := I)) where
  toFun coins :=
    let history := run (secret rest) (witness, coins.1) rounds coins.2
    (history, folded (challenge history rest) (message rest witness) coins.1)
  invFun visible :=
    let blind := (foldedEquiv (challenge visible.1 rest)
      (hchallenge visible.1 rest) (message rest witness)).symm visible.2
    (blind, recover (secret rest) (witness, blind) visible.1)
  left_inv coins := by
    let history := run (secret rest) (witness, coins.1) rounds coins.2
    change
      ((foldedEquiv (challenge history rest) (hchallenge history rest)
          (message rest witness)).symm
          (foldedEquiv (challenge history rest) (hchallenge history rest)
            (message rest witness) coins.1),
        recover (secret rest)
          (witness,
            (foldedEquiv (challenge history rest) (hchallenge history rest)
              (message rest witness)).symm
              (foldedEquiv (challenge history rest) (hchallenge history rest)
                (message rest witness) coins.1)) history) = coins
    rw [Equiv.symm_apply_apply]
    exact Prod.ext rfl (recover_run (secret rest) (witness, coins.1) coins.2)
  right_inv visible := by
    let blind := (foldedEquiv (challenge visible.1 rest)
      (hchallenge visible.1 rest) (message rest witness)).symm visible.2
    change
      (run (secret rest) (witness, blind) rounds
          (recover (secret rest) (witness, blind) visible.1),
        folded
          (challenge
            (run (secret rest) (witness, blind) rounds
              (recover (secret rest) (witness, blind) visible.1)) rest)
          (message rest witness) blind) = visible
    have hrun : run (secret rest) (witness, blind) rounds
        (recover (secret rest) (witness, blind) visible.1) = visible.1 :=
      run_recover (secret rest) (witness, blind) visible.1
    rw [hrun]
    exact Prod.ext rfl
      ((foldedEquiv (challenge visible.1 rest)
        (hchallenge visible.1 rest) (message rest witness)).apply_symm_apply
          visible.2)

/-- Translate the joint outer blinder and causal mask tape between witnesses. -/
noncomputable def coinEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (left right : W) (rest : Rest) : Equiv
      (PreCoins (K := K) (I := I) (rounds := rounds))
      (PreCoins (K := K) (I := I) (rounds := rounds)) :=
  (stateEquiv secret challenge hchallenge message left rest).trans
    (stateEquiv secret challenge hchallenge message right rest).symm

theorem stateEquiv_coinEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (left right : W) (rest : Rest)
    (coins : PreCoins (K := K) (I := I) (rounds := rounds)) :
    stateEquiv secret challenge hchallenge message right rest
        (coinEquiv secret challenge hchallenge message left right rest coins) =
      stateEquiv secret challenge hchallenge message left rest coins := by
  exact (stateEquiv secret challenge hchallenge message right rest).apply_symm_apply
    (stateEquiv secret challenge hchallenge message left rest coins)

theorem functional_eq_of_folded_eq
    (c : GhashField) (hc : c ≠ 0)
    (functional : Blind (I := I) →ₗ[GhashField] GhashField)
    (leftMessage rightMessage leftBlind rightBlind : Blind (I := I))
    (hkernel : functional (rightMessage - leftMessage) = 0)
    (hfolded : folded c rightMessage rightBlind =
      folded c leftMessage leftBlind) :
    functional rightBlind = functional leftBlind := by
  have hmessage : functional rightMessage = functional leftMessage := by
    rw [← sub_eq_zero, ← map_sub]
    exact hkernel
  have h := congrArg functional hfolded
  simp only [folded, map_add, map_smul] at h
  rw [hmessage] at h
  apply mul_left_cancel₀ hc
  simpa only [smul_eq_mul] using add_left_cancel h

noncomputable def outerView
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (message : Rest → W → Blind (I := I))
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (witness : W) (rest : Rest)
    (history : Prefix (K := K) (rounds := rounds))
    (blind : Blind (I := I)) : OuterView (I := I) (P := P) :=
  (folded (challenge history rest) (message rest witness) blind,
    fun publicIndex => functionals history rest publicIndex blind)

theorem outerView_coinEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest publicIndex left right,
      statement left = statement right →
        functionals history rest publicIndex
          (message rest right - message rest left) = 0)
    (left right : W) (hpublic : statement left = statement right)
    (rest : Rest)
    (coins : PreCoins (K := K) (I := I) (rounds := rounds)) :
    let translated :=
      coinEquiv secret challenge hchallenge message left right rest coins
    let leftHistory := run (secret rest) (left, coins.1) rounds coins.2
    let rightHistory := run (secret rest) (right, translated.1) rounds translated.2
    (leftHistory,
      outerView challenge message functionals left rest leftHistory coins.1) =
    (rightHistory,
      outerView challenge message functionals right rest rightHistory
        translated.1) := by
  dsimp only
  have hstate := stateEquiv_coinEquiv secret challenge hchallenge message
    left right rest coins
  have hhistory := congrArg Prod.fst hstate
  have hfolded := congrArg Prod.snd hstate
  change
    run (secret rest)
        (right,
          (coinEquiv secret challenge hchallenge message
            left right rest coins).1)
        rounds
        (coinEquiv secret challenge hchallenge message
          left right rest coins).2 =
      run (secret rest) (left, coins.1) rounds coins.2 at hhistory
  change
      folded
          (challenge
            (run (secret rest)
              (right,
                (coinEquiv secret challenge hchallenge message
                  left right rest coins).1)
              rounds
              (coinEquiv secret challenge hchallenge message
                left right rest coins).2)
            rest)
          (message rest right)
          (coinEquiv secret challenge hchallenge message
            left right rest coins).1 =
        folded
          (challenge
            (run (secret rest) (left, coins.1) rounds coins.2) rest)
          (message rest left) coins.1 at hfolded
  apply Prod.ext
  · exact hhistory.symm
  · apply Prod.ext
    · exact hfolded.symm
    · funext publicIndex
      change
        functionals
            (run (secret rest) (left, coins.1) rounds coins.2)
            rest publicIndex coins.1 =
          functionals
            (run (secret rest)
              (right,
                (coinEquiv secret challenge hchallenge message
                  left right rest coins).1)
              rounds
              (coinEquiv secret challenge hchallenge message
                left right rest coins).2)
            rest publicIndex
            (coinEquiv secret challenge hchallenge message
              left right rest coins).1
      rw [hhistory]
      symm
      apply functional_eq_of_folded_eq
        (challenge (run (secret rest) (left, coins.1) rounds coins.2) rest)
        (hchallenge _ rest)
        (functionals
          (run (secret rest) (left, coins.1) rounds coins.2) rest publicIndex)
        (message rest left) (message rest right) coins.1
        (coinEquiv secret challenge hchallenge message left right rest coins).1
      · exact hpublicKernel _ rest publicIndex left right hpublic
      · simpa only [hhistory] using hfolded

end VeiledFlock.ProductionOuterPcs

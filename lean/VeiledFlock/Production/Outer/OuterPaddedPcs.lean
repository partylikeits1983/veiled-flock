import VeiledFlock.Production.Outer.OuterPcs

/-!
# Outer PCS with raw L0 openings

Production L0 opens raw rows of both `[mask || witness]` and the full PCS
blinder `g`, while every later Ligerito value is computed from their nonzero
fold.  These values must be simulated jointly.  We factor the complete coin
triple `(message padding, g, causal FLOCK pads)` through the invariant data

`(visible prefix, full folded message, opened raw message rows)`.

The raw `g` rows are then forced to agree by linearity and the nonzero fold
coefficient.  This closes the correlation that a fold-only argument misses.
-/

namespace VeiledFlock.ProductionOuterPaddedPcs

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.Field128Ghash
open VeiledFlock.JointPcs
open VeiledFlock.ProductionOuterPcs

variable {K I P Pad Opened W Public Rest : Type*}
variable {rounds : ℕ}
variable [AddCommGroup Pad] [Module GhashField Pad]
variable [AddCommGroup Opened] [Module GhashField Opened]

abbrev State := W × Pad × Blind (I := I)
abbrev PreCoins :=
  Pad × Blind (I := I) × PcsMasks (K := K) (rounds := rounds)

/-- Conservative complete outer view: the full recursive fold, both families
of raw L0 openings, and every public-direct evaluation of `g`. -/
abbrev OuterPaddedView :=
  Blind (I := I) × Opened × Opened × (P → GhashField)

noncomputable def fullMessage
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (rest : Rest) (witness : W) (padding : Pad) : Blind (I := I) :=
  baseMessage rest witness + paddingEmbed rest padding

/-- Recover the unique padding vector producing a requested raw opening. -/
noncomputable def solvePadding
    (baseMessage : Rest → W → Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (rest : Rest) (witness : W) (target : Opened) : Pad :=
  (paddingOpening rest).symm
    (target - opening rest (baseMessage rest witness))

theorem solvePadding_opening_fullMessage
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (rest : Rest) (witness : W) (padding : Pad) :
    solvePadding baseMessage opening paddingOpening rest witness
        (opening rest
          (fullMessage baseMessage paddingEmbed rest witness padding)) =
      padding := by
  apply (paddingOpening rest).injective
  simp only [solvePadding, LinearEquiv.apply_symm_apply, fullMessage, map_add,
    hpadding]
  abel

theorem opening_fullMessage_solvePadding
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (rest : Rest) (witness : W) (target : Opened) :
    opening rest
        (fullMessage baseMessage paddingEmbed rest witness
          (solvePadding baseMessage opening paddingOpening rest witness
            target)) =
      target := by
  simp only [fullMessage, map_add, solvePadding, hpadding,
    LinearEquiv.apply_symm_apply]
  abel

/-- Exact factorization of every outer hiding coin through the three invariant
values needed by the verifier. -/
noncomputable def stateEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (witness : W) (rest : Rest) : Equiv
      (PreCoins (K := K) (I := I) (Pad := Pad) (rounds := rounds))
      (Prefix (K := K) (rounds := rounds) ×
        (Blind (I := I) × Opened)) where
  toFun coins :=
    let history := run (secret rest) (witness, coins.1, coins.2.1)
      rounds coins.2.2
    let message := fullMessage baseMessage paddingEmbed rest witness coins.1
    (history,
      (folded (challenge history rest) message coins.2.1,
        opening rest message))
  invFun visible :=
    let padding := solvePadding baseMessage opening paddingOpening rest
      witness visible.2.2
    let message := fullMessage baseMessage paddingEmbed rest witness padding
    let blind := (foldedEquiv (challenge visible.1 rest)
      (hchallenge visible.1 rest) message).symm visible.2.1
    (padding, blind,
      recover (secret rest) (witness, padding, blind) visible.1)
  left_inv coins := by
    let history := run (secret rest) (witness, coins.1, coins.2.1)
      rounds coins.2.2
    let message := fullMessage baseMessage paddingEmbed rest witness coins.1
    have hpad := solvePadding_opening_fullMessage baseMessage paddingEmbed
      opening paddingOpening hpadding rest witness coins.1
    change
      (solvePadding baseMessage opening paddingOpening rest witness
          (opening rest message),
        (foldedEquiv (challenge history rest) (hchallenge history rest)
          (fullMessage baseMessage paddingEmbed rest witness
            (solvePadding baseMessage opening paddingOpening rest witness
              (opening rest message)))).symm
            (folded (challenge history rest) message coins.2.1),
        recover (secret rest)
          (witness,
            solvePadding baseMessage opening paddingOpening rest witness
              (opening rest message),
            (foldedEquiv (challenge history rest) (hchallenge history rest)
              (fullMessage baseMessage paddingEmbed rest witness
                (solvePadding baseMessage opening paddingOpening rest witness
                  (opening rest message)))).symm
                (folded (challenge history rest) message coins.2.1))
          history) = coins
    rw [hpad]
    change
      (coins.1,
        (foldedEquiv (challenge history rest) (hchallenge history rest)
          message).symm
            (foldedEquiv (challenge history rest) (hchallenge history rest)
              message coins.2.1),
        recover (secret rest)
          (witness, coins.1,
            (foldedEquiv (challenge history rest) (hchallenge history rest)
              message).symm
              (foldedEquiv (challenge history rest) (hchallenge history rest)
                message coins.2.1)) history) = coins
    rw [Equiv.symm_apply_apply]
    exact Prod.ext rfl (Prod.ext rfl
      (recover_run (secret rest) (witness, coins.1, coins.2.1) coins.2.2))
  right_inv visible := by
    rcases visible with ⟨history, foldTarget, openedTarget⟩
    let padding := solvePadding baseMessage opening paddingOpening rest
      witness openedTarget
    let message := fullMessage baseMessage paddingEmbed rest witness padding
    let blind := (foldedEquiv (challenge history rest)
      (hchallenge history rest) message).symm foldTarget
    have hrun : run (secret rest) (witness, padding, blind) rounds
        (recover (secret rest) (witness, padding, blind) history) =
      history := run_recover (secret rest) (witness, padding, blind) history
    change
      (run (secret rest) (witness, padding, blind) rounds
          (recover (secret rest) (witness, padding, blind) history),
        (folded
          (challenge
            (run (secret rest) (witness, padding, blind) rounds
              (recover (secret rest) (witness, padding, blind) history)) rest)
          message blind,
        opening rest message)) = (history, foldTarget, openedTarget)
    rw [hrun]
    have hfold : folded (challenge history rest) message blind = foldTarget :=
      (foldedEquiv (challenge history rest)
        (hchallenge history rest) message).apply_symm_apply foldTarget
    have hopen : opening rest message = openedTarget :=
      opening_fullMessage_solvePadding baseMessage paddingEmbed opening
        paddingOpening hpadding rest witness openedTarget
    exact Prod.ext rfl (Prod.ext hfold hopen)

noncomputable def coinEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (left right : W) (rest : Rest) : Equiv
      (PreCoins (K := K) (I := I) (Pad := Pad) (rounds := rounds))
      (PreCoins (K := K) (I := I) (Pad := Pad) (rounds := rounds)) :=
  (stateEquiv secret challenge hchallenge baseMessage paddingEmbed opening
    paddingOpening hpadding left rest).trans
  (stateEquiv secret challenge hchallenge baseMessage paddingEmbed opening
    paddingOpening hpadding right rest).symm

theorem stateEquiv_coinEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (left right : W) (rest : Rest)
    (coins : PreCoins (K := K) (I := I) (Pad := Pad) (rounds := rounds)) :
    stateEquiv secret challenge hchallenge baseMessage paddingEmbed opening
        paddingOpening hpadding right rest
        (coinEquiv secret challenge hchallenge baseMessage paddingEmbed opening
          paddingOpening hpadding left right rest coins) =
      stateEquiv secret challenge hchallenge baseMessage paddingEmbed opening
        paddingOpening hpadding left rest coins := by
  exact (stateEquiv secret challenge hchallenge baseMessage paddingEmbed
    opening paddingOpening hpadding right rest).apply_symm_apply
      (stateEquiv secret challenge hchallenge baseMessage paddingEmbed opening
        paddingOpening hpadding left rest coins)

/-- If a linear opening sees the same two messages and their nonzero folds are
equal, it also sees the same two blinders.  This is the algebraic reason the
raw `g` rows in the initial Merkle proof remain unchanged. -/
theorem opening_blind_eq_of_message_and_folded_eq
    (c : GhashField) (hc : c ≠ 0)
    (opening : Blind (I := I) →ₗ[GhashField] Opened)
    (leftMessage rightMessage leftBlind rightBlind : Blind (I := I))
    (hmessage : opening rightMessage = opening leftMessage)
    (hfolded : folded c rightMessage rightBlind =
      folded c leftMessage leftBlind) :
    opening rightBlind = opening leftBlind := by
  have h := congrArg opening hfolded
  simp only [folded, map_add, map_smul] at h
  rw [hmessage] at h
  exact smul_right_injective Opened hc (add_left_cancel h)

/-- The conservative verifier-visible outer state, including every value
needed for the salted initial Merkle openings and every exposed public-direct
blinder functional. -/
noncomputable def outerPaddedView
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (witness : W) (padding : Pad) (rest : Rest)
    (history : Prefix (K := K) (rounds := rounds))
    (blind : Blind (I := I)) :
    OuterPaddedView (I := I) (P := P) (Opened := Opened) :=
  let message := fullMessage baseMessage paddingEmbed rest witness padding
  (folded (challenge history rest) message blind,
    (opening rest message,
      (opening rest blind,
        fun publicIndex => functionals history rest publicIndex blind)))

/-- The joint padding/blinder/FLOCK-mask translation preserves the complete
outer verifier view.  The kernel premise says that public-direct claims depend
only on the common public statement; production packed-direct claims satisfy
it because the low mask half has zero coefficient and valid witnesses have
the same claimed public evaluations. -/
theorem outerPaddedView_coinEquiv
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest publicIndex left right leftPadding rightPadding,
      statement left = statement right →
        functionals history rest publicIndex
          (fullMessage baseMessage paddingEmbed rest right rightPadding -
            fullMessage baseMessage paddingEmbed rest left leftPadding) = 0)
    (left right : W) (hpublic : statement left = statement right)
    (rest : Rest)
    (coins : PreCoins (K := K) (I := I) (Pad := Pad) (rounds := rounds)) :
    let translated := coinEquiv secret challenge hchallenge baseMessage
      paddingEmbed opening paddingOpening hpadding left right rest coins
    let leftHistory := run (secret rest) (left, coins.1, coins.2.1)
      rounds coins.2.2
    let rightHistory := run (secret rest)
      (right, translated.1, translated.2.1) rounds translated.2.2
    (leftHistory,
      outerPaddedView challenge baseMessage paddingEmbed opening functionals
        left coins.1 rest leftHistory coins.2.1) =
    (rightHistory,
      outerPaddedView challenge baseMessage paddingEmbed opening functionals
        right translated.1 rest rightHistory translated.2.1) := by
  dsimp only
  let translated := coinEquiv secret challenge hchallenge baseMessage
    paddingEmbed opening paddingOpening hpadding left right rest coins
  let leftHistory := run (secret rest) (left, coins.1, coins.2.1)
    rounds coins.2.2
  let rightHistory := run (secret rest)
    (right, translated.1, translated.2.1) rounds translated.2.2
  let leftMessage := fullMessage baseMessage paddingEmbed rest left coins.1
  let rightMessage := fullMessage baseMessage paddingEmbed rest right translated.1
  have hstate := stateEquiv_coinEquiv secret challenge hchallenge baseMessage
    paddingEmbed opening paddingOpening hpadding left right rest coins
  have hhistory := congrArg Prod.fst hstate
  have hfolded := congrArg (fun state => state.2.1) hstate
  have hmessage := congrArg (fun state => state.2.2) hstate
  change rightHistory = leftHistory at hhistory
  change folded (challenge rightHistory rest) rightMessage translated.2.1 =
    folded (challenge leftHistory rest) leftMessage coins.2.1 at hfolded
  change opening rest rightMessage = opening rest leftMessage at hmessage
  have hfoldedAtLeft :
      folded (challenge leftHistory rest) rightMessage translated.2.1 =
        folded (challenge leftHistory rest) leftMessage coins.2.1 := by
    simpa only [hhistory] using hfolded
  have hblindOpening : opening rest translated.2.1 =
      opening rest coins.2.1 :=
    opening_blind_eq_of_message_and_folded_eq
      (challenge leftHistory rest) (hchallenge leftHistory rest)
      (opening rest) leftMessage rightMessage coins.2.1 translated.2.1
      hmessage hfoldedAtLeft
  change
    (leftHistory,
      (folded (challenge leftHistory rest) leftMessage coins.2.1,
        (opening rest leftMessage,
          (opening rest coins.2.1,
            fun publicIndex =>
              functionals leftHistory rest publicIndex coins.2.1)))) =
    (rightHistory,
      (folded (challenge rightHistory rest) rightMessage translated.2.1,
        (opening rest rightMessage,
          (opening rest translated.2.1,
            fun publicIndex =>
              functionals rightHistory rest publicIndex translated.2.1))))
  have hfunctionals :
      (fun publicIndex =>
        functionals leftHistory rest publicIndex coins.2.1) =
      (fun publicIndex =>
        functionals leftHistory rest publicIndex translated.2.1) := by
    funext publicIndex
    symm
    apply functional_eq_of_folded_eq
      (challenge leftHistory rest) (hchallenge leftHistory rest)
      (functionals leftHistory rest publicIndex)
      leftMessage rightMessage coins.2.1 translated.2.1
    · exact hpublicKernel leftHistory rest publicIndex left right
        coins.1 translated.1 hpublic
    · exact hfoldedAtLeft
  rw [hhistory]
  exact Prod.ext rfl
    (Prod.ext hfoldedAtLeft.symm
      (Prod.ext hmessage.symm
        (Prod.ext hblindOpening.symm hfunctionals)))

end VeiledFlock.ProductionOuterPaddedPcs

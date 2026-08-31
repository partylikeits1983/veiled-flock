import VeiledFlock.Algebra.AdditiveReedSolomon
import VeiledFlock.Algebra.JointPcs
import VeiledFlock.Algebra.OneTimePad
import VeiledFlock.Core.Probability
import VeiledFlock.Algebra.VeilMultiplicationPadding

/-!
# Joint algebraic VEIL--FLOCK view

This file composes the four port-specific hiding mechanisms into one theorem
about one joint transcript and one joint source of independent coins:

* coordinate-wise FLOCK one-time pads;
* VEIL's two multiplication-padding rows;
* Reed--Solomon padding at the queried coordinates; and
* the joint message/blinder PCS opening.

The proof constructs one explicit bijection between the coins used for two
witnesses with the same public statement.  Every component of the complete
algebraic view is pointwise invariant under that bijection, so finite uniform
reparameterization gives exact equality of the two PMFs.
-/

namespace VeiledFlock.AlgebraicProtocol

open Function
open VeiledFlock.AdditiveReedSolomon
open VeiledFlock.JointPcs
open VeiledFlock.VeilMultiplicationPadding

variable {F I Data Padding J W Public : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype I] [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J]
variable [Fintype (I → F)] [Fintype (Padding → F)] [Fintype (J → F)]

/-- All independent algebraic coins, in protocol order. -/
abbrev Coins :=
  (I → F) × (F × F × F) × (Padding → F) × (J → F)

/-- The complete algebraic view covered by the joint masking argument. -/
abbrev View :=
  (I → F) × (F × F × F) × (Padding → F) × ((J → F) × F)

private def flockCoinEquiv (left right : I → F) : (I → F) ≃ (I → F) :=
  Equiv.addRight (left - right)

private noncomputable def veilCoinEquiv (alpha : F) (halpha : alpha ≠ 0)
    (hplus : 1 + alpha ≠ 0) (left right : F × F × F) :
    (F × F × F) ≃ (F × F × F) :=
  ((dummyViewEquiv alpha halpha hplus).trans
    (Equiv.addRight (left - right))).trans
      (dummyViewEquiv alpha halpha hplus).symm

private noncomputable def paddingCoinEquiv
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (left right : Padding → F) : (Padding → F) ≃ (Padding → F) :=
  let codeEquiv := paddingQueryEquiv base hbase queries hqueries hdisjoint
  (codeEquiv.toEquiv.trans (Equiv.addRight (left - right))).trans
    codeEquiv.toEquiv.symm

private def pcsCoinEquiv (c : F) (delta : J → F) : (J → F) ≃ (J → F) :=
  Equiv.addRight (-c⁻¹ • delta)

/-- Reparameterization from honest algebraic coins to the coins sampled by the
public-input-only simulator. -/
noncomputable def simulatorCoinEquiv
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (flockSecret : I → F) (veilSecret : F × F × F)
    (querySecret : Padding → F) (message : J → F) :
    Coins (F := F) (I := I) (Padding := Padding) (J := J) ≃
      Coins (F := F) (I := I) (Padding := Padding) (J := J) :=
  Equiv.prodCongr (Equiv.addRight flockSecret)
    (Equiv.prodCongr
      ((dummyViewEquiv alpha halpha hplus).trans
        (Equiv.addRight veilSecret))
      (Equiv.prodCongr
        ((paddingQueryEquiv base hbase queries hqueries hdisjoint).toEquiv.trans
          (Equiv.addRight querySecret))
        (foldedEquiv c hc message)))

omit [Fintype F] [DecidableEq F] [Fintype I] [Fintype (I → F)] in
@[simp]
private theorem flockCoinEquiv_apply (left right coins : I → F) :
    flockCoinEquiv left right coins = coins + (left - right) := rfl

omit [Fintype F] [DecidableEq F] in
private theorem dummyView_veilCoinEquiv
    (alpha : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (left right coins : F × F × F) :
    dummyView alpha (veilCoinEquiv alpha halpha hplus left right coins) =
      dummyView alpha coins + (left - right) := by
  change dummyViewEquiv alpha halpha hplus
      ((dummyViewEquiv alpha halpha hplus).symm
        (dummyViewEquiv alpha halpha hplus coins + (left - right))) = _
  rw [Equiv.apply_symm_apply, dummyViewEquiv_apply]

omit [Fintype F] [DecidableEq F] [Fintype (Padding → F)] in
private theorem paddingToQueries_paddingCoinEquiv
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (left right coins : Padding → F) :
    paddingToQueries base hbase queries
        (paddingCoinEquiv base hbase queries hqueries hdisjoint left right coins) =
      paddingToQueries base hbase queries coins + (left - right) := by
  let codeEquiv := paddingQueryEquiv base hbase queries hqueries hdisjoint
  change codeEquiv
      (codeEquiv.symm (codeEquiv coins + (left - right))) = _
  rw [LinearEquiv.apply_symm_apply, paddingQueryEquiv_apply]

omit [Fintype F] [DecidableEq F] [Fintype J] [Fintype (J → F)] in
@[simp]
private theorem pcsCoinEquiv_apply (c : F) (delta coins : J → F) :
    pcsCoinEquiv c delta coins = translateBlind c delta coins := by
  simp only [pcsCoinEquiv, translateBlind, Equiv.coe_addRight,
    sub_eq_add_neg, neg_smul]

private noncomputable def coinEquiv
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (flockLeft flockRight : I → F)
    (veilLeft veilRight : F × F × F)
    (queriesLeft queriesRight : Padding → F)
    (messageLeft messageRight : J → F) :
    Coins (F := F) (I := I) (Padding := Padding) (J := J) ≃
      Coins (F := F) (I := I) (Padding := Padding) (J := J) :=
  Equiv.prodCongr (flockCoinEquiv flockLeft flockRight)
    (Equiv.prodCongr (veilCoinEquiv alpha halpha hplus veilLeft veilRight)
      (Equiv.prodCongr
        (paddingCoinEquiv base hbase queries hqueries hdisjoint
          queriesLeft queriesRight)
        (pcsCoinEquiv c (messageRight - messageLeft))))

/-- Public name for the explicit algebraic coin translation between two
witnesses.  Exposing this equivalence lets later state-machine modules compose
it with the causal transcript-mask and oracle reparameterizations. -/
noncomputable def witnessCoinEquiv
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (flockLeft flockRight : I → F)
    (veilLeft veilRight : F × F × F)
    (queriesLeft queriesRight : Padding → F)
    (messageLeft messageRight : J → F) :
    Coins (F := F) (I := I) (Padding := Padding) (J := J) ≃
      Coins (F := F) (I := I) (Padding := Padding) (J := J) :=
  coinEquiv alpha c halpha hplus base hbase queries hqueries hdisjoint
    flockLeft flockRight veilLeft veilRight queriesLeft queriesRight
    messageLeft messageRight

/-- Evaluation of the complete modeled algebraic view. -/
noncomputable def realView
    (alpha c : F)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (witness : W)
    (coins : Coins (F := F) (I := I) (Padding := Padding) (J := J)) :
    View (F := F) (I := I) (Padding := Padding) (J := J) :=
  (coins.1 + flockSecret witness,
    dummyView alpha coins.2.1 + veilSecret witness,
    paddingToQueries base hbase queries coins.2.2.1 + querySecret witness,
    (folded c (message witness) coins.2.2.2,
      functional coins.2.2.2))

/-- Public-input-only algebraic simulator.  Its first three components are
sampled uniformly; the PCS component is reconstructed from the public linear
functional of the witness message. -/
noncomputable def simulatedView
    (c : F) (functional : (J → F) →ₗ[F] F)
    (publicMessageValue : F)
    (coins : Coins (F := F) (I := I) (Padding := Padding) (J := J)) :
    View (F := F) (I := I) (Padding := Padding) (J := J) :=
  (coins.1, coins.2.1, coins.2.2.1,
    simulatedOpeningView c functional publicMessageValue coins.2.2.2)

omit [Fintype F] [DecidableEq F] [Fintype I] [Fintype J] [Fintype (I → F)] [Fintype (Padding → F)] [Fintype (J → F)] in
theorem realView_simulator_transport
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (witness : W)
    (coins : Coins (F := F) (I := I) (Padding := Padding) (J := J)) :
    realView alpha c base hbase queries functional flockSecret veilSecret
        querySecret message witness coins =
      simulatedView c functional (functional (message witness))
        (simulatorCoinEquiv alpha c halpha hplus hc base hbase queries
          hqueries hdisjoint (flockSecret witness) (veilSecret witness)
          (querySecret witness) (message witness) coins) := by
  rcases coins with ⟨flockCoins, veilCoins, queryCoins, pcsCoins⟩
  apply Prod.ext
  · change flockCoins + flockSecret witness =
      flockCoins + flockSecret witness
    rfl
  · apply Prod.ext
    · change dummyView alpha veilCoins + veilSecret witness =
        dummyView alpha veilCoins + veilSecret witness
      rfl
    · apply Prod.ext
      · change paddingToQueries base hbase queries queryCoins +
            querySecret witness =
          paddingQueryEquiv base hbase queries hqueries hdisjoint queryCoins +
            querySecret witness
        rw [paddingQueryEquiv_apply]
      · change realOpeningView c functional (message witness) pcsCoins =
          simulatedOpeningView c functional (functional (message witness))
            (foldedEquiv c hc (message witness) pcsCoins)
        exact realOpeningView_foldedEquiv c hc functional
          (message witness) pcsCoins

omit [Fintype F] [DecidableEq F] [Fintype I] [Fintype J] [Fintype (I → F)] [Fintype (Padding → F)] [Fintype (J → F)] in
private theorem pointwise_transport
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (left right : W)
    (hkernel : functional (message right - message left) = 0)
    (coins : Coins (F := F) (I := I) (Padding := Padding) (J := J)) :
    realView alpha c base hbase queries functional flockSecret veilSecret
        querySecret message left coins =
      realView alpha c base hbase queries functional flockSecret veilSecret
        querySecret message right
        (coinEquiv alpha c halpha hplus base hbase queries hqueries hdisjoint
          (flockSecret left) (flockSecret right)
          (veilSecret left) (veilSecret right)
          (querySecret left) (querySecret right)
          (message left) (message right) coins) := by
  rcases coins with ⟨flockCoins, veilCoins, queryCoins, pcsCoins⟩
  apply Prod.ext
  · change flockCoins + flockSecret left =
      flockCoinEquiv (flockSecret left) (flockSecret right) flockCoins +
        flockSecret right
    rw [flockCoinEquiv_apply]
    abel
  · apply Prod.ext
    · change dummyView alpha veilCoins + veilSecret left =
        dummyView alpha
            (veilCoinEquiv alpha halpha hplus
              (veilSecret left) (veilSecret right) veilCoins) +
          veilSecret right
      rw [dummyView_veilCoinEquiv]
      abel
    · apply Prod.ext
      · change paddingToQueries base hbase queries queryCoins + querySecret left =
          paddingToQueries base hbase queries
              (paddingCoinEquiv base hbase queries hqueries hdisjoint
                (querySecret left) (querySecret right) queryCoins) +
            querySecret right
        rw [paddingToQueries_paddingCoinEquiv]
        abel
      · apply Prod.ext
        · change folded c (message left) pcsCoins =
            folded c (message right)
              (pcsCoinEquiv c (message right - message left) pcsCoins)
          rw [pcsCoinEquiv_apply]
          have hmessage : message left + (message right - message left) =
              message right := by abel
          calc
            folded c (message left) pcsCoins =
                folded c (message left + (message right - message left))
                  (translateBlind c (message right - message left) pcsCoins) :=
              (folded_translate c hc (message left) pcsCoins
                (message right - message left)).symm
            _ = folded c (message right)
                (translateBlind c (message right - message left) pcsCoins) := by
              rw [hmessage]
        · change functional pcsCoins =
            functional (pcsCoinEquiv c (message right - message left) pcsCoins)
          rw [pcsCoinEquiv_apply]
          exact (functional_translate c pcsCoins (message right - message left)
            functional hkernel).symm

omit [Fintype F] [DecidableEq F] [Fintype I] [Fintype J] [Fintype (I → F)] [Fintype (Padding → F)] [Fintype (J → F)] in
/-- The joint algebraic view is pointwise preserved by
`witnessCoinEquiv`. -/
theorem realView_witnessCoinEquiv
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (left right : W)
    (hkernel : functional (message right - message left) = 0)
    (coins : Coins (F := F) (I := I) (Padding := Padding) (J := J)) :
    realView alpha c base hbase queries functional flockSecret veilSecret
        querySecret message left coins =
      realView alpha c base hbase queries functional flockSecret veilSecret
        querySecret message right
        (witnessCoinEquiv alpha c halpha hplus base hbase queries hqueries
          hdisjoint (flockSecret left) (flockSecret right)
          (veilSecret left) (veilSecret right)
          (querySecret left) (querySecret right)
          (message left) (message right) coins) :=
  pointwise_transport alpha c halpha hplus hc base hbase queries hqueries
    hdisjoint functional flockSecret veilSecret querySecret message left right
    hkernel coins

omit [DecidableEq F] [Fintype I] [Fintype J] in
/-- **Explicit algebraic simulator.** The simulator receives only the public
statement, samples fresh uniform algebraic coins, and produces exactly the
honest algebraic view distribution. -/
theorem algebraicSimulator_exact
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (statement : W → Public)
    (publicMessageValue : Public → F)
    (hpublicMessage : ∀ witness,
      publicMessageValue (statement witness) = functional (message witness))
    (witness : W) :
    (PMF.uniformOfFintype
      (Coins (F := F) (I := I) (Padding := Padding) (J := J))).map
        (realView alpha c base hbase queries functional flockSecret veilSecret
          querySecret message witness) =
      (PMF.uniformOfFintype
        (Coins (F := F) (I := I) (Padding := Padding) (J := J))).map
          (simulatedView c functional
            (publicMessageValue (statement witness))) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (simulatorCoinEquiv alpha c halpha hplus hc base hbase queries hqueries
      hdisjoint (flockSecret witness) (veilSecret witness)
      (querySecret witness) (message witness))
  intro coins
  rw [hpublicMessage witness]
  exact realView_simulator_transport alpha c halpha hplus hc base hbase queries
    hqueries hdisjoint functional flockSecret veilSecret querySecret message
    witness coins

omit [DecidableEq F] [Fintype I] [Fintype J] in
/-- **Exact algebraic end-to-end zero knowledge.** For witnesses with the same
public statement, the entire modeled algebraic VEIL--FLOCK view has identical
distribution.  The only relation-specific premise is that the exposed public
PCS functional annihilates the difference of equal-statement messages. -/
theorem algebraic_e2e_zeroKnowledge
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Injective base)
    (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (statement : W → Public)
    (hpublicKernel : ∀ left right, statement left = statement right →
      functional (message right - message left) = 0)
    {left right : W} (hpublic : statement left = statement right) :
    (PMF.uniformOfFintype
      (Coins (F := F) (I := I) (Padding := Padding) (J := J))).map
        (realView alpha c base hbase queries functional flockSecret veilSecret
          querySecret message left) =
      (PMF.uniformOfFintype
        (Coins (F := F) (I := I) (Padding := Padding) (J := J))).map
          (realView alpha c base hbase queries functional flockSecret veilSecret
            querySecret message right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv alpha c halpha hplus base hbase queries hqueries hdisjoint
      (flockSecret left) (flockSecret right)
      (veilSecret left) (veilSecret right)
      (querySecret left) (querySecret right)
      (message left) (message right))
  exact pointwise_transport alpha c halpha hplus hc base hbase queries hqueries
    hdisjoint functional flockSecret veilSecret querySecret message left right
    (hpublicKernel left right hpublic)

section Fiberwise

variable {Rest FullView : Type*}

omit [DecidableEq F] [Fintype I] [Fintype J] in
/-- **Challenge-dependent algebraic zero knowledge.**  All Fiat--Shamir
challenges, evaluation points, linear functionals, and witness-derived
algebraic messages may depend on a fixed fiber containing the complete public
random-oracle interaction.  The algebraic coins are reparameterized separately
inside every such fiber, so arbitrary post-processing of the joint view is
still witness independent.

This is the form needed by the interactive VEIL--FLOCK transcript: once the
masked prefix and oracle table are fixed, the accepted challenges are fixed,
but they need not have been chosen before the protocol began. -/
theorem fiberwise_algebraic_e2e_zeroKnowledge
    [Fintype Rest] [Nonempty Rest]
    (alpha c : Rest → F)
    (halpha : ∀ rest, alpha rest ≠ 0)
    (hplus : ∀ rest, 1 + alpha rest ≠ 0)
    (hc : ∀ rest, c rest ≠ 0)
    (base : Rest → Data ⊕ Padding → F)
    (hbase : ∀ rest, Injective (base rest))
    (queries : Rest → Padding → F)
    (hqueries : ∀ rest, Injective (queries rest))
    (hdisjoint : ∀ rest d q, base rest (Sum.inl d) ≠ queries rest q)
    (functional : Rest → (J → F) →ₗ[F] F)
    (flockSecret : Rest → W → I → F)
    (veilSecret : Rest → W → F × F × F)
    (querySecret : Rest → W → Padding → F)
    (message : Rest → W → J → F)
    (statement : W → Public)
    (hpublicKernel : ∀ rest left right,
      statement left = statement right →
        functional rest (message rest right - message rest left) = 0)
    {left right : W} (hpublic : statement left = statement right)
    (continueWith : Rest →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView) :
    (PMF.uniformOfFintype
      (Coins (F := F) (I := I) (Padding := Padding) (J := J) × Rest)).map
        (fun coins => continueWith coins.2
          (realView (alpha coins.2) (c coins.2) (base coins.2)
            (hbase coins.2) (queries coins.2) (functional coins.2)
            (flockSecret coins.2) (veilSecret coins.2)
            (querySecret coins.2) (message coins.2) left coins.1)) =
      (PMF.uniformOfFintype
        (Coins (F := F) (I := I) (Padding := Padding) (J := J) × Rest)).map
          (fun coins => continueWith coins.2
            (realView (alpha coins.2) (c coins.2) (base coins.2)
              (hbase coins.2) (queries coins.2) (functional coins.2)
              (flockSecret coins.2) (veilSecret coins.2)
              (querySecret coins.2) (message coins.2) right coins.1)) := by
  let split :
      (Coins (F := F) (I := I) (Padding := Padding) (J := J) × Rest) ≃
        (Coins (F := F) (I := I) (Padding := Padding) (J := J) × Rest) :=
    Equiv.refl _
  let equiv := VeiledFlock.Probability.fiberwiseEquiv split
    (fun rest => coinEquiv (alpha rest) (c rest) (halpha rest) (hplus rest)
      (base rest) (hbase rest) (queries rest) (hqueries rest)
      (hdisjoint rest)
      (flockSecret rest left) (flockSecret rest right)
      (veilSecret rest left) (veilSecret rest right)
      (querySecret rest left) (querySecret rest right)
      (message rest left) (message rest right))
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv equiv
  intro coins
  simp only [equiv, split]
  apply congrArg (continueWith coins.2)
  exact pointwise_transport (alpha coins.2) (c coins.2)
    (halpha coins.2) (hplus coins.2) (hc coins.2)
    (base coins.2) (hbase coins.2) (queries coins.2) (hqueries coins.2)
    (hdisjoint coins.2) (functional coins.2) (flockSecret coins.2)
    (veilSecret coins.2) (querySecret coins.2) (message coins.2) left right
    (hpublicKernel coins.2 left right hpublic) coins.1

end Fiberwise

end VeiledFlock.AlgebraicProtocol

import VeiledFlock.Production.Outer.OuterCodeDomains
import VeiledFlock.Production.Algebra.CorrelatedLayerSpec

/-!
# Corrected complete algebraic VEIL--FLOCK view

This is the load-bearing algebraic composition theorem.  Unlike the earlier
fold-only abstraction, it jointly translates the outer active message mask,
the complete PCS blinder, and every causal FLOCK pad.  It preserves both raw
families of salted L0 Merkle rows as well as the recursive fold and all
public-direct blinder values.  In that unchanged fiber it then translates all
VEIL multiplication, linear-code, Hadamard-code, and product-mask coins.
-/

namespace VeiledFlock.ProductionPaddedAlgebraicE2E

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionCorrelatedLayerSpec
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionCorrelatedVeilLayer

variable {K I P Pad Opened W Public Rest : Type*}
variable {rounds : ℕ}
variable [AddCommGroup Pad] [Module GhashField Pad]
variable [AddCommGroup Opened] [Module GhashField Opened]

abbrev OuterCoins :=
  VeiledFlock.ProductionOuterPaddedPcs.PreCoins
    (K := K) (I := I) (Pad := Pad) (rounds := rounds)

abbrev Coins (shape : BatchShape) :=
  OuterCoins (K := K) (I := I) (Pad := Pad) (rounds := rounds) ×
    (LayerCoins shape × Rest)

abbrev View (shape : BatchShape) :=
  Rest × Prefix (K := K) (rounds := rounds) ×
    VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
      (I := I) (P := P) (Opened := Opened) ×
    LayerView shape

noncomputable def view (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := I) (P := P) (Opened := Opened) →
      Rest → Spec shape W Public)
    (witness : W)
    (coins : Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
      (rounds := rounds) shape) :
    View (K := K) (I := I) (P := P) (Opened := Opened) (Rest := Rest)
      (rounds := rounds) shape :=
  let history := run (secret coins.2.2)
    (witness, coins.1.1, coins.1.2.1) rounds coins.1.2.2
  let outer := VeiledFlock.ProductionOuterPaddedPcs.outerPaddedView
    challenge baseMessage paddingEmbed opening functionals witness coins.1.1
    coins.2.2 history coins.1.2.1
  (coins.2.2, history, outer,
    ProductionCorrelatedLayerSpec.view (layerSpec history outer coins.2.2)
      witness coins.2.1)

noncomputable def outerStage (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (paddingOpening : Rest → Pad ≃ₗ[GhashField] Opened)
    (hpadding : ∀ rest padding,
      opening rest (paddingEmbed rest padding) = paddingOpening rest padding)
    (left right : W) : Equiv
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape)
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape) where
  toFun coins :=
    (VeiledFlock.ProductionOuterPaddedPcs.coinEquiv secret challenge
      hchallenge baseMessage paddingEmbed opening paddingOpening hpadding
      left right coins.2.2 coins.1, coins.2)
  invFun coins :=
    ((VeiledFlock.ProductionOuterPaddedPcs.coinEquiv secret challenge
      hchallenge baseMessage paddingEmbed opening paddingOpening hpadding
      left right coins.2.2).symm coins.1, coins.2)
  left_inv coins := by simp
  right_inv coins := by simp

noncomputable def veilStage (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (baseMessage : Rest → W → Blind (I := I))
    (paddingEmbed : Rest → Pad →ₗ[GhashField] Blind (I := I))
    (opening : Rest → Blind (I := I) →ₗ[GhashField] Opened)
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := I) (P := P) (Opened := Opened) →
      Rest → Spec shape W Public)
    (historyWitness left right : W) : Equiv
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape)
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape) where
  toFun coins :=
    let history := run (secret coins.2.2)
      (historyWitness, coins.1.1, coins.1.2.1) rounds coins.1.2.2
    let outer := VeiledFlock.ProductionOuterPaddedPcs.outerPaddedView
      challenge baseMessage paddingEmbed opening functionals historyWitness
      coins.1.1 coins.2.2 history coins.1.2.1
    (coins.1,
      (ProductionCorrelatedLayerSpec.coinEquiv
        (layerSpec history outer coins.2.2) left right coins.2.1,
        coins.2.2))
  invFun coins :=
    let history := run (secret coins.2.2)
      (historyWitness, coins.1.1, coins.1.2.1) rounds coins.1.2.2
    let outer := VeiledFlock.ProductionOuterPaddedPcs.outerPaddedView
      challenge baseMessage paddingEmbed opening functionals historyWitness
      coins.1.1 coins.2.2 history coins.1.2.1
    (coins.1,
      ((ProductionCorrelatedLayerSpec.coinEquiv
        (layerSpec history outer coins.2.2) left right).symm coins.2.1,
        coins.2.2))
  left_inv coins := by simp
  right_inv coins := by simp

/-- One bijection over every algebraic privacy coin in the production
outer-PCS/FLOCK/VEIL composition. -/
noncomputable def coinEquiv (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
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
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := I) (P := P) (Opened := Opened) →
      Rest → Spec shape W Public)
    (left right : W) : Equiv
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape)
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape) :=
  (outerStage shape secret challenge hchallenge baseMessage paddingEmbed
    opening paddingOpening hpadding left right).trans
  (veilStage shape secret challenge baseMessage paddingEmbed opening
    functionals layerSpec right left right)

theorem view_coinEquiv (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
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
          (VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest right rightPadding -
            VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest left leftPadding) = 0)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := I) (P := P) (Opened := Opened) →
      Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    (left right : W) (hpublic : statement left = statement right)
    (coins : Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
      (rounds := rounds) shape) :
    view shape secret challenge baseMessage paddingEmbed opening functionals
        layerSpec left coins =
      view shape secret challenge baseMessage paddingEmbed opening functionals
        layerSpec right
        (coinEquiv shape secret challenge hchallenge baseMessage paddingEmbed
          opening paddingOpening hpadding functionals layerSpec left right coins) := by
  rcases coins with ⟨outerCoins, layerCoins, rest⟩
  let translatedOuter := VeiledFlock.ProductionOuterPaddedPcs.coinEquiv
    secret challenge hchallenge baseMessage paddingEmbed opening paddingOpening
    hpadding left right rest outerCoins
  have hprefixOuter :=
    VeiledFlock.ProductionOuterPaddedPcs.outerPaddedView_coinEquiv
      secret challenge hchallenge baseMessage paddingEmbed opening paddingOpening
      hpadding functionals statement hpublicKernel left right hpublic rest outerCoins
  have hhistory := congrArg Prod.fst hprefixOuter
  have houter := congrArg Prod.snd hprefixOuter
  let leftHistory := run (secret rest)
    (left, outerCoins.1, outerCoins.2.1) rounds outerCoins.2.2
  let rightHistory := run (secret rest)
    (right, translatedOuter.1, translatedOuter.2.1)
    rounds translatedOuter.2.2
  let leftOuter := VeiledFlock.ProductionOuterPaddedPcs.outerPaddedView
    challenge baseMessage paddingEmbed opening functionals left outerCoins.1
    rest leftHistory outerCoins.2.1
  let rightOuter := VeiledFlock.ProductionOuterPaddedPcs.outerPaddedView
    challenge baseMessage paddingEmbed opening functionals right translatedOuter.1
    rest rightHistory translatedOuter.2.1
  change
    (rest, leftHistory, leftOuter,
      ProductionCorrelatedLayerSpec.view (layerSpec leftHistory leftOuter rest)
        left layerCoins) =
    (rest, rightHistory, rightOuter,
      ProductionCorrelatedLayerSpec.view (layerSpec rightHistory rightOuter rest)
        right
        (ProductionCorrelatedLayerSpec.coinEquiv
          (layerSpec rightHistory rightOuter rest) left right layerCoins))
  change leftHistory = rightHistory at hhistory
  change leftOuter = rightOuter at houter
  rw [← hhistory, ← houter]
  simp only [Prod.mk.injEq, true_and]
  apply ProductionCorrelatedLayerSpec.view_coinEquiv
  simpa only [hspecStatement] using hpublic

theorem witness_independent
    [Fintype K] [Fintype (K → GhashField)]
    [Fintype I] [Fintype (I → GhashField)]
    [Fintype Pad] [Fintype Opened]
    [Fintype Rest] [Nonempty Rest]
    (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := VeiledFlock.ProductionOuterPaddedPcs.State
        (I := I) (Pad := Pad) (W := W)))
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
          (VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest right rightPadding -
            VeiledFlock.ProductionOuterPaddedPcs.fullMessage
              baseMessage paddingEmbed rest left leftPadding) = 0)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := I) (P := P) (Opened := Opened) →
      Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    {left right : W} (hpublic : statement left = statement right) :
    (PMF.uniformOfFintype
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape)).map
      (view shape secret challenge baseMessage paddingEmbed opening functionals
        layerSpec left) =
    (PMF.uniformOfFintype
      (Coins (K := K) (I := I) (Pad := Pad) (Rest := Rest)
        (rounds := rounds) shape)).map
      (view shape secret challenge baseMessage paddingEmbed opening functionals
        layerSpec right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv shape secret challenge hchallenge baseMessage paddingEmbed
      opening paddingOpening hpadding functionals layerSpec left right)
  exact view_coinEquiv shape secret challenge hchallenge baseMessage
    paddingEmbed opening paddingOpening hpadding functionals statement
    hpublicKernel layerSpec hspecStatement left right hpublic

end VeiledFlock.ProductionPaddedAlgebraicE2E

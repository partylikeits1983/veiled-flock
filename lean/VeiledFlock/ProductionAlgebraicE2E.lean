import VeiledFlock.ProductionOuterPcs
import VeiledFlock.ProductionLayerSpec

/-!
# Complete production algebraic VEIL--FLOCK view

This file joins the outer shielded PCS, the causal FLOCK transcript masks, and
the complete VEIL layer under one triangular coin equivalence. The outer step
preserves the masked prefix and folded PCS view; the VEIL step is selected in
that unchanged public fiber and preserves all dummy-product, padded-code, and
product-mask data.
-/

namespace VeiledFlock.ProductionAlgebraicE2E

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionLayerSpec
open VeiledFlock.ProductionOuterPcs
open VeiledFlock.ProductionVeilLayer

variable {K I P W Public Rest : Type*}
variable {rounds : ℕ}

abbrev Coins (shape : BatchShape) :=
  PreCoins (K := K) (I := I) (rounds := rounds) ×
    (LayerCoins shape × Rest)

abbrev View (shape : BatchShape) :=
  Rest × Prefix (K := K) (rounds := rounds) ×
    OuterView (I := I) (P := P) × LayerView shape

noncomputable def view (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (message : Rest → W → Blind (I := I))
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      OuterView (I := I) (P := P) → Rest → Spec shape W Public)
    (witness : W)
    (coins : Coins (K := K) (I := I) (Rest := Rest)
      (rounds := rounds) shape) :
    View (K := K) (I := I) (P := P) (Rest := Rest)
      (rounds := rounds) shape :=
  let history := run (secret coins.2.2) (witness, coins.1.1)
    rounds coins.1.2
  let outer := outerView challenge message functionals witness coins.2.2
    history coins.1.1
  (coins.2.2, history, outer,
    ProductionLayerSpec.view (layerSpec history outer coins.2.2)
      witness coins.2.1)

/-- First triangular stage: jointly translate the outer PCS blinder and all
causal FLOCK pads, fiberwise in the untouched VEIL/rest tape. -/
noncomputable def outerStage (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (left right : W) : Equiv
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape)
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape) where
  toFun coins :=
    (ProductionOuterPcs.coinEquiv secret challenge hchallenge message
      left right coins.2.2 coins.1, coins.2)
  invFun coins :=
    ((ProductionOuterPcs.coinEquiv secret challenge hchallenge message
      left right coins.2.2).symm coins.1, coins.2)
  left_inv coins := by simp
  right_inv coins := by simp

/-- Second triangular stage: translate every VEIL coin in the already
preserved prefix/outer-view fiber. -/
noncomputable def veilStage (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (message : Rest → W → Blind (I := I))
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      OuterView (I := I) (P := P) → Rest → Spec shape W Public)
    (right left rightWitness : W) : Equiv
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape)
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape) where
  toFun coins :=
    let history := run (secret coins.2.2) (right, coins.1.1)
      rounds coins.1.2
    let outer := outerView challenge message functionals right coins.2.2
      history coins.1.1
    (coins.1,
      (ProductionLayerSpec.coinEquiv
        (layerSpec history outer coins.2.2) left rightWitness coins.2.1,
        coins.2.2))
  invFun coins :=
    let history := run (secret coins.2.2) (right, coins.1.1)
      rounds coins.1.2
    let outer := outerView challenge message functionals right coins.2.2
      history coins.1.1
    (coins.1,
      ((ProductionLayerSpec.coinEquiv
        (layerSpec history outer coins.2.2) left rightWitness).symm coins.2.1,
        coins.2.2))
  left_inv coins := by simp
  right_inv coins := by simp

/-- One equivalence over every algebraic privacy coin used before the
witness-independent recursive continuation. -/
noncomputable def coinEquiv (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K)
      (W := State (I := I) (W := W)))
    (challenge : Prefix (K := K) (rounds := rounds) → Rest → GhashField)
    (hchallenge : ∀ history rest, challenge history rest ≠ 0)
    (message : Rest → W → Blind (I := I))
    (functionals : Prefix (K := K) (rounds := rounds) → Rest → P →
      Blind (I := I) →ₗ[GhashField] GhashField)
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      OuterView (I := I) (P := P) → Rest → Spec shape W Public)
    (left right : W) : Equiv
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape)
      (Coins (K := K) (I := I) (Rest := Rest) (rounds := rounds) shape) :=
  (outerStage shape secret challenge hchallenge message left right).trans
    (veilStage shape secret challenge message functionals layerSpec
      right left right)

theorem view_coinEquiv (shape : BatchShape)
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
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      OuterView (I := I) (P := P) → Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    (left right : W) (hpublic : statement left = statement right)
    (coins : Coins (K := K) (I := I) (Rest := Rest)
      (rounds := rounds) shape) :
    view shape secret challenge message functionals layerSpec left coins =
      view shape secret challenge message functionals layerSpec right
        (coinEquiv shape secret challenge hchallenge message functionals
          layerSpec left right coins) := by
  rcases coins with ⟨preCoins, layerCoins, rest⟩
  let translatedPre := ProductionOuterPcs.coinEquiv secret challenge
    hchallenge message left right rest preCoins
  have hprefixOuter := ProductionOuterPcs.outerView_coinEquiv secret challenge
    hchallenge message functionals statement hpublicKernel left right hpublic
    rest preCoins
  have hhistory := congrArg Prod.fst hprefixOuter
  have houter := congrArg Prod.snd hprefixOuter
  let leftHistory := run (secret rest) (left, preCoins.1) rounds preCoins.2
  let rightHistory := run (secret rest) (right, translatedPre.1)
    rounds translatedPre.2
  let leftOuter := outerView challenge message functionals left rest
    leftHistory preCoins.1
  let rightOuter := outerView challenge message functionals right rest
    rightHistory translatedPre.1
  change
    (rest, leftHistory, leftOuter,
      ProductionLayerSpec.view (layerSpec leftHistory leftOuter rest)
        left layerCoins) =
    (rest, rightHistory, rightOuter,
      ProductionLayerSpec.view (layerSpec rightHistory rightOuter rest)
        right
        (ProductionLayerSpec.coinEquiv
          (layerSpec rightHistory rightOuter rest) left right layerCoins))
  change leftHistory = rightHistory at hhistory
  change leftOuter = rightOuter at houter
  rw [← hhistory, ← houter]
  simp only [Prod.mk.injEq, true_and]
  apply ProductionLayerSpec.view_coinEquiv
  simpa only [hspecStatement] using hpublic

theorem witness_independent
    [Fintype K] [Fintype (K → GhashField)]
    [Fintype I] [Fintype (I → GhashField)]
    [Fintype Rest] [Nonempty Rest]
    (shape : BatchShape)
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
    (layerSpec : Prefix (K := K) (rounds := rounds) →
      OuterView (I := I) (P := P) → Rest → Spec shape W Public)
    (hspecStatement : ∀ history outer rest,
      (layerSpec history outer rest).statement = statement)
    {left right : W} (hpublic : statement left = statement right) :
    (PMF.uniformOfFintype
      (Coins (K := K) (I := I) (Rest := Rest)
        (rounds := rounds) shape)).map
        (view shape secret challenge message functionals layerSpec left) =
      (PMF.uniformOfFintype
        (Coins (K := K) (I := I) (Rest := Rest)
          (rounds := rounds) shape)).map
          (view shape secret challenge message functionals layerSpec right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv shape secret challenge hchallenge message functionals
      layerSpec left right)
  exact view_coinEquiv shape secret challenge hchallenge message functionals
    statement hpublicKernel layerSpec hspecStatement left right hpublic

end VeiledFlock.ProductionAlgebraicE2E

import VeiledFlock.Oracle.AdaptiveOneTimePad
import VeiledFlock.Production.Algebra.LayerSpec

/-!
# Causal FLOCK masking composed with the complete VEIL layer

The production FLOCK transcript consumes 754--760 scalar masks causally:
later unmasked messages depend on earlier masked messages and Fiat--Shamir
answers. After translating that mask tape, the entire visible history is
unchanged. The VEIL layer translation is then selected in that unchanged
history/rest fiber. This file proves the two dependent translations form one
coin equivalence and preserve the complete algebraic view pointwise.
-/

namespace VeiledFlock.ProductionFlockVeil

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionLayerSpec
open VeiledFlock.ProductionVeilLayer

variable {K W Public Rest : Type*}
variable {rounds : ℕ}

abbrev FlockMasks := Masks (F := GhashField) (I := K) rounds

abbrev Coins (shape : BatchShape) :=
  FlockMasks (K := K) (rounds := rounds) × (LayerCoins shape × Rest)

abbrev AlgebraicView (shape : BatchShape) :=
  Rest × History (F := GhashField) (I := K) rounds × LayerView shape

noncomputable def view (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K) (W := W))
    (spec : History (F := GhashField) (I := K) rounds → Rest →
      Spec shape W Public)
    (witness : W)
    (coins : Coins (K := K) (Rest := Rest) (rounds := rounds) shape) :
    AlgebraicView (K := K) (Rest := Rest) (rounds := rounds) shape :=
  let history := run (secret coins.2.2) witness rounds coins.1
  (coins.2.2, history,
    ProductionLayerSpec.view (spec history coins.2.2) witness coins.2.1)

noncomputable def maskStage (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K) (W := W))
    (left right : W) : Equiv
      (Coins (K := K) (Rest := Rest) (rounds := rounds) shape)
      (Coins (K := K) (Rest := Rest) (rounds := rounds) shape) where
  toFun coins :=
    (witnessCoinEquiv (secret coins.2.2) left right rounds coins.1, coins.2)
  invFun coins :=
    ((witnessCoinEquiv (secret coins.2.2) left right rounds).symm coins.1,
      coins.2)
  left_inv coins := by simp
  right_inv coins := by simp

noncomputable def layerStage (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K) (W := W))
    (spec : History (F := GhashField) (I := K) rounds → Rest →
      Spec shape W Public)
    (historyWitness : W) (left right : W) : Equiv
      (Coins (K := K) (Rest := Rest) (rounds := rounds) shape)
      (Coins (K := K) (Rest := Rest) (rounds := rounds) shape) where
  toFun coins :=
    let history := run (secret coins.2.2) historyWitness rounds coins.1
    (coins.1,
      (ProductionLayerSpec.coinEquiv (spec history coins.2.2)
        left right coins.2.1, coins.2.2))
  invFun coins :=
    let history := run (secret coins.2.2) historyWitness rounds coins.1
    (coins.1,
      ((ProductionLayerSpec.coinEquiv (spec history coins.2.2)
        left right).symm coins.2.1, coins.2.2))
  left_inv coins := by simp
  right_inv coins := by simp

/-- Complete algebraic coin translation: causal FLOCK masks first, then every
VEIL coin in the preserved transcript fiber. -/
noncomputable def coinEquiv (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K) (W := W))
    (spec : History (F := GhashField) (I := K) rounds → Rest →
      Spec shape W Public)
    (left right : W) : Equiv
      (Coins (K := K) (Rest := Rest) (rounds := rounds) shape)
      (Coins (K := K) (Rest := Rest) (rounds := rounds) shape) :=
  (maskStage shape secret left right).trans
    (layerStage shape secret spec right left right)

theorem view_coinEquiv (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K) (W := W))
    (spec : History (F := GhashField) (I := K) rounds → Rest →
      Spec shape W Public)
    (statement : W → Public)
    (hspecStatement : ∀ history rest,
      (spec history rest).statement = statement)
    (left right : W) (hpublic : statement left = statement right)
    (coins : Coins (K := K) (Rest := Rest) (rounds := rounds) shape) :
    view shape secret spec left coins =
      view shape secret spec right
        (coinEquiv shape secret spec left right coins) := by
  rcases coins with ⟨masks, layerCoins, rest⟩
  let masks' := witnessCoinEquiv (secret rest) left right rounds masks
  have hhistory : run (secret rest) right rounds masks' =
      run (secret rest) left rounds masks :=
    run_witnessCoinEquiv (secret rest) left right rounds masks
  let history := run (secret rest) left rounds masks
  change
    (rest, history,
      ProductionLayerSpec.view (spec history rest) left layerCoins) =
    (rest, run (secret rest) right rounds masks',
      ProductionLayerSpec.view
        (spec (run (secret rest) right rounds masks') rest) right
        (ProductionLayerSpec.coinEquiv
          (spec (run (secret rest) right rounds masks') rest)
          left right layerCoins))
  rw [hhistory]
  dsimp [history]
  simp only [Prod.mk.injEq, true_and]
  apply ProductionLayerSpec.view_coinEquiv
  simpa only [hspecStatement] using hpublic

theorem witness_independent
    [Fintype K] [Fintype (K → GhashField)]
    [Fintype Rest] [Nonempty Rest]
    (shape : BatchShape)
    (secret : Rest → Secret (F := GhashField) (I := K) (W := W))
    (spec : History (F := GhashField) (I := K) rounds → Rest →
      Spec shape W Public)
    (statement : W → Public)
    (hspecStatement : ∀ history rest,
      (spec history rest).statement = statement)
    {left right : W} (hpublic : statement left = statement right) :
    (PMF.uniformOfFintype
      (Coins (K := K) (Rest := Rest) (rounds := rounds) shape)).map
        (view shape secret spec left) =
      (PMF.uniformOfFintype
        (Coins (K := K) (Rest := Rest) (rounds := rounds) shape)).map
          (view shape secret spec right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (coinEquiv shape secret spec left right)
  exact view_coinEquiv shape secret spec statement hspecStatement
    left right hpublic

end VeiledFlock.ProductionFlockVeil

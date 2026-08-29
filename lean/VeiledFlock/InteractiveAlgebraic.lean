import VeiledFlock.AdaptiveOneTimePad
import VeiledFlock.AlgebraicProtocol

/-!
# Interactive masking plus challenge-dependent algebraic hiding

The production transcript interleaves fresh one-time-padded FLOCK messages
with Fiat--Shamir challenges, then exposes VEIL multiplication rows, queried
Reed--Solomon coordinates, and a folded PCS opening.  Treating all challenges
as fixed before the mask tape is sampled is therefore unsound.

This module composes two triangular reparameterizations.  First it translates
the adaptive message pads while preserving the complete visible transcript.
Then, in the fiber selected by that unchanged transcript and the external
oracle state, it translates all remaining algebraic hiding coins.  The result
is exact witness independence through arbitrary deterministic continuation.
-/

namespace VeiledFlock.InteractiveAlgebraic

open Function
open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AlgebraicProtocol

variable {F K I Data Padding J W Public Rest FullView : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype K] [Fintype (K → F)]
variable [Fintype I] [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J]
variable [Fintype (I → F)] [Fintype (Padding → F)] [Fintype (J → F)]
variable [Fintype Rest] [Nonempty Rest]
variable {rounds : ℕ}

abbrev JointCoins (rounds : ℕ) :=
  Masks (F := F) (I := K) rounds ×
    (Coins (F := F) (I := I) (Padding := Padding) (J := J) × Rest)

noncomputable instance jointCoinsNonempty (rounds : ℕ) :
    Nonempty
      (JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds) := by
  let rest : Rest := Classical.choice inferInstance
  exact ⟨(fun _ _ => 0,
    ((fun _ => 0, ((0, 0, 0), (fun _ => 0), fun _ => 0)), rest))⟩

private def rotateCoins (rounds : ℕ) :
    JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ≃
      Coins (F := F) (I := I) (Padding := Padding) (J := J) ×
        (Masks (F := F) (I := K) rounds × Rest) where
  toFun coins := (coins.2.1, (coins.1, coins.2.2))
  invFun coins := (coins.2.1, (coins.1, coins.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- First-stage equivalence: translate only the causal FLOCK mask tape. -/
def adaptiveMaskEquiv
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (left right : W) (rounds : ℕ) :
    JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ≃
      JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds :=
  VeiledFlock.Probability.fiberwiseEquiv (Equiv.refl _)
    (fun rest => witnessCoinEquiv (secret rest.2) left right rounds)

/-- Second-stage equivalence: with the visible transcript fixed, translate
the VEIL padding, queried-code padding, and PCS fold/blinder coins. -/
noncomputable def algebraicFiberEquiv
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Injective (queries history rest))
    (hdisjoint : ∀ history rest d q,
      base history rest (Sum.inl d) ≠ queries history rest q)
    (flockSecret : History (F := F) (I := K) rounds → Rest → W → I → F)
    (veilSecret : History (F := F) (I := K) rounds → Rest → W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (left right : W) :
    JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ≃
      JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds :=
  VeiledFlock.Probability.fiberwiseEquiv (rotateCoins rounds)
    (fun maskRest =>
      let history := run (secret maskRest.2) right rounds maskRest.1
      AlgebraicProtocol.witnessCoinEquiv
        (alpha history maskRest.2) (c history maskRest.2)
        (halpha history maskRest.2) (hplus history maskRest.2)
        (base history maskRest.2) (hbase history maskRest.2)
        (queries history maskRest.2) (hqueries history maskRest.2)
        (hdisjoint history maskRest.2)
        (flockSecret history maskRest.2 left)
        (flockSecret history maskRest.2 right)
        (veilSecret history maskRest.2 left)
        (veilSecret history maskRest.2 right)
        (querySecret history maskRest.2 left)
        (querySecret history maskRest.2 right)
        (message history maskRest.2 left)
        (message history maskRest.2 right))

/-- The complete two-stage uniform-coin reparameterization. -/
noncomputable def jointWitnessCoinEquiv
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Injective (queries history rest))
    (hdisjoint : ∀ history rest d q,
      base history rest (Sum.inl d) ≠ queries history rest q)
    (flockSecret : History (F := F) (I := K) rounds → Rest → W → I → F)
    (veilSecret : History (F := F) (I := K) rounds → Rest → W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (left right : W) :
    JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds ≃
      JointCoins (F := F) (K := K) (I := I) (Padding := Padding) (J := J)
        (Rest := Rest) rounds :=
  (adaptiveMaskEquiv secret left right rounds).trans
    (algebraicFiberEquiv secret alpha c halpha hplus base hbase queries
      hqueries hdisjoint flockSecret veilSecret querySecret message left right)

/-- Evaluate the joint visible transcript and all four algebraic hiding
boundaries before an arbitrary witness-independent continuation. -/
noncomputable def realJointView
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (flockSecret : History (F := F) (I := K) rounds → Rest → W → I → F)
    (veilSecret : History (F := F) (I := K) rounds → Rest → W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (continueWith : Rest → History (F := F) (I := K) rounds →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    (witness : W)
    (coins : JointCoins (F := F) (K := K) (I := I) (Padding := Padding)
      (J := J) (Rest := Rest) rounds) : FullView :=
  let history := run (secret coins.2.2) witness rounds coins.1
  continueWith coins.2.2 history
    (realView (alpha history coins.2.2) (c history coins.2.2)
      (base history coins.2.2) (hbase history coins.2.2)
      (queries history coins.2.2) (functional history coins.2.2)
      (flockSecret history coins.2.2) (veilSecret history coins.2.2)
      (querySecret history coins.2.2) (message history coins.2.2)
      witness coins.2.1)

/-- Pointwise preservation of the whole interactive algebraic view. -/
theorem realJointView_transport
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (hc : ∀ history rest, c history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Injective (queries history rest))
    (hdisjoint : ∀ history rest d q,
      base history rest (Sum.inl d) ≠ queries history rest q)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (flockSecret : History (F := F) (I := K) rounds → Rest → W → I → F)
    (veilSecret : History (F := F) (I := K) rounds → Rest → W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest left right,
      statement left = statement right →
        functional history rest
          (message history rest right - message history rest left) = 0)
    (continueWith : Rest → History (F := F) (I := K) rounds →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    {left right : W} (hpublic : statement left = statement right)
    (coins : JointCoins (F := F) (K := K) (I := I) (Padding := Padding)
      (J := J) (Rest := Rest) rounds) :
    realJointView secret alpha c base hbase queries functional flockSecret
        veilSecret querySecret message continueWith left coins =
      realJointView secret alpha c base hbase queries functional flockSecret
        veilSecret querySecret message continueWith right
        (jointWitnessCoinEquiv secret alpha c halpha hplus base hbase queries
          hqueries hdisjoint flockSecret veilSecret querySecret message
          left right coins) := by
  rcases coins with ⟨masks, algebraic, rest⟩
  let masks' := witnessCoinEquiv (secret rest) left right rounds masks
  have hhistory : run (secret rest) right rounds masks' =
      run (secret rest) left rounds masks :=
    run_witnessCoinEquiv (secret rest) left right rounds masks
  simp only [jointWitnessCoinEquiv, Equiv.trans_apply, adaptiveMaskEquiv,
    algebraicFiberEquiv, VeiledFlock.Probability.fiberwiseEquiv,
    rotateCoins, Equiv.refl_apply]
  change realJointView secret alpha c base hbase queries functional flockSecret
      veilSecret querySecret message continueWith left (masks, algebraic, rest) =
    realJointView secret alpha c base hbase queries functional flockSecret
      veilSecret querySecret message continueWith right
        (masks',
          AlgebraicProtocol.witnessCoinEquiv
            (alpha (run (secret rest) right rounds masks') rest)
            (c (run (secret rest) right rounds masks') rest)
            (halpha (run (secret rest) right rounds masks') rest)
            (hplus (run (secret rest) right rounds masks') rest)
            (base (run (secret rest) right rounds masks') rest)
            (hbase (run (secret rest) right rounds masks') rest)
            (queries (run (secret rest) right rounds masks') rest)
            (hqueries (run (secret rest) right rounds masks') rest)
            (hdisjoint (run (secret rest) right rounds masks') rest)
            (flockSecret (run (secret rest) right rounds masks') rest left)
            (flockSecret (run (secret rest) right rounds masks') rest right)
            (veilSecret (run (secret rest) right rounds masks') rest left)
            (veilSecret (run (secret rest) right rounds masks') rest right)
            (querySecret (run (secret rest) right rounds masks') rest left)
            (querySecret (run (secret rest) right rounds masks') rest right)
            (message (run (secret rest) right rounds masks') rest left)
            (message (run (secret rest) right rounds masks') rest right)
            algebraic,
          rest)
  simp only [realJointView]
  simp only [hhistory]
  apply congrArg (continueWith rest (run (secret rest) left rounds masks))
  exact AlgebraicProtocol.realView_witnessCoinEquiv
    (alpha (run (secret rest) left rounds masks) rest)
    (c (run (secret rest) left rounds masks) rest)
    (halpha (run (secret rest) left rounds masks) rest)
    (hplus (run (secret rest) left rounds masks) rest)
    (hc (run (secret rest) left rounds masks) rest)
    (base (run (secret rest) left rounds masks) rest)
    (hbase (run (secret rest) left rounds masks) rest)
    (queries (run (secret rest) left rounds masks) rest)
    (hqueries (run (secret rest) left rounds masks) rest)
    (hdisjoint (run (secret rest) left rounds masks) rest)
    (functional (run (secret rest) left rounds masks) rest)
    (flockSecret (run (secret rest) left rounds masks) rest)
    (veilSecret (run (secret rest) left rounds masks) rest)
    (querySecret (run (secret rest) left rounds masks) rest)
    (message (run (secret rest) left rounds masks) rest)
    left right
    (hpublicKernel (run (secret rest) left rounds masks) rest left right hpublic)
    algebraic

/-- Exact distributional zero knowledge for the complete interleaved
algebraic protocol, before random-oracle bad events are charged. -/
theorem interactiveAlgebraic_zeroKnowledge
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (hc : ∀ history rest, c history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Injective (queries history rest))
    (hdisjoint : ∀ history rest d q,
      base history rest (Sum.inl d) ≠ queries history rest q)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (flockSecret : History (F := F) (I := K) rounds → Rest → W → I → F)
    (veilSecret : History (F := F) (I := K) rounds → Rest → W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest left right,
      statement left = statement right →
        functional history rest
          (message history rest right - message history rest left) = 0)
    (continueWith : Rest → History (F := F) (I := K) rounds →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    {left right : W} (hpublic : statement left = statement right) :
    (PMF.uniformOfFintype
      (JointCoins (F := F) (K := K) (I := I) (Padding := Padding)
        (J := J) (Rest := Rest) rounds)).map
        (realJointView secret alpha c base hbase queries functional flockSecret
          veilSecret querySecret message continueWith left) =
      (PMF.uniformOfFintype
        (JointCoins (F := F) (K := K) (I := I) (Padding := Padding)
          (J := J) (Rest := Rest) rounds)).map
          (realJointView secret alpha c base hbase queries functional flockSecret
            veilSecret querySecret message continueWith right) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (jointWitnessCoinEquiv secret alpha c halpha hplus base hbase queries
      hqueries hdisjoint flockSecret veilSecret querySecret message left right)
  exact realJointView_transport secret alpha c halpha hplus hc base hbase
    queries hqueries hdisjoint functional flockSecret veilSecret querySecret
    message statement hpublicKernel continueWith hpublic

/-- Explicit public-input simulator corollary.  A public-fiber representative
need not satisfy the original nonlinear relation: it is merely the assignment
used by the simulator to evaluate the witness-independent linear continuation.
All values hidden behind the proved masking boundaries are reparameterized
away before they reach `continueWith`. -/
theorem interactiveAlgebraic_simulatorExact
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (hc : ∀ history rest, c history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Injective (queries history rest))
    (hdisjoint : ∀ history rest d q,
      base history rest (Sum.inl d) ≠ queries history rest q)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (flockSecret : History (F := F) (I := K) rounds → Rest → W → I → F)
    (veilSecret : History (F := F) (I := K) rounds → Rest → W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest left right,
      statement left = statement right →
        functional history rest
          (message history rest right - message history rest left) = 0)
    (representative : Public → W)
    (hrepresentative : ∀ publicInput,
      statement (representative publicInput) = publicInput)
    (continueWith : Rest → History (F := F) (I := K) rounds →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    (witness : W) :
    (PMF.uniformOfFintype
      (JointCoins (F := F) (K := K) (I := I) (Padding := Padding)
        (J := J) (Rest := Rest) rounds)).map
        (realJointView secret alpha c base hbase queries functional flockSecret
          veilSecret querySecret message continueWith witness) =
      (PMF.uniformOfFintype
        (JointCoins (F := F) (K := K) (I := I) (Padding := Padding)
          (J := J) (Rest := Rest) rounds)).map
          (realJointView secret alpha c base hbase queries functional flockSecret
            veilSecret querySecret message continueWith
            (representative (statement witness))) := by
  apply interactiveAlgebraic_zeroKnowledge secret alpha c halpha hplus hc
    base hbase queries hqueries hdisjoint functional flockSecret veilSecret
    querySecret message statement hpublicKernel continueWith
  exact (hrepresentative (statement witness)).symm

end VeiledFlock.InteractiveAlgebraic

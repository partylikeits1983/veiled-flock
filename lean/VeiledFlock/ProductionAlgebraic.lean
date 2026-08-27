import VeiledFlock.InteractiveAlgebraic

/-!
# Production algebraic tape (one FLOCK mask channel)

`InteractiveAlgebraic` is deliberately generic enough to compose two
independent additive mask channels.  The Rust VEIL--FLOCK path has only one:
the 754--760 scalar tape consumed causally by `MaskingChallenger`,
`mask_proofs`, and `mask_ring_claims`.

This module gives the faithful specialization.  The causal tape is the sole
FLOCK mask source; the older fixed FLOCK coordinate in `AlgebraicProtocol` is
instantiated at `Fin 0`, whose function space is a singleton.  The remaining
coins are precisely VEIL multiplication padding, queried Reed--Solomon
padding, and the PCS blinder.
-/

namespace VeiledFlock.ProductionAlgebraic

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.AlgebraicProtocol
open VeiledFlock.InteractiveAlgebraic

variable {F K Data Padding J W Public Rest FullView : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype K] [Fintype (K → F)]
variable [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J]
variable [Fintype (Padding → F)] [Fintype (J → F)]
variable [Fintype Rest] [Nonempty Rest]
variable {rounds : ℕ}

abbrev ProductionCoins (rounds : ℕ) :=
  JointCoins (F := F) (K := K) (I := Fin 0) (Padding := Padding)
    (J := J) (Rest := Rest) rounds

abbrev ProductionAlgebraicView :=
  View (F := F) (I := Fin 0) (Padding := Padding) (J := J)

def emptyFlockSecret :
    History (F := F) (I := K) rounds → Rest → W → Fin 0 → F :=
  fun _ _ _ impossible => Fin.elim0 impossible

/-- Exact witness independence for the production algebraic randomness
inventory.  There is one causal transcript-mask tape, followed by VEIL
padding, queried-code padding, and the PCS blinder. -/
theorem productionAlgebraic_zeroKnowledge
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (hc : ∀ history rest, c history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Function.Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Function.Injective (queries history rest))
    (hdisjoint : ∀ history rest d q,
      base history rest (Sum.inl d) ≠ queries history rest q)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (veilSecret : History (F := F) (I := K) rounds → Rest →
      W → F × F × F)
    (querySecret : History (F := F) (I := K) rounds → Rest →
      W → Padding → F)
    (message : History (F := F) (I := K) rounds → Rest → W → J → F)
    (statement : W → Public)
    (hpublicKernel : ∀ history rest left right,
      statement left = statement right →
        functional history rest
          (message history rest right - message history rest left) = 0)
    (continueWith : Rest → History (F := F) (I := K) rounds →
      ProductionAlgebraicView (F := F) (Padding := Padding) (J := J) →
        FullView)
    {left right : W} (hpublic : statement left = statement right) :
    (PMF.uniformOfFintype
      (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
        (Rest := Rest) rounds)).map
        (realJointView secret alpha c base hbase queries functional
          emptyFlockSecret veilSecret querySecret message continueWith left) =
      (PMF.uniformOfFintype
        (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
          (Rest := Rest) rounds)).map
          (realJointView secret alpha c base hbase queries functional
            emptyFlockSecret veilSecret querySecret message continueWith
            right) := by
  exact interactiveAlgebraic_zeroKnowledge secret alpha c halpha hplus hc
    base hbase queries hqueries hdisjoint functional emptyFlockSecret
    veilSecret querySecret message statement hpublicKernel continueWith hpublic

/-- Public-input simulator corollary for the same exact production tape. -/
theorem productionAlgebraic_simulatorExact
    (secret : Rest → Secret (F := F) (I := K) (W := W))
    (alpha c : History (F := F) (I := K) rounds → Rest → F)
    (halpha : ∀ history rest, alpha history rest ≠ 0)
    (hplus : ∀ history rest, 1 + alpha history rest ≠ 0)
    (hc : ∀ history rest, c history rest ≠ 0)
    (base : History (F := F) (I := K) rounds → Rest →
      Data ⊕ Padding → F)
    (hbase : ∀ history rest, Function.Injective (base history rest))
    (queries : History (F := F) (I := K) rounds → Rest → Padding → F)
    (hqueries : ∀ history rest, Function.Injective (queries history rest))
    (hdisjoint : ∀ history rest d q,
      base history rest (Sum.inl d) ≠ queries history rest q)
    (functional : History (F := F) (I := K) rounds → Rest →
      (J → F) →ₗ[F] F)
    (veilSecret : History (F := F) (I := K) rounds → Rest →
      W → F × F × F)
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
      ProductionAlgebraicView (F := F) (Padding := Padding) (J := J) →
        FullView)
    (witness : W) :
    (PMF.uniformOfFintype
      (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
        (Rest := Rest) rounds)).map
        (realJointView secret alpha c base hbase queries functional
          emptyFlockSecret veilSecret querySecret message continueWith witness) =
      (PMF.uniformOfFintype
        (ProductionCoins (F := F) (K := K) (Padding := Padding) (J := J)
          (Rest := Rest) rounds)).map
          (realJointView secret alpha c base hbase queries functional
            emptyFlockSecret veilSecret querySecret message continueWith
            (representative (statement witness))) := by
  exact interactiveAlgebraic_simulatorExact secret alpha c halpha hplus hc
    base hbase queries hqueries hdisjoint functional emptyFlockSecret
    veilSecret querySecret message statement hpublicKernel representative
    hrepresentative continueWith witness

end VeiledFlock.ProductionAlgebraic

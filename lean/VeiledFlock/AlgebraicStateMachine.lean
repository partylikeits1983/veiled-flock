import VeiledFlock.AlgebraicProtocol
import VeiledFlock.Probability

/-!
# Algebraic state-machine lifting

The algebraic simulator theorem remains valid through any deterministic
witness-independent continuation: serialization, hashing, Merkle building,
and verifier post-processing may consume the simulated algebraic view and
the same public auxiliary state.  This module records the explicit full-coin
bijection and pointwise transport needed by the end-to-end game.
-/

namespace VeiledFlock.AlgebraicStateMachine

open VeiledFlock.AlgebraicProtocol

variable {F I Data Padding J W Public Aux FullView : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype I] [Fintype Data] [Fintype Padding] [Nonempty Padding]
variable [DecidableEq Data] [DecidableEq Padding]
variable [Fintype J]
variable [Fintype (I → F)] [Fintype (Padding → F)] [Fintype (J → F)]
variable [Fintype Aux] [Nonempty Aux]

abbrev FullCoins :=
  Coins (F := F) (I := I) (Padding := Padding) (J := J) × Aux

noncomputable def realMachine
    (alpha c : F)
    (base : Data ⊕ Padding → F) (hbase : Function.Injective base)
    (queries : Padding → F)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (continueWith : Aux →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    (witness : W) (coins : FullCoins
      (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux)) : FullView :=
  continueWith coins.2
    (realView alpha c base hbase queries functional flockSecret veilSecret
      querySecret message witness coins.1)

noncomputable def simulatedMachine
    (c : F) (functional : (J → F) →ₗ[F] F)
    (publicMessageValue : F)
    (continueWith : Aux →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    (coins : FullCoins
      (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux)) : FullView :=
  continueWith coins.2
    (simulatedView c functional publicMessageValue coins.1)

noncomputable def fullCoinEquiv
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Function.Injective base)
    (queries : Padding → F) (hqueries : Function.Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (flockSecret : I → F) (veilSecret : F × F × F)
    (querySecret : Padding → F) (message : J → F) :
    FullCoins (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) ≃
      FullCoins (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux) :=
  Equiv.prodCongr
    (simulatorCoinEquiv alpha c halpha hplus hc base hbase queries hqueries
      hdisjoint flockSecret veilSecret querySecret message)
    (Equiv.refl Aux)

/-- Pointwise equality of the honest and simulated full state machines after
the explicit algebraic coin reparameterization. -/
theorem realMachine_transport
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Function.Injective base)
    (queries : Padding → F) (hqueries : Function.Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (continueWith : Aux →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    (witness : W)
    (coins : FullCoins
      (F := F) (I := I) (Padding := Padding) (J := J) (Aux := Aux)) :
    realMachine alpha c base hbase queries functional flockSecret veilSecret
        querySecret message continueWith witness coins =
      simulatedMachine c functional (functional (message witness)) continueWith
        (fullCoinEquiv alpha c halpha hplus hc base hbase queries hqueries
          hdisjoint (flockSecret witness) (veilSecret witness)
          (querySecret witness) (message witness) coins) := by
  apply congrArg (continueWith coins.2)
  exact realView_simulator_transport alpha c halpha hplus hc base hbase queries
    hqueries hdisjoint functional flockSecret veilSecret querySecret message
    witness coins.1

/-- Exact full-view distributional simulation through an arbitrary public
continuation. -/
theorem fullSimulator_exact
    (alpha c : F) (halpha : alpha ≠ 0) (hplus : 1 + alpha ≠ 0)
    (hc : c ≠ 0)
    (base : Data ⊕ Padding → F) (hbase : Function.Injective base)
    (queries : Padding → F) (hqueries : Function.Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (functional : (J → F) →ₗ[F] F)
    (flockSecret : W → I → F)
    (veilSecret : W → F × F × F)
    (querySecret : W → Padding → F)
    (message : W → J → F)
    (continueWith : Aux →
      View (F := F) (I := I) (Padding := Padding) (J := J) → FullView)
    (witness : W) :
    (PMF.uniformOfFintype
      (FullCoins (F := F) (I := I) (Padding := Padding) (J := J)
        (Aux := Aux))).map
        (realMachine alpha c base hbase queries functional flockSecret veilSecret
          querySecret message continueWith witness) =
      (PMF.uniformOfFintype
        (FullCoins (F := F) (I := I) (Padding := Padding) (J := J)
          (Aux := Aux))).map
          (simulatedMachine c functional (functional (message witness))
            continueWith) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (fullCoinEquiv alpha c halpha hplus hc base hbase queries hqueries
      hdisjoint (flockSecret witness) (veilSecret witness)
      (querySecret witness) (message witness))
  exact realMachine_transport alpha c halpha hplus hc base hbase queries
    hqueries hdisjoint functional flockSecret veilSecret querySecret message
    continueWith witness

end VeiledFlock.AlgebraicStateMachine

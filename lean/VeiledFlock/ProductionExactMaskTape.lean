import VeiledFlock.ConcreteTranscript
import VeiledFlock.Probability
import VeiledFlock.ProductionConcreteAlgebraic
import VeiledFlock.ProductionMaskLayout

/-!
# Exact production flat mask tape

The Rust prover samples one flat vector of `expectedMasks shape` field
elements.  The algebraic theorem represents the same randomness as
`expectedMasks shape` rounds of one-coordinate adaptive pads.  This file
gives the explicit equivalence between those coin spaces and records that the
literal Rust cursor consumes precisely the whole vector.
-/

namespace VeiledFlock.ProductionExactMaskTape

open VeiledFlock.AdaptiveOneTimePad
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionCorrelatedVeilLayer
open VeiledFlock.ProductionOuterCodeDomains

variable {Rest : Type*}

abbrev FlatMasks (shape : BatchShape) :=
  Fin (expectedMasks shape) → GhashField

/-- Coin layout closest to the Rust prover: message padding, PCS blinder,
one flat transcript-mask vector, the VEIL hiding coins, and auxiliary tape. -/
abbrev RustCoins (shape : BatchShape) (Rest : Type*) :=
  (ActivePadding shape ×
      (BaseWord shape × FlatMasks shape)) ×
    (LayerCoins shape × Rest)

/-- The corresponding coin type used by the complete production algebraic
theorem, specialized to scalar messages and the registered mask count. -/
abbrev AlgebraicCoins (shape : BatchShape) (Rest : Type*) :=
  VeiledFlock.ProductionPaddedAlgebraicE2E.Coins
    (K := Unit) (I := BaseScalarIndex shape)
    (Pad := ActivePadding shape) (Rest := Rest)
    (rounds := expectedMasks shape) shape

/-- Exact restructuring of the implementation's flat mask tape into the
adaptive one-coordinate tape used by the algebraic theorem. -/
def coinEquiv (shape : BatchShape) :
    RustCoins shape Rest ≃ AlgebraicCoins shape Rest :=
  Equiv.prodCongr
    (Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodCongr (Equiv.refl _)
        (VeiledFlock.ConcreteTranscript.scalarMaskEquiv
          (F := GhashField) (expectedMasks shape))))
    (Equiv.refl _)

@[simp]
theorem coinEquiv_flatMask (shape : BatchShape)
    (coins : RustCoins shape Rest) (site : Fin (expectedMasks shape)) :
    ((coinEquiv shape coins).1.2.2 site ()) = coins.1.2.2 site := rfl

/-- Reparameterizing the flat Rust tape as the algebraic tape preserves every
induced view distribution exactly. -/
theorem uniform_map_coinEquiv {View : Type*}
    [Fintype Rest] [Nonempty Rest]
    (shape : BatchShape) (view : AlgebraicCoins shape Rest → View) :
    (PMF.uniformOfFintype (RustCoins shape Rest)).map
        (fun coins ↦ view (coinEquiv shape coins)) =
      (PMF.uniformOfFintype (AlgebraicCoins shape Rest)).map view := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv (coinEquiv shape)
  intro coins
  rfl

/-- The final Rust ring-mask coordinate is literally the final sampled mask;
there is no unmodeled suffix and no reused element. -/
theorem cursor_exhausts_flat_tape (shape : BatchShape) :
    (VeiledFlock.ProductionMaskLayout.ringIndex shape
      ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨127, by decide⟩).val + 1 =
        Fintype.card (Fin (expectedMasks shape)) := by
  simpa using
    VeiledFlock.ProductionMaskLayout.finalRingIndex_is_last shape

end VeiledFlock.ProductionExactMaskTape

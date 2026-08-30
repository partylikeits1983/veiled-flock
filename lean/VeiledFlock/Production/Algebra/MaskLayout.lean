import VeiledFlock.Concrete.ConcreteParameters
import VeiledFlock.Algebra.RingScale

/-!
# Exact production mask cursor

`MaskingChallenger`, `mask_proofs`, `mask_ring_claims`, and
`ExpressionCursor` consume one flat mask vector in the following order:

1. 64 zerocheck `round1_ab` values;
2. 64 zerocheck `round1_c` values;
3. two values for each remaining zerocheck round;
4. the terminal `a` and `b` values;
5. two values for each lincheck round;
6. 64 `z_partial` values;
7. for each of two ring claims, 128 witness values followed by 128 blinder
   values.

This file gives every segment its literal Rust offset in the 754--760 element
vector and proves that the last cursor position is exactly `expectedMasks` for
all registered shapes.
-/

namespace VeiledFlock.ProductionMaskLayout

open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.RingScale

def ell : ℕ := 2 ^ kSkip
def zerocheckRounds (shape : BatchShape) : ℕ := m shape - kSkip
def lincheckRounds : ℕ := kLog - kSkip
def zPartialLength : ℕ := 2 ^ kSkip

def round1AbOffset : ℕ := 0
def round1COffset : ℕ := ell
def zerocheckRoundOffset : ℕ := 2 * ell
def finalOffset (shape : BatchShape) : ℕ :=
  zerocheckRoundOffset + 2 * zerocheckRounds shape
def lincheckRoundOffset (shape : BatchShape) : ℕ :=
  finalOffset shape + 2
def zPartialOffset (shape : BatchShape) : ℕ :=
  lincheckRoundOffset shape + 2 * lincheckRounds
def ringOffset (shape : BatchShape) : ℕ :=
  zPartialOffset shape + zPartialLength

theorem ringOffset_eq_piopCount (shape : BatchShape) :
    ringOffset shape = piopCount shape := by
  cases shape <;> decide

theorem ringCursorEnd_eq_expectedMasks (shape : BatchShape) :
    ringOffset shape + 2 * ringClaimCount * ringWidth =
      expectedMasks shape := by
  cases shape <;> decide

abbrev MaskIndex (shape : BatchShape) := Fin (expectedMasks shape)
abbrev PiopIndex (shape : BatchShape) := Fin (piopCount shape)
abbrev PairIndex := Fin 2
abbrev ClaimIndex := Fin ringClaimCount
abbrev ChannelIndex := Fin 2

def round1AbIndex (shape : BatchShape) (index : Fin ell) :
    MaskIndex shape :=
  ⟨round1AbOffset + index.val, by
    cases shape <;> simp [round1AbOffset, ell, kSkip, expectedMasks] at * <;>
      omega⟩

def round1CIndex (shape : BatchShape) (index : Fin ell) :
    MaskIndex shape :=
  ⟨round1COffset + index.val, by
    cases shape <;> simp [round1COffset, ell, kSkip, expectedMasks] at * <;>
      omega⟩

def zerocheckRoundIndex (shape : BatchShape)
    (round : Fin (zerocheckRounds shape)) (entry : PairIndex) :
    MaskIndex shape :=
  ⟨zerocheckRoundOffset + 2 * round.val + entry.val, by
    cases shape <;>
      simp [zerocheckRoundOffset, zerocheckRounds, ell, kSkip, m,
        expectedMasks] at * <;> omega⟩

def finalIndex (shape : BatchShape) (entry : PairIndex) : MaskIndex shape :=
  ⟨finalOffset shape + entry.val, by
    cases shape <;>
      simp [finalOffset, zerocheckRoundOffset, zerocheckRounds, ell, kSkip,
        m, expectedMasks] at * <;> omega⟩

def lincheckRoundIndex (shape : BatchShape)
    (round : Fin lincheckRounds) (entry : PairIndex) : MaskIndex shape :=
  ⟨lincheckRoundOffset shape + 2 * round.val + entry.val, by
    cases shape <;>
      simp [lincheckRoundOffset, finalOffset, zerocheckRoundOffset,
        zerocheckRounds, lincheckRounds, ell, kSkip, kLog, m,
        expectedMasks] at * <;> omega⟩

def zPartialIndex (shape : BatchShape) (index : Fin zPartialLength) :
    MaskIndex shape :=
  ⟨zPartialOffset shape + index.val, by
    cases shape <;>
      simp [zPartialOffset, lincheckRoundOffset, finalOffset,
        zerocheckRoundOffset, zerocheckRounds, lincheckRounds,
        zPartialLength, ell, kSkip, kLog, m, expectedMasks] at * <;> omega⟩

/-- Exact flattening of `(claim, witness-or-blind, bit-coordinate)` used by
the nested loops in `mask_ring_claims` and `shifted_verifier_circuit`. -/
def ringIndex (shape : BatchShape) (claim : ClaimIndex)
    (channel : ChannelIndex) (coordinate : SliceIndex) : MaskIndex shape :=
  ⟨ringOffset shape +
      (2 * claim.val + channel.val) * ringWidth + coordinate.val, by
    cases shape <;>
      simp [ringOffset, zPartialOffset, lincheckRoundOffset, finalOffset,
        zerocheckRoundOffset, zerocheckRounds, lincheckRounds,
        zPartialLength, ell, kSkip, kLog, m, ringClaimCount, ringWidth,
        expectedMasks] at * <;> omega⟩

/-- The PIOP masks form the literal prefix consumed before the two ring
claims. -/
def piopIndex (shape : BatchShape) (index : PiopIndex shape) :
    MaskIndex shape :=
  ⟨index.val, by
    cases shape <;>
      simp [piopCount, m, kSkip, kLog, expectedMasks] at * <;> omega⟩

noncomputable def piopRestriction (shape : BatchShape) :
    (MaskIndex shape → GhashField) →ₗ[GhashField]
      (PiopIndex shape → GhashField) where
  toFun values index := values (piopIndex shape index)
  map_add' left right := rfl
  map_smul' scalar values := rfl

@[simp] theorem piopRestriction_apply (shape : BatchShape)
    (values : MaskIndex shape → GhashField) (index : PiopIndex shape) :
    piopRestriction shape values index = values (piopIndex shape index) := rfl

@[simp] theorem round1AbIndex_val (shape : BatchShape) (index : Fin ell) :
    (round1AbIndex shape index).val = index.val := by
  simp [round1AbIndex, round1AbOffset]

@[simp] theorem round1CIndex_val (shape : BatchShape) (index : Fin ell) :
    (round1CIndex shape index).val = ell + index.val := rfl

@[simp] theorem zerocheckRoundIndex_val (shape : BatchShape)
    (round : Fin (zerocheckRounds shape)) (entry : PairIndex) :
    (zerocheckRoundIndex shape round entry).val =
      2 * ell + 2 * round.val + entry.val := rfl

@[simp] theorem finalIndex_val (shape : BatchShape) (entry : PairIndex) :
    (finalIndex shape entry).val = finalOffset shape + entry.val := rfl

@[simp] theorem lincheckRoundIndex_val (shape : BatchShape)
    (round : Fin lincheckRounds) (entry : PairIndex) :
    (lincheckRoundIndex shape round entry).val =
      lincheckRoundOffset shape + 2 * round.val + entry.val := rfl

@[simp] theorem zPartialIndex_val (shape : BatchShape)
    (index : Fin zPartialLength) :
    (zPartialIndex shape index).val = zPartialOffset shape + index.val := rfl

@[simp] theorem ringIndex_val (shape : BatchShape) (claim : ClaimIndex)
    (channel : ChannelIndex) (coordinate : SliceIndex) :
    (ringIndex shape claim channel coordinate).val =
      ringOffset shape +
        (2 * claim.val + channel.val) * ringWidth + coordinate.val := rfl

theorem ringIndex_injective (shape : BatchShape) :
    Function.Injective (fun input : ClaimIndex × ChannelIndex × SliceIndex =>
      ringIndex shape input.1 input.2.1 input.2.2) := by
  rintro ⟨leftClaim, ⟨leftChannel, leftCoordinate⟩⟩
    ⟨rightClaim, ⟨rightChannel, rightCoordinate⟩⟩ heq
  have hval := congrArg Fin.val heq
  simp only [ringIndex_val] at hval
  have hlc : leftClaim.val < 2 := by
    simpa [ringClaimCount] using leftClaim.isLt
  have hrc : rightClaim.val < 2 := by
    simpa [ringClaimCount] using rightClaim.isLt
  have hll := leftChannel.isLt
  have hrl := rightChannel.isLt
  have hlx := leftCoordinate.isLt
  have hrx := rightCoordinate.isLt
  simp [ringWidth] at hval
  have hclaim : leftClaim.val = rightClaim.val := by omega
  have hchannel : leftChannel.val = rightChannel.val := by omega
  have hcoordinate : leftCoordinate.val = rightCoordinate.val := by omega
  exact congrArg₂ Prod.mk (Fin.ext hclaim)
    (congrArg₂ Prod.mk (Fin.ext hchannel) (Fin.ext hcoordinate))

/-- The final ring coordinate is the final element of the registered vector;
there is neither an unused suffix nor an implicit extra mask. -/
theorem finalRingIndex_is_last (shape : BatchShape) :
    (ringIndex shape ⟨1, by decide⟩ ⟨1, by decide⟩
      ⟨127, by decide⟩).val + 1 = expectedMasks shape := by
  cases shape <;> decide

end VeiledFlock.ProductionMaskLayout

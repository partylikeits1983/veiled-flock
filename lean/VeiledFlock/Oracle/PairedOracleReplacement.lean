import VeiledFlock.Oracle.OracleProgramming

/-!
# Pairwise fresh-input oracle replacement

`Equiv.extendSubtype` may permute arbitrary complement points.  For the
salted-Merkle hybrid we need the stronger fact that only corresponding real
and simulated hidden inputs move, while every point outside those two
families is fixed.  Fixed location framing gives the required cross-family
property: equality between a real input at `i` and a simulated input at `j`
implies `i = j`.
-/

namespace VeiledFlock.PairedOracleReplacement

open Function

variable {Index Point Outcome : Type*}
variable [Finite Index] [DecidableEq Point]

/-- Swap each corresponding pair and fix the complement.  If a pair already
coincides, that point remains fixed. -/
noncomputable def pairedSwap (left right : Index → Point) (point : Point) :
    Point := by
  classical
  exact if hleft : ∃ index, left index = point then
    right (Classical.choose hleft)
  else if hright : ∃ index, right index = point then
    left (Classical.choose hright)
  else point

omit [Finite Index] [DecidableEq Point] in
theorem pairedSwap_left (left right : Index → Point)
    (hleft : Injective left) (index : Index) :
    pairedSwap left right (left index) = right index := by
  classical
  rw [pairedSwap]
  split
  next hexists =>
    congr 1
    apply hleft
    exact (Classical.choose_spec hexists).trans rfl
  next hnone => exact False.elim (hnone ⟨index, rfl⟩)

omit [Finite Index] [DecidableEq Point] in
theorem pairedSwap_right (left right : Index → Point)
    (hright : Injective right)
    (hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex)
    (index : Index) :
    pairedSwap left right (right index) = left index := by
  classical
  rw [pairedSwap]
  split
  next hexists =>
    have hchosen : left (Classical.choose hexists) = right index :=
      Classical.choose_spec hexists
    have hindex : Classical.choose hexists = index :=
      hcross (Classical.choose hexists) index hchosen
    rw [hindex]
    exact hchosen.symm.trans (congrArg left hindex)
  next hnotLeft =>
    split
    next hexists =>
      congr 1
      apply hright
      exact (Classical.choose_spec hexists).trans rfl
    next hnone => exact False.elim (hnone ⟨index, rfl⟩)

omit [Finite Index] [DecidableEq Point] in
theorem pairedSwap_off (left right : Index → Point) (point : Point)
    (hoffLeft : ∀ index, point ≠ left index)
    (hoffRight : ∀ index, point ≠ right index) :
    pairedSwap left right point = point := by
  classical
  simp only [pairedSwap]
  split
  next hexists =>
    obtain ⟨index, hindex⟩ := hexists
    exact False.elim (hoffLeft index hindex.symm)
  next _ =>
    split
    next hexists =>
      obtain ⟨index, hindex⟩ := hexists
      exact False.elim (hoffRight index hindex.symm)
    next _ => rfl

omit [Finite Index] [DecidableEq Point] in
theorem pairedSwap_involutive (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    (hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex) :
    Function.Involutive (pairedSwap left right) := by
  classical
  intro point
  by_cases hleftRange : ∃ index, left index = point
  · obtain ⟨index, rfl⟩ := hleftRange
    rw [pairedSwap_left left right hleft,
      pairedSwap_right left right hright hcross]
  · by_cases hrightRange : ∃ index, right index = point
    · obtain ⟨index, rfl⟩ := hrightRange
      rw [pairedSwap_right left right hright hcross,
        pairedSwap_left left right hleft]
    · have hoffLeft : ∀ index, point ≠ left index := by
        intro index heq
        exact hleftRange ⟨index, heq.symm⟩
      have hoffRight : ∀ index, point ≠ right index := by
        intro index heq
        exact hrightRange ⟨index, heq.symm⟩
      rw [pairedSwap_off left right point hoffLeft hoffRight,
        pairedSwap_off left right point hoffLeft hoffRight]

/-- The complement-fixing point permutation. -/
noncomputable def pairedPointEquiv (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    (hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex) :
    Point ≃ Point where
  toFun := pairedSwap left right
  invFun := pairedSwap left right
  left_inv := pairedSwap_involutive left right hleft hright hcross
  right_inv := pairedSwap_involutive left right hleft hright hcross

/-- Pull a random-oracle table through the pairwise permutation. -/
noncomputable def renameOracle (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    (hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex) :
    (Point → Outcome) ≃ (Point → Outcome) where
  toFun oracle point := oracle (pairedSwap left right point)
  invFun oracle point := oracle (pairedSwap left right point)
  left_inv oracle := by
    funext point
    change oracle (pairedSwap left right (pairedSwap left right point)) =
      oracle point
    rw [pairedSwap_involutive left right hleft hright hcross point]
  right_inv oracle := by
    funext point
    change oracle (pairedSwap left right (pairedSwap left right point)) =
      oracle point
    rw [pairedSwap_involutive left right hleft hright hcross point]

omit [Finite Index] [DecidableEq Point] in
@[simp]
theorem renameOracle_at_right (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    (hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex)
    (oracle : Point → Outcome) (index : Index) :
    renameOracle left right hleft hright hcross oracle (right index) =
      oracle (left index) := by
  exact congrArg oracle (pairedSwap_right left right hright hcross index)

omit [Finite Index] [DecidableEq Point] in
@[simp]
theorem renameOracle_at_left (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    (hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex)
    (oracle : Point → Outcome) (index : Index) :
    renameOracle left right hleft hright hcross oracle (left index) =
      oracle (right index) := by
  exact congrArg oracle (pairedSwap_left left right hleft index)

omit [Finite Index] [DecidableEq Point] in
/-- Every point outside both moved families retains its exact oracle answer. -/
theorem renameOracle_off (left right : Index → Point)
    (hleft : Injective left) (hright : Injective right)
    (hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex)
    (oracle : Point → Outcome) (point : Point)
    (hoffLeft : ∀ index, point ≠ left index)
    (hoffRight : ∀ index, point ≠ right index) :
    renameOracle left right hleft hright hcross oracle point =
      oracle point := by
  exact congrArg oracle (pairedSwap_off left right point hoffLeft hoffRight)

section Fiberwise

variable {Rest : Type*}
variable [Fintype Point]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]
variable [Fintype Outcome] [DecidableEq Outcome]

private def swapRestOracle :
    (Rest × (Point → Outcome)) ≃ ((Point → Outcome) × Rest) where
  toFun input := (input.2, input.1)
  invFun input := (input.2, input.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pairwise oracle replacement selected independently in every fixed random
tape fiber. -/
noncomputable def fiberwiseRenameOracle
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest))
    (hcross : ∀ rest leftIndex rightIndex,
      left rest leftIndex = right rest rightIndex →
        leftIndex = rightIndex) :
    (Rest × (Point → Outcome)) ≃ (Rest × (Point → Outcome)) :=
  VeiledFlock.Probability.fiberwiseEquiv swapRestOracle
    (fun rest ↦ renameOracle (left rest) (right rest)
      (hleft rest) (hright rest) (hcross rest))

omit [Nonempty Rest] in
omit [Fintype Point] [Fintype Rest] [DecidableEq Rest] [Fintype Outcome] [DecidableEq Outcome] in
omit [Finite Index] [DecidableEq Point] in
theorem fiberwiseRenameOracle_rest
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest))
    (hcross : ∀ rest leftIndex rightIndex,
      left rest leftIndex = right rest rightIndex →
        leftIndex = rightIndex)
    (input : Rest × (Point → Outcome)) :
    (fiberwiseRenameOracle left right hleft hright hcross input).1 =
      input.1 := by
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapRestOracle
    (fun rest ↦ renameOracle (left rest) (right rest)
      (hleft rest) (hright rest) (hcross rest)) input
  exact congrArg Prod.snd hsplit

omit [Finite Index] [DecidableEq Point] in
omit [Nonempty Rest] in
omit [Fintype Point] [Fintype Rest] [DecidableEq Rest] [Fintype Outcome] [DecidableEq Outcome] in
theorem fiberwiseRenameOracle_at_right
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest))
    (hcross : ∀ rest leftIndex rightIndex,
      left rest leftIndex = right rest rightIndex →
        leftIndex = rightIndex)
    (input : Rest × (Point → Outcome)) (index : Index) :
    (fiberwiseRenameOracle left right hleft hright hcross input).2
        (right input.1 index) = input.2 (left input.1 index) := by
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapRestOracle
    (fun rest ↦ renameOracle (left rest) (right rest)
      (hleft rest) (hright rest) (hcross rest)) input
  have horacle :
      (fiberwiseRenameOracle left right hleft hright hcross input).2 =
        renameOracle (left input.1) (right input.1)
          (hleft input.1) (hright input.1) (hcross input.1) input.2 :=
    congrArg Prod.fst hsplit
  rw [horacle]
  exact renameOracle_at_right (left input.1) (right input.1)
    (hleft input.1) (hright input.1) (hcross input.1) input.2 index

omit [Finite Index] [DecidableEq Point] in
omit [Nonempty Rest] in
omit [Fintype Point] [Fintype Rest] [DecidableEq Rest] [Fintype Outcome] [DecidableEq Outcome] in
theorem fiberwiseRenameOracle_off
    (left right : Rest → Index → Point)
    (hleft : ∀ rest, Injective (left rest))
    (hright : ∀ rest, Injective (right rest))
    (hcross : ∀ rest leftIndex rightIndex,
      left rest leftIndex = right rest rightIndex →
        leftIndex = rightIndex)
    (input : Rest × (Point → Outcome)) (point : Point)
    (hoffLeft : ∀ index, point ≠ left input.1 index)
    (hoffRight : ∀ index, point ≠ right input.1 index) :
    (fiberwiseRenameOracle left right hleft hright hcross input).2 point =
      input.2 point := by
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapRestOracle
    (fun rest ↦ renameOracle (left rest) (right rest)
      (hleft rest) (hright rest) (hcross rest)) input
  have horacle :
      (fiberwiseRenameOracle left right hleft hright hcross input).2 =
        renameOracle (left input.1) (right input.1)
          (hleft input.1) (hright input.1) (hcross input.1) input.2 :=
    congrArg Prod.fst hsplit
  rw [horacle]
  exact renameOracle_off (left input.1) (right input.1)
    (hleft input.1) (hright input.1) (hcross input.1) input.2 point
    hoffLeft hoffRight

end Fiberwise

end VeiledFlock.PairedOracleReplacement

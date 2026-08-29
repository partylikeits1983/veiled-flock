import VeiledFlock.Probability
import VeiledFlock.ProductionNizkConcreteCoupling

/-!
# Operational probability tape for the production experiments

The previous arithmetic ledger used a product of event-specific synthetic
coordinates.  Such a tape cannot be decoded into the coins actually consumed
by `productionRealView` and `productionSimulatedView`.  The ledger used by the
end-to-end theorem is instead the operational sample space itself: the full
`ProductionCoins`, the single shared bounded oracle table, and the adversary's
private coins.

This makes `productionDecode` a lossless projection, not a distributional
assumption.  Every subsequent bad event must therefore be defined and bounded
on these concrete coordinates.
-/

namespace VeiledFlock.ProductionOperationalTape

open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.Framing
open VeiledFlock.NonceSerialization
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionNizkAdversary
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionVeilLayer

/-- The one random-oracle table read and programmed by both the protocol and
the adaptive adversary.  Logical oracle domains are separated only by their
serialized inputs; they are not independent tables. -/
abbrev ProductionSharedOracleTable (shape : BatchShape)
    (maxStartLength : ℕ) :=
  BoundedBytes (ProductionMaxPointLength shape maxStartLength) → OracleBlock

/-- Every random coordinate consumed by one production experiment. -/
abbrev ProductionOperationalRandomness (shape : BatchShape)
    (maxStartLength : ℕ) (AdversaryCoins : Type*) :=
  ProductionCoins shape ×
    ProductionSharedOracleTable shape maxStartLength × AdversaryCoins

/-- Every protocol coin except the fresh 256-bit proof nonce.  This is the
fixed fiber in the adaptive prequery bound. -/
abbrev ProductionCoinsWithoutProofNonce (shape : BatchShape) :=
  VeiledFlock.ProductionOuterPaddedPcs.PreCoins
      (K := Unit) (I := BaseScalarIndex shape)
      (Pad := ActivePadding shape) (rounds := expectedMasks shape) ×
    LayerCoins shape × InitialTreeNonces ×
      (Fin (2 ^ (m shape - 11)) → NumericNonce) ×
      (Fin (2 ^ 13) → NumericNonce) ×
      (Fin (2 ^ 11) → NumericNonce) ×
      History (Outcome := OracleBlock) (programmedPoints shape)

noncomputable instance productionCoinsWithoutProofNonceFintype
    (shape : BatchShape) : Fintype (ProductionCoinsWithoutProofNonce shape) :=
  letI : Fintype (VeiledFlock.ProductionOuterPaddedPcs.PreCoins
      (K := Unit) (I := BaseScalarIndex shape)
      (Pad := ActivePadding shape) (rounds := expectedMasks shape)) :=
    Fintype.ofFinite _
  letI : Fintype (LayerCoins shape) := Fintype.ofFinite _
  letI : Fintype (Fin (2 ^ (m shape - 11)) → NumericNonce) :=
    Fintype.ofFinite _
  letI : Fintype (Fin (2 ^ 13) → NumericNonce) := Fintype.ofFinite _
  letI : Fintype (Fin (2 ^ 11) → NumericNonce) := Fintype.ofFinite _
  letI : Fintype
      (History (Outcome := OracleBlock) (programmedPoints shape)) :=
    Fintype.ofFinite _
  Fintype.ofFinite _

noncomputable def productionCoinsProofNonceEquiv (shape : BatchShape) :
    ProductionCoins shape ≃ Nonce256 × ProductionCoinsWithoutProofNonce shape where
  toFun coins :=
    (coins.proofNonce,
      (coins.outer, coins.layer, coins.treeNonces, coins.outerSalts,
        coins.linearSalts, coins.hadamardSalts, coins.simulatedAnswers))
  invFun coins :=
    { outer := coins.2.1
      layer := coins.2.2.1
      proofNonce := coins.1
      treeNonces := coins.2.2.2.1
      outerSalts := coins.2.2.2.2.1
      linearSalts := coins.2.2.2.2.2.1
      hadamardSalts := coins.2.2.2.2.2.2.1
      simulatedAnswers := coins.2.2.2.2.2.2.2 }
  left_inv coins := by cases coins; rfl
  right_inv coins := by
    rcases coins with ⟨proofNonce, outer, layer, treeNonces, outerSalts,
      linearSalts, hadamardSalts, simulatedAnswers⟩
    rfl

/-- Exact split of the operational tape at the proof nonce.  The oracle
table and adversary coins are entirely in the other component. -/
noncomputable def productionProofNonceSplit
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*) :
    ProductionOperationalRandomness shape maxStartLength AdversaryCoins ≃
      Nonce256 ×
        (ProductionCoinsWithoutProofNonce shape ×
          ProductionSharedOracleTable shape maxStartLength ×
          AdversaryCoins) :=
  (productionCoinsProofNonceEquiv shape).prodCongr
      (Equiv.refl (ProductionSharedOracleTable shape maxStartLength ×
        AdversaryCoins)) |>.trans
    (Equiv.prodAssoc Nonce256 (ProductionCoinsWithoutProofNonce shape)
      (ProductionSharedOracleTable shape maxStartLength × AdversaryCoins))

/-- The three independently salted production leaf families, with their
actual registered dimensions. -/
abbrev ProductionHiddenLeafIndex (shape : BatchShape) :=
  (Fin (2 ^ (m shape - 11)) ⊕ Fin (2 ^ 13)) ⊕ Fin (2 ^ 11)

abbrev ProductionHiddenSalts (shape : BatchShape) :=
  ProductionHiddenLeafIndex shape → NumericNonce

/-- Canonical finite enumeration of the three disjoint leaf families.  It is
used only for counting; the operational split itself retains the exact
tree/index sum type. -/
noncomputable def productionHiddenSaltsFinEquiv (shape : BatchShape) :
    ProductionHiddenSalts shape ≃
      (Fin (Fintype.card (ProductionHiddenLeafIndex shape)) → NumericNonce) where
  toFun salts site :=
    salts ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site)
  invFun salts site :=
    salts (Fintype.equivFin (ProductionHiddenLeafIndex shape) site)
  left_inv salts := by
    funext site
    simp
  right_inv salts := by
    funext site
    simp

@[simp] theorem productionHiddenSaltsFinEquiv_apply
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (site : Fin (Fintype.card (ProductionHiddenLeafIndex shape))) :
    productionHiddenSaltsFinEquiv shape salts site =
      salts ((Fintype.equivFin (ProductionHiddenLeafIndex shape)).symm site) :=
  rfl

@[simp] theorem productionHiddenSaltsFinEquiv_symm_apply
    (shape : BatchShape)
    (salts : Fin (Fintype.card (ProductionHiddenLeafIndex shape)) →
      NumericNonce)
    (site : ProductionHiddenLeafIndex shape) :
    (productionHiddenSaltsFinEquiv shape).symm salts site =
      salts (Fintype.equivFin (ProductionHiddenLeafIndex shape) site) :=
  rfl

/-- Every protocol coin other than the three hidden Merkle salt vectors. -/
abbrev ProductionCoinsWithoutHiddenSalts (shape : BatchShape) :=
  VeiledFlock.ProductionOuterPaddedPcs.PreCoins
      (K := Unit) (I := BaseScalarIndex shape)
      (Pad := ActivePadding shape) (rounds := expectedMasks shape) ×
    LayerCoins shape × Nonce256 × InitialTreeNonces ×
      History (Outcome := OracleBlock) (programmedPoints shape)

noncomputable instance productionCoinsWithoutHiddenSaltsFintype
    (shape : BatchShape) : Fintype (ProductionCoinsWithoutHiddenSalts shape) :=
  letI : Fintype (VeiledFlock.ProductionOuterPaddedPcs.PreCoins
      (K := Unit) (I := BaseScalarIndex shape)
      (Pad := ActivePadding shape) (rounds := expectedMasks shape)) :=
    Fintype.ofFinite _
  letI : Fintype (LayerCoins shape) := Fintype.ofFinite _
  letI : Fintype
      (History (Outcome := OracleBlock) (programmedPoints shape)) :=
    Fintype.ofFinite _
  Fintype.ofFinite _

/-- Exact product split of the real production coins at all hidden leaf
salts. -/
noncomputable def productionCoinsHiddenSaltsEquiv (shape : BatchShape) :
    ProductionCoins shape ≃
      ProductionHiddenSalts shape × ProductionCoinsWithoutHiddenSalts shape where
  toFun coins :=
    (fun index => match index with
      | .inl (.inl outer) => coins.outerSalts outer
      | .inl (.inr linear) => coins.linearSalts linear
      | .inr hadamard => coins.hadamardSalts hadamard,
    (coins.outer, coins.layer, coins.proofNonce, coins.treeNonces,
      coins.simulatedAnswers))
  invFun pair :=
    { outer := pair.2.1
      layer := pair.2.2.1
      proofNonce := pair.2.2.2.1
      treeNonces := pair.2.2.2.2.1
      outerSalts := fun index => pair.1 (.inl (.inl index))
      linearSalts := fun index => pair.1 (.inl (.inr index))
      hadamardSalts := fun index => pair.1 (.inr index)
      simulatedAnswers := pair.2.2.2.2.2 }
  left_inv coins := by cases coins; rfl
  right_inv pair := by
    rcases pair with ⟨salts, outer, layer, proofNonce, treeNonces, answers⟩
    apply Prod.ext
    · funext index
      rcases index with (outerIndex | hadamardIndex)
      · rcases outerIndex with (outer | linear) <;> rfl
      · rfl
    · rfl

@[simp] theorem productionCoinsHiddenSaltsEquiv_rest_outer
    (shape : BatchShape) (coins : ProductionCoins shape) :
    (productionCoinsHiddenSaltsEquiv shape coins).2.1 = coins.outer := rfl

@[simp] theorem productionCoinsHiddenSaltsEquiv_rest_layer
    (shape : BatchShape) (coins : ProductionCoins shape) :
    (productionCoinsHiddenSaltsEquiv shape coins).2.2.1 = coins.layer := rfl

@[simp] theorem productionCoinsHiddenSaltsEquiv_rest_proofNonce
    (shape : BatchShape) (coins : ProductionCoins shape) :
    (productionCoinsHiddenSaltsEquiv shape coins).2.2.2.1 =
      coins.proofNonce := rfl

@[simp] theorem productionCoinsHiddenSaltsEquiv_rest_treeNonces
    (shape : BatchShape) (coins : ProductionCoins shape) :
    (productionCoinsHiddenSaltsEquiv shape coins).2.2.2.2.1 =
      coins.treeNonces := rfl

@[simp] theorem productionCoinsHiddenSaltsEquiv_rest_simulatedAnswers
    (shape : BatchShape) (coins : ProductionCoins shape) :
    (productionCoinsHiddenSaltsEquiv shape coins).2.2.2.2.2 =
      coins.simulatedAnswers := rfl

/-- Exact operational-tape split used to count hidden Merkle-input guesses. -/
noncomputable def productionHiddenSaltsSplit
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*) :
    ProductionOperationalRandomness shape maxStartLength AdversaryCoins ≃
      ProductionHiddenSalts shape ×
        (ProductionCoinsWithoutHiddenSalts shape ×
          ProductionSharedOracleTable shape maxStartLength ×
          AdversaryCoins) :=
  (productionCoinsHiddenSaltsEquiv shape).prodCongr
      (Equiv.refl (ProductionSharedOracleTable shape maxStartLength ×
        AdversaryCoins)) |>.trans
    (Equiv.prodAssoc (ProductionHiddenSalts shape)
      (ProductionCoinsWithoutHiddenSalts shape)
      (ProductionSharedOracleTable shape maxStartLength × AdversaryCoins))

/-- Reassemble the exact production coin record after fixing the three hidden
salt vectors separately from all other protocol coins. -/
noncomputable def productionCoinsWithHiddenSalts (shape : BatchShape)
    (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) : ProductionCoins shape :=
  (productionCoinsHiddenSaltsEquiv shape).symm (salts, rest)

@[simp] theorem productionCoinsHiddenSaltsEquiv_withHiddenSalts
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    productionCoinsHiddenSaltsEquiv shape
        (productionCoinsWithHiddenSalts shape salts rest) =
      (salts, rest) := by
  unfold productionCoinsWithHiddenSalts
  exact (productionCoinsHiddenSaltsEquiv shape).apply_symm_apply (salts, rest)

@[simp] theorem productionCoinsWithHiddenSalts_equiv
    (shape : BatchShape) (coins : ProductionCoins shape) :
    productionCoinsWithHiddenSalts shape
        (productionCoinsHiddenSaltsEquiv shape coins).1
        (productionCoinsHiddenSaltsEquiv shape coins).2 =
      coins := by
  unfold productionCoinsWithHiddenSalts
  exact (productionCoinsHiddenSaltsEquiv shape).symm_apply_apply coins

@[simp] theorem productionCoinsWithHiddenSalts_outerSalts
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).outerSalts =
      fun index => salts (.inl (.inl index)) := rfl

@[simp] theorem productionCoinsWithHiddenSalts_linearSalts
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).linearSalts =
      fun index => salts (.inl (.inr index)) := rfl

@[simp] theorem productionCoinsWithHiddenSalts_hadamardSalts
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).hadamardSalts =
      fun index => salts (.inr index) := rfl

@[simp] theorem productionCoinsWithHiddenSalts_treeNonces
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).treeNonces =
      rest.2.2.2.1 := rfl

@[simp] theorem productionCoinsWithHiddenSalts_outer
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).outer = rest.1 := rfl

@[simp] theorem productionCoinsWithHiddenSalts_layer
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).layer = rest.2.1 := rfl

@[simp] theorem productionCoinsWithHiddenSalts_proofNonce
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).proofNonce =
      rest.2.2.1 := rfl

@[simp] theorem productionCoinsWithHiddenSalts_simulatedAnswers
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (rest : ProductionCoinsWithoutHiddenSalts shape) :
    (productionCoinsWithHiddenSalts shape salts rest).simulatedAnswers =
      rest.2.2.2.2 := rfl

/-- Replacing only the hidden salt tape preserves every other concrete coin
coordinate definitionally. -/
@[simp] theorem productionCoinsWithHiddenSalts_fromCoins_outer
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (coins : ProductionCoins shape) :
    (productionCoinsWithHiddenSalts shape salts
      (productionCoinsHiddenSaltsEquiv shape coins).2).outer = coins.outer := rfl

@[simp] theorem productionCoinsWithHiddenSalts_fromCoins_layer
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (coins : ProductionCoins shape) :
    (productionCoinsWithHiddenSalts shape salts
      (productionCoinsHiddenSaltsEquiv shape coins).2).layer = coins.layer := rfl

@[simp] theorem productionCoinsWithHiddenSalts_fromCoins_proofNonce
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (coins : ProductionCoins shape) :
    (productionCoinsWithHiddenSalts shape salts
      (productionCoinsHiddenSaltsEquiv shape coins).2).proofNonce =
        coins.proofNonce := rfl

@[simp] theorem productionCoinsWithHiddenSalts_fromCoins_treeNonces
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (coins : ProductionCoins shape) :
    (productionCoinsWithHiddenSalts shape salts
      (productionCoinsHiddenSaltsEquiv shape coins).2).treeNonces =
        coins.treeNonces := rfl

@[simp] theorem productionCoinsWithHiddenSalts_fromCoins_simulatedAnswers
    (shape : BatchShape) (salts : ProductionHiddenSalts shape)
    (coins : ProductionCoins shape) :
    (productionCoinsWithHiddenSalts shape salts
      (productionCoinsHiddenSaltsEquiv shape coins).2).simulatedAnswers =
        coins.simulatedAnswers := rfl

@[simp] theorem productionHiddenSaltsSplit_fst
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*)
    (tape : ProductionOperationalRandomness shape maxStartLength
      AdversaryCoins) :
    (productionHiddenSaltsSplit shape maxStartLength AdversaryCoins tape).1 =
      fun index => match index with
        | .inl (.inl outer) => tape.1.outerSalts outer
        | .inl (.inr linear) => tape.1.linearSalts linear
        | .inr hadamard => tape.1.hadamardSalts hadamard := rfl

@[simp] theorem productionHiddenSaltsSplit_snd_table
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*)
    (tape : ProductionOperationalRandomness shape maxStartLength
      AdversaryCoins) :
    (productionHiddenSaltsSplit shape maxStartLength AdversaryCoins tape).2.2.1 =
      tape.2.1 := rfl

@[simp] theorem productionHiddenSaltsSplit_snd_adversaryCoins
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*)
    (tape : ProductionOperationalRandomness shape maxStartLength
      AdversaryCoins) :
    (productionHiddenSaltsSplit shape maxStartLength AdversaryCoins tape).2.2.2 =
      tape.2.2 := rfl

@[simp] theorem productionCoinsWithHiddenSalts_split
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*)
    (tape : ProductionOperationalRandomness shape maxStartLength
      AdversaryCoins) :
    productionCoinsWithHiddenSalts shape
        (productionHiddenSaltsSplit shape maxStartLength AdversaryCoins tape).1
        (productionHiddenSaltsSplit shape maxStartLength AdversaryCoins tape).2.1 =
      tape.1 := by
  change (productionCoinsHiddenSaltsEquiv shape).symm
      (productionCoinsHiddenSaltsEquiv shape tape.1) = tape.1
  exact (productionCoinsHiddenSaltsEquiv shape).symm_apply_apply tape.1

@[simp] theorem productionProofNonceSplit_fst
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*)
    (tape : ProductionOperationalRandomness shape maxStartLength
      AdversaryCoins) :
    (productionProofNonceSplit shape maxStartLength AdversaryCoins tape).1 =
      tape.1.proofNonce := rfl

@[simp] theorem productionProofNonceSplit_snd_table
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*)
    (tape : ProductionOperationalRandomness shape maxStartLength
      AdversaryCoins) :
    (productionProofNonceSplit shape maxStartLength AdversaryCoins tape).2.2.1 =
      tape.2.1 := rfl

@[simp] theorem productionProofNonceSplit_snd_adversaryCoins
    (shape : BatchShape) (maxStartLength : ℕ) (AdversaryCoins : Type*)
    (tape : ProductionOperationalRandomness shape maxStartLength
      AdversaryCoins) :
    (productionProofNonceSplit shape maxStartLength AdversaryCoins tape).2.2.2 =
      tape.2.2 := rfl

/-- The probability-ledger tape is definitionally the operational sample
space.  This prevents an event from being charged on unrelated synthetic
coins. -/
abbrev ProductionLedgerTape (shape : BatchShape) (maxStartLength : ℕ)
    (AdversaryCoins : Type*) :=
  ProductionOperationalRandomness shape maxStartLength AdversaryCoins

/-- Decode a ledger tape into exactly the randomness consumed by the concrete
real and simulated experiments. -/
def productionDecode {shape : BatchShape} {maxStartLength : ℕ}
    {AdversaryCoins : Type*}
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    ProductionOperationalRandomness shape maxStartLength AdversaryCoins :=
  tape

@[simp] theorem productionDecode_protocolCoins
    {shape : BatchShape} {maxStartLength : ℕ} {AdversaryCoins : Type*}
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    (productionDecode tape).1 = tape.1 := rfl

@[simp] theorem productionDecode_oracleTable
    {shape : BatchShape} {maxStartLength : ℕ} {AdversaryCoins : Type*}
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    (productionDecode tape).2.1 = tape.2.1 := rfl

@[simp] theorem productionDecode_adversaryCoins
    {shape : BatchShape} {maxStartLength : ℕ} {AdversaryCoins : Type*}
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    (productionDecode tape).2.2 = tape.2.2 := rfl

/-- The shared state supplied to `productionRealView` and
`productionSimulatedView`; both executions start from this same decoded table. -/
def productionInitialOracleState
    {shape : BatchShape} {maxStartLength : ℕ} {AdversaryCoins : Type*}
    (tape : ProductionLedgerTape shape maxStartLength AdversaryCoins) :
    SharedOracleState (ProductionMaxPointLength shape maxStartLength) :=
  initialSharedOracleState (productionDecode tape).2.1

/-- Decoding preserves the exact finite uniform operational distribution.
This is a pushforward equality, not a hypothesis. -/
theorem productionDecode_measure_preserving
    {shape : BatchShape} {maxStartLength : ℕ} {AdversaryCoins : Type*}
    [Fintype AdversaryCoins] [Nonempty AdversaryCoins] :
    (PMF.uniformOfFintype
      (ProductionLedgerTape shape maxStartLength AdversaryCoins)).map
        productionDecode =
      PMF.uniformOfFintype
        (ProductionOperationalRandomness shape maxStartLength
          AdversaryCoins) := by
  change
    (PMF.uniformOfFintype
      (ProductionOperationalRandomness shape maxStartLength
        AdversaryCoins)).map id =
      PMF.uniformOfFintype
        (ProductionOperationalRandomness shape maxStartLength
          AdversaryCoins)
  exact PMF.map_id _

end VeiledFlock.ProductionOperationalTape

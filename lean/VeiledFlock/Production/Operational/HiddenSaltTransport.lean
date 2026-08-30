import VeiledFlock.Production.Operational.OperationalTape

/-!
# Hidden-salt transport for the concrete production protocol

This file constructs the production-specific two-salt permutation needed for
the adaptive post-proof Merkle bound.  The first salt tape is an independent
dummy.  The second component is the actual `ProductionCoins` record.  Swapping
the two tapes changes no algebraic coin, proof nonce, tree nonce, or simulated
answer coordinate.
-/

namespace VeiledFlock.ProductionHiddenSaltTransport

open Function
open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionConcreteAlgebraic
open VeiledFlock.ProductionConcreteOuter
open VeiledFlock.ProductionEqualitySampler
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionMerklePrelude
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionNizkProof
open VeiledFlock.ProductionOuterCodeDomains
open VeiledFlock.ProductionOuterPaddedPcs
open VeiledFlock.ProductionOperationalTape
open VeiledFlock.ProductionThreeTree
open VeiledFlock.ProductionTranscriptFraming
open VeiledFlock.TranscriptSchedule

variable {AdversaryCoins : Type*}

/-- Reconstruct a successful concrete execution from the five defining
equations.  This is the converse of `productionRealTrace_facts`; it introduces
no coupling or probability assumption. -/
theorem productionRealTrace_eq_some_of_facts
    {W : Type*} {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (statement : ProductionStatement shape) (witness : W)
    (coins : ProductionCoins shape)
    (table : BoundedBytes maxPointLength → OracleBlock)
    (trace : ProductionExecutionTrace shape)
    (facts : ProductionTraceFacts shape fallback r1csDigest causalSecret
      completion baseMessage statement witness coins table trace) :
    productionRealTrace shape fallback r1csDigest causalSecret completion
      baseMessage statement witness coins table = some trace := by
  simp only [productionRealTrace]
  rw [facts.outerCommitment, facts.linearCommitment]
  rw [facts.equalityPoint]
  simp only
  rw [facts.answers]
  rw [facts.tail]

/-- Every oracle location reached by the honest adaptive zerocheck run remains
in the Fiat--Shamir byte domain. -/
theorem realZerocheck_tracePoint_isFiatShamir
    {W : Type*} (shape : BatchShape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (absorbedPrefix : List Byte) (hfiat : isFiatShamirPoint absorbedPrefix)
    (witness : W) (coins : ProductionCoins shape)
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (site : Fin (programmedPoints shape)) :
    isFiatShamirPoint
      (tracePoint
        (zerocheckRealByteSchedule shape causalSecret completion
          absorbedPrefix witness coins) answers site) := by
  let transcript :=
    VeiledFlock.ProductionCausalScheduleTransport.honestStartTranscript shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2
  let step := scalarRoundStep consumeScalar
    (encodeField VeiledFlock.Field128Serialization.encodeGhashField)
    (VeiledFlock.ProductionCausalScheduleTransport.honestFirst shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2)
    (VeiledFlock.ProductionCausalScheduleTransport.honestSecond shape
      causalSecret completion (witness, coins.outer.1, coins.outer.2.1)
      coins.outer.2.2)
  obtain ⟨suffix, hsuffix⟩ := tracePoint_appendSchedule_hasPrefix
    (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
      transcript) step answers site
  change isFiatShamirPoint
    (tracePoint
      (appendSchedule
        (VeiledFlock.ProductionZerocheckSchedule.start shape absorbedPrefix
          transcript) step) answers site)
  rw [hsuffix]
  have hnonempty : absorbedPrefix ≠ [] := by
    intro hempty
    simp [isFiatShamirPoint, hempty] at hfiat
  simpa [isFiatShamirPoint,
    VeiledFlock.ProductionZerocheckSchedule.start, hnonempty] using hfiat

/-- Causal oracle noninterference does not require the point space itself to
be finite.  The production byte schedule lives over `List Byte`; only the
bounded table representation used for probability counting is finite. -/
theorem run_eq_of_eq_on_trace_unbounded
    {Point Outcome : Type*}
    (next : Schedule (Point := Point) (Outcome := Outcome))
    (left right : Point → Outcome) {rounds : ℕ}
    (hagrees : ∀ site : Fin rounds,
      right (tracePoint next (AdaptiveOracleProgramming.run next left rounds)
        site) =
      left (tracePoint next (AdaptiveOracleProgramming.run next left rounds)
        site)) :
    AdaptiveOracleProgramming.run next right rounds =
      AdaptiveOracleProgramming.run next left rounds := by
  have hprefix : ∀ count (hle : count ≤ rounds),
      AdaptiveOracleProgramming.run next right count =
        AdaptiveOracleProgramming.run next left count := by
    intro count
    induction count with
    | zero =>
        intro _
        rfl
    | succ count ih =>
        intro hle
        have hprevious := ih (Nat.le_trans (Nat.le_succ count) hle)
        funext site
        refine Fin.lastCases ?_ (fun prior => ?_) site
        · rw [run_succ_last, run_succ_last, hprevious]
          let fullSite : Fin rounds := ⟨count, Nat.lt_of_succ_le hle⟩
          have hagree := hagrees fullSite
          rw [tracePoint, priorAnswers_run] at hagree
          exact hagree
        · rw [run_succ_castSucc, run_succ_castSucc]
          exact congrFun hprevious prior
  exact hprefix rounds (le_refl rounds)

/-- Independent dummy salts together with the actual production coins and
the adversary's private coins. -/
abbrev ExpandedProtocolCoins (shape : BatchShape) (AdversaryCoins : Type*) :=
  ProductionHiddenSalts shape × (ProductionCoins shape × AdversaryCoins)

/-- Canonical salt-independent representative of the Merkle geometry carried
by a production coin record.  Only tree nonces and public dimensions enter
`productionTreeGeometry`; all hidden salts are replaced by zero here so the
representative is unchanged by the real/dummy salt swap. -/
noncomputable def saltIndependentGeometryCoins (shape : BatchShape)
    (coins : ProductionCoins shape) : ProductionCoins shape :=
  productionCoinsWithHiddenSalts shape (fun _ => 0)
    (productionCoinsHiddenSaltsEquiv shape coins).2

@[simp] theorem saltIndependentGeometryCoins_treeNonces
    (shape : BatchShape) (coins : ProductionCoins shape) :
    (saltIndependentGeometryCoins shape coins).treeNonces =
      coins.treeNonces := by
  simp [saltIndependentGeometryCoins]

theorem saltIndependentGeometryCoins_geometry
    (shape : BatchShape) (coins : ProductionCoins shape) :
    productionTreeGeometry shape (saltIndependentGeometryCoins shape coins) =
      productionTreeGeometry shape coins := by
  funext tree
  cases tree <;> rfl

/-- Swap the dummy salt tape with exactly the hidden-salt projection of the
actual production coins, retaining every other coin coordinate. -/
noncomputable def expandedHiddenSaltSwap
    (shape : BatchShape) (AdversaryCoins : Type*) :
    ExpandedProtocolCoins shape AdversaryCoins ≃
      ExpandedProtocolCoins shape AdversaryCoins where
  toFun input :=
    let actual := productionCoinsHiddenSaltsEquiv shape input.2.1
    (actual.1,
      (productionCoinsWithHiddenSalts shape input.1 actual.2, input.2.2))
  invFun input :=
    let actual := productionCoinsHiddenSaltsEquiv shape input.2.1
    (actual.1,
      (productionCoinsWithHiddenSalts shape input.1 actual.2, input.2.2))
  left_inv input := by
    rcases input with ⟨dummy, coins, adversaryCoins⟩
    dsimp
    change
      ((productionCoinsHiddenSaltsEquiv shape
          (productionCoinsWithHiddenSalts shape dummy
            (productionCoinsHiddenSaltsEquiv shape coins).2)).1,
        (productionCoinsWithHiddenSalts shape
          (productionCoinsHiddenSaltsEquiv shape coins).1
          (productionCoinsHiddenSaltsEquiv shape
            (productionCoinsWithHiddenSalts shape dummy
              (productionCoinsHiddenSaltsEquiv shape coins).2)).2,
          adversaryCoins)) = _
    rw [productionCoinsHiddenSaltsEquiv_withHiddenSalts,
      productionCoinsWithHiddenSalts_equiv]
  right_inv input := by
    rcases input with ⟨dummy, coins, adversaryCoins⟩
    dsimp
    change
      ((productionCoinsHiddenSaltsEquiv shape
          (productionCoinsWithHiddenSalts shape dummy
            (productionCoinsHiddenSaltsEquiv shape coins).2)).1,
        (productionCoinsWithHiddenSalts shape
          (productionCoinsHiddenSaltsEquiv shape coins).1
          (productionCoinsHiddenSaltsEquiv shape
            (productionCoinsWithHiddenSalts shape dummy
              (productionCoinsHiddenSaltsEquiv shape coins).2)).2,
          adversaryCoins)) = _
    rw [productionCoinsHiddenSaltsEquiv_withHiddenSalts,
      productionCoinsWithHiddenSalts_equiv]

@[simp] theorem expandedHiddenSaltSwap_dummy
    (shape : BatchShape) (input : ExpandedProtocolCoins shape AdversaryCoins) :
    (expandedHiddenSaltSwap shape AdversaryCoins input).1 =
      (productionCoinsHiddenSaltsEquiv shape input.2.1).1 := by
  rfl

@[simp] theorem expandedHiddenSaltSwap_actual
    (shape : BatchShape) (input : ExpandedProtocolCoins shape AdversaryCoins) :
    (expandedHiddenSaltSwap shape AdversaryCoins input).2.1 =
      productionCoinsWithHiddenSalts shape input.1
        (productionCoinsHiddenSaltsEquiv shape input.2.1).2 := by
  rfl

@[simp] theorem expandedHiddenSaltSwap_adversaryCoins
    (shape : BatchShape) (input : ExpandedProtocolCoins shape AdversaryCoins) :
    (expandedHiddenSaltSwap shape AdversaryCoins input).2.2 = input.2.2 := by
  rfl

section MerkleTransport

variable {PublicCoord W : Type*} [Fintype PublicCoord]

/-- Lift the exact three production tree materials to the expanded two-salt
coin space.  Only the actual production-coin projection is interpreted as
Merkle material; the independent dummy salts and adversary coins are not. -/
noncomputable def expandedProductionTreeMaterial
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W) :
    ∀ tree,
      VeiledFlock.ProductionCombinedMerkleTransport.TreeMaterial
        (productionTreeGeometry shape geometryCoins tree)
        (ExpandedProtocolCoins shape AdversaryCoins) := fun tree =>
  let material := productionTreeMaterial shape geometryCoins causalSecret
    baseMessage publicPositions weights context answers rest witness tree
  { salts := fun input => material.salts input.2.1
    payload := fun input => material.payload input.2.1 }

theorem expandedProductionTreeMaterial_fits
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength) :
    FamilyFits (maxLength := maxPointLength)
      (productionTreeGeometry shape geometryCoins)
      (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
        shape geometryCoins causalSecret baseMessage publicPositions weights
        context answers rest witness) := by
  intro tree input index
  exact productionTreeMaterial_fits shape geometryCoins causalSecret
    baseMessage publicPositions weights context answers rest witness houter
    hlinear hhadamard tree input.2.1 index

/-- At a fixed successful trace context, simultaneously swap the actual and
dummy salt tapes and transport all three concrete salted-leaf families in the
single bounded production oracle. -/
noncomputable def fixedTraceHiddenSaltCoinOracleEquiv
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength) :
    (ExpandedProtocolCoins shape AdversaryCoins ×
        (BoundedBytes maxPointLength → OracleBlock)) ≃
      (ExpandedProtocolCoins shape AdversaryCoins ×
        (BoundedBytes maxPointLength → OracleBlock)) :=
  boundedFamilyCoinOracleEquiv
    (expandedHiddenSaltSwap shape AdversaryCoins)
    (productionTreeGeometry shape geometryCoins)
    (productionTreeGeometry_channel_injective shape geometryCoins)
    (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
      shape geometryCoins causalSecret baseMessage publicPositions weights
      context answers rest witness)
    (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
      shape geometryCoins causalSecret baseMessage publicPositions weights
      context answers rest witness)
    (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
      baseMessage publicPositions weights context answers rest witness houter
      hlinear hhadamard)
    (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
      baseMessage publicPositions weights context answers rest witness houter
      hlinear hhadamard)

@[simp] theorem fixedTraceHiddenSaltCoinOracleEquiv_coins
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock)) :
    (fixedTraceHiddenSaltCoinOracleEquiv shape geometryCoins causalSecret
      baseMessage publicPositions weights context answers rest witness houter
      hlinear hhadamard input).1 =
        expandedHiddenSaltSwap shape AdversaryCoins input.1 := by
  rfl

/-- The fixed transport depends on the geometry coin only through its
non-salt coordinates. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_saltIndependentGeometry
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength) :
    fixedTraceHiddenSaltCoinOracleEquiv
        (AdversaryCoins := AdversaryCoins) shape
        (saltIndependentGeometryCoins shape geometryCoins) causalSecret
        baseMessage publicPositions weights context answers rest witness houter
        hlinear hhadamard =
      fixedTraceHiddenSaltCoinOracleEquiv shape geometryCoins causalSecret
        baseMessage publicPositions weights context answers rest witness houter
        hlinear hhadamard := by
  apply Equiv.ext
  intro input
  rfl

/-- The fixed-trace salt swap preserves all three concrete production roots
exactly.  This is the byte-level Merkle transport, not a symbolic commitment
assumption. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_roots
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength) (fallback : OracleBlock)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (tree : ProductionTree) :
    let material := expandedProductionTreeMaterial
      (AdversaryCoins := AdversaryCoins) shape geometryCoins causalSecret
      baseMessage publicPositions weights context answers rest witness
    let moved := fixedTraceHiddenSaltCoinOracleEquiv shape geometryCoins
      causalSecret baseMessage publicPositions weights context answers rest
      witness houter hlinear hhadamard input
    boundedRoot fallback (productionTreeGeometry shape geometryCoins tree)
        (material tree) moved.1 moved.2 =
      boundedRoot fallback (productionTreeGeometry shape geometryCoins tree)
        (material tree) input.1 input.2 := by
  dsimp only
  exact boundedFamilyCoinOracleEquiv_roots_exact
    (expandedHiddenSaltSwap shape AdversaryCoins)
    (productionTreeGeometry shape geometryCoins)
    (productionTreeGeometry_channel_injective shape geometryCoins)
    (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
      shape geometryCoins causalSecret baseMessage publicPositions weights
      context answers rest witness)
    (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
      shape geometryCoins causalSecret baseMessage publicPositions weights
      context answers rest witness)
    (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
      baseMessage publicPositions weights context answers rest witness houter
      hlinear hhadamard)
    (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
      baseMessage publicPositions weights context answers rest witness houter
      hlinear hhadamard)
    hnodes fallback input tree

/-- Hidden-leaf transport is invisible on every Fiat--Shamir point, including
the fail-closed case outside the finite bounded oracle universe. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_answer_fiat_all
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (point : List Byte) (hfiat : isFiatShamirPoint point) :
    let moved := fixedTraceHiddenSaltCoinOracleEquiv shape geometryCoins
      causalSecret baseMessage publicPositions weights context answers rest
      witness houter hlinear hhadamard input
    answerBounded fallback moved.2 point =
      answerBounded fallback input.2 point := by
  by_cases hpoint : point.length ≤ maxPointLength
  · exact boundedFamilyCoinOracleEquiv_answer_fiat
      (expandedHiddenSaltSwap shape AdversaryCoins)
      (productionTreeGeometry shape geometryCoins)
      (productionTreeGeometry_channel_injective shape geometryCoins)
      (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
        shape geometryCoins causalSecret baseMessage publicPositions weights
        context answers rest witness)
      (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
        shape geometryCoins causalSecret baseMessage publicPositions weights
        context answers rest witness)
      (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
        baseMessage publicPositions weights context answers rest witness houter
        hlinear hhadamard)
      (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
        baseMessage publicPositions weights context answers rest witness houter
        hlinear hhadamard)
      fallback input point hfiat hpoint
  · simp [answerBounded, hpoint]

/-- Hidden-leaf transport is likewise invisible on every first-success PoW
query used by the production grinding loops. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_answer_pow_all
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (fallback : OracleBlock)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (state : Nonce256) (nonce : Word64) :
    let moved := fixedTraceHiddenSaltCoinOracleEquiv shape geometryCoins
      causalSecret baseMessage publicPositions weights context answers rest
      witness houter hlinear hhadamard input
    answerBounded fallback moved.2 (encodePowPoint state nonce) =
      answerBounded fallback input.2 (encodePowPoint state nonce) := by
  by_cases hpoint : (encodePowPoint state nonce).length ≤ maxPointLength
  · exact boundedFamilyCoinOracleEquiv_answer_pow
      (expandedHiddenSaltSwap shape AdversaryCoins)
      (productionTreeGeometry shape geometryCoins)
      (productionTreeGeometry_channel_injective shape geometryCoins)
      (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
        shape geometryCoins causalSecret baseMessage publicPositions weights
        context answers rest witness)
      (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
        shape geometryCoins causalSecret baseMessage publicPositions weights
        context answers rest witness)
      (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
        baseMessage publicPositions weights context answers rest witness houter
        hlinear hhadamard)
      (expandedProductionTreeMaterial_fits shape geometryCoins causalSecret
        baseMessage publicPositions weights context answers rest witness houter
        hlinear hhadamard)
      fallback input state nonce hpoint
  · have hlength : ¬41 ≤ maxPointLength := by simpa using hpoint
    simp [answerBounded, hlength]

/-- The two Merkle roots computed before Fiat--Shamir sampling are exactly
preserved by the concrete salt/oracle transport. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_initialRoots
    {maxPointLength : ℕ}
    (shape : BatchShape) (geometryCoins : ProductionCoins shape)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (answers : History (Outcome := OracleBlock) (programmedPoints shape))
    (rest : ProductionRest shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength) (fallback : OracleBlock)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (hgeometry : geometryCoins = input.1.2.1) :
    let moved := fixedTraceHiddenSaltCoinOracleEquiv shape geometryCoins
      causalSecret baseMessage publicPositions weights context answers rest
      witness houter hlinear hhadamard input
    outerRoot shape baseMessage witness moved.1.2.1
          (answerBounded fallback moved.2) =
        outerRoot shape baseMessage witness input.1.2.1
          (answerBounded fallback input.2) ∧
      linearRoot shape moved.1.2.1 (answerBounded fallback moved.2) =
      linearRoot shape input.1.2.1 (answerBounded fallback input.2) := by
  subst geometryCoins
  let moved := fixedTraceHiddenSaltCoinOracleEquiv shape input.1.2.1
    causalSecret baseMessage publicPositions weights context answers rest
    witness houter hlinear hhadamard input
  have houterRoot := fixedTraceHiddenSaltCoinOracleEquiv_roots
    shape input.1.2.1 causalSecret baseMessage publicPositions weights
    context answers rest witness houter hlinear hhadamard hnodes fallback input
    (.outer)
  have hlinearRoot := fixedTraceHiddenSaltCoinOracleEquiv_roots
    shape input.1.2.1 causalSecret baseMessage publicPositions weights
    context answers rest witness houter hlinear hhadamard hnodes fallback input
    (.veilLinear)
  change
    outerRoot shape baseMessage witness moved.1.2.1
          (answerBounded fallback moved.2) =
        outerRoot shape baseMessage witness input.1.2.1
          (answerBounded fallback input.2) at houterRoot
  change
    linearRoot shape moved.1.2.1 (answerBounded fallback moved.2) =
      linearRoot shape input.1.2.1 (answerBounded fallback input.2) at hlinearRoot
  exact ⟨houterRoot, hlinearRoot⟩

/-- The hidden-salt/oracle permutation maps a successful real production run
to the exact same complete trace.  In particular, it preserves the accepted
rejection sample and the first-success grinding nonces jointly, not merely
their marginal laws. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_productionRealTrace
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion baseMessage statement witness input.1.2.1 input.2 =
        some trace) :
    let moved := fixedTraceHiddenSaltCoinOracleEquiv shape input.1.2.1
      causalSecret baseMessage publicPositions weights context trace.answers
      trace.tail.rest witness houter hlinear hhadamard input
    productionRealTrace shape fallback r1csDigest causalSecret completion
      baseMessage statement witness moved.1.2.1 moved.2 = some trace := by
  dsimp only
  let moved := fixedTraceHiddenSaltCoinOracleEquiv shape input.1.2.1
    causalSecret baseMessage publicPositions weights context trace.answers
    trace.tail.rest witness houter hlinear hhadamard input
  let originalCoins := input.1.2.1
  let originalOracle := answerBounded fallback input.2
  let movedOracle := answerBounded fallback moved.2
  have facts := productionRealTrace_facts shape fallback r1csDigest
    causalSecret completion baseMessage statement witness originalCoins input.2
    trace htrace
  have hmovedCoins : moved.1.2.1 =
      productionCoinsWithHiddenSalts shape input.1.1
        (productionCoinsHiddenSaltsEquiv shape originalCoins).2 := by
    rfl
  have hroots := fixedTraceHiddenSaltCoinOracleEquiv_initialRoots
    shape originalCoins causalSecret baseMessage publicPositions weights
    context trace.answers trace.tail.rest witness houter hlinear hhadamard
    hnodes fallback input rfl
  have houterCommitment : outerRoot shape baseMessage witness moved.1.2.1
      movedOracle = trace.outerCommitment := hroots.1.trans facts.outerCommitment
  have hlinearCommitment : linearRoot shape moved.1.2.1 movedOracle =
      trace.linearCommitment := hroots.2.trans facts.linearCommitment
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest originalCoins.proofNonce originalCoins.treeNonces.outer
    originalCoins.treeNonces.veilLinear originalCoins.treeNonces.veilHadamard
    trace.outerCommitment trace.linearCommitment
  have hpreludeFiat : isFiatShamirPoint prelude :=
    preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _
  have hmovedSample : sampleEqualityPointPrefix movedOracle
      (m shape - kSkip - 7) veilSamplingTrials prelude =
        some trace.equalityPoint := by
    rw [sampleEqualityPointPrefix_oracle_congr_fiat_bounded
      originalOracle movedOracle (m shape - kSkip - 7) veilSamplingTrials
      (prelude.length + 106 +
        veilSamplingTrials * (10 + 16 * (m shape - kSkip - 7)) + 18)
      prelude hpreludeFiat (by omega)]
    · exact facts.equalityPoint
    · intro point hfiat _
      exact fixedTraceHiddenSaltCoinOracleEquiv_answer_fiat_all
        shape originalCoins causalSecret baseMessage publicPositions weights
        context trace.answers trace.tail.rest witness houter hlinear hhadamard
        fallback input point hfiat
  have hmovedEquality : sampleEqualityPointPrefix movedOracle
      (m shape - kSkip - 7) veilSamplingTrials
      (preEqualityTranscript (productionStatementDigest statement) r1csDigest
        moved.1.2.1.proofNonce moved.1.2.1.treeNonces.outer
        moved.1.2.1.treeNonces.veilLinear
        moved.1.2.1.treeNonces.veilHadamard trace.outerCommitment
        trace.linearCommitment) = some trace.equalityPoint := by
    simpa [prelude, originalCoins, hmovedCoins] using hmovedSample
  have htraceFiat : isFiatShamirPoint trace.equalityPoint.2.2 :=
    sampleEqualityPointPrefix_some_isFiatShamir originalOracle
      (m shape - kSkip - 7) veilSamplingTrials prelude hpreludeFiat
      trace.equalityPoint facts.equalityPoint
  let schedule := zerocheckRealByteSchedule shape causalSecret completion
    trace.equalityPoint.2.2 witness originalCoins
  have hmovedSchedule : zerocheckRealByteSchedule shape causalSecret completion
      trace.equalityPoint.2.2 witness moved.1.2.1 = schedule := by
    simp [schedule, originalCoins, hmovedCoins, zerocheckRealByteSchedule]
  have hmovedAnswersAtSchedule : AdaptiveOracleProgramming.run schedule
      movedOracle (programmedPoints shape) = trace.answers := by
    calc
      AdaptiveOracleProgramming.run schedule movedOracle
          (programmedPoints shape) =
        AdaptiveOracleProgramming.run schedule originalOracle
          (programmedPoints shape) := by
            apply run_eq_of_eq_on_trace_unbounded schedule originalOracle
              movedOracle
            intro site
            exact fixedTraceHiddenSaltCoinOracleEquiv_answer_fiat_all
              shape originalCoins causalSecret baseMessage publicPositions
              weights context trace.answers trace.tail.rest witness houter
              hlinear hhadamard fallback input _
              (realZerocheck_tracePoint_isFiatShamir shape causalSecret
                completion trace.equalityPoint.2.2 htraceFiat witness
                originalCoins
                (AdaptiveOracleProgramming.run schedule originalOracle
                  (programmedPoints shape)) site)
      _ = trace.answers := facts.answers
  have hmovedAnswers : AdaptiveOracleProgramming.run
      (zerocheckRealByteSchedule shape causalSecret completion
        trace.equalityPoint.2.2 witness moved.1.2.1)
      movedOracle (programmedPoints shape) = trace.answers := by
    rw [hmovedSchedule]
    exact hmovedAnswersAtSchedule
  let postZerocheck := afterZerocheck shape causalSecret completion
    trace.equalityPoint.2.2 witness originalCoins trace.answers
  have hpostFiat : isFiatShamirPoint postZerocheck :=
    afterZerocheck_isFiatShamir shape causalSecret completion
      trace.equalityPoint.2.2 htraceFiat witness originalCoins trace.answers
  have hmovedTailAtOriginalPost : sampleProductionTail shape movedOracle
      trace.equalityPoint postZerocheck = some trace.tail := by
    rw [sampleProductionTail_oracle_congr shape originalOracle movedOracle
      trace.equalityPoint postZerocheck hpostFiat]
    · exact facts.tail
    · intro point hfiat
      exact fixedTraceHiddenSaltCoinOracleEquiv_answer_fiat_all
        shape originalCoins causalSecret baseMessage publicPositions weights
        context trace.answers trace.tail.rest witness houter hlinear hhadamard
        fallback input point hfiat
    · intro state nonce
      exact fixedTraceHiddenSaltCoinOracleEquiv_answer_pow_all
        shape originalCoins causalSecret baseMessage publicPositions weights
        context trace.answers trace.tail.rest witness houter hlinear hhadamard
        fallback input state nonce
  have hmovedTail : sampleProductionTail shape movedOracle trace.equalityPoint
      (afterZerocheck shape causalSecret completion trace.equalityPoint.2.2
        witness moved.1.2.1 trace.answers) = some trace.tail := by
    simpa [postZerocheck, originalCoins, hmovedCoins, afterZerocheck] using
      hmovedTailAtOriginalPost
  apply productionRealTrace_eq_some_of_facts shape fallback r1csDigest
    causalSecret completion baseMessage statement witness moved.1.2.1 moved.2
    trace
  exact {
    outerCommitment := houterCommitment
    linearCommitment := hlinearCommitment
    equalityPoint := hmovedEquality
    answers := hmovedAnswers
    tail := hmovedTail }

/-- Strong form of trace preservation: a transport parameterized by any fixed
trace context leaves the real execution result unchanged, including failure.
This makes the trace-indexed transport usable as a genuine permutation of the
entire operational sample space. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_productionRealTrace_eq
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (transportTrace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock)) :
    let moved := fixedTraceHiddenSaltCoinOracleEquiv shape input.1.2.1
      causalSecret baseMessage publicPositions weights context
      transportTrace.answers transportTrace.tail.rest witness houter hlinear
      hhadamard input
    productionRealTrace shape fallback r1csDigest causalSecret completion
        baseMessage statement witness moved.1.2.1 moved.2 =
      productionRealTrace shape fallback r1csDigest causalSecret completion
        baseMessage statement witness input.1.2.1 input.2 := by
  dsimp only
  let moved := fixedTraceHiddenSaltCoinOracleEquiv shape input.1.2.1
    causalSecret baseMessage publicPositions weights context
    transportTrace.answers transportTrace.tail.rest witness houter hlinear
    hhadamard input
  let originalCoins := input.1.2.1
  let originalOracle := answerBounded fallback input.2
  let movedOracle := answerBounded fallback moved.2
  have hmovedCoins : moved.1.2.1 =
      productionCoinsWithHiddenSalts shape input.1.1
        (productionCoinsHiddenSaltsEquiv shape originalCoins).2 := by
    rfl
  have hroots := fixedTraceHiddenSaltCoinOracleEquiv_initialRoots
    shape originalCoins causalSecret baseMessage publicPositions weights
    context transportTrace.answers transportTrace.tail.rest witness houter
    hlinear hhadamard hnodes fallback input rfl
  let prelude := preEqualityTranscript (productionStatementDigest statement)
    r1csDigest originalCoins.proofNonce originalCoins.treeNonces.outer
    originalCoins.treeNonces.veilLinear originalCoins.treeNonces.veilHadamard
    (outerRoot shape baseMessage witness originalCoins originalOracle)
    (linearRoot shape originalCoins originalOracle)
  have hpreludeFiat : isFiatShamirPoint prelude :=
    preEqualityTranscript_isFiatShamir _ _ _ _ _ _ _ _
  have hsample : sampleEqualityPointPrefix movedOracle
      (m shape - kSkip - 7) veilSamplingTrials prelude =
    sampleEqualityPointPrefix originalOracle
      (m shape - kSkip - 7) veilSamplingTrials prelude := by
    exact sampleEqualityPointPrefix_oracle_congr_fiat_bounded
      originalOracle movedOracle (m shape - kSkip - 7) veilSamplingTrials
      (prelude.length + 106 +
        veilSamplingTrials * (10 + 16 * (m shape - kSkip - 7)) + 18)
      prelude hpreludeFiat (by omega) (fun point hfiat _ =>
        fixedTraceHiddenSaltCoinOracleEquiv_answer_fiat_all
          shape originalCoins causalSecret baseMessage publicPositions weights
          context transportTrace.answers transportTrace.tail.rest witness
          houter hlinear hhadamard fallback input point hfiat)
  have hmovedProofNonce : moved.1.2.1.proofNonce =
      originalCoins.proofNonce := by simp [hmovedCoins, originalCoins]
  have hmovedTreeNonces : moved.1.2.1.treeNonces =
      originalCoins.treeNonces := by simp [hmovedCoins, originalCoins]
  simp only [productionRealTrace]
  rw [hroots.1, hroots.2, hmovedProofNonce, hmovedTreeNonces]
  change (match sampleEqualityPointPrefix movedOracle
      (m shape - kSkip - 7) veilSamplingTrials prelude with
    | none => none
    | some equalityPoint =>
      let answers := AdaptiveOracleProgramming.run
        (zerocheckRealByteSchedule shape causalSecret completion
          equalityPoint.2.2 witness moved.1.2.1) movedOracle
        (programmedPoints shape)
      match sampleProductionTail shape movedOracle equalityPoint
          (afterZerocheck shape causalSecret completion equalityPoint.2.2
            witness moved.1.2.1 answers) with
      | none => none
      | some tail => some ({
          outerCommitment := outerRoot shape baseMessage witness originalCoins
            originalOracle
          linearCommitment := linearRoot shape originalCoins originalOracle
          equalityPoint := equalityPoint
          answers := answers
          tail := tail } : ProductionExecutionTrace shape)) = _
  rw [hsample]
  generalize hequality : sampleEqualityPointPrefix originalOracle
    (m shape - kSkip - 7) veilSamplingTrials prelude = equalityResult
  cases equalityResult with
  | none => rfl
  | some equalityPoint =>
      simp only
      have hequalityFiat : isFiatShamirPoint equalityPoint.2.2 :=
        sampleEqualityPointPrefix_some_isFiatShamir originalOracle
          (m shape - kSkip - 7) veilSamplingTrials prelude hpreludeFiat
          equalityPoint hequality
      let schedule := zerocheckRealByteSchedule shape causalSecret completion
        equalityPoint.2.2 witness originalCoins
      have hmovedSchedule : zerocheckRealByteSchedule shape causalSecret
          completion equalityPoint.2.2 witness moved.1.2.1 = schedule := by
        simp [schedule, originalCoins, hmovedCoins,
          zerocheckRealByteSchedule]
      have hrun : AdaptiveOracleProgramming.run schedule movedOracle
          (programmedPoints shape) =
        AdaptiveOracleProgramming.run schedule originalOracle
          (programmedPoints shape) := by
        apply run_eq_of_eq_on_trace_unbounded schedule originalOracle
          movedOracle
        intro site
        exact fixedTraceHiddenSaltCoinOracleEquiv_answer_fiat_all
          shape originalCoins causalSecret baseMessage publicPositions weights
          context transportTrace.answers transportTrace.tail.rest witness
          houter hlinear hhadamard fallback input _
          (realZerocheck_tracePoint_isFiatShamir shape causalSecret completion
            equalityPoint.2.2 hequalityFiat witness originalCoins
            (AdaptiveOracleProgramming.run schedule originalOracle
              (programmedPoints shape)) site)
      rw [hmovedSchedule, hrun]
      let answers := AdaptiveOracleProgramming.run schedule originalOracle
        (programmedPoints shape)
      let post := afterZerocheck shape causalSecret completion
        equalityPoint.2.2 witness originalCoins answers
      have hpostFiat : isFiatShamirPoint post :=
        afterZerocheck_isFiatShamir shape causalSecret completion
          equalityPoint.2.2 hequalityFiat witness originalCoins answers
      have htail : sampleProductionTail shape movedOracle equalityPoint post =
          sampleProductionTail shape originalOracle equalityPoint post := by
        exact sampleProductionTail_oracle_congr shape originalOracle
          movedOracle equalityPoint post hpostFiat
          (fun point hfiat =>
            fixedTraceHiddenSaltCoinOracleEquiv_answer_fiat_all
              shape originalCoins causalSecret baseMessage publicPositions
              weights context transportTrace.answers transportTrace.tail.rest
              witness houter hlinear hhadamard fallback input point hfiat)
          (fun state nonce =>
            fixedTraceHiddenSaltCoinOracleEquiv_answer_pow_all
              shape originalCoins causalSecret baseMessage publicPositions
              weights context transportTrace.answers transportTrace.tail.rest
              witness houter hlinear hhadamard fallback input state nonce)
      have hmovedPost : afterZerocheck shape causalSecret completion
          equalityPoint.2.2 witness moved.1.2.1 answers = post := by
        simp [post, answers, originalCoins, hmovedCoins, afterZerocheck]
      rw [hmovedPost, htail]
      rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The same concrete transport preserves the complete serialized-level formal
proof object associated with the fixed trace. -/
theorem fixedTraceHiddenSaltCoinOracleEquiv_productionTraceProof
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (witness : W) (trace : ProductionExecutionTrace shape)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock)) :
    let moved := fixedTraceHiddenSaltCoinOracleEquiv shape input.1.2.1
      causalSecret baseMessage publicPositions weights context trace.answers
      trace.tail.rest witness houter hlinear hhadamard input
    productionTraceProof shape fallback causalSecret baseMessage
        publicPositions weights context witness moved.1.2.1 moved.2 trace =
      productionTraceProof shape fallback causalSecret baseMessage
        publicPositions weights context witness input.1.2.1 input.2 trace := by
  dsimp only
  let moved := fixedTraceHiddenSaltCoinOracleEquiv shape input.1.2.1
    causalSecret baseMessage publicPositions weights context trace.answers
    trace.tail.rest witness houter hlinear hhadamard input
  let originalCoins := input.1.2.1
  have hmovedCoins : moved.1.2.1 =
      productionCoinsWithHiddenSalts shape input.1.1
        (productionCoinsHiddenSaltsEquiv shape originalCoins).2 := by
    rfl
  have hroot := fixedTraceHiddenSaltCoinOracleEquiv_roots
    shape originalCoins causalSecret baseMessage publicPositions weights
    context trace.answers trace.tail.rest witness houter hlinear hhadamard
    hnodes fallback input (.veilHadamard)
  have hhadamardRoot : hadamardRoot shape
      (productionLayerSpecAt shape causalSecret baseMessage publicPositions
        weights context trace.answers trace.tail.rest witness moved.1.2.1)
      witness moved.1.2.1 (answerBounded fallback moved.2) =
    hadamardRoot shape
      (productionLayerSpecAt shape causalSecret baseMessage publicPositions
        weights context trace.answers trace.tail.rest witness originalCoins)
      witness originalCoins (answerBounded fallback input.2) := by
    change hadamardRoot shape
        (productionLayerSpecAt shape causalSecret baseMessage publicPositions
          weights context trace.answers trace.tail.rest witness moved.1.2.1)
        witness moved.1.2.1 (answerBounded fallback moved.2) =
      hadamardRoot shape
        (productionLayerSpecAt shape causalSecret baseMessage publicPositions
          weights context trace.answers trace.tail.rest witness originalCoins)
        witness originalCoins (answerBounded fallback input.2) at hroot
    exact hroot
  have halgebraic : productionAlgebraicProof shape causalSecret baseMessage
      publicPositions weights context trace.answers witness moved.1.2.1
        trace.tail.rest =
    productionAlgebraicProof shape causalSecret baseMessage publicPositions
      weights context trace.answers witness originalCoins trace.tail.rest := by
    rw [hmovedCoins]
    rfl
  unfold productionLayerSpecAt at hhadamardRoot
  rw [halgebraic] at hhadamardRoot
  unfold productionTraceProof productionProofOfTrace finishProductionProof
  rw [halgebraic]
  dsimp only
  rw [hhadamardRoot]
  unfold assembleProductionProof
  simp [originalCoins]

set_option maxHeartbeats 5000000 in
/-- A single bijection on the whole expanded operational tape.  Successful
inputs select their concretely computed trace as the transport context;
aborting inputs are fixed. -/
noncomputable def productionHiddenSaltTransportEquiv
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength) :
    (ExpandedProtocolCoins shape AdversaryCoins ×
        (BoundedBytes maxPointLength → OracleBlock)) ≃
      (ExpandedProtocolCoins shape AdversaryCoins ×
        (BoundedBytes maxPointLength → OracleBlock)) where
  toFun input :=
    match productionRealTrace shape fallback r1csDigest causalSecret
        completion baseMessage statement witness input.1.2.1 input.2 with
    | none => input
    | some trace =>
        fixedTraceHiddenSaltCoinOracleEquiv shape
          (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard input
  invFun input :=
    match productionRealTrace shape fallback r1csDigest causalSecret
        completion baseMessage statement witness input.1.2.1 input.2 with
    | none => input
    | some trace =>
        (fixedTraceHiddenSaltCoinOracleEquiv shape
          (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard).symm input
  left_inv input := by
    generalize htrace : productionRealTrace shape fallback r1csDigest
      causalSecret completion baseMessage statement witness input.1.2.1
      input.2 = result
    cases result with
    | none => simp [htrace]
    | some trace =>
        let transport := fixedTraceHiddenSaltCoinOracleEquiv
          (AdversaryCoins := AdversaryCoins) shape
          (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard
        have hpreserveActual :=
          fixedTraceHiddenSaltCoinOracleEquiv_productionRealTrace_eq
            (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
            causalSecret completion baseMessage publicPositions weights context
            statement witness trace houter hlinear hhadamard hnodes input
        have htransportEq :=
          fixedTraceHiddenSaltCoinOracleEquiv_saltIndependentGeometry
            (AdversaryCoins := AdversaryCoins) shape input.1.2.1 causalSecret
            baseMessage publicPositions weights context trace.answers
            trace.tail.rest witness houter hlinear hhadamard
        have hpreserve : productionRealTrace shape fallback r1csDigest
            causalSecret completion baseMessage statement witness
              (transport input).1.2.1 (transport input).2 = some trace := by
          have happly := congrArg (fun equivalence => equivalence input)
            htransportEq
          change transport input = _ at happly
          rw [happly]
          exact hpreserveActual.trans htrace
        have hcanonical : saltIndependentGeometryCoins shape
            (transport input).1.2.1 =
          saltIndependentGeometryCoins shape input.1.2.1 := by
          rfl
        simp only [htrace]
        rw [hpreserve]
        rw [hcanonical]
        exact transport.symm_apply_apply input
  right_inv input := by
    generalize htrace : productionRealTrace shape fallback r1csDigest
      causalSecret completion baseMessage statement witness input.1.2.1
      input.2 = result
    cases result with
    | none => simp [htrace]
    | some trace =>
        let transport := fixedTraceHiddenSaltCoinOracleEquiv
          (AdversaryCoins := AdversaryCoins) shape
          (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard
        let inverseInput := transport.symm input
        have hcanonical : saltIndependentGeometryCoins shape
            inverseInput.1.2.1 =
          saltIndependentGeometryCoins shape input.1.2.1 := by
          rfl
        let inverseTransport := fixedTraceHiddenSaltCoinOracleEquiv
          (AdversaryCoins := AdversaryCoins) shape
          (saltIndependentGeometryCoins shape inverseInput.1.2.1) causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard
        have hpreserveActual :=
          fixedTraceHiddenSaltCoinOracleEquiv_productionRealTrace_eq
            (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
            causalSecret completion baseMessage publicPositions weights context
            statement witness trace houter hlinear hhadamard hnodes inverseInput
        have htransportEq :=
          fixedTraceHiddenSaltCoinOracleEquiv_saltIndependentGeometry
            (AdversaryCoins := AdversaryCoins) shape inverseInput.1.2.1
            causalSecret baseMessage publicPositions weights context
            trace.answers trace.tail.rest witness houter hlinear hhadamard
        have hpreserve : productionRealTrace shape fallback r1csDigest
            causalSecret completion baseMessage statement witness
              (inverseTransport inverseInput).1.2.1
              (inverseTransport inverseInput).2 =
          productionRealTrace shape fallback r1csDigest causalSecret
            completion baseMessage statement witness inverseInput.1.2.1
              inverseInput.2 := by
          have happly := congrArg (fun equivalence => equivalence inverseInput)
            htransportEq
          change inverseTransport inverseInput = _ at happly
          rw [happly]
          exact hpreserveActual
        have hinverseTransport : inverseTransport = transport := by
          unfold inverseTransport transport
          rw [hcanonical]
        have hforward : inverseTransport inverseInput = input := by
          rw [hinverseTransport]
          exact transport.apply_symm_apply input
        rw [hforward, htrace] at hpreserve
        have hinverseTrace : productionRealTrace shape fallback r1csDigest
            causalSecret completion baseMessage statement witness
              inverseInput.1.2.1 inverseInput.2 = some trace := hpreserve.symm
        simp only [htrace]
        rw [hinverseTrace]
        exact hforward

theorem productionHiddenSaltTransportEquiv_apply_of_trace
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion baseMessage statement witness input.1.2.1 input.2 =
        some trace) :
    productionHiddenSaltTransportEquiv
        (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
        causalSecret completion baseMessage publicPositions weights context
        statement witness houter hlinear hhadamard hnodes input =
      fixedTraceHiddenSaltCoinOracleEquiv shape
        (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
        baseMessage publicPositions weights context trace.answers
        trace.tail.rest witness houter hlinear hhadamard input := by
  simp [productionHiddenSaltTransportEquiv, htrace]

/-- On a successful trace, the global transport changes the shared oracle
only at the two concrete honest hidden-leaf families whose salt tapes are
exchanged.  This raw-table form is the bridge used for adaptive adversarial
queries. -/
theorem productionHiddenSaltTransportEquiv_oracle_off_of_trace
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion baseMessage statement witness input.1.2.1 input.2 =
        some trace)
    (point : BoundedBytes maxPointLength)
    (hoffLeft : ∀ index,
      point ≠ boundedFamilyLeafPoint
        (productionTreeGeometry shape
          (saltIndependentGeometryCoins shape input.1.2.1))
        (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
          shape (saltIndependentGeometryCoins shape input.1.2.1)
          causalSecret baseMessage publicPositions weights context
          trace.answers trace.tail.rest witness)
        (expandedProductionTreeMaterial_fits shape
          (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard)
        input.1 index)
    (hoffRight : ∀ index,
      point ≠ boundedFamilyLeafPoint
        (productionTreeGeometry shape
          (saltIndependentGeometryCoins shape input.1.2.1))
        (expandedProductionTreeMaterial (AdversaryCoins := AdversaryCoins)
          shape (saltIndependentGeometryCoins shape input.1.2.1)
          causalSecret baseMessage publicPositions weights context
          trace.answers trace.tail.rest witness)
        (expandedProductionTreeMaterial_fits shape
          (saltIndependentGeometryCoins shape input.1.2.1) causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard)
        (expandedHiddenSaltSwap shape AdversaryCoins input.1) index) :
    let moved := productionHiddenSaltTransportEquiv
      (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
      causalSecret completion baseMessage publicPositions weights context
      statement witness houter hlinear hhadamard hnodes input
    moved.2 point = input.2 point := by
  classical
  dsimp only
  rw [productionHiddenSaltTransportEquiv_apply_of_trace shape fallback
    r1csDigest causalSecret completion baseMessage publicPositions weights
    context statement witness houter hlinear hhadamard hnodes input trace
    htrace]
  let geometryCoins := saltIndependentGeometryCoins shape input.1.2.1
  let material := expandedProductionTreeMaterial
    (AdversaryCoins := AdversaryCoins) shape geometryCoins causalSecret
    baseMessage publicPositions weights context trace.answers trace.tail.rest
    witness
  let fits := expandedProductionTreeMaterial_fits
    (AdversaryCoins := AdversaryCoins) shape geometryCoins causalSecret
    baseMessage publicPositions weights context trace.answers trace.tail.rest
    witness houter hlinear hhadamard
  have hbound : (unboundBytes point).length ≤ maxPointLength := by
    rcases point with ⟨length, bytes⟩
    simp only [unboundBytes, List.Vector.toList_length]
    exact Nat.le_of_lt_succ length.isLt
  have hrebound : boundBytes (unboundBytes point) hbound = point := by
    apply unboundBytes_injective
    simp
  have hoff := boundedFamilyCoinOracleEquiv_answer_off
    (expandedHiddenSaltSwap shape AdversaryCoins)
    (productionTreeGeometry shape geometryCoins)
    (productionTreeGeometry_channel_injective shape geometryCoins)
    material material fits fits fallback input (unboundBytes point)
    hbound (fun index heq => hoffLeft index (by
      apply unboundBytes_injective
      exact heq)) (fun index heq => hoffRight index (by
        apply unboundBytes_injective
        exact heq))
  dsimp only at hoff
  simp only [answerBounded, dif_pos hbound] at hoff
  rw [hrebound] at hoff
  exact hoff

theorem productionHiddenSaltTransportEquiv_trace
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock)) :
    let moved := productionHiddenSaltTransportEquiv
      (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
      causalSecret completion baseMessage publicPositions weights context
      statement witness houter hlinear hhadamard hnodes input
    productionRealTrace shape fallback r1csDigest causalSecret completion
        baseMessage statement witness moved.1.2.1 moved.2 =
      productionRealTrace shape fallback r1csDigest causalSecret completion
        baseMessage statement witness input.1.2.1 input.2 := by
  dsimp only
  generalize htrace : productionRealTrace shape fallback r1csDigest
    causalSecret completion baseMessage statement witness input.1.2.1
    input.2 = result
  cases result with
  | none => simp [productionHiddenSaltTransportEquiv, htrace]
  | some trace =>
      rw [productionHiddenSaltTransportEquiv_apply_of_trace shape fallback
        r1csDigest causalSecret completion baseMessage publicPositions weights
        context statement witness houter hlinear hhadamard hnodes input trace
        htrace]
      have htransportEq :=
        fixedTraceHiddenSaltCoinOracleEquiv_saltIndependentGeometry
          (AdversaryCoins := AdversaryCoins) shape input.1.2.1 causalSecret
          baseMessage publicPositions weights context trace.answers
          trace.tail.rest witness houter hlinear hhadamard
      rw [htransportEq]
      exact (fixedTraceHiddenSaltCoinOracleEquiv_productionRealTrace_eq
        (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
        causalSecret completion baseMessage publicPositions weights context
        statement witness trace houter hlinear hhadamard hnodes input).trans
          htrace

theorem productionHiddenSaltTransportEquiv_proof_of_trace
    {maxPointLength : ℕ}
    (shape : BatchShape) (fallback : OracleBlock) (r1csDigest : List Byte)
    (causalSecret : ProductionCausalSecret (W := W) shape)
    (completion : Completion OracleBlock (programmedPoints shape))
    (baseMessage : W → BaseWord shape)
    (publicPositions : PublicCoord → ResidualDataIndex shape × LaneIndex)
    (weights : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      ProductionRest shape → Unit → PublicCoord → GhashField)
    (context : History (Outcome := OracleBlock) (programmedPoints shape) →
      VeiledFlock.ProductionOuterPcs.Prefix
        (K := Unit) (rounds := expectedMasks shape) →
      VeiledFlock.ProductionOuterPaddedPcs.OuterPaddedView
        (I := BaseScalarIndex shape) (P := Unit)
        (Opened := OpenedRows shape) → ProductionRest shape →
      LayerContext shape W (ProductionConcreteAlgebraic.Public shape)
        (ProductionConcreteOuter.publicStatement shape publicPositions
          baseMessage))
    (statement : ProductionStatement shape) (witness : W)
    (houter : 108 + 16 * (2 * outerLaneCount) ≤ maxPointLength)
    (hlinear : 108 + 32 ≤ maxPointLength)
    (hhadamard : 108 + 64 ≤ maxPointLength)
    (hnodes : 140 ≤ maxPointLength)
    (input : ExpandedProtocolCoins shape AdversaryCoins ×
      (BoundedBytes maxPointLength → OracleBlock))
    (trace : ProductionExecutionTrace shape)
    (htrace : productionRealTrace shape fallback r1csDigest causalSecret
      completion baseMessage statement witness input.1.2.1 input.2 =
        some trace) :
    let moved := productionHiddenSaltTransportEquiv
      (AdversaryCoins := AdversaryCoins) shape fallback r1csDigest
      causalSecret completion baseMessage publicPositions weights context
      statement witness houter hlinear hhadamard hnodes input
    productionTraceProof shape fallback causalSecret baseMessage
        publicPositions weights context witness moved.1.2.1 moved.2 trace =
      productionTraceProof shape fallback causalSecret baseMessage
        publicPositions weights context witness input.1.2.1 input.2 trace := by
  dsimp only
  rw [productionHiddenSaltTransportEquiv_apply_of_trace shape fallback
    r1csDigest causalSecret completion baseMessage publicPositions weights
    context statement witness houter hlinear hhadamard hnodes input trace
    htrace]
  have htransportEq :=
    fixedTraceHiddenSaltCoinOracleEquiv_saltIndependentGeometry
      (AdversaryCoins := AdversaryCoins) shape input.1.2.1 causalSecret
      baseMessage publicPositions weights context trace.answers trace.tail.rest
      witness houter hlinear hhadamard
  rw [htransportEq]
  exact fixedTraceHiddenSaltCoinOracleEquiv_productionTraceProof
    (AdversaryCoins := AdversaryCoins) shape fallback causalSecret baseMessage
    publicPositions weights context witness trace houter hlinear hhadamard
    hnodes input

end MerkleTransport

end VeiledFlock.ProductionHiddenSaltTransport

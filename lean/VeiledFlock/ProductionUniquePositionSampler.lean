import VeiledFlock.ProductionChallengeSampler

/-!
# Exact production distinct-position sampler

`sample_unique_positions` repeatedly samples and reabsorbs one `F128`, inserts
its masked low coordinate into an ordered set, checks completion before every
draw, and fails closed after 4096 iterations.  Ordering of the final set is
deterministic post-processing, so the semantic state here is a `Finset`.
-/

namespace VeiledFlock.ProductionUniquePositionSampler

open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Framing
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionChallengeSampler
open VeiledFlock.ProductionCombinedMerkleTransport
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionThreeTree
open VeiledFlock.ProductionTranscriptFraming

/-- Exact bounded loop.  The completion check occurs before the next draw,
matching the Rust `for` loop. -/
noncomputable def collectUnique {domain : ℕ}
    (position : GhashField → Fin domain) (target : ℕ)
    (oracle : List Byte → OracleBlock) :
    ℕ → List Byte → Finset (Fin domain) →
      Option (Finset (Fin domain) × List Byte)
  | 0, transcript, selected =>
      if selected.card = target then some (selected, transcript) else none
  | trials + 1, transcript, selected =>
      if selected.card = target then some (selected, transcript)
      else
        let sample := sampleScalar oracle transcript
        collectUnique position target oracle trials sample.2
          (insert (position sample.1) selected)

/-- Starting from the empty set, this is the result returned before Rust's
deterministic ascending `BTreeSet::into_iter` conversion. -/
noncomputable def sampleUniquePositions {domain : ℕ}
    (position : GhashField → Fin domain) (target trials : ℕ)
    (oracle : List Byte → OracleBlock) (transcript : List Byte) :=
  collectUnique position target oracle trials transcript ∅

theorem collectUnique_oracle_congr_fiat_bounded {domain : ℕ}
    (position : GhashField → Fin domain) (target : ℕ)
    (leftOracle rightOracle : List Byte → OracleBlock)
    (trials maxLength : ℕ) (transcript : List Byte)
    (selected : Finset (Fin domain))
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + trials * 18 ≤ maxLength)
    (horacle : ∀ point, isFiatShamirPoint point →
      point.length ≤ maxLength → rightOracle point = leftOracle point) :
    collectUnique position target rightOracle trials transcript selected =
      collectUnique position target leftOracle trials transcript selected := by
  classical
  induction trials generalizing transcript selected with
  | zero => rfl
  | succ trials inductionHypothesis =>
      simp only [collectUnique]
      split
      · rfl
      · have hquery : transcript.length + 10 ≤ maxLength := by omega
        have hsample := sampleScalar_oracle_congr leftOracle rightOracle
          transcript (horacle (scalarPoint transcript)
            (scalarPoint_isFiatShamir hfiat) (by simpa using hquery))
        rw [hsample]
        apply inductionHypothesis
        · exact sampleScalar_next_isFiatShamir hfiat leftOracle
        · rw [sampleScalar_snd_length]
          simp only [Nat.add_mul, one_mul] at hbudget
          omega

theorem sampleUniquePositions_oracle_congr_fiat_bounded {domain : ℕ}
    (position : GhashField → Fin domain) (target : ℕ)
    (leftOracle rightOracle : List Byte → OracleBlock)
    (trials maxLength : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + trials * 18 ≤ maxLength)
    (horacle : ∀ point, isFiatShamirPoint point →
      point.length ≤ maxLength → rightOracle point = leftOracle point) :
    sampleUniquePositions position target trials rightOracle transcript =
      sampleUniquePositions position target trials leftOracle transcript := by
  exact collectUnique_oracle_congr_fiat_bounded position target leftOracle
    rightOracle trials maxLength transcript ∅ hfiat hbudget horacle

/-- Successful production sampling returns exactly the requested number of
distinct positions. -/
theorem collectUnique_some_card {domain : ℕ}
    (position : GhashField → Fin domain) (target trials : ℕ)
    (oracle : List Byte → OracleBlock) (transcript : List Byte)
    (selected result : Finset (Fin domain)) (next : List Byte)
    (hsome : collectUnique position target oracle trials transcript selected =
      some (result, next)) : result.card = target := by
  classical
  induction trials generalizing transcript selected with
  | zero =>
      simp only [collectUnique] at hsome
      split at hsome
      · rename_i hcard
        have hp := Option.some.inj hsome
        have hresult : selected = result := congrArg Prod.fst hp
        simpa [← hresult] using hcard
      · contradiction
  | succ trials inductionHypothesis =>
      simp only [collectUnique] at hsome
      split at hsome
      · rename_i hcard
        have hp := Option.some.inj hsome
        have hresult : selected = result := congrArg Prod.fst hp
        simpa [← hresult] using hcard
      · exact inductionHypothesis _ _ hsome

/-- The simultaneous three-tree transport fixes the exact Hadamard and linear
position-sampling loops (and any other instance of the same production
routine). -/
theorem threeTree_sampleUniquePositions_exact
    {Coins : Type*} {maxLength domain : ℕ}
    (position : GhashField → Fin domain) (target : ℕ)
    (coinEquiv : Coins ≃ Coins) (outer linear hadamard : TreeShape)
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (productionGeometry outer linear hadamard tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) leftMaterial)
    (hright : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) rightMaterial)
    (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (trials : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + trials * 18 ≤ maxLength) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv
      (productionGeometry outer linear hadamard)
      (productionGeometry_channel_injective outer linear hadamard)
      leftMaterial rightMaterial hleft hright input
    sampleUniquePositions position target trials
        (answerBounded fallback transported.2) transcript =
      sampleUniquePositions position target trials
        (answerBounded fallback input.2) transcript := by
  classical
  dsimp only
  apply sampleUniquePositions_oracle_congr_fiat_bounded position target
    (answerBounded fallback input.2)
    (answerBounded fallback
      (boundedFamilyCoinOracleEquiv coinEquiv
        (productionGeometry outer linear hadamard)
        (productionGeometry_channel_injective outer linear hadamard)
        leftMaterial rightMaterial hleft hright input).2)
    trials maxLength transcript hfiat hbudget
  intro point hpointFiat hpointLength
  exact threeTree_answer_fiat coinEquiv outer linear hadamard leftMaterial
    rightMaterial hleft hright fallback input point hpointFiat hpointLength

end VeiledFlock.ProductionUniquePositionSampler

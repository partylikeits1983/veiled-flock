import VeiledFlock.Production.Merkle.ThreeTree

/-!
# Exact bounded scalar challenge samplers

Rust's `sample_nonzero` and `sample_not_zero_or_one` repeatedly call
`FsChallenger::sample_f128`, reabsorbing each rejected scalar, and fail closed
after 4096 attempts.  This module models that state transition byte for byte
and proves transport through the finite three-tree oracle permutation.
-/

namespace VeiledFlock.ProductionChallengeSampler

open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.Framing
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCombinedMerkleTransport
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionThreeTree
open VeiledFlock.ProductionTranscriptFraming

/-- Field value parsed from the low 16 bytes of the exact scalar-squeeze
oracle block. -/
noncomputable def scalarField (oracle : List Byte → OracleBlock)
    (transcript : List Byte) : GhashField :=
  encodeGhashFieldEquiv.symm
    (oracleBlockSplit (oracle (scalarPoint transcript))).1

/-- One scalar squeeze and the exact live transcript after reabsorption. -/
noncomputable def sampleScalar (oracle : List Byte → OracleBlock)
    (transcript : List Byte) : GhashField × List Byte :=
  let block := oracle (scalarPoint transcript)
  (encodeGhashFieldEquiv.symm (oracleBlockSplit block).1,
    afterScalar transcript block)

@[simp]
theorem sampleScalar_snd_length (oracle : List Byte → OracleBlock)
    (transcript : List Byte) :
    (sampleScalar oracle transcript).2.length = transcript.length + 18 := by
  simp [sampleScalar]

theorem scalarPoint_isFiatShamir {transcript : List Byte}
    (hfiat : isFiatShamirPoint transcript) :
    isFiatShamirPoint (scalarPoint transcript) := by
  have hnonempty : transcript ≠ [] := by
    intro hempty
    rw [hempty] at hfiat
    simp [isFiatShamirPoint] at hfiat
  simp [isFiatShamirPoint, scalarPoint, hnonempty]
  simpa [isFiatShamirPoint] using hfiat

theorem sampleScalar_next_isFiatShamir {transcript : List Byte}
    (hfiat : isFiatShamirPoint transcript)
    (oracle : List Byte → OracleBlock) :
    isFiatShamirPoint (sampleScalar oracle transcript).2 := by
  have hnonempty : transcript ≠ [] := by
    intro hempty
    rw [hempty] at hfiat
    simp [isFiatShamirPoint] at hfiat
  simp [isFiatShamirPoint, sampleScalar, afterScalar, hnonempty]
  simpa [isFiatShamirPoint] using hfiat

/-- One scalar squeeze depends on exactly one oracle point. -/
theorem sampleScalar_oracle_congr
    (leftOracle rightOracle : List Byte → OracleBlock)
    (transcript : List Byte)
    (horacle : rightOracle (scalarPoint transcript) =
      leftOracle (scalarPoint transcript)) :
    sampleScalar rightOracle transcript = sampleScalar leftOracle transcript := by
  simp only [sampleScalar, horacle]

/-- Exact bounded rejection sampler, parameterized by its accepted set. -/
noncomputable def sampleScalarUntil (good : GhashField → Prop)
    [DecidablePred good] (oracle : List Byte → OracleBlock) :
    ℕ → List Byte → Option (GhashField × List Byte)
  | 0, _ => none
  | trials + 1, transcript =>
      let sample := sampleScalar oracle transcript
      if good sample.1 then some sample
      else sampleScalarUntil good oracle trials sample.2

/-- Exact trace congruence for any fail-closed scalar rejection sampler. -/
theorem sampleScalarUntil_oracle_congr_fiat_bounded
    (good : GhashField → Prop) [DecidablePred good]
    (leftOracle rightOracle : List Byte → OracleBlock)
    (trials maxLength : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + trials * 18 ≤ maxLength)
    (horacle : ∀ point, isFiatShamirPoint point →
      point.length ≤ maxLength → rightOracle point = leftOracle point) :
    sampleScalarUntil good rightOracle trials transcript =
      sampleScalarUntil good leftOracle trials transcript := by
  classical
  induction trials generalizing transcript with
  | zero => rfl
  | succ trials inductionHypothesis =>
      simp only [sampleScalarUntil]
      have hquery : transcript.length + 10 ≤ maxLength := by omega
      have hsample := sampleScalar_oracle_congr leftOracle rightOracle
        transcript (horacle (scalarPoint transcript)
          (scalarPoint_isFiatShamir hfiat) (by simpa using hquery))
      rw [hsample]
      split
      · rfl
      · apply inductionHypothesis
        · exact sampleScalar_next_isFiatShamir hfiat leftOracle
        · rw [sampleScalar_snd_length]
          simp only [Nat.add_mul, one_mul] at hbudget
          omega

def nonzero (value : GhashField) : Prop := value ≠ 0
def notZeroOrOne (value : GhashField) : Prop := value ≠ 0 ∧ value ≠ 1

noncomputable instance nonzeroDecidable : DecidablePred nonzero :=
  fun _value => Classical.dec _

noncomputable instance notZeroOrOneDecidable : DecidablePred notZeroOrOne :=
  fun _value => Classical.dec _

noncomputable def sampleNonzero (oracle : List Byte → OracleBlock)
    (trials : ℕ) (transcript : List Byte) :=
  sampleScalarUntil nonzero oracle trials transcript

noncomputable def sampleNotZeroOrOne (oracle : List Byte → OracleBlock)
    (trials : ℕ) (transcript : List Byte) :=
  sampleScalarUntil notZeroOrOne oracle trials transcript

/-- Any value returned by the exact nonzero sampler satisfies its advertised
postcondition. -/
theorem sampleScalarUntil_some_good (good : GhashField → Prop)
    [DecidablePred good] (oracle : List Byte → OracleBlock)
    (trials : ℕ) (transcript : List Byte) (value : GhashField)
    (next : List Byte)
    (hsome : sampleScalarUntil good oracle trials transcript =
      some (value, next)) : good value := by
  induction trials generalizing transcript with
  | zero => simp [sampleScalarUntil] at hsome
  | succ trials inductionHypothesis =>
      simp only [sampleScalarUntil] at hsome
      split at hsome
      · rename_i hgood
        have hsamp := Option.some.inj hsome
        have hfst : (sampleScalar oracle transcript).1 = value :=
          congrArg Prod.fst hsamp
        rw [hfst] at hgood
        exact hgood
      · exact inductionHypothesis _ hsome

theorem sampleNonzero_some_ne_zero (oracle : List Byte → OracleBlock)
    (trials : ℕ) (transcript : List Byte) (value : GhashField)
    (next : List Byte)
    (hsome : sampleNonzero oracle trials transcript = some (value, next)) :
    value ≠ 0 := by
  exact sampleScalarUntil_some_good nonzero oracle trials transcript value next
    hsome

theorem sampleNotZeroOrOne_some (oracle : List Byte → OracleBlock)
    (trials : ℕ) (transcript : List Byte) (value : GhashField)
    (next : List Byte)
    (hsome : sampleNotZeroOrOne oracle trials transcript =
      some (value, next)) : value ≠ 0 ∧ value ≠ 1 := by
  exact sampleScalarUntil_some_good notZeroOrOne oracle trials transcript value
    next hsome

/-- All exact bounded scalar-rejection calls are unchanged by the simultaneous
outer/linear/Hadamard tree transport. -/
theorem threeTree_sampleScalarUntil_exact {Coins : Type*}
    {maxLength : ℕ} (good : GhashField → Prop) [DecidablePred good]
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
    sampleScalarUntil good (answerBounded fallback transported.2)
        trials transcript =
      sampleScalarUntil good (answerBounded fallback input.2)
        trials transcript := by
  classical
  dsimp only
  apply sampleScalarUntil_oracle_congr_fiat_bounded good
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

end VeiledFlock.ProductionChallengeSampler

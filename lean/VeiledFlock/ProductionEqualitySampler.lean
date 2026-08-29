import VeiledFlock.PairedOracleReplacement
import VeiledFlock.ProductionMerkleTree
import VeiledFlock.ProductionTranscriptFraming

/-!
# Exact production equality-point rejection sampler

`sample_eq_point_bounded` first performs one six-field vector squeeze and then
up to 4096 whole-vector suffix squeezes, accepting the first suffix with no
coordinate equal to one.  This file models the exact SHA-256 block/counter
schedule and proves that salted-leaf oracle replacement preserves every
answer, the accepted attempt, and the final absorbed transcript.
-/

namespace VeiledFlock.ProductionEqualitySampler

open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization
open VeiledFlock.Framing
open VeiledFlock.NonceSerialization
open VeiledFlock.PairedOracleReplacement
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleTree
open VeiledFlock.ProductionTranscriptFraming

/-- Field `index` of a vector squeeze comes from the low or high 16-byte half
of counter block `index / 2`. -/
noncomputable def sliceField (oracle : List Byte → OracleBlock)
    (transcript : List Byte) (length : ℕ) (index : Fin length) : GhashField :=
  let block := oracle
    (slicePoint transcript length (BitVec.ofNat 64 (index.val / 2)))
  let half := if index.val % 2 = 0 then
    (oracleBlockSplit block).1
  else
    (oracleBlockSplit block).2
  encodeGhashFieldEquiv.symm half

noncomputable def sampleSlice (oracle : List Byte → OracleBlock)
    (transcript : List Byte) (length : ℕ) : Fin length → GhashField :=
  sliceField oracle transcript length

/-- State after the vector answer has been reabsorbed. -/
noncomputable def sampleSliceNext (oracle : List Byte → OracleBlock)
    (transcript : List Byte) (length : ℕ) : List Byte :=
  afterSlice transcript (sampleSlice oracle transcript length)

/-- A vector squeeze depends only on the oracle blocks at its exact counter
points. -/
theorem sampleSlice_oracle_congr
    (leftOracle rightOracle : List Byte → OracleBlock)
    (transcript : List Byte) (length : ℕ)
    (horacle : ∀ counter,
      rightOracle (slicePoint transcript length counter) =
        leftOracle (slicePoint transcript length counter)) :
    sampleSlice rightOracle transcript length =
      sampleSlice leftOracle transcript length := by
  funext index
  unfold sampleSlice sliceField
  rw [horacle]

theorem slicePoint_isFiatShamir {transcript : List Byte}
    (hprefix : isFiatShamirPoint transcript) (length : ℕ)
    (counter : ProductionFraming.Word64) :
    isFiatShamirPoint (slicePoint transcript length counter) := by
  have hnonempty : transcript ≠ [] := by
    intro hempty
    rw [hempty] at hprefix
    simp [isFiatShamirPoint] at hprefix
  simp [isFiatShamirPoint, slicePoint, hnonempty, hprefix]
  simpa [isFiatShamirPoint] using hprefix

theorem sampleSliceNext_isFiatShamir {transcript : List Byte}
    (hprefix : isFiatShamirPoint transcript) (oracle : List Byte → OracleBlock)
    (length : ℕ) :
    isFiatShamirPoint (sampleSliceNext oracle transcript length) := by
  have hnonempty : transcript ≠ [] := by
    intro hempty
    rw [hempty] at hprefix
    simp [isFiatShamirPoint] at hprefix
  simp [isFiatShamirPoint, sampleSliceNext, afterSlice, hnonempty, hprefix]
  simpa [isFiatShamirPoint] using hprefix

/-- Every counter query in a vector squeeze is disjoint from every exact
production Merkle leaf point by its first role byte. -/
theorem slicePoint_ne_productionLeafPoint {transcript : List Byte}
    (hprefix : isFiatShamirPoint transcript) (length : ℕ)
    (counter : ProductionFraming.Word64)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : ProductionFraming.Word64) (depth : ℕ)
    (leafIndex : Fin (2 ^ depth)) (salt : NumericNonce)
    (payload : List Byte) :
    slicePoint transcript length counter ≠
      productionLeafPoint channel treeDepth treeNonce leafLength depth
        leafIndex salt payload := by
  exact fiatShamir_ne_merkle (slicePoint_isFiatShamir hprefix length counter)
    .leaf channel treeDepth treeNonce leafLength (BitVec.ofNat 32 depth)
    (BitVec.ofNat 64 leafIndex.val)
    (nonceBytes (numericNonceBytes salt) ++ payload)

/-- Generic complement-fixing transport for one vector squeeze. -/
theorem sampleSlice_renameOracle_off_exact
    {Index : Type*} [Finite Index]
    (oracle : List Byte → OracleBlock)
    (leftPoint rightPoint : Index → List Byte)
    (hleft : Function.Injective leftPoint)
    (hright : Function.Injective rightPoint)
    (hcross : ∀ left right,
      leftPoint left = rightPoint right → left = right)
    (transcript : List Byte) (length : ℕ)
    (hoffLeft : ∀ counter index,
      slicePoint transcript length counter ≠ leftPoint index)
    (hoffRight : ∀ counter index,
      slicePoint transcript length counter ≠ rightPoint index) :
    sampleSlice
        (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft
          hright hcross oracle)
        transcript length = sampleSlice oracle transcript length := by
  funext index
  unfold sampleSlice sliceField
  rw [PairedOracleReplacement.renameOracle_off leftPoint rightPoint hleft
    hright hcross]
  · exact hoffLeft (BitVec.ofNat 64 (index.val / 2))
  · exact hoffRight (BitVec.ofNat 64 (index.val / 2))

/-- Pairwise salted-leaf replacement fixes an entire vector squeeze at any
Fiat--Shamir transcript. -/
theorem sampleSlice_pairedOracle_exact
    (oracle : List Byte → OracleBlock)
    (transcript : List Byte) (hprefix : isFiatShamirPoint transcript)
    (length : ℕ)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : ProductionFraming.Word64) (depth : ℕ)
    (hdepth : depth ≤ 64)
    (leftSalts rightSalts : Fin (2 ^ depth) → NumericNonce)
    (leftPayload rightPayload : Fin (2 ^ depth) → List Byte) :
    let leftPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (leftSalts index) (leftPayload index)
    let rightPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (rightSalts index) (rightPayload index)
    let hleft := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth leftSalts leftPayload
    let hright := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth rightSalts rightPayload
    let hcross := fun left right equality =>
      productionLeafPoint_cross_index channel treeDepth treeNonce leafLength
        depth hdepth leftSalts rightSalts leftPayload rightPayload equality
    sampleSlice
        (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft
          hright hcross oracle)
        transcript length = sampleSlice oracle transcript length := by
  classical
  dsimp only
  let leftPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (leftSalts index) (leftPayload index)
  let rightPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (rightSalts index) (rightPayload index)
  let hleft := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth leftSalts leftPayload
  let hright := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth rightSalts rightPayload
  let hcross : ∀ left right, leftPoint left = rightPoint right → left = right :=
    fun left right equality => productionLeafPoint_cross_index channel
      treeDepth treeNonce leafLength depth hdepth leftSalts rightSalts
      leftPayload rightPayload equality
  funext index
  unfold sampleSlice sliceField
  rw [PairedOracleReplacement.renameOracle_off leftPoint rightPoint hleft
    hright hcross]
  · intro leafIndex heq
    exact slicePoint_ne_productionLeafPoint hprefix length
      (BitVec.ofNat 64 (index.val / 2)) channel treeDepth treeNonce leafLength
      depth leafIndex (leftSalts leafIndex) (leftPayload leafIndex) heq
  · intro leafIndex heq
    exact slicePoint_ne_productionLeafPoint hprefix length
      (BitVec.ofNat 64 (index.val / 2)) channel treeDepth treeNonce leafLength
      depth leafIndex (rightSalts leafIndex) (rightPayload leafIndex) heq

def accepted {length : ℕ} (answer : Fin length → GhashField) : Prop :=
  ∀ index, answer index ≠ 1

noncomputable instance acceptedDecidable {length : ℕ}
    (answer : Fin length → GhashField) : Decidable (accepted answer) :=
  Classical.dec _

/-- Whole-vector bounded rejection loop.  Every rejected answer is reabsorbed
before the next attempt, exactly as in `sample_eq_point_bounded`. -/
noncomputable def sampleUntilAccepted (oracle : List Byte → OracleBlock)
    (length : ℕ) : ℕ → List Byte →
      Option ((Fin length → GhashField) × List Byte)
  | 0, _ => none
  | trials + 1, transcript =>
      let answer := sampleSlice oracle transcript length
      let next := afterSlice transcript answer
      if accepted answer then some (answer, next)
      else sampleUntilAccepted oracle length trials next

/-- A successful bounded rejection loop consumes no more than one complete
vector-observation frame per permitted attempt.  The bound concerns the
actual returned transcript, so it also covers every rejected prefix. -/
theorem sampleUntilAccepted_some_length_le
    (oracle : List Byte → OracleBlock) (length trials : ℕ)
    (transcript : List Byte) (answer : Fin length → GhashField)
    (finalTranscript : List Byte)
    (hsome : sampleUntilAccepted oracle length trials transcript =
      some (answer, finalTranscript)) :
    finalTranscript.length ≤
      transcript.length + trials * (10 + 16 * length) := by
  induction trials generalizing transcript with
  | zero =>
      simp [sampleUntilAccepted] at hsome
  | succ trials ih =>
      simp only [sampleUntilAccepted] at hsome
      split at hsome
      · have hpair := Option.some.inj hsome
        have hlength :
            (afterSlice transcript
              (sampleSlice oracle transcript length)).length =
              finalTranscript.length := by
          simpa only using congrArg (fun pair => pair.2.length) hpair
        rw [← hlength, afterSlice_length]
        simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
        omega
      · have htail := ih
          (afterSlice transcript (sampleSlice oracle transcript length)) hsome
        rw [afterSlice_length] at htail
        simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
        omega

/-- Every successful rejection trace retains its initial transcript as a
literal byte prefix, including across all rejected attempts. -/
theorem sampleUntilAccepted_some_prefix
    (oracle : List Byte → OracleBlock) (length trials : ℕ)
    (transcript : List Byte) (answer : Fin length → GhashField)
    (finalTranscript : List Byte)
    (hsome : sampleUntilAccepted oracle length trials transcript =
      some (answer, finalTranscript)) :
    transcript <+: finalTranscript := by
  induction trials generalizing transcript with
  | zero => simp [sampleUntilAccepted] at hsome
  | succ trials ih =>
      simp only [sampleUntilAccepted] at hsome
      split at hsome
      · have hpair := Option.some.inj hsome
        have hfinal : finalTranscript =
            afterSlice transcript (sampleSlice oracle transcript length) := by
          simpa only using (congrArg Prod.snd hpair).symm
        rw [hfinal]
        unfold afterSlice
        simpa only [List.append_assoc] using
          (List.prefix_append transcript
            (squeezeSliceTag length ++
              sliceAnswerBytes (sampleSlice oracle transcript length)))
      · have hstep : transcript <+:
            afterSlice transcript (sampleSlice oracle transcript length) := by
          unfold afterSlice
          simpa only [List.append_assoc] using
            (List.prefix_append transcript
              (squeezeSliceTag length ++
                sliceAnswerBytes (sampleSlice oracle transcript length)))
        exact hstep.trans (ih _ hsome)

/-- Oracle extensionality restricted to the exact bounded rejection trace.
The arithmetic budget is invariant across a rejected attempt. -/
theorem sampleUntilAccepted_oracle_congr_bounded
    (leftOracle rightOracle : List Byte → OracleBlock)
    (length trials maxLength : ℕ) (transcript : List Byte)
    (hbudget : transcript.length + trials * (10 + 16 * length) + 18 ≤
      maxLength)
    (horacle : ∀ point, point.length ≤ maxLength →
      rightOracle point = leftOracle point) :
    sampleUntilAccepted rightOracle length trials transcript =
      sampleUntilAccepted leftOracle length trials transcript := by
  classical
  induction trials generalizing transcript with
  | zero => rfl
  | succ trials inductionHypothesis =>
      simp only [sampleUntilAccepted]
      have hquery : transcript.length + 18 ≤ maxLength := by
        omega
      have hanswer := sampleSlice_oracle_congr leftOracle rightOracle
        transcript length (fun counter =>
          horacle (slicePoint transcript length counter) (by
            simpa using hquery))
      rw [hanswer]
      split
      · rfl
      · apply inductionHypothesis
        rw [afterSlice_length]
        simp only [Nat.add_mul, one_mul] at hbudget
        omega

/-- Oracle extensionality restricted both to the exact bounded rejection trace
and to the Fiat--Shamir role.  This is the form needed after a finite oracle
permutation has moved Merkle leaf points: those points may be inside the byte
budget, but role separation proves that no rejection-sampler query is one of
them. -/
theorem sampleUntilAccepted_oracle_congr_fiat_bounded
    (leftOracle rightOracle : List Byte → OracleBlock)
    (length trials maxLength : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + trials * (10 + 16 * length) + 18 ≤
      maxLength)
    (horacle : ∀ point, isFiatShamirPoint point →
      point.length ≤ maxLength → rightOracle point = leftOracle point) :
    sampleUntilAccepted rightOracle length trials transcript =
      sampleUntilAccepted leftOracle length trials transcript := by
  classical
  induction trials generalizing transcript with
  | zero => rfl
  | succ trials inductionHypothesis =>
      simp only [sampleUntilAccepted]
      have hquery : transcript.length + 18 ≤ maxLength := by
        omega
      have hanswer := sampleSlice_oracle_congr leftOracle rightOracle
        transcript length (fun counter =>
          horacle (slicePoint transcript length counter)
            (slicePoint_isFiatShamir hfiat length counter) (by
              simpa using hquery))
      rw [hanswer]
      split
      · rfl
      · apply inductionHypothesis
        · exact sampleSliceNext_isFiatShamir hfiat leftOracle length
        · rw [afterSlice_length]
          simp only [Nat.add_mul, one_mul] at hbudget
          omega

/-- Salted-leaf replacement preserves the complete bounded rejection loop,
including all rejected vectors and the accepted attempt. -/
theorem sampleUntilAccepted_pairedOracle_exact
    (oracle : List Byte → OracleBlock)
    (length trials : ℕ) (transcript : List Byte)
    (hprefix : isFiatShamirPoint transcript)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : ProductionFraming.Word64) (depth : ℕ)
    (hdepth : depth ≤ 64)
    (leftSalts rightSalts : Fin (2 ^ depth) → NumericNonce)
    (leftPayload rightPayload : Fin (2 ^ depth) → List Byte) :
    let leftPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (leftSalts index) (leftPayload index)
    let rightPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (rightSalts index) (rightPayload index)
    let hleft := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth leftSalts leftPayload
    let hright := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth rightSalts rightPayload
    let hcross := fun left right equality =>
      productionLeafPoint_cross_index channel treeDepth treeNonce leafLength
        depth hdepth leftSalts rightSalts leftPayload rightPayload equality
    sampleUntilAccepted
        (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft
          hright hcross oracle)
        length trials transcript =
      sampleUntilAccepted oracle length trials transcript := by
  classical
  dsimp only
  let leftPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (leftSalts index) (leftPayload index)
  let rightPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (rightSalts index) (rightPayload index)
  let hleft := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth leftSalts leftPayload
  let hright := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth rightSalts rightPayload
  let hcross : ∀ left right, leftPoint left = rightPoint right → left = right :=
    fun left right equality => productionLeafPoint_cross_index channel
      treeDepth treeNonce leafLength depth hdepth leftSalts rightSalts
      leftPayload rightPayload equality
  induction trials generalizing transcript with
  | zero => rfl
  | succ trials inductionHypothesis =>
      simp only [sampleUntilAccepted]
      have hanswer := sampleSlice_pairedOracle_exact oracle transcript hprefix
        length channel treeDepth treeNonce leafLength depth hdepth leftSalts
        rightSalts leftPayload rightPayload
      dsimp only at hanswer
      rw [hanswer]
      split
      · rfl
      · apply inductionHypothesis
        exact sampleSliceNext_isFiatShamir hprefix oracle length

/-- Generic rejection-loop transport when every Fiat--Shamir counter point is
outside both moved point families. -/
theorem sampleUntilAccepted_renameOracle_off_exact
    {Index : Type*} [Finite Index]
    (oracle : List Byte → OracleBlock)
    (leftPoint rightPoint : Index → List Byte)
    (hleft : Function.Injective leftPoint)
    (hright : Function.Injective rightPoint)
    (hcross : ∀ left right,
      leftPoint left = rightPoint right → left = right)
    (length trials : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hoffLeft : ∀ current (hcurrent : isFiatShamirPoint current)
      squeezeLength counter index,
      slicePoint current squeezeLength counter ≠ leftPoint index)
    (hoffRight : ∀ current (hcurrent : isFiatShamirPoint current)
      squeezeLength counter index,
      slicePoint current squeezeLength counter ≠ rightPoint index) :
    sampleUntilAccepted
        (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft
          hright hcross oracle)
        length trials transcript =
      sampleUntilAccepted oracle length trials transcript := by
  classical
  induction trials generalizing transcript with
  | zero => rfl
  | succ trials inductionHypothesis =>
      simp only [sampleUntilAccepted]
      have hanswer := sampleSlice_renameOracle_off_exact oracle leftPoint
        rightPoint hleft hright hcross transcript length
        (hoffLeft transcript hfiat length) (hoffRight transcript hfiat length)
      rw [hanswer]
      split
      · rfl
      · apply inductionHypothesis
        · exact sampleSliceNext_isFiatShamir hfiat oracle length

/-- Output of the exact equality-point transcript sampler: the six free skip
coordinates, the first accepted outer suffix, and the complete live transcript
after all vector squeezes. -/
abbrev EqualitySample (outerLength : ℕ) :=
  (Fin 6 → GhashField) × (Fin outerLength → GhashField) × List Byte

noncomputable def sampleEqualityPointPrefix
    (oracle : List Byte → OracleBlock) (outerLength trials : ℕ)
    (transcript : List Byte) : Option (EqualitySample outerLength) :=
  let skip := sampleSlice oracle transcript 6
  let afterSkip := afterSlice transcript skip
  match sampleUntilAccepted oracle outerLength trials afterSkip with
  | none => none
  | some (outer, finalPrefix) => some (skip, outer, finalPrefix)

/-- Closed transcript-length bound for the complete equality-point sampler:
one six-field squeeze followed by at most `trials` outer-vector attempts. -/
theorem sampleEqualityPointPrefix_some_length_le
    (oracle : List Byte → OracleBlock) (outerLength trials : ℕ)
    (transcript : List Byte) (sample : EqualitySample outerLength)
    (hsome : sampleEqualityPointPrefix oracle outerLength trials transcript =
      some sample) :
    sample.2.2.length ≤ transcript.length + (10 + 16 * 6) +
      trials * (10 + 16 * outerLength) := by
  simp only [sampleEqualityPointPrefix] at hsome
  generalize hresult : sampleUntilAccepted oracle outerLength trials
      (afterSlice transcript (sampleSlice oracle transcript 6)) = result at hsome
  cases result with
  | none => simp at hsome
  | some result =>
      rcases result with ⟨outer, finalTranscript⟩
      simp only at hsome
      have hsample := Option.some.inj hsome
      have hfinal : sample.2.2 = finalTranscript := by
        simpa only using (congrArg (fun value => value.2.2) hsample).symm
      rw [hfinal]
      have hbound := sampleUntilAccepted_some_length_le oracle outerLength
        trials (afterSlice transcript (sampleSlice oracle transcript 6)) outer
        finalTranscript hresult
      rw [afterSlice_length] at hbound
      omega

/-- The complete successful equality-point transcript begins with the exact
production prelude, irrespective of the number of rejected outer vectors. -/
theorem sampleEqualityPointPrefix_some_prefix
    (oracle : List Byte → OracleBlock) (outerLength trials : ℕ)
    (transcript : List Byte) (sample : EqualitySample outerLength)
    (hsome : sampleEqualityPointPrefix oracle outerLength trials transcript =
      some sample) :
    transcript <+: sample.2.2 := by
  simp only [sampleEqualityPointPrefix] at hsome
  generalize hresult : sampleUntilAccepted oracle outerLength trials
      (afterSlice transcript (sampleSlice oracle transcript 6)) = result at hsome
  cases result with
  | none => simp at hsome
  | some result =>
      rcases result with ⟨outer, finalTranscript⟩
      simp only at hsome
      have hsample := Option.some.inj hsome
      have hfinal : sample.2.2 = finalTranscript := by
        simpa only using (congrArg (fun value => value.2.2) hsample).symm
      rw [hfinal]
      have hstep : transcript <+:
          afterSlice transcript (sampleSlice oracle transcript 6) := by
        unfold afterSlice
        simpa only [List.append_assoc] using
          (List.prefix_append transcript
            (squeezeSliceTag 6 ++
              sliceAnswerBytes (sampleSlice oracle transcript 6)))
      exact hstep.trans
        (sampleUntilAccepted_some_prefix oracle outerLength trials
          (afterSlice transcript (sampleSlice oracle transcript 6)) outer
          finalTranscript hresult)

/-- The complete equality sampler only reads points below the displayed
closed-form byte bound: one six-field squeeze, at most `trials` outer-vector
squeezes, and one eight-byte counter suffix. -/
theorem sampleEqualityPointPrefix_oracle_congr_bounded
    (leftOracle rightOracle : List Byte → OracleBlock)
    (outerLength trials maxLength : ℕ) (transcript : List Byte)
    (hbudget : transcript.length + 106 +
        trials * (10 + 16 * outerLength) + 18 ≤ maxLength)
    (horacle : ∀ point, point.length ≤ maxLength →
      rightOracle point = leftOracle point) :
    sampleEqualityPointPrefix rightOracle outerLength trials transcript =
      sampleEqualityPointPrefix leftOracle outerLength trials transcript := by
  classical
  unfold sampleEqualityPointPrefix
  have hskipQuery : transcript.length + 18 ≤ maxLength := by omega
  have hskip := sampleSlice_oracle_congr leftOracle rightOracle transcript 6
    (fun counter => horacle (slicePoint transcript 6 counter) (by
      simpa using hskipQuery))
  rw [hskip]
  have hloop := sampleUntilAccepted_oracle_congr_bounded leftOracle
    rightOracle outerLength trials maxLength
    (afterSlice transcript (sampleSlice leftOracle transcript 6)) (by
      rw [afterSlice_length]
      omega) horacle
  simp only [hloop]

/-- The complete equality sampler only needs equality of bounded oracle
answers in the Fiat--Shamir role.  Merkle-role coordinates may therefore be
permuted simultaneously without weakening this exact trace statement. -/
theorem sampleEqualityPointPrefix_oracle_congr_fiat_bounded
    (leftOracle rightOracle : List Byte → OracleBlock)
    (outerLength trials maxLength : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hbudget : transcript.length + 106 +
        trials * (10 + 16 * outerLength) + 18 ≤ maxLength)
    (horacle : ∀ point, isFiatShamirPoint point →
      point.length ≤ maxLength → rightOracle point = leftOracle point) :
    sampleEqualityPointPrefix rightOracle outerLength trials transcript =
      sampleEqualityPointPrefix leftOracle outerLength trials transcript := by
  classical
  unfold sampleEqualityPointPrefix
  have hskipQuery : transcript.length + 18 ≤ maxLength := by omega
  have hskip := sampleSlice_oracle_congr leftOracle rightOracle transcript 6
    (fun counter => horacle (slicePoint transcript 6 counter)
      (slicePoint_isFiatShamir hfiat 6 counter) (by
        simpa using hskipQuery))
  rw [hskip]
  have hloop := sampleUntilAccepted_oracle_congr_fiat_bounded leftOracle
    rightOracle outerLength trials maxLength
    (afterSlice transcript (sampleSlice leftOracle transcript 6))
    (sampleSliceNext_isFiatShamir hfiat leftOracle 6) (by
      rw [afterSlice_length]
      omega) horacle
  simp only [hloop]

/-- The entire production equality-point sampler is unchanged by salted-leaf
replacement once its initial transcript is a Fiat--Shamir transcript. -/
theorem sampleEqualityPointPrefix_pairedOracle_exact
    (oracle : List Byte → OracleBlock)
    (outerLength trials : ℕ) (transcript : List Byte)
    (hprefix : isFiatShamirPoint transcript)
    (channel : RoChannel) (treeDepth : Byte) (treeNonce : Nonce256)
    (leafLength : ProductionFraming.Word64) (depth : ℕ)
    (hdepth : depth ≤ 64)
    (leftSalts rightSalts : Fin (2 ^ depth) → NumericNonce)
    (leftPayload rightPayload : Fin (2 ^ depth) → List Byte) :
    let leftPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (leftSalts index) (leftPayload index)
    let rightPoint := fun index =>
      productionLeafPoint channel treeDepth treeNonce leafLength depth index
        (rightSalts index) (rightPayload index)
    let hleft := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth leftSalts leftPayload
    let hright := productionLeafPoint_index_injective channel treeDepth
      treeNonce leafLength depth hdepth rightSalts rightPayload
    let hcross := fun left right equality =>
      productionLeafPoint_cross_index channel treeDepth treeNonce leafLength
        depth hdepth leftSalts rightSalts leftPayload rightPayload equality
    sampleEqualityPointPrefix
        (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft
          hright hcross oracle)
        outerLength trials transcript =
      sampleEqualityPointPrefix oracle outerLength trials transcript := by
  classical
  dsimp only
  let leftPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (leftSalts index) (leftPayload index)
  let rightPoint := fun index =>
    productionLeafPoint channel treeDepth treeNonce leafLength depth index
      (rightSalts index) (rightPayload index)
  let hleft := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth leftSalts leftPayload
  let hright := productionLeafPoint_index_injective channel treeDepth treeNonce
    leafLength depth hdepth rightSalts rightPayload
  let hcross : ∀ left right, leftPoint left = rightPoint right → left = right :=
    fun left right equality => productionLeafPoint_cross_index channel
      treeDepth treeNonce leafLength depth hdepth leftSalts rightSalts
      leftPayload rightPayload equality
  unfold sampleEqualityPointPrefix
  have hskip := sampleSlice_pairedOracle_exact oracle transcript hprefix 6 channel
    treeDepth treeNonce leafLength depth hdepth leftSalts rightSalts
    leftPayload rightPayload
  dsimp only at hskip
  rw [hskip]
  have hloop := sampleUntilAccepted_pairedOracle_exact oracle outerLength
    trials (afterSlice transcript (sampleSlice oracle transcript 6))
    (sampleSliceNext_isFiatShamir hprefix oracle 6) channel treeDepth treeNonce
    leafLength depth hdepth leftSalts rightSalts leftPayload rightPayload
  dsimp only at hloop
  simp only [hloop]

/-- Generic complete equality-sampler transport for a complement-fixing point
permutation whose moved families are disjoint from the Fiat--Shamir domain. -/
theorem sampleEqualityPointPrefix_renameOracle_off_exact
    {Index : Type*} [Finite Index]
    (oracle : List Byte → OracleBlock)
    (leftPoint rightPoint : Index → List Byte)
    (hleft : Function.Injective leftPoint)
    (hright : Function.Injective rightPoint)
    (hcross : ∀ left right,
      leftPoint left = rightPoint right → left = right)
    (outerLength trials : ℕ) (transcript : List Byte)
    (hfiat : isFiatShamirPoint transcript)
    (hoffLeft : ∀ current (hcurrent : isFiatShamirPoint current)
      squeezeLength counter index,
      slicePoint current squeezeLength counter ≠ leftPoint index)
    (hoffRight : ∀ current (hcurrent : isFiatShamirPoint current)
      squeezeLength counter index,
      slicePoint current squeezeLength counter ≠ rightPoint index) :
    sampleEqualityPointPrefix
        (PairedOracleReplacement.renameOracle leftPoint rightPoint hleft
          hright hcross oracle)
        outerLength trials transcript =
      sampleEqualityPointPrefix oracle outerLength trials transcript := by
  classical
  unfold sampleEqualityPointPrefix
  have hskip := sampleSlice_renameOracle_off_exact oracle leftPoint rightPoint
    hleft hright hcross transcript 6 (hoffLeft transcript hfiat 6)
    (hoffRight transcript hfiat 6)
  rw [hskip]
  have hloop := sampleUntilAccepted_renameOracle_off_exact oracle leftPoint
    rightPoint hleft hright hcross outerLength trials
    (afterSlice transcript (sampleSlice oracle transcript 6))
    (sampleSliceNext_isFiatShamir hfiat oracle 6) hoffLeft hoffRight
  simp only [hloop]

end VeiledFlock.ProductionEqualitySampler

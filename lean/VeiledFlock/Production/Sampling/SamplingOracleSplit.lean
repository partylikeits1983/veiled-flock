import VeiledFlock.Production.Sampling.SamplingSchedule

/-!
# Exact shared-oracle domain split for production sampling

This is an equivalence of the single finite production random-oracle table,
not an assumption of independent protocol oracles.  The first component is
the serialized Fiat--Shamir/PoW domain used by the bounded sampling schedule;
the second is its literal complement, which contains the Merkle domains.
-/

namespace VeiledFlock.ProductionSamplingOracleSplit

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.Framing
open VeiledFlock.OptionalAdaptiveOracle
open VeiledFlock.OracleCausalOneTimePad
open VeiledFlock.ProductionCausalOperational
open VeiledFlock.ProductionNizkCoupling
open VeiledFlock.ProductionNizkExperiment
open VeiledFlock.ProductionSamplingBadTape
open VeiledFlock.ProductionSamplingLayout
open VeiledFlock.ProductionSamplingSchedule

/-- The two serialized domains queried by the post-Merkle sampling state
machine.  This predicate is on actual bytes, not symbolic tags. -/
def IsSamplingBytes (point : List Byte) : Prop :=
  point.head? = some (0x01 : Byte) ∨ point.head? = some (0x12 : Byte)

instance isSamplingBytesDecidable : DecidablePred IsSamplingBytes :=
  fun point => inferInstanceAs (Decidable
    (point.head? = some (0x01 : Byte) ∨ point.head? = some (0x12 : Byte)))

def IsSamplingPoint {maxPointLength : ℕ}
    (point : BoundedBytes maxPointLength) : Prop :=
  IsSamplingBytes (unboundBytes point)

instance isSamplingPointDecidable (maxPointLength : ℕ) :
    DecidablePred (IsSamplingPoint (maxPointLength := maxPointLength)) :=
  fun point => isSamplingBytesDecidable (unboundBytes point)

abbrev SamplingPoint (maxPointLength : ℕ) :=
  { point : BoundedBytes maxPointLength // IsSamplingPoint point }

abbrev NonSamplingPoint (maxPointLength : ℕ) :=
  { point : BoundedBytes maxPointLength // ¬ IsSamplingPoint point }

/-- Reindex the one bounded domain by the sampling predicate and its exact
complement. -/
def pointDomainEquiv (maxPointLength : ℕ) :
    SamplingPoint maxPointLength ⊕ NonSamplingPoint maxPointLength ≃
      BoundedBytes maxPointLength :=
  Equiv.sumCompl (IsSamplingPoint (maxPointLength := maxPointLength))

/-- Exact table equivalence exposing the restrictions of one oracle function
to the two disjoint serialized domains. -/
def splitSharedOracle (maxPointLength : ℕ) :
    (BoundedBytes maxPointLength → OracleBlock) ≃
      ((SamplingPoint maxPointLength → OracleBlock) ×
        (NonSamplingPoint maxPointLength → OracleBlock)) :=
  (Equiv.arrowCongr (pointDomainEquiv maxPointLength).symm
      (Equiv.refl OracleBlock)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp]
theorem splitSharedOracle_sampling (maxPointLength : ℕ)
    (oracle : BoundedBytes maxPointLength → OracleBlock)
    (point : SamplingPoint maxPointLength) :
    (splitSharedOracle maxPointLength oracle).1 point = oracle point := by
  rfl

@[simp]
theorem splitSharedOracle_nonsampling (maxPointLength : ℕ)
    (oracle : BoundedBytes maxPointLength → OracleBlock)
    (point : NonSamplingPoint maxPointLength) :
    (splitSharedOracle maxPointLength oracle).2 point = oracle point := by
  rfl

@[simp]
theorem splitSharedOracle_symm_sampling (maxPointLength : ℕ)
    (sampling : SamplingPoint maxPointLength → OracleBlock)
    (other : NonSamplingPoint maxPointLength → OracleBlock)
    (point : SamplingPoint maxPointLength) :
    (splitSharedOracle maxPointLength).symm (sampling, other) point =
      sampling point := by
  simp [splitSharedOracle, pointDomainEquiv,
    Equiv.sumCompl_symm_apply_of_pos point.property]

@[simp]
theorem splitSharedOracle_symm_nonsampling (maxPointLength : ℕ)
    (sampling : SamplingPoint maxPointLength → OracleBlock)
    (other : NonSamplingPoint maxPointLength → OracleBlock)
    (point : NonSamplingPoint maxPointLength) :
    (splitSharedOracle maxPointLength).symm (sampling, other) point =
      other point := by
  simp [splitSharedOracle, pointDomainEquiv,
    Equiv.sumCompl_symm_apply_of_neg point.property]

section Schedule

variable {W : Type*}
variable (shape : BatchShape)
variable (causalSecret : ProductionCausalSecret (W := W) shape)
variable (completion : Completion OracleBlock (programmedPoints shape))
variable (witness : W) (coins : ProductionCoins shape)
variable (prelude : List Byte)

/-- Public serialization audit required to embed the literal byte schedule in
the finite shared-oracle universe. -/
def ScheduleFits (maxPointLength : ℕ) : Prop :=
  ∀ (round : Fin productionSamplingSlots)
      (answers : History (Outcome := OracleBlock) round) point,
    freshSchedule shape causalSecret completion witness coins prelude
        round answers = some point →
      point.length ≤ maxPointLength

/-- Every active literal query is in the Fiat--Shamir/PoW side of the exact
byte-domain split. -/
def ScheduleClassified : Prop :=
  ∀ (round : Fin productionSamplingSlots)
      (answers : History (Outcome := OracleBlock) round) point,
    freshSchedule shape causalSecret completion witness coins prelude
        round answers = some point →
      IsSamplingBytes point

noncomputable def boundedFreshSchedule (maxPointLength : ℕ)
    (hfits : ScheduleFits shape causalSecret completion witness coins prelude
      maxPointLength)
    (hclassified : ScheduleClassified shape causalSecret completion witness
      coins prelude) :
    OptionalSchedule (Point := SamplingPoint maxPointLength)
      (Outcome := OracleBlock) productionSamplingSlots :=
  fun round answers =>
    match hquery : freshSchedule shape causalSecret completion witness coins
        prelude round answers with
    | none => none
    | some point =>
        some ⟨boundBytes point (hfits round answers point hquery), by
          simpa [IsSamplingPoint] using
            hclassified round answers point hquery⟩

theorem boundedFreshSchedule_of_raw (maxPointLength : ℕ)
    (hfits : ScheduleFits shape causalSecret completion witness coins prelude
      maxPointLength)
    (hclassified : ScheduleClassified shape causalSecret completion witness
      coins prelude)
    (round : Fin productionSamplingSlots)
    (answers : History (Outcome := OracleBlock) round)
    (point : List Byte)
    (hquery : freshSchedule shape causalSecret completion witness coins prelude
      round answers = some point) :
    boundedFreshSchedule shape causalSecret completion witness coins prelude
        maxPointLength hfits hclassified round answers =
      some ⟨boundBytes point (hfits round answers point hquery), by
        simpa [IsSamplingPoint] using
          hclassified round answers point hquery⟩ := by
  unfold boundedFreshSchedule
  split
  · rename_i hnone
    rw [hquery] at hnone
    contradiction
  · rename_i raw hraw
    have heq : raw = point := Option.some.inj (hraw.symm.trans hquery)
    subst point
    rfl

theorem boundedFreshSchedule_some_raw (maxPointLength : ℕ)
    (hfits : ScheduleFits shape causalSecret completion witness coins prelude
      maxPointLength)
    (hclassified : ScheduleClassified shape causalSecret completion witness
      coins prelude)
    (round : Fin productionSamplingSlots)
    (answers : History (Outcome := OracleBlock) round)
    (point : SamplingPoint maxPointLength)
    (hsome : boundedFreshSchedule shape causalSecret completion witness coins
      prelude maxPointLength hfits hclassified round answers = some point) :
    freshSchedule shape causalSecret completion witness coins prelude round
      answers = some (unboundBytes point.1) := by
  simp only [boundedFreshSchedule] at hsome
  split at hsome
  · simp at hsome
  · rename_i raw hraw
    have hpoint : point =
        ⟨boundBytes raw (hfits round answers raw hraw),
          by simpa [IsSamplingPoint] using
            hclassified round answers raw hraw⟩ := by
      simpa using hsome.symm
    rw [hraw]
    congr 1
    simpa [hpoint]

theorem boundedFreshSchedule_activeInjective (maxPointLength : ℕ)
    (hfits : ScheduleFits shape causalSecret completion witness coins prelude
      maxPointLength)
    (hclassified : ScheduleClassified shape causalSecret completion witness
      coins prelude)
    (answers : History (Outcome := OracleBlock) productionSamplingSlots) :
    ActiveInjective
      (boundedFreshSchedule shape causalSecret completion witness coins prelude
        maxPointLength hfits hclassified) answers := by
  classical
  intro left right leftPoint rightPoint hleft hright heq
  apply freshSchedule_activeInjective shape causalSecret completion witness
    coins prelude answers left right (unboundBytes leftPoint.1)
      (unboundBytes rightPoint.1)
  · exact boundedFreshSchedule_some_raw shape causalSecret completion witness
      coins prelude maxPointLength hfits hclassified left
      (priorAnswers answers left) leftPoint hleft
  · exact boundedFreshSchedule_some_raw shape causalSecret completion witness
      coins prelude maxPointLength hfits hclassified right
      (priorAnswers answers right) rightPoint hright
  · exact congrArg (fun point : SamplingPoint maxPointLength =>
      unboundBytes point.1) heq

/-- Exact normalized failure probability for the concrete optional sampling
schedule once its serialized points have been audited. -/
theorem boundedFreshSchedule_globalBad_probability_le (maxPointLength : ℕ)
    (hfits : ScheduleFits shape causalSecret completion witness coins prelude
      maxPointLength)
    (hclassified : ScheduleClassified shape causalSecret completion witness
      coins prelude) :
    ((optionalBadInputs
        (boundedFreshSchedule shape causalSecret completion witness coins
          prelude maxPointLength hfits hclassified)
        (globalBad shape)).card : ℚ) /
        Fintype.card
          ((SamplingPoint maxPointLength → OracleBlock) ×
            (Fin (productionSamplingSlots + 1) → OracleBlock)) ≤
      samplingAbortBound shape := by
  rw [optionalBadInputs_probability_eq _
    (boundedFreshSchedule_activeInjective shape causalSecret completion witness
      coins prelude maxPointLength hfits hclassified) (globalBad shape)]
  exact globalBad_probability_le shape

end Schedule

end VeiledFlock.ProductionSamplingOracleSplit

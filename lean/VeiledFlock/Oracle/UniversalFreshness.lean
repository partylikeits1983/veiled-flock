import VeiledFlock.Concrete.ConcreteFraming
import VeiledFlock.Oracle.ProgrammableOracle

/-!
# Freshness uniformly over counterfactual transcript histories

An adaptive oracle equivalence ranges over every proposed answer vector, so
freshness must hold for every suffix that those answers can induce.  Counting
each suffix separately would introduce an invalid exponential loss.  The
production framing avoids that loss: at a fixed programming site, equality of
two points reveals equality of the 256-bit proof nonce even when their answer-
dependent suffixes differ.
-/

namespace VeiledFlock.UniversalFreshness

open Function

variable {Nonce Site Context Point : Type*}
variable [Fintype Nonce] [DecidableEq Nonce]
variable [Fintype Site] [DecidableEq Site]
variable [DecidableEq Point]

/-- A nonce is universally bad when some programming site under some
counterfactual causal history was already queried. -/
noncomputable def badNonces
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point) : Finset Nonce := by
  classical
  exact Finset.univ.filter fun nonce ↦
    ∃ site context, programPoint site nonce context ∈ priorQueries

theorem mem_badNonces_iff
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point) (nonce : Nonce) :
    nonce ∈ badNonces programPoint priorQueries ↔
      ∃ site context, programPoint site nonce context ∈ priorQueries := by
  classical
  simp [badNonces]

/-- Membership chooses one site witnessing a universally bad nonce. -/
noncomputable def witnessSite
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point)
    (nonce : {nonce // nonce ∈ badNonces programPoint priorQueries}) : Site :=
  Classical.choose
    ((mem_badNonces_iff programPoint priorQueries nonce.1).1 nonce.2)

/-- Membership chooses one counterfactual history at the witness site. -/
noncomputable def witnessContext
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point)
    (nonce : {nonce // nonce ∈ badNonces programPoint priorQueries}) : Context :=
  Classical.choose (Classical.choose_spec
    ((mem_badNonces_iff programPoint priorQueries nonce.1).1 nonce.2))

theorem witnessPoint_mem
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point)
    (nonce : {nonce // nonce ∈ badNonces programPoint priorQueries}) :
    programPoint (witnessSite programPoint priorQueries nonce) nonce.1
        (witnessContext programPoint priorQueries nonce) ∈ priorQueries := by
  exact Classical.choose_spec (Classical.choose_spec
    ((mem_badNonces_iff programPoint priorQueries nonce.1).1 nonce.2))

/-- Map each bad nonce to one programming site and one colliding prior point. -/
noncomputable def collisionWitness
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point)
    (nonce : {nonce // nonce ∈ badNonces programPoint priorQueries}) :
    Site × {point // point ∈ priorQueries} :=
  (witnessSite programPoint priorQueries nonce,
    ⟨programPoint (witnessSite programPoint priorQueries nonce) nonce.1
      (witnessContext programPoint priorQueries nonce),
      witnessPoint_mem programPoint priorQueries nonce⟩)

/-- The universal bad set costs only `sites * priorQueries`, independently of
the number of possible answer histories. -/
theorem card_badNonces_le
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point)
    (hcross : ∀ site leftNonce leftContext rightNonce rightContext,
      programPoint site leftNonce leftContext =
          programPoint site rightNonce rightContext →
        leftNonce = rightNonce) :
    (badNonces programPoint priorQueries).card ≤
      Fintype.card Site * priorQueries.card := by
  classical
  have hinjective : Injective (collisionWitness programPoint priorQueries) := by
    intro left right heq
    apply Subtype.ext
    have hsite := congrArg Prod.fst heq
    have hpoint := congrArg (fun output => output.2.1) heq
    change witnessSite programPoint priorQueries left =
      witnessSite programPoint priorQueries right at hsite
    change
      programPoint (witnessSite programPoint priorQueries left) left.1
          (witnessContext programPoint priorQueries left) =
        programPoint (witnessSite programPoint priorQueries right) right.1
          (witnessContext programPoint priorQueries right) at hpoint
    rw [← hsite] at hpoint
    exact hcross
      (witnessSite programPoint priorQueries left) left.1
      (witnessContext programPoint priorQueries left) right.1
      (witnessContext programPoint priorQueries right)
      hpoint
  have hcard := Fintype.card_le_of_injective
    (collisionWitness programPoint priorQueries) hinjective
  simpa only [Fintype.card_coe, Fintype.card_prod] using hcard

/-- Avoiding the universally bad set gives freshness simultaneously at every
site and for every counterfactual history. -/
theorem fresh_of_not_mem_badNonces
    (programPoint : Site → Nonce → Context → Point)
    (priorQueries : Finset Point) (nonce : Nonce)
    (hgood : nonce ∉ badNonces programPoint priorQueries) :
    ∀ site context, programPoint site nonce context ∉ priorQueries := by
  intro site context hmem
  exact hgood ((mem_badNonces_iff programPoint priorQueries nonce).2
    ⟨site, context, hmem⟩)

/-! ## Fixed-offset byte framing -/

open VeiledFlock.Framing
open VeiledFlock.NonceSerialization

/-- A fixed-length injective middle field identifies its value even across
two unrelated suffix functions. -/
theorem fixedOffsetFrame_cross_injective {A Left Right : Type*}
    (head : List Byte) (encode : A → List Byte)
    (leftSuffix : Left → A → List Byte)
    (rightSuffix : Right → A → List Byte) (length : ℕ)
    (hlength : ∀ value, (encode value).length = length)
    (hinjective : Injective encode)
    {left : A} {leftContext : Left} {right : A} {rightContext : Right}
    (heq : fixedOffsetFrame head encode (leftSuffix leftContext) left =
      fixedOffsetFrame head encode (rightSuffix rightContext) right) :
    left = right := by
  simp only [fixedOffsetFrame] at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have heq' : encode left ++ leftSuffix leftContext left =
      encode right ++ rightSuffix rightContext right :=
    List.append_cancel_left heq
  have htake := congrArg (List.take length) heq'
  have hleft :
      (encode left ++ leftSuffix leftContext left).take length = encode left := by
    rw [List.take_append_of_le_length (by simp [hlength])]
    simp [hlength]
  have hright :
      (encode right ++ rightSuffix rightContext right).take length =
        encode right := by
    rw [List.take_append_of_le_length (by simp [hlength])]
    simp [hlength]
  rw [hleft, hright] at htake
  exact hinjective htake

/-- The exact tagged proof-nonce frame identifies a numeric nonce across all
answer-dependent transcript suffixes. -/
theorem transcriptPoint_cross_injective {Left Right : Type*}
    (head : List Byte)
    (leftSuffix : Left → NumericNonce → List Byte)
    (rightSuffix : Right → NumericNonce → List Byte)
    {left : NumericNonce} {leftContext : Left}
    {right : NumericNonce} {rightContext : Right}
    (heq : ConcreteFraming.transcriptPoint head
        (leftSuffix leftContext) left =
      ConcreteFraming.transcriptPoint head
        (rightSuffix rightContext) right) :
    left = right := by
  exact fixedOffsetFrame_cross_injective head
    (fun value => transcriptNonceFrame (numericNonceBytes value))
    leftSuffix rightSuffix 41
    (fun value => length_transcriptNonceFrame (numericNonceBytes value))
    (Framing.transcriptNonceFrame_injective.comp
      numericNonceBytes.injective) heq

/-- Bounded-byte wrapping preserves the same uniform-over-histories nonce
recovery property used by the finite random-oracle model. -/
theorem boundedTranscriptPoint_cross_injective
    {Left Right : Type*} {maxLength : ℕ}
    (head : List Byte)
    (leftSuffix : Left → NumericNonce → List Byte)
    (rightSuffix : Right → NumericNonce → List Byte)
    (hleft : ∀ context nonce,
      (ConcreteFraming.transcriptPoint head (leftSuffix context) nonce).length
        ≤ maxLength)
    (hright : ∀ context nonce,
      (ConcreteFraming.transcriptPoint head (rightSuffix context) nonce).length
        ≤ maxLength)
    {left : NumericNonce} {leftContext : Left}
    {right : NumericNonce} {rightContext : Right}
    (heq : boundBytes
        (ConcreteFraming.transcriptPoint head (leftSuffix leftContext) left)
        (hleft leftContext left) =
      boundBytes
        (ConcreteFraming.transcriptPoint head (rightSuffix rightContext) right)
        (hright rightContext right)) :
    left = right := by
  apply transcriptPoint_cross_injective head leftSuffix rightSuffix
  exact boundBytes_injective heq

end VeiledFlock.UniversalFreshness

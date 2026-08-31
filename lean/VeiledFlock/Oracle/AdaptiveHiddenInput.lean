import VeiledFlock.Oracle.MerkleHiding
import VeiledFlock.Oracle.PairedOracleReplacement
import VeiledFlock.Core.Probability
import VeiledFlock.Production.Nizk.NizkAdversary

/-!
# Averaged hidden-input bound after adaptive post-processing

This is the finite-pROM analogue of an identical-until-bad commitment-hiding
argument.  A proof may contain a random-oracle value at a hidden salted input,
and a post-proof adversary may choose later queries from that proof and all
earlier answers.  The theorem below never conditions on a fixed salt.  It adds
an independent dummy salt tape, swaps the two hidden-input families together
with the oracle table, and reduces a real hit to one of two query logs that is
independent of the salt being guessed.
-/

namespace VeiledFlock.AdaptiveHiddenInput

open Function
open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.MerkleHiding
open VeiledFlock.PairedOracleReplacement
open VeiledFlock.ProductionNizkAdversary

variable {Salt Rest Proof : Type*}
variable [Fintype Salt] [DecidableEq Salt] [Nonempty Salt]
variable [Fintype Rest] [DecidableEq Rest] [Nonempty Rest]

abbrev SaltTape (hidden : ℕ) := Fin hidden → Salt
abbrev Oracle (maxPointLength : ℕ) :=
  BoundedBytes maxPointLength → OracleBlock
abbrev OriginalCoins (hidden maxPointLength : ℕ) :=
  SaltTape (Salt := Salt) hidden × (Rest × Oracle maxPointLength)
abbrev ExpandedCoins (hidden maxPointLength : ℕ) :=
  SaltTape (Salt := Salt) hidden ×
    OriginalCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength

def pointFamily {hidden maxPointLength : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (rest : Rest) (salts : SaltTape (Salt := Salt) hidden) :
    Fin hidden → BoundedBytes maxPointLength :=
  fun site => point rest site (salts site)

def postHistory {hidden maxPointLength queries : ℕ}
    (_point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : OriginalCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :
    List (BoundedBytes maxPointLength × OracleBlock) :=
  runQueryValues
    (nextQuery coins.2.1 (proof coins.2.1 coins.1 coins.2.2))
    coins.2.2 (List.ofFn id) []

def PostHit {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : OriginalCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) : Prop :=
  QueryHistoryHits (pointFamily point coins.2.1 coins.1)
    (postHistory point proof nextQuery coins)

/-- The independent dummy salt, rather than the salt used to construct the
proof, is hit by the actual post-proof query history. -/
def DummyHit {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) : Prop :=
  QueryHistoryHits (pointFamily point coins.2.2.1 coins.1)
    (postHistory point proof nextQuery coins.2)

/-- The set of distinct random-oracle inputs selected during the post-proof
adaptive phase. -/
noncomputable def postQueryPointSet {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : OriginalCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) : Finset (BoundedBytes maxPointLength) :=
  ((postHistory point proof nextQuery coins).map Prod.fst).toFinset

omit [Fintype Salt] [DecidableEq Salt] [Nonempty Salt] [Fintype Rest] [DecidableEq Rest] [Nonempty Rest] in
theorem postQueryPointSet_card_le {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : OriginalCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :
    (postQueryPointSet point proof nextQuery coins).card ≤ queries := by
  classical
  calc
    (postQueryPointSet point proof nextQuery coins).card ≤
        (postHistory point proof nextQuery coins).length := by
      exact (List.toFinset_card_le _).trans_eq (by simp)
    _ ≤ queries := by
      unfold postHistory
      have hlength := runQueryValues_length_le
        (nextQuery coins.2.1 (proof coins.2.1 coins.1 coins.2.2))
        coins.2.2 (List.ofFn id) []
      simpa using hlength

omit [Nonempty Salt] [Fintype Rest] [DecidableEq Rest] [Nonempty Rest] in
theorem dummyHit_iff_mem_hiddenInputBadAssignments
    {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :
    DummyHit point proof nextQuery coins ↔
      coins.1 ∈ hiddenInputBadAssignments
        (fun site salt => point coins.2.2.1 site salt)
        (postQueryPointSet point proof nextQuery coins.2) := by
  classical
  rw [MerkleHiding.mem_hiddenInputBadAssignments_iff]
  simp only [DummyHit, QueryHistoryHits, postQueryPointSet,
    pointFamily, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨call, hcall, site, hpoint⟩
    exact ⟨site, ⟨call, hcall, hpoint⟩⟩
  · rintro ⟨site, call, hcall, hpoint⟩
    exact ⟨call, hcall, site, hpoint⟩

/-- Swap the real and dummy salt tapes and simultaneously swap their hidden
random-oracle locations.  The map is an involution and therefore preserves
the finite uniform distribution exactly. -/
noncomputable def saltOracleSwap {hidden maxPointLength : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (hindexCross : ∀ (rest : Rest)
      (leftSalts rightSalts : SaltTape (Salt := Salt) hidden)
      (left right : Fin hidden),
      point rest left (leftSalts left) =
        point rest right (rightSalts right) → left = right) :
    ExpandedCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength ≃
      ExpandedCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength where
  toFun coins :=
    let dummy := coins.1
    let actual := coins.2.1
    let rest := coins.2.2.1
    let oracle := coins.2.2.2
    let left := pointFamily point rest actual
    let right := pointFamily point rest dummy
    let hleft : Injective left := fun _ _ heq =>
      hindexCross rest actual actual _ _ heq
    let hright : Injective right := fun _ _ heq =>
      hindexCross rest dummy dummy _ _ heq
    let hcross : ∀ leftIndex rightIndex,
        left leftIndex = right rightIndex → leftIndex = rightIndex :=
      fun _ _ heq => hindexCross rest actual dummy _ _ heq
    (actual, (dummy, rest,
      PairedOracleReplacement.renameOracle left right hleft hright hcross
        oracle))
  invFun coins :=
    let dummy := coins.1
    let actual := coins.2.1
    let rest := coins.2.2.1
    let oracle := coins.2.2.2
    let left := pointFamily point rest dummy
    let right := pointFamily point rest actual
    let hleft : Injective left := fun _ _ heq =>
      hindexCross rest dummy dummy _ _ heq
    let hright : Injective right := fun _ _ heq =>
      hindexCross rest actual actual _ _ heq
    let hcross : ∀ leftIndex rightIndex,
        left leftIndex = right rightIndex → leftIndex = rightIndex :=
      fun _ _ heq => hindexCross rest dummy actual _ _ heq
    (actual, (dummy, rest,
      PairedOracleReplacement.renameOracle left right hleft hright hcross
        oracle))
  left_inv coins := by
    classical
    rcases coins with ⟨dummy, actual, rest, oracle⟩
    change (dummy, actual, rest, _) = (dummy, actual, rest, oracle)
    congr 3
    exact (PairedOracleReplacement.renameOracle
      (pointFamily point rest actual) (pointFamily point rest dummy)
      (fun _ _ heq => hindexCross rest actual actual _ _ heq)
      (fun _ _ heq => hindexCross rest dummy dummy _ _ heq)
      (fun _ _ heq => hindexCross rest actual dummy _ _ heq)).left_inv oracle
  right_inv coins := by
    classical
    rcases coins with ⟨dummy, actual, rest, oracle⟩
    change (dummy, actual, rest, _) = (dummy, actual, rest, oracle)
    congr 3
    exact (PairedOracleReplacement.renameOracle
      (pointFamily point rest dummy) (pointFamily point rest actual)
      (fun _ _ heq => hindexCross rest dummy dummy _ _ heq)
      (fun _ _ heq => hindexCross rest actual actual _ _ heq)
      (fun _ _ heq => hindexCross rest dummy actual _ _ heq)).left_inv oracle

set_option maxHeartbeats 800000 in
omit [Fintype Salt] [DecidableEq Salt] [Nonempty Salt] [Fintype Rest] [DecidableEq Rest] [Nonempty Rest] in
/-- Pointwise identical-until-bad reduction.  A post-proof hit of the real
hidden family implies that either the original query log hits the independent
dummy family, or the transported query log hits the now-independent old salt
family. -/
theorem postHit_implies_dummyHit_or_swappedDummyHit
    {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (hindexCross : ∀ (rest : Rest)
      (leftSalts rightSalts : SaltTape (Salt := Salt) hidden)
      (left right : Fin hidden),
      point rest left (leftSalts left) =
        point rest right (rightSalts right) → left = right)
    (hproof : ∀ rest leftSalts rightSalts oracle,
      let left := pointFamily point rest leftSalts
      let right := pointFamily point rest rightSalts
      let hleft : Injective left := fun _ _ heq =>
        hindexCross rest leftSalts leftSalts _ _ heq
      let hright : Injective right := fun _ _ heq =>
        hindexCross rest rightSalts rightSalts _ _ heq
      let hcross : ∀ leftIndex rightIndex,
          left leftIndex = right rightIndex → leftIndex = rightIndex :=
        fun _ _ heq => hindexCross rest leftSalts rightSalts _ _ heq
      proof rest rightSalts
          (PairedOracleReplacement.renameOracle left right hleft hright hcross
            oracle) =
        proof rest leftSalts oracle)
    (coins : ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength)
    (hhit : PostHit point proof nextQuery coins.2) :
    DummyHit point proof nextQuery coins ∨
      DummyHit point proof nextQuery
        (saltOracleSwap point hindexCross coins) := by
  classical
  let dummy := coins.1
  let actual := coins.2.1
  let rest := coins.2.2.1
  let oracle := coins.2.2.2
  let left := pointFamily point rest actual
  let right := pointFamily point rest dummy
  let hleft : Injective left := fun _ _ heq =>
    hindexCross rest actual actual _ _ heq
  let hright : Injective right := fun _ _ heq =>
    hindexCross rest dummy dummy _ _ heq
  let hcross : ∀ leftIndex rightIndex,
      left leftIndex = right rightIndex → leftIndex = rightIndex :=
    fun _ _ heq => hindexCross rest actual dummy _ _ heq
  let movedOracle := PairedOracleReplacement.renameOracle left right hleft
    hright hcross oracle
  have hproofEq : proof rest dummy movedOracle = proof rest actual oracle := by
    exact hproof rest actual dummy oracle
  have hoff : ∀ query,
      (∀ index, query ≠ left index) →
      (∀ index, query ≠ right index) →
      movedOracle query = oracle query := by
    intro query hleftOff hrightOff
    exact PairedOracleReplacement.renameOracle_off left right hleft hright
      hcross oracle query hleftOff hrightOff
  have htransport := runQueryValues_hit_transport
    (nextQuery rest (proof rest actual oracle)) left right oracle movedOracle
    (List.ofFn id) [] (by simp [QueryHistoryHits])
    (by simp [QueryHistoryHits]) hoff hhit
  rcases htransport with horiginal | htransported
  · left
    simpa [DummyHit, postHistory, pointFamily, dummy, actual, rest, oracle,
      right] using horiginal
  · right
    rw [← hproofEq] at htransported
    simpa [DummyHit, postHistory, pointFamily, saltOracleSwap, dummy, actual,
      rest, oracle, left, movedOracle] using htransported

/-! ## Averaging the transport over uniform finite coins -/

noncomputable def postHitSet {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength)) :
    Finset (OriginalCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) := by
  classical
  exact Finset.univ.filter fun coins => PostHit point proof nextQuery coins

noncomputable def dummyHitSet {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength)) :
    Finset (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :=
  VeiledFlock.Probability.liftFiberBad
    (Equiv.refl (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength))
    (fun coins => hiddenInputBadAssignments
      (fun site salt => point coins.2.1 site salt)
      (postQueryPointSet point proof nextQuery coins))

noncomputable def liftedPostHitSet {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength)) :
    Finset (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :=
  VeiledFlock.Probability.liftBad
    (Equiv.prodComm
      (SaltTape (Salt := Salt) hidden)
      (OriginalCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength))
    (postHitSet point proof nextQuery)

noncomputable def swappedDummyHitSet {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (hindexCross : ∀ (rest : Rest)
      (leftSalts rightSalts : SaltTape (Salt := Salt) hidden)
      (left right : Fin hidden),
      point rest left (leftSalts left) =
        point rest right (rightSalts right) → left = right) :
    Finset (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) := by
  classical
  exact Finset.univ.filter fun coins =>
    saltOracleSwap point hindexCross coins ∈
      dummyHitSet point proof nextQuery

omit [DecidableEq Salt] [Nonempty Salt] [DecidableEq Rest] [Nonempty Rest] in
theorem mem_postHitSet_iff {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : OriginalCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :
    coins ∈ postHitSet point proof nextQuery ↔
      PostHit point proof nextQuery coins := by
  classical
  simp [postHitSet]

omit [Nonempty Salt] [DecidableEq Rest] [Nonempty Rest] in
theorem mem_dummyHitSet_iff {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :
    coins ∈ dummyHitSet point proof nextQuery ↔
      DummyHit point proof nextQuery coins := by
  classical
  rw [dummyHitSet, VeiledFlock.Probability.mem_liftFiberBad_iff]
  exact (dummyHit_iff_mem_hiddenInputBadAssignments point proof nextQuery
    coins).symm

omit [Nonempty Salt] [Nonempty Rest] in
theorem mem_liftedPostHitSet_iff {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (coins : ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :
    coins ∈ liftedPostHitSet point proof nextQuery ↔
      PostHit point proof nextQuery coins.2 := by
  classical
  rw [liftedPostHitSet, VeiledFlock.Probability.mem_liftBad_iff]
  exact mem_postHitSet_iff point proof nextQuery coins.2

omit [Nonempty Salt] [DecidableEq Rest] [Nonempty Rest] in
theorem mem_swappedDummyHitSet_iff {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (hindexCross : ∀ (rest : Rest)
      (leftSalts rightSalts : SaltTape (Salt := Salt) hidden)
      (left right : Fin hidden),
      point rest left (leftSalts left) =
        point rest right (rightSalts right) → left = right)
    (coins : ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
      maxPointLength) :
    coins ∈ swappedDummyHitSet point proof nextQuery hindexCross ↔
      DummyHit point proof nextQuery
        (saltOracleSwap point hindexCross coins) := by
  classical
  simp [swappedDummyHitSet, mem_dummyHitSet_iff]

omit [DecidableEq Rest] in
/-- Averaging the independent dummy salt over every fixed actual execution
costs at most `hidden * queries / |Salt|`. -/
theorem dummyHitSet_probability_le
    {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (hsaltInjective : ∀ rest site, Injective (point rest site)) :
    ((dummyHitSet point proof nextQuery).card : ℚ) /
        Fintype.card
          (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength) ≤
      (hidden * queries : ℕ) / Fintype.card Salt := by
  classical
  apply VeiledFlock.Probability.liftFiberBad_probability_le
    (Equiv.refl
      (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength))
    (fun coins => hiddenInputBadAssignments
      (fun site salt => point coins.2.1 site salt)
      (postQueryPointSet point proof nextQuery coins))
    ((hidden * queries : ℕ) / Fintype.card Salt)
  intro coins
  have hbase := hiddenInputProbability_le
    (fun site salt => point coins.2.1 site salt)
    (postQueryPointSet point proof nextQuery coins)
    (hsaltInjective coins.2.1)
  calc
    ((hiddenInputBadAssignments
          (fun site salt => point coins.2.1 site salt)
          (postQueryPointSet point proof nextQuery coins)).card : ℚ) /
        Fintype.card (SaltTape (Salt := Salt) hidden) ≤
      (hidden * (postQueryPointSet point proof nextQuery coins).card : ℕ) /
        Fintype.card Salt := by
      simpa only [SaltTape, Nat.cast_mul] using hbase
    _ ≤ (hidden * queries : ℕ) / Fintype.card Salt := by
      gcongr
      exact postQueryPointSet_card_le point proof nextQuery coins

theorem card_swappedDummyHitSet_eq
    {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (hindexCross : ∀ (rest : Rest)
      (leftSalts rightSalts : SaltTape (Salt := Salt) hidden)
      (left right : Fin hidden),
      point rest left (leftSalts left) =
        point rest right (rightSalts right) → left = right) :
    (swappedDummyHitSet point proof nextQuery hindexCross).card =
      (dummyHitSet point proof nextQuery).card := by
  classical
  refine Finset.card_equiv (saltOracleSwap point hindexCross) fun coins => ?_
  simp only [mem_swappedDummyHitSet_iff, mem_dummyHitSet_iff]

theorem liftedPostHitSet_subset_dummy_union
    {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (hindexCross : ∀ (rest : Rest)
      (leftSalts rightSalts : SaltTape (Salt := Salt) hidden)
      (left right : Fin hidden),
      point rest left (leftSalts left) =
        point rest right (rightSalts right) → left = right)
    (hproof : ∀ rest leftSalts rightSalts oracle,
      let left := pointFamily point rest leftSalts
      let right := pointFamily point rest rightSalts
      let hleft : Injective left := fun _ _ heq =>
        hindexCross rest leftSalts leftSalts _ _ heq
      let hright : Injective right := fun _ _ heq =>
        hindexCross rest rightSalts rightSalts _ _ heq
      let hcross : ∀ leftIndex rightIndex,
          left leftIndex = right rightIndex → leftIndex = rightIndex :=
        fun _ _ heq => hindexCross rest leftSalts rightSalts _ _ heq
      proof rest rightSalts
          (PairedOracleReplacement.renameOracle left right hleft hright hcross
            oracle) =
        proof rest leftSalts oracle) :
    ∀ coins,
      coins ∈ liftedPostHitSet point proof nextQuery →
        coins ∈ dummyHitSet point proof nextQuery ∨
          coins ∈ swappedDummyHitSet point proof nextQuery hindexCross := by
  classical
  intro coins hcoins
  have hpost : PostHit point proof nextQuery coins.2 :=
    (mem_liftedPostHitSet_iff point proof nextQuery coins).1 hcoins
  rcases postHit_implies_dummyHit_or_swappedDummyHit point proof nextQuery
      hindexCross hproof coins hpost with horiginal | hswapped
  · exact Or.inl
      ((mem_dummyHitSet_iff point proof nextQuery coins).2 horiginal)
  · exact Or.inr
      ((mem_swappedDummyHitSet_iff point proof nextQuery hindexCross coins).2
        hswapped)

theorem liftedPostHitSet_probability_eq
    {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength)) :
    ((liftedPostHitSet point proof nextQuery).card : ℚ) /
        Fintype.card
          (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength) =
      ((postHitSet point proof nextQuery).card : ℚ) /
        Fintype.card
          (OriginalCoins (Salt := Salt) (Rest := Rest) hidden
            maxPointLength) := by
  classical
  exact VeiledFlock.Probability.liftBad_probability_eq
    (Equiv.prodComm
      (SaltTape (Salt := Salt) hidden)
      (OriginalCoins (Salt := Salt) (Rest := Rest) hidden maxPointLength))
    (postHitSet point proof nextQuery)

/-- Adaptive post-proof discovery of a uniformly salted hidden input is
bounded only after averaging over the actual salt.  The factor two is the
standard two-salt transport loss: one dummy-hit event in the original tape
and one in the measure-preserving transported tape. -/
theorem postHitSet_probability_le_two_mul
    {hidden maxPointLength queries : ℕ}
    (point : Rest → Fin hidden → Salt → BoundedBytes maxPointLength)
    (proof : Rest → SaltTape (Salt := Salt) hidden →
      Oracle maxPointLength → Proof)
    (nextQuery : Rest → Proof → Fin queries →
      List (BoundedBytes maxPointLength × OracleBlock) →
        Option (BoundedBytes maxPointLength))
    (hindexCross : ∀ (rest : Rest)
      (leftSalts rightSalts : SaltTape (Salt := Salt) hidden)
      (left right : Fin hidden),
      point rest left (leftSalts left) =
        point rest right (rightSalts right) → left = right)
    (hsaltInjective : ∀ rest site, Injective (point rest site))
    (hproof : ∀ rest leftSalts rightSalts oracle,
      let left := pointFamily point rest leftSalts
      let right := pointFamily point rest rightSalts
      let hleft : Injective left := fun _ _ heq =>
        hindexCross rest leftSalts leftSalts _ _ heq
      let hright : Injective right := fun _ _ heq =>
        hindexCross rest rightSalts rightSalts _ _ heq
      let hcross : ∀ leftIndex rightIndex,
          left leftIndex = right rightIndex → leftIndex = rightIndex :=
        fun _ _ heq => hindexCross rest leftSalts rightSalts _ _ heq
      proof rest rightSalts
          (PairedOracleReplacement.renameOracle left right hleft hright hcross
            oracle) =
        proof rest leftSalts oracle) :
    ((postHitSet point proof nextQuery).card : ℚ) /
        Fintype.card
          (OriginalCoins (Salt := Salt) (Rest := Rest) hidden
            maxPointLength) ≤
      2 * ((hidden * queries : ℕ) : ℚ) / Fintype.card Salt := by
  classical
  let lifted := liftedPostHitSet point proof nextQuery
  let dummy := dummyHitSet point proof nextQuery
  let swapped := swappedDummyHitSet point proof nextQuery hindexCross
  have hsubset : lifted ⊆ dummy ∪ swapped := by
    intro coins hcoins
    exact Finset.mem_union.mpr
      (liftedPostHitSet_subset_dummy_union point proof nextQuery hindexCross
        hproof coins hcoins)
  have hswappedCard : swapped.card = dummy.card := by
    exact card_swappedDummyHitSet_eq point proof nextQuery hindexCross
  have hcount : lifted.card ≤ 2 * dummy.card := by
    calc
      lifted.card ≤ (dummy ∪ swapped).card := Finset.card_le_card hsubset
      _ ≤ dummy.card + swapped.card := Finset.card_union_le dummy swapped
      _ = 2 * dummy.card := by omega
  have hcountQ : (lifted.card : ℚ) ≤ (2 * dummy.card : ℕ) := by
    exact_mod_cast hcount
  have hdummy := dummyHitSet_probability_le point proof nextQuery
    hsaltInjective
  calc
    ((postHitSet point proof nextQuery).card : ℚ) /
          Fintype.card
            (OriginalCoins (Salt := Salt) (Rest := Rest) hidden
              maxPointLength) =
        (lifted.card : ℚ) /
          Fintype.card
            (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
              maxPointLength) := by
      exact (liftedPostHitSet_probability_eq point proof nextQuery).symm
    _ ≤ ((2 * dummy.card : ℕ) : ℚ) /
          Fintype.card
            (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
              maxPointLength) := by
      gcongr
    _ = 2 * ((dummy.card : ℚ) /
          Fintype.card
            (ExpandedCoins (Salt := Salt) (Rest := Rest) hidden
              maxPointLength)) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ 2 * (((hidden * queries : ℕ) : ℚ) /
          Fintype.card Salt) := by
      gcongr
    _ = 2 * ((hidden * queries : ℕ) : ℚ) /
          Fintype.card Salt := by ring

end VeiledFlock.AdaptiveHiddenInput

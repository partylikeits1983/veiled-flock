import VeiledFlock.Oracle.ProgrammableOracle
import VeiledFlock.Oracle.OracleProgramming
import VeiledFlock.Oracle.UniversalFreshness

/-!
# Salted hidden-Merkle inputs

The simulator replaces witness-dependent initial Merkle material.  A hidden
oracle input is protected by its own fresh 256-bit salt.  This file proves the
finite classical-random-oracle counting lemma for a vector of independent
salts and its adaptive multi-proof composition.
-/

namespace VeiledFlock.MerkleHiding

open Function
open VeiledFlock.ProgrammableOracle

variable {Salt Point : Type*} [Fintype Salt] [DecidableEq Salt]
variable [DecidableEq Point]

/-- Split one coordinate from a finite vector. -/
private def splitCoordinate {count : ℕ} (site : Fin count) :
    (Fin count → Salt) ≃
      (({other : Fin count // other ≠ site} → Salt) × Salt) where
  toFun := fun values => (fun other => values other.1, values site)
  invFun := fun pair other =>
    if h : other = site then pair.2 else pair.1 ⟨other, h⟩
  left_inv := fun values => by
    funext other
    by_cases h : other = site
    · subst other
      simp
    · simp [h]
  right_inv := fun pair => by
    apply Prod.ext
    · funext other
      simp [other.property]
    · simp

/-- Assignments whose selected coordinate belongs to `bad`. -/
noncomputable def coordinateBad {count : ℕ} (site : Fin count)
    (bad : Finset Salt) : Finset (Fin count → Salt) :=
  ((Finset.univ : Finset ({other : Fin count // other ≠ site} → Salt)).product
    bad).map (splitCoordinate site).symm.toEmbedding

omit [DecidableEq Salt] in
theorem mem_coordinateBad_iff {count : ℕ} (site : Fin count)
    (bad : Finset Salt) (values : Fin count → Salt) :
    values ∈ coordinateBad site bad ↔ values site ∈ bad := by
  classical
  simp [coordinateBad, splitCoordinate]

private theorem card_otherCoordinates {count : ℕ} (site : Fin count) :
    Fintype.card {other : Fin count // other ≠ site} = count - 1 := by
  rw [Fintype.card_subtype_compl
    (p := fun other : Fin count => other = site)]
  simp

omit [DecidableEq Salt] in
/-- Fixing one coordinate to a set of `b` values leaves all other coordinates
free, hence exactly `b * |Salt|^(count-1)` assignments. -/
theorem card_coordinateBad {count : ℕ} (site : Fin count)
    (bad : Finset Salt) :
    (coordinateBad site bad).card =
      bad.card * Fintype.card Salt ^ (count - 1) := by
  classical
  simp [coordinateBad,  card_otherCoordinates site,
    Nat.mul_comm]

/-- Salt values that expose one framed hidden input to the adversary's prior
query set. -/
def badSalts (point : Salt → Point) (priorQueries : Finset Point) :
    Finset Salt :=
  badNonces (fun _ : Fin 1 => point) priorQueries

theorem card_badSalts_le (point : Salt → Point)
    (priorQueries : Finset Point) (hinjective : Injective point) :
    (badSalts point priorQueries).card ≤ priorQueries.card := by
  simpa [badSalts] using
    (card_badNonces_le (fun _ : Fin 1 => point) priorQueries
      (fun _ => hinjective))

/-- Independent salt assignments exposing at least one hidden input. -/
noncomputable def hiddenInputBadAssignments {hidden : ℕ}
    (point : Fin hidden → Salt → Point)
    (priorQueries : Finset Point) : Finset (Fin hidden → Salt) :=
  Finset.univ.biUnion fun site =>
    coordinateBad site (badSalts (point site) priorQueries)

theorem mem_hiddenInputBadAssignments_iff {hidden : ℕ}
    (point : Fin hidden → Salt → Point)
    (priorQueries : Finset Point) (salts : Fin hidden → Salt) :
    salts ∈ hiddenInputBadAssignments point priorQueries ↔
      ∃ site, point site (salts site) ∈ priorQueries := by
  classical
  simp [hiddenInputBadAssignments, mem_coordinateBad_iff, badSalts,
    ProgrammableOracle.mem_badNonces_iff]

/-- At most `hidden * queries * |Salt|^(hidden-1)` salt vectors expose a
hidden input. -/
theorem card_hiddenInputBadAssignments_le {hidden : ℕ}
    (point : Fin hidden → Salt → Point)
    (priorQueries : Finset Point)
    (hinjective : ∀ site, Injective (point site)) :
    (hiddenInputBadAssignments point priorQueries).card ≤
      hidden * priorQueries.card * Fintype.card Salt ^ (hidden - 1) := by
  classical
  calc
    (hiddenInputBadAssignments point priorQueries).card ≤
        ∑ site : Fin hidden,
          (coordinateBad site
            (badSalts (point site) priorQueries)).card := by
      simpa [hiddenInputBadAssignments] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin hidden)))
          (t := fun site =>
            coordinateBad site (badSalts (point site) priorQueries)))
    _ = ∑ site : Fin hidden,
          (badSalts (point site) priorQueries).card *
            Fintype.card Salt ^ (hidden - 1) := by
      apply Finset.sum_congr rfl
      intro site _
      exact card_coordinateBad site _
    _ ≤ ∑ _site : Fin hidden,
          priorQueries.card * Fintype.card Salt ^ (hidden - 1) := by
      apply Finset.sum_le_sum
      intro site _
      gcongr
      exact card_badSalts_le (point site) priorQueries (hinjective site)
    _ = hidden * priorQueries.card *
          Fintype.card Salt ^ (hidden - 1) := by
      simp [mul_assoc]

/-- One-proof probability of exposing any independently salted hidden input. -/
theorem hiddenInputProbability_le [Nonempty Salt] {hidden : ℕ}
    (point : Fin hidden → Salt → Point)
    (priorQueries : Finset Point)
    (hinjective : ∀ site, Injective (point site)) :
    ((hiddenInputBadAssignments point priorQueries).card : ℚ) /
        Fintype.card (Fin hidden → Salt) ≤
      (hidden * priorQueries.card : ℚ) / Fintype.card Salt := by
  by_cases hhidden : hidden = 0
  · subst hidden
    norm_num [hiddenInputBadAssignments]
  have hsalt : (0 : ℚ) < Fintype.card Salt := by positivity
  have hcount :
      ((hiddenInputBadAssignments point priorQueries).card : ℚ) ≤
        hidden * priorQueries.card *
          Fintype.card Salt ^ (hidden - 1) := by
    exact_mod_cast
      card_hiddenInputBadAssignments_le point priorQueries hinjective
  have hcard : (Fintype.card (Fin hidden → Salt) : ℚ) =
      Fintype.card Salt ^ hidden := by
    norm_cast
    simp
  rw [hcard]
  have hpow : (0 : ℚ) < (Fintype.card Salt : ℚ) ^ hidden :=
    pow_pos hsalt _
  rw [div_le_iff₀ hpow]
  have hpow_split : (Fintype.card Salt : ℚ) ^ hidden =
      Fintype.card Salt ^ (hidden - 1) * Fintype.card Salt := by
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hhidden
    simp [pow_succ]
  rw [hpow_split]
  field_simp
  nlinarith [hcount]

/-! ## Exact replacement once the salted leaf inputs are fresh -/

section ExactReplacement

variable {Outcome W View : Type*}
variable [Fintype Point] [Fintype Outcome] [DecidableEq Outcome]
variable [Nonempty Outcome] [Nonempty Salt]

abbrev LeafOracle := Point → Outcome

def leafAnswers {hidden : ℕ}
    (point : W → Fin hidden → Salt → Point)
    (witness : W) (salts : Fin hidden → Salt)
    (oracle : LeafOracle (Point := Point) (Outcome := Outcome)) :
    Fin hidden → Outcome :=
  fun site => oracle (point witness site (salts site))

private def swapSaltOracle {hidden : ℕ} :
    ((Fin hidden → Salt) × LeafOracle (Point := Point) (Outcome := Outcome)) ≃
      (LeafOracle (Point := Point) (Outcome := Outcome) ×
        (Fin hidden → Salt)) where
  toFun coins := (coins.2, coins.1)
  invFun coins := (coins.2, coins.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full-coin permutation used for replacing all hidden initial leaves.  The
salt tape is fixed and the random-oracle table is renamed in that salt fiber.
-/
noncomputable def saltedLeafCoinEquiv {hidden : ℕ}
    (point : W → Fin hidden → Salt → Point)
    (left right : W)
    (hinjective : ∀ (witness : W) (salts : Fin hidden → Salt),
      Function.Injective (fun site => point witness site (salts site))) :
    ((Fin hidden → Salt) × LeafOracle (Point := Point) (Outcome := Outcome)) ≃
      ((Fin hidden → Salt) ×
        LeafOracle (Point := Point) (Outcome := Outcome)) :=
  VeiledFlock.Probability.fiberwiseEquiv swapSaltOracle
    (fun salts => VeiledFlock.OracleProgramming.renameOracle
      (fun site => point left site (salts site))
      (fun site => point right site (salts site))
      (hinjective left salts) (hinjective right salts))

omit [Nonempty Outcome] [Nonempty Salt] in
omit [Fintype Salt] [DecidableEq Salt] [Fintype Outcome] [DecidableEq Outcome] in
omit [DecidableEq Point] in
/-- Corresponding salted leaves receive exactly the same oracle answers under
the coin permutation. -/
theorem leafAnswers_saltedLeafCoinEquiv {hidden : ℕ}
    (point : W → Fin hidden → Salt → Point)
    (left right : W)
    (hinjective : ∀ (witness : W) (salts : Fin hidden → Salt),
      Function.Injective (fun site => point witness site (salts site)))
    (coins : (Fin hidden → Salt) ×
      LeafOracle (Point := Point) (Outcome := Outcome)) :
    leafAnswers point right (saltedLeafCoinEquiv point left right hinjective coins).1
        (saltedLeafCoinEquiv point left right hinjective coins).2 =
      leafAnswers point left coins.1 coins.2 := by
  classical
  have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
    swapSaltOracle
    (fun salts => VeiledFlock.OracleProgramming.renameOracle
      (fun site => point left site (salts site))
      (fun site => point right site (salts site))
      (hinjective left salts) (hinjective right salts)) coins
  have hsalt : (saltedLeafCoinEquiv point left right hinjective coins).1 =
      coins.1 := congrArg Prod.snd hsplit
  have horacle : (saltedLeafCoinEquiv point left right hinjective coins).2 =
      VeiledFlock.OracleProgramming.renameOracle
        (fun index => point left index (coins.1 index))
        (fun index => point right index (coins.1 index))
        (hinjective left coins.1) (hinjective right coins.1) coins.2 :=
    congrArg Prod.fst hsplit
  funext site
  simp only [leafAnswers]
  rw [hsalt, horacle]
  exact VeiledFlock.OracleProgramming.renameOracle_at
    (fun index => point left index (coins.1 index))
    (fun index => point right index (coins.1 index))
    (hinjective left coins.1) (hinjective right coins.1) coins.2 site

omit [DecidableEq Salt] [DecidableEq Outcome] in
/-- Perfect hiding of the entire vector of fresh salted leaf hashes.  An
arbitrary deterministic Merkle continuation may depend on the salts and leaf
answers; therefore all internal hashing and the final root are covered once
their inputs are reconstructed from these values. -/
theorem saltedLeafReplacement_exact {hidden : ℕ}
    (point : W → Fin hidden → Salt → Point)
    (hinjective : ∀ (witness : W) (salts : Fin hidden → Salt),
      Function.Injective (fun site => point witness site (salts site)))
    (continueWith : (Fin hidden → Salt) → (Fin hidden → Outcome) → View)
    (left right : W) :
    (PMF.uniformOfFintype
      ((Fin hidden → Salt) ×
        LeafOracle (Point := Point) (Outcome := Outcome))).map
        (fun coins => continueWith coins.1
          (leafAnswers point left coins.1 coins.2)) =
      (PMF.uniformOfFintype
        ((Fin hidden → Salt) ×
          LeafOracle (Point := Point) (Outcome := Outcome))).map
          (fun coins => continueWith coins.1
            (leafAnswers point right coins.1 coins.2)) := by
  apply VeiledFlock.Probability.uniform_map_eq_of_equiv
    (saltedLeafCoinEquiv point left right hinjective)
  intro coins
  have hsalt : (saltedLeafCoinEquiv point left right hinjective coins).1 =
      coins.1 := by
    have hsplit := VeiledFlock.Probability.fiberwiseEquiv_split_apply
      swapSaltOracle
      (fun salts => VeiledFlock.OracleProgramming.renameOracle
        (fun site => point left site (salts site))
        (fun site => point right site (salts site))
        (hinjective left salts) (hinjective right salts)) coins
    exact congrArg Prod.snd hsplit
  rw [hsalt]
  exact congrArg (continueWith coins.1)
    (leafAnswers_saltedLeafCoinEquiv point left right hinjective coins).symm

/-- Join already-observed oracle points with fresh salted-leaf inputs. -/
def combinedPoints {Prior Leaf : Type*}
    (prior : Prior → Point) (leaf : Leaf → Point) : Prior ⊕ Leaf → Point :=
  Sum.elim prior leaf

omit [DecidableEq Point] [Fintype Point] in
theorem combinedPoints_injective {Prior Leaf : Type*}
    (prior : Prior → Point) (leaf : Leaf → Point)
    (hprior : Function.Injective prior)
    (hleaf : Function.Injective leaf)
    (hdisjoint : ∀ priorIndex leafIndex,
      prior priorIndex ≠ leaf leafIndex) :
    Function.Injective (combinedPoints prior leaf) := by
  intro left right heq
  cases left with
  | inl leftPrior =>
      cases right with
      | inl rightPrior => exact congrArg Sum.inl (hprior heq)
      | inr rightLeaf => exact False.elim (hdisjoint leftPrior rightLeaf heq)
  | inr leftLeaf =>
      cases right with
      | inl rightPrior =>
          exact False.elim (hdisjoint rightPrior leftLeaf heq.symm)
      | inr rightLeaf => exact congrArg Sum.inr (hleaf heq)

/-- Exact salted-leaf replacement while preserving a complete vector of
earlier oracle answers.  The no-prequery good event supplies `hdisjoint`; the
counting theorem above bounds its complement. -/
theorem saltedLeafReplacement_withPrior_exact
    {hidden : ℕ} {Prior : Type*} [Fintype Prior]
    (priorPoint : (Fin hidden → Salt) → Prior → Point)
    (leafPoint : W → (Fin hidden → Salt) → Fin hidden → Point)
    (hprior : ∀ salts, Function.Injective (priorPoint salts))
    (hleaf : ∀ witness salts,
      Function.Injective (leafPoint witness salts))
    (hdisjoint : ∀ witness salts priorIndex leafIndex,
      priorPoint salts priorIndex ≠ leafPoint witness salts leafIndex)
    (continueWith : (Fin hidden → Salt) →
      (Prior → Outcome) → (Fin hidden → Outcome) → View)
    (left right : W) :
    (PMF.uniformOfFintype
      ((Fin hidden → Salt) ×
        LeafOracle (Point := Point) (Outcome := Outcome))).map
        (fun coins => continueWith coins.1
          (fun priorIndex => coins.2 (priorPoint coins.1 priorIndex))
          (fun leafIndex => coins.2 (leafPoint left coins.1 leafIndex))) =
      (PMF.uniformOfFintype
        ((Fin hidden → Salt) ×
          LeafOracle (Point := Point) (Outcome := Outcome))).map
          (fun coins => continueWith coins.1
            (fun priorIndex => coins.2 (priorPoint coins.1 priorIndex))
            (fun leafIndex => coins.2 (leafPoint right coins.1 leafIndex))) := by
  let leftPoints := fun salts =>
    combinedPoints (priorPoint salts) (leafPoint left salts)
  let rightPoints := fun salts =>
    combinedPoints (priorPoint salts) (leafPoint right salts)
  have hleft : ∀ salts, Function.Injective (leftPoints salts) := by
    intro salts
    exact combinedPoints_injective _ _ (hprior salts) (hleaf left salts)
      (hdisjoint left salts)
  have hright : ∀ salts, Function.Injective (rightPoints salts) := by
    intro salts
    exact combinedPoints_injective _ _ (hprior salts) (hleaf right salts)
      (hdisjoint right salts)
  exact VeiledFlock.OracleProgramming.fiberwiseFreshFamilyReplacement_exact
    leftPoints rightPoints hleft hright
    (fun salts answers => continueWith salts
      (fun priorIndex => answers (Sum.inl priorIndex))
      (fun leafIndex => answers (Sum.inr leafIndex)))

end ExactReplacement

section Adaptive

variable [Nonempty Salt]

/-- Adaptive multi-proof Merkle-hiding bound.  Both the framed hidden inputs
and the adversary's prior queries may depend on the full prior salt-vector
history. -/
theorem adaptiveHiddenInputProbability_le
    (proofs hidden queries : ℕ)
    (point : List (Fin hidden → Salt) → Fin hidden → Salt → Point)
    (priorQueries : List (Fin hidden → Salt) → Finset Point)
    (hinjective : ∀ history site, Injective (point history site))
    (hqueries : ∀ history, (priorQueries history).card ≤ queries) :
    ((Finset.univ.filter fun assignments =>
      runFails
        (fun history => hiddenInputBadAssignments
          (point history) (priorQueries history))
        [] proofs assignments = true).card : ℚ) /
        Fintype.card (Fin proofs → (Fin hidden → Salt)) ≤
      (proofs * hidden * queries : ℚ) / Fintype.card Salt := by
  by_cases hhidden : hidden = 0
  · subst hidden
    have hnever : ∀ (rounds : ℕ) (history : List (Fin 0 → Salt))
        (assignments : Fin rounds → (Fin 0 → Salt)),
        runFails (fun _ => ∅) history rounds assignments = false := by
      intro rounds
      induction rounds with
      | zero => simp [runFails]
      | succ rounds ih =>
          intro history assignments
          simp [runFails, ih]
    norm_num [hiddenInputBadAssignments, hnever]
  let perProof := hidden * queries * Fintype.card Salt ^ (hidden - 1)
  have hbad : ∀ history,
      (hiddenInputBadAssignments (point history)
        (priorQueries history)).card ≤ perProof := by
    intro history
    exact (card_hiddenInputBadAssignments_le
      (point history) (priorQueries history) (hinjective history)).trans
        (by
          dsimp [perProof]
          gcongr
          exact hqueries history)
  have hadaptive := adaptiveCollisionProbability_le
    (Nonce := Fin hidden → Salt)
    (fun history => hiddenInputBadAssignments
      (point history) (priorQueries history))
    perProof proofs hbad
  have hcard : Fintype.card (Fin hidden → Salt) =
      Fintype.card Salt ^ hidden := by simp
  have hsalt : (0 : ℚ) < Fintype.card Salt := by positivity
  have hpow_split : (Fintype.card Salt : ℚ) ^ hidden =
      Fintype.card Salt ^ (hidden - 1) * Fintype.card Salt := by
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hhidden
    simp [pow_succ]
  have hrhs :
      (proofs : ℚ) * (perProof : ℚ) /
          Fintype.card (Fin hidden → Salt) =
        (proofs * hidden * queries : ℚ) / Fintype.card Salt := by
    dsimp [perProof]
    rw [hcard]
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    rw [hpow_split]
    field_simp
  exact hadaptive.trans_eq hrhs

end Adaptive

/-! ## Payload-universal hidden-input counting -/

section UniversalContext

variable {Context : Type*}

/-- Hidden salt assignments that expose a framed point for at least one site
and at least one counterfactual payload/transcript suffix. -/
noncomputable def universalHiddenInputBadAssignments {hidden : ℕ}
    (point : Fin hidden → Salt → Context → Point)
    (priorQueries : Finset Point) : Finset (Fin hidden → Salt) :=
  Finset.univ.biUnion fun site =>
    coordinateBad site
      (VeiledFlock.UniversalFreshness.badNonces
        (fun _ : Fin 1 => point site) priorQueries)

omit [DecidableEq Point] in
theorem mem_universalHiddenInputBadAssignments_iff {hidden : ℕ}
    (point : Fin hidden → Salt → Context → Point)
    (priorQueries : Finset Point) (salts : Fin hidden → Salt) :
    salts ∈ universalHiddenInputBadAssignments point priorQueries ↔
      ∃ site context, point site (salts site) context ∈ priorQueries := by
  classical
  simp [universalHiddenInputBadAssignments, mem_coordinateBad_iff,
    VeiledFlock.UniversalFreshness.mem_badNonces_iff]

/-- Quantifying over every counterfactual suffix has no cardinality cost:
at a fixed site and prior point, cross-context injectivity recovers at most
one salt. -/
theorem card_universalHiddenInputBadAssignments_le {hidden : ℕ}
    (point : Fin hidden → Salt → Context → Point)
    (priorQueries : Finset Point)
    (hcross : ∀ site leftSalt leftContext rightSalt rightContext,
      point site leftSalt leftContext = point site rightSalt rightContext →
        leftSalt = rightSalt) :
    (universalHiddenInputBadAssignments point priorQueries).card ≤
      hidden * priorQueries.card * Fintype.card Salt ^ (hidden - 1) := by
  classical
  calc
    (universalHiddenInputBadAssignments point priorQueries).card ≤
        ∑ site : Fin hidden,
          (coordinateBad site
            (VeiledFlock.UniversalFreshness.badNonces
              (fun _ : Fin 1 => point site) priorQueries)).card := by
      simpa [universalHiddenInputBadAssignments] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin hidden)))
          (t := fun site => coordinateBad site
            (VeiledFlock.UniversalFreshness.badNonces
              (fun _ : Fin 1 => point site) priorQueries)))
    _ = ∑ site : Fin hidden,
          (VeiledFlock.UniversalFreshness.badNonces
              (fun _ : Fin 1 => point site) priorQueries).card *
            Fintype.card Salt ^ (hidden - 1) := by
      apply Finset.sum_congr rfl
      intro site _
      exact card_coordinateBad site _
    _ ≤ ∑ _site : Fin hidden,
          priorQueries.card * Fintype.card Salt ^ (hidden - 1) := by
      apply Finset.sum_le_sum
      intro site _
      gcongr
      exact (VeiledFlock.UniversalFreshness.card_badNonces_le
        (fun _ : Fin 1 => point site) priorQueries
        (fun _ => hcross site)).trans (by simp)
    _ = hidden * priorQueries.card *
          Fintype.card Salt ^ (hidden - 1) := by
      simp [mul_assoc]

theorem universalHiddenInputProbability_le [Nonempty Salt] {hidden : ℕ}
    (point : Fin hidden → Salt → Context → Point)
    (priorQueries : Finset Point)
    (hcross : ∀ site leftSalt leftContext rightSalt rightContext,
      point site leftSalt leftContext = point site rightSalt rightContext →
        leftSalt = rightSalt) :
    ((universalHiddenInputBadAssignments point priorQueries).card : ℚ) /
        Fintype.card (Fin hidden → Salt) ≤
      (hidden * priorQueries.card : ℚ) / Fintype.card Salt := by
  by_cases hhidden : hidden = 0
  · subst hidden
    norm_num [universalHiddenInputBadAssignments]
  have hsalt : (0 : ℚ) < Fintype.card Salt := by positivity
  have hcount :
      ((universalHiddenInputBadAssignments point priorQueries).card : ℚ) ≤
        hidden * priorQueries.card *
          Fintype.card Salt ^ (hidden - 1) := by
    exact_mod_cast card_universalHiddenInputBadAssignments_le point
      priorQueries hcross
  have hcard : (Fintype.card (Fin hidden → Salt) : ℚ) =
      Fintype.card Salt ^ hidden := by
    norm_cast
    simp
  rw [hcard]
  have hpow : (0 : ℚ) < (Fintype.card Salt : ℚ) ^ hidden :=
    pow_pos hsalt _
  rw [div_le_iff₀ hpow]
  have hpow_split : (Fintype.card Salt : ℚ) ^ hidden =
      Fintype.card Salt ^ (hidden - 1) * Fintype.card Salt := by
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hhidden
    simp [pow_succ]
  rw [hpow_split]
  field_simp
  exact hcount

end UniversalContext

end VeiledFlock.MerkleHiding

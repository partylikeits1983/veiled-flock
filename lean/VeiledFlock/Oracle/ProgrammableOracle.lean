import Flockzk.MaskingMixture
import Mathlib

/-!
# Programmable-random-oracle freshness

The Rust simulator refuses to program any point that was queried or defined
earlier.  Every programmed point contains the proof's fresh 256-bit nonce in
an injective transcript frame.  This file proves the finite counting argument
behind that check: for `p` injectively nonce-framed programming sites and any
set of `q` prior oracle queries, at most `p*q` nonces collide.
-/

namespace VeiledFlock.ProgrammableOracle

open Function

variable {Nonce Point : Type*} [Fintype Nonce] [DecidableEq Nonce]
variable [DecidableEq Point]

/-- Nonces for which at least one planned programming point is already in the
set of prior oracle queries. -/
def badNonces {programmed : ℕ}
    (programPoint : Fin programmed → Nonce → Point)
    (priorQueries : Finset Point) : Finset Nonce :=
  Finset.univ.filter fun nonce =>
    ∃ site : Fin programmed, programPoint site nonce ∈ priorQueries

theorem mem_badNonces_iff {programmed : ℕ}
    (programPoint : Fin programmed → Nonce → Point)
    (priorQueries : Finset Point) (nonce : Nonce) :
    nonce ∈ badNonces programPoint priorQueries ↔
      ∃ site, programPoint site nonce ∈ priorQueries := by
  simp [badNonces]

/-- Outside the counted bad set, the complete programming family is disjoint
from the prior-query set. -/
theorem range_disjoint_prior_of_nonce_not_bad {programmed : ℕ}
    (programPoint : Fin programmed → Nonce → Point)
    (priorQueries : Finset Point) (nonce : Nonce)
    (hgood : nonce ∉ badNonces programPoint priorQueries) :
    Set.range (fun site => programPoint site nonce) ∩
      (priorQueries : Set Point) = ∅ := by
  ext point
  constructor
  · rintro ⟨⟨site, rfl⟩, hprior⟩
    exact False.elim (hgood ((mem_badNonces_iff
      programPoint priorQueries nonce).2 ⟨site, hprior⟩))
  · intro h
    exact False.elim (by simpa using h)

/-- Injective nonce framing gives the exact `programmed * queries` union
bound on programming collisions. -/
theorem card_badNonces_le {programmed : ℕ}
    (programPoint : Fin programmed → Nonce → Point)
    (priorQueries : Finset Point)
    (hinjective : ∀ site, Injective (programPoint site)) :
    (badNonces programPoint priorQueries).card ≤
      programmed * priorQueries.card := by
  classical
  let fiber : Fin programmed → Finset Nonce := fun site =>
    Finset.univ.filter fun nonce => programPoint site nonce ∈ priorQueries
  have hsubset : badNonces programPoint priorQueries ⊆
      Finset.univ.biUnion fiber := by
    intro nonce hnonce
    rw [badNonces, Finset.mem_filter] at hnonce
    obtain ⟨site, hsite⟩ := hnonce.2
    rw [Finset.mem_biUnion]
    exact ⟨site, Finset.mem_univ _, by
      change nonce ∈ Finset.univ.filter fun value =>
        programPoint site value ∈ priorQueries
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hsite⟩⟩
  have hfiber : ∀ site : Fin programmed,
      (fiber site).card ≤ priorQueries.card := by
    intro site
    calc
      (fiber site).card = ((fiber site).image (programPoint site)).card := by
        symm
        exact Finset.card_image_iff.mpr fun left _ right _ heq =>
          hinjective site heq
      _ ≤ priorQueries.card := by
        apply Finset.card_le_card
        intro point hpoint
        obtain ⟨nonce, hnonce, rfl⟩ := Finset.mem_image.mp hpoint
        change nonce ∈ Finset.univ.filter (fun value =>
          programPoint site value ∈ priorQueries) at hnonce
        rw [Finset.mem_filter] at hnonce
        exact hnonce.2
  calc
    (badNonces programPoint priorQueries).card ≤
        (Finset.univ.biUnion fiber).card := Finset.card_le_card hsubset
    _ ≤ ∑ site ∈ (Finset.univ : Finset (Fin programmed)),
        (fiber site).card := Finset.card_biUnion_le
    _ ≤ ∑ _site ∈ (Finset.univ : Finset (Fin programmed)),
        priorQueries.card := Finset.sum_le_sum fun site _ => hfiber site
    _ = programmed * priorQueries.card := by simp

/-- Probability form of `card_badNonces_le` for a uniform nonce. -/
theorem collisionProbability_le {programmed : ℕ}
    (programPoint : Fin programmed → Nonce → Point)
    (priorQueries : Finset Point)
    (hinjective : ∀ site, Injective (programPoint site)) :
    ((badNonces programPoint priorQueries).card : ℚ) /
        Fintype.card Nonce ≤
      (programmed * priorQueries.card : ℚ) / Fintype.card Nonce := by
  gcongr
  exact_mod_cast card_badNonces_le programPoint priorQueries hinjective

/-- The exact nonce space used by the implementation. -/
abbrev Nonce256 := Fin (2 ^ 256)

/-- Concrete classical pROM bound for one proof with a fresh 256-bit nonce. -/
theorem collisionProbability_256_le {Point : Type*} [DecidableEq Point]
    {programmed : ℕ}
    (programPoint : Fin programmed → Nonce256 → Point)
    (priorQueries : Finset Point)
    (hinjective : ∀ site, Injective (programPoint site)) :
    ((badNonces programPoint priorQueries).card : ℚ) / (2 ^ 256 : ℕ) ≤
      (programmed * priorQueries.card : ℚ) / (2 ^ 256 : ℕ) := by
  simpa only [Fintype.card_fin] using
    collisionProbability_le programPoint priorQueries hinjective

section Adaptive

variable [Nonempty Nonce]

/-- Whether a sequence of fresh nonces hits a history-dependent bad set at
any proof.  The bad set for the next proof may depend on the complete prior
nonce history, which captures adaptive sequential composition. -/
def runFails (badAt : List Nonce → Finset Nonce) (history : List Nonce) :
    (rounds : ℕ) → (Fin rounds → Nonce) → Bool
  | 0, _ => false
  | rounds + 1, nonces =>
      decide (nonces 0 ∈ badAt history) ||
        runFails badAt (history ++ [nonces 0]) rounds
          (fun site => nonces site.succ)

/-- Split a nonce vector into its tail and first element. -/
private def splitFirst (rounds : ℕ) :
    (Fin (rounds + 1) → Nonce) ≃ ((Fin rounds → Nonce) × Nonce) where
  toFun nonces := (fun site => nonces site.succ, nonces 0)
  invFun pair := Fin.cases pair.2 pair.1
  left_inv nonces := by
    funext site
    refine Fin.cases ?_ (fun tailSite => ?_) site <;> rfl
  right_inv pair := by
    apply Prod.ext
    · funext site
      rfl
    · rfl

@[simp]
private theorem splitFirst_symm_zero (rounds : ℕ)
    (pair : (Fin rounds → Nonce) × Nonce) :
    (splitFirst rounds).symm pair 0 = pair.2 := rfl

@[simp]
private theorem splitFirst_symm_succ (rounds : ℕ)
    (pair : (Fin rounds → Nonce) × Nonce) (site : Fin rounds) :
    (splitFirst rounds).symm pair site.succ = pair.1 site := rfl

private theorem card_runFails_succ
    (badAt : List Nonce → Finset Nonce) (history : List Nonce)
    (rounds : ℕ) :
    (Finset.univ.filter fun nonces =>
      runFails badAt history (rounds + 1) nonces = true).card =
      ∑ first : Nonce,
        (Finset.univ.filter fun tail : Fin rounds → Nonce =>
          first ∈ badAt history ∨
            runFails badAt (history ++ [first]) rounds tail = true).card := by
  classical
  calc
    (Finset.univ.filter fun nonces =>
        runFails badAt history (rounds + 1) nonces = true).card =
        (Finset.univ.filter fun pair : (Fin rounds → Nonce) × Nonce =>
          runFails badAt history (rounds + 1)
            ((splitFirst rounds).symm pair) = true).card := by
      refine Finset.card_equiv (splitFirst rounds) fun nonces => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    _ = ∑ first : Nonce,
        (Finset.univ.filter fun tail : Fin rounds → Nonce =>
          first ∈ badAt history ∨
            runFails badAt (history ++ [first]) rounds tail = true).card := by
      simpa only [runFails, splitFirst_symm_zero, splitFirst_symm_succ,
        Bool.or_eq_true, decide_eq_true_eq] using
        (FlockZk.card_filter_prod_eq_sum
          (g := fun tail first =>
            decide (first ∈ badAt history ∨
              runFails badAt (history ++ [first]) rounds tail = true)) true)

/-- Adaptive union bound.  If every history leaves at most `perProof` bad
nonces for the next proof, then among all `rounds`-nonce executions at most
`rounds * perProof * |Nonce|^(rounds-1)` ever hit a bad set. -/
theorem card_adaptive_runFails_le
    (badAt : List Nonce → Finset Nonce) (perProof : ℕ)
    (hbad : ∀ history, (badAt history).card ≤ perProof)
    (history : List Nonce) (rounds : ℕ) :
    (Finset.univ.filter fun nonces =>
      runFails badAt history rounds nonces = true).card ≤
      rounds * perProof * Fintype.card Nonce ^ (rounds - 1) := by
  classical
  induction rounds generalizing history with
  | zero => simp [runFails]
  | succ rounds ih =>
      rw [card_runFails_succ]
      have hslices : ∀ first : Nonce,
          (Finset.univ.filter fun tail : Fin rounds → Nonce =>
              first ∈ badAt history ∨
                runFails badAt (history ++ [first]) rounds tail = true).card ≤
            (if first ∈ badAt history then
                Fintype.card Nonce ^ rounds else 0) +
              rounds * perProof * Fintype.card Nonce ^ (rounds - 1) := by
        intro first
        by_cases hfirst : first ∈ badAt history
        · simp only [hfirst, true_or, Finset.filter_true, Finset.card_univ,
            Fintype.card_fun, Fintype.card_fin, if_pos]
          omega
        · simpa [hfirst] using
            ih (history ++ [first])
      calc
        ∑ first : Nonce,
            (Finset.univ.filter fun tail : Fin rounds → Nonce =>
              first ∈ badAt history ∨
                runFails badAt (history ++ [first]) rounds tail = true).card
          ≤ ∑ first : Nonce,
              ((if first ∈ badAt history then
                  Fintype.card Nonce ^ rounds else 0) +
                rounds * perProof * Fintype.card Nonce ^ (rounds - 1)) :=
            Finset.sum_le_sum fun first _ => hslices first
        _ = (badAt history).card * Fintype.card Nonce ^ rounds +
              Fintype.card Nonce *
                (rounds * perProof * Fintype.card Nonce ^ (rounds - 1)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            congr 1
            rw [← Finset.sum_filter]
            simp
        _ ≤ perProof * Fintype.card Nonce ^ rounds +
              Fintype.card Nonce *
                (rounds * perProof * Fintype.card Nonce ^ (rounds - 1)) := by
            gcongr
            exact hbad history
        _ = (rounds + 1) * perProof *
              Fintype.card Nonce ^ ((rounds + 1) - 1) := by
            cases rounds with
            | zero => simp
            | succ rounds =>
                simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
                  Nat.add_sub_cancel_left, pow_succ]
                ring

/-- Probability form of the adaptive multi-proof freshness bound. -/
theorem adaptiveCollisionProbability_le
    (badAt : List Nonce → Finset Nonce) (perProof rounds : ℕ)
    (hbad : ∀ history, (badAt history).card ≤ perProof) :
    ((Finset.univ.filter fun nonces =>
      runFails badAt [] rounds nonces = true).card : ℚ) /
        Fintype.card (Fin rounds → Nonce) ≤
      (rounds * perProof : ℚ) / Fintype.card Nonce := by
  have hcount := card_adaptive_runFails_le badAt perProof hbad [] rounds
  by_cases hrounds : rounds = 0
  · subst rounds
    norm_num [runFails]
  have hnonce : (0 : ℚ) < Fintype.card Nonce := by positivity
  have hcard : (Fintype.card (Fin rounds → Nonce) : ℚ) =
      Fintype.card Nonce ^ rounds := by
    norm_cast
    simp [Fintype.card_fun]
  rw [hcard]
  have hpow : (0 : ℚ) < (Fintype.card Nonce : ℚ) ^ rounds := pow_pos hnonce _
  rw [div_le_iff₀ hpow]
  have hcountQ :
      ((Finset.univ.filter fun nonces =>
        runFails badAt [] rounds nonces = true).card : ℚ) ≤
        rounds * perProof * Fintype.card Nonce ^ (rounds - 1) := by
    exact_mod_cast hcount
  have hpow_split : (Fintype.card Nonce : ℚ) ^ rounds =
      Fintype.card Nonce ^ (rounds - 1) * Fintype.card Nonce := by
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrounds
    simp [pow_succ]
  rw [hpow_split]
  field_simp
  nlinarith [hcountQ]

/-- Concrete adaptive classical-pROM bound used by VEIL--FLOCK.  At every
history there are `programmed` injectively nonce-framed sites and at most
`queries` prior adversarial oracle queries.  Across `proofs` sequential proofs,
the programming-collision probability is at most
`proofs * programmed * queries / 2^256`. -/
theorem adaptiveProgrammingCollision256_le
    {Point : Type*} [DecidableEq Point]
    (proofs programmed queries : ℕ)
    (programPoint : List Nonce256 → Fin programmed → Nonce256 → Point)
    (priorQueries : List Nonce256 → Finset Point)
    (hinjective : ∀ history site, Injective (programPoint history site))
    (hqueries : ∀ history, (priorQueries history).card ≤ queries) :
    ((Finset.univ.filter fun nonces =>
      runFails
        (fun history => badNonces (programPoint history) (priorQueries history))
        [] proofs nonces = true).card : ℚ) /
        Fintype.card (Fin proofs → Nonce256) ≤
      (proofs * programmed * queries : ℚ) / (2 ^ 256 : ℕ) := by
  have hbad : ∀ history,
      (badNonces (programPoint history) (priorQueries history)).card ≤
        programmed * queries := by
    intro history
    exact (card_badNonces_le (programPoint history) (priorQueries history)
      (hinjective history)).trans
        (Nat.mul_le_mul_left programmed (hqueries history))
  simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
    mul_assoc] using
    (adaptiveCollisionProbability_le
      (Nonce := Nonce256)
      (fun history => badNonces (programPoint history) (priorQueries history))
      (programmed * queries) proofs hbad)

end Adaptive

end VeiledFlock.ProgrammableOracle

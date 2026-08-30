import Flockzk.ConditionalReplacement
import VeiledFlock.Algebra.AlgebraicProtocol
import VeiledFlock.Oracle.ProgrammableOracle

/-!
# End-to-end finite-game composition

This file states zero knowledge as total-variation distance between the full
views induced by uniform finite coins.  It proves the two game transformations
used by VEIL--FLOCK:

1. an explicit bijection may reparameterize all honest coins at zero cost;
2. if the reparameterized real and simulated views agree unless a bad event
   occurs, their total-variation distance is at most the bad-event mass.

Together, these make the algebraic bijection and pROM freshness theorem
composable without an informal appeal to a hybrid argument.
-/

namespace VeiledFlock.EndToEnd

open Function

variable {Coins View : Type*}
variable [Fintype Coins] [Nonempty Coins]
variable [Fintype View] [DecidableEq View]

/-- Exact mass of one view under uniform finite coins.  The inert `Unit`
factor makes this definition line up definitionally with the generic mixture
lemma used below; its cardinality is one. -/
def uniformFiberMass (viewFn : Coins → View) (view : View) : ℚ :=
  (((Finset.univ : Finset (Unit × Coins)).filter fun coins =>
    viewFn coins.2 = view).card : ℚ) /
    ((Fintype.card Unit : ℚ) * Fintype.card Coins)

/-- Total-variation distance between two views of the same uniform finite coin
space, written directly as exact rational fiber counts. -/
def uniformTV (left right : Coins → View) : ℚ :=
  (1 / 2 : ℚ) * ∑ view : View,
    abs (uniformFiberMass left view - uniformFiberMass right view)

/-- Reparameterizing uniform coins through a bijection has zero statistical
cost. -/
theorem uniformTV_reparameterize_left (equiv : Coins ≃ Coins)
    (left right : Coins → View) :
    uniformTV (left ∘ equiv) right = uniformTV left right := by
  have hfiber : ∀ view : View,
      ((Finset.univ : Finset (Unit × Coins)).filter fun coins =>
        (left ∘ equiv) coins.2 = view).card =
      ((Finset.univ : Finset (Unit × Coins)).filter fun coins =>
        left coins.2 = view).card := by
    intro view
    refine Finset.card_equiv
      (Equiv.prodCongr (Equiv.refl Unit) equiv) fun coins => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, comp_apply]
    rfl
  simp only [uniformTV, uniformFiberMass]
  congr 1
  apply Finset.sum_congr rfl
  intro view _
  rw [hfiber view]

theorem uniformTV_comm (left right : Coins → View) :
    uniformTV left right = uniformTV right left := by
  unfold uniformTV
  congr 1
  apply Finset.sum_congr rfl
  intro view _
  rw [← abs_neg]
  congr 2 <;> ring

/-- Uniform reparameterization is equally valid on the simulator side. -/
theorem uniformTV_reparameterize_right (equiv : Coins ≃ Coins)
    (left right : Coins → View) :
    uniformTV left (right ∘ equiv) = uniformTV left right := by
  rw [uniformTV_comm, uniformTV_reparameterize_left, uniformTV_comm]

set_option maxHeartbeats 800000 in
/-- Conditional replacement: two full views that agree outside `bad` have
total-variation distance at most the uniform mass of `bad`. -/
theorem conditionalReplacementTV (left right : Coins → View)
    (bad : Finset Coins)
    (hsame : ∀ coins, coins ∉ bad → left coins = right coins) :
    uniformTV left right ≤ (bad.card : ℚ) / Fintype.card Coins := by
  let transcript : Bool → Unit → Coins → View := fun side _ coins =>
    if side then right coins else left coins
  have hgood : ∀ side₁ side₂ : Bool, () = () →
      ∀ coins, coins ∉ bad → ∀ view : View,
        (Finset.univ.filter fun _unit : Unit =>
          transcript side₁ _unit coins = view).card =
        (Finset.univ.filter fun _unit : Unit =>
          transcript side₂ _unit coins = view).card := by
    intro side₁ side₂ _ coins hcoins view
    cases side₁ <;> cases side₂ <;> simp [transcript, hsame coins hcoins]
  have h := FlockZk.mixture_tv_bad_set transcript (fun _ : Bool => ()) bad
    hgood (w := false) (w' := true) rfl
  simpa only [uniformTV, uniformFiberMass, transcript, Bool.false_eq_true,
    if_false, if_true]
    using h

/-! ## Total variation for arbitrary complete-view types

`ProductionView` contains finite query histories represented by `List`, so
its ambient type is intentionally not finite even though a bounded experiment
has finite support.  The following definition sums over exactly that finite
support.  It is the ordinary total-variation distance of the two pushforward
uniform distributions, without imposing a false `Fintype ProductionView`
assumption. -/

section FiniteSupport

variable {Output : Type*} [DecidableEq Output]

/-- Union of the supports of two deterministic experiments over a finite
uniform coin space. -/
def uniformSupport (left right : Coins → Output) : Finset Output :=
  Finset.univ.image left ∪ Finset.univ.image right

/-- The left experiment, with its output restricted to the common finite
support. -/
def supportedLeft (left right : Coins → Output) (coins : Coins) :
    {view // view ∈ uniformSupport left right} :=
  ⟨left coins, by simp [uniformSupport]⟩

/-- The right experiment, with its output restricted to the common finite
support. -/
def supportedRight (left right : Coins → Output) (coins : Coins) :
    {view // view ∈ uniformSupport left right} :=
  ⟨right coins, by simp [uniformSupport]⟩

/-- Exact total-variation distance of two finite-support pushforward
distributions.  The result remains meaningful when `View` itself is infinite. -/
noncomputable def finiteSupportTV (left right : Coins → Output) : ℚ := by
  classical
  exact (1 / 2 : ℚ) * ∑ view ∈ uniformSupport left right,
    abs (uniformFiberMass left view - uniformFiberMass right view)

/-- The standard coupling inequality specialized to a deterministic coupling
of two uniformly sampled finite coin experiments. -/
theorem finiteSupportTV_le_badProbability (left right : Coins → Output)
    (bad : Finset Coins)
    (hsame : ∀ coins, coins ∉ bad → left coins = right coins) :
    finiteSupportTV left right ≤ (bad.card : ℚ) / Fintype.card Coins := by
  classical
  have hrepresentation :
      finiteSupportTV left right =
        uniformTV (supportedLeft left right) (supportedRight left right) := by
    unfold finiteSupportTV uniformTV
    congr 1
    rw [Finset.sum_subtype (uniformSupport left right) (by
      intro view
      rfl)]
    apply Finset.sum_congr rfl
    intro view hview
    congr 1
    unfold uniformFiberMass
    have hfilterLeft :
        (Finset.univ : Finset (Unit × Coins)).filter
            (fun coins => left coins.2 = view.1) =
          Finset.univ.filter
            (fun coins => supportedLeft left right coins.2 = view) := by
      apply Finset.filter_congr
      intro coins _
      simp only [supportedLeft, Subtype.ext_iff]
    have hfilterRight :
        (Finset.univ : Finset (Unit × Coins)).filter
            (fun coins => right coins.2 = view.1) =
          Finset.univ.filter
            (fun coins => supportedRight left right coins.2 = view) := by
      apply Finset.filter_congr
      intro coins _
      simp only [supportedRight, Subtype.ext_iff]
    rw [hfilterLeft, hfilterRight]
  rw [hrepresentation]
  apply conditionalReplacementTV
  intro coins hcoins
  apply Subtype.ext
  exact hsame coins hcoins

theorem uniformSupport_comp_equiv_right (equiv : Coins ≃ Coins)
    (left right : Coins → Output) :
    uniformSupport left (right ∘ equiv) = uniformSupport left right := by
  classical
  apply Finset.ext
  intro view
  simp only [uniformSupport, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and, comp_apply]
  constructor
  · rintro (⟨coins, hleft⟩ | ⟨coins, hright⟩)
    · exact Or.inl ⟨coins, hleft⟩
    · exact Or.inr ⟨equiv coins, hright⟩
  · rintro (⟨coins, hleft⟩ | ⟨coins, hright⟩)
    · exact Or.inl ⟨coins, hleft⟩
    · exact Or.inr ⟨equiv.symm coins, by simpa using hright⟩

/-- A permutation of the uniformly sampled coins on either side does not
change the exact finite-support total-variation distance. -/
theorem finiteSupportTV_reparameterize_right (equiv : Coins ≃ Coins)
    (left right : Coins → Output) :
    finiteSupportTV left (right ∘ equiv) = finiteSupportTV left right := by
  classical
  unfold finiteSupportTV
  have hs := uniformSupport_comp_equiv_right equiv left right
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro view _
  have hfiber : uniformFiberMass (right ∘ equiv) view =
      uniformFiberMass right view := by
    unfold uniformFiberMass
    congr 2
    refine Finset.card_equiv
      (Equiv.prodCongr (Equiv.refl Unit) equiv) fun coins => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, comp_apply]
    rfl
  rw [hfiber]

end FiniteSupport

/-- **Generic end-to-end ZK game theorem.** An algebraic coin bijection costs
nothing; a pROM simulation failure can distinguish only on its bad set. -/
theorem e2e_zk_of_coin_bijection (real simulated : Coins → View)
    (coinEquiv : Coins ≃ Coins) (bad : Finset Coins)
    (hgood : ∀ coins, coins ∉ bad →
      real (coinEquiv coins) = simulated coins) :
    uniformTV real simulated ≤ (bad.card : ℚ) / Fintype.card Coins := by
  rw [← uniformTV_reparameterize_left coinEquiv real simulated]
  exact conditionalReplacementTV (real ∘ coinEquiv) simulated bad hgood

section BadEventUnion

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
variable [DecidableEq Coins]

/-- Union of a finite, explicitly indexed bad-event ledger. -/
def badUnion (bad : Index → Finset Coins) : Finset Coins :=
  Finset.univ.biUnion bad

theorem mem_badUnion_iff (bad : Index → Finset Coins) (coins : Coins) :
    coins ∈ badUnion bad ↔ ∃ index, coins ∈ bad index := by
  simp [badUnion]

/-- Exact finite union bound, normalized by the uniform coin-space mass. -/
theorem badUnionProbability_le_sum (bad : Index → Finset Coins) :
    ((badUnion bad).card : ℚ) / Fintype.card Coins ≤
      ∑ index, ((bad index).card : ℚ) / Fintype.card Coins := by
  have hcount : (badUnion bad).card ≤ ∑ index, (bad index).card := by
    simpa [badUnion] using
      (Finset.card_biUnion_le (s := (Finset.univ : Finset Index))
        (t := bad))
  have hcountQ : ((badUnion bad).card : ℚ) ≤
      ∑ index, ((bad index).card : ℚ) := by
    exact_mod_cast hcount
  calc
    ((badUnion bad).card : ℚ) / Fintype.card Coins ≤
        (∑ index, ((bad index).card : ℚ)) / Fintype.card Coins := by
      gcongr
    _ = ∑ index, ((bad index).card : ℚ) / Fintype.card Coins := by
      rw [Finset.sum_div]

/-- A ledger entry may be replaced by any proved upper bound. -/
theorem badUnionProbability_le_bounds (bad : Index → Finset Coins)
    (bound : Index → ℚ)
    (hbound : ∀ index,
      ((bad index).card : ℚ) / Fintype.card Coins ≤ bound index) :
    ((badUnion bad).card : ℚ) / Fintype.card Coins ≤
      ∑ index, bound index := by
  exact (badUnionProbability_le_sum bad).trans
    (Finset.sum_le_sum fun index _ => hbound index)

/-- **Ledger form of the end-to-end ZK theorem.** The full real and simulated
views agree after algebraic coin reparameterization whenever no listed bad
event occurs.  Their statistical distance is therefore at most the sum of the
individually proved ledger entries. -/
theorem e2e_zk_of_bad_event_ledger (real simulated : Coins → View)
    (coinEquiv : Coins ≃ Coins) (bad : Index → Finset Coins)
    (bound : Index → ℚ)
    (hgood : ∀ coins, (∀ index, coins ∉ bad index) →
      real (coinEquiv coins) = simulated coins)
    (hbound : ∀ index,
      ((bad index).card : ℚ) / Fintype.card Coins ≤ bound index) :
    uniformTV real simulated ≤ ∑ index, bound index := by
  have hsame : ∀ coins, coins ∉ badUnion bad →
      real (coinEquiv coins) = simulated coins := by
    intro coins hcoins
    apply hgood coins
    intro index hbad
    exact hcoins ((mem_badUnion_iff bad coins).2 ⟨index, hbad⟩)
  exact (e2e_zk_of_coin_bijection real simulated coinEquiv
    (badUnion bad) hsame).trans
      (badUnionProbability_le_bounds bad bound hbound)

end BadEventUnion

end VeiledFlock.EndToEnd

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Lagrange
import VeiledFlock.Core.Probability

/-!
# Reed--Solomon properties used by VEIL

The implementation represents a message as evaluations of a low-degree polynomial on an
additive subspace and evaluates that polynomial on a disjoint affine coset.  The proofs in this
file use only distinctness and disjointness of those evaluation points.  The additive geometry is
needed by the fast transform, but not by the Reed--Solomon security arguments.
-/

open scoped Polynomial

namespace VeiledFlock.AdditiveReedSolomon

open Function
open Polynomial

variable {F : Type*} [Field F]

/-- Evaluating a polynomial of degree less than the number of distinct points is a linear
equivalence. -/
noncomputable def evaluationEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (points : ι → F) (hpoints : Injective points) :
    degreeLT F (Fintype.card ι) ≃ₗ[F] (ι → F) where
  toFun p i := p.1.eval (points i)
  invFun values :=
    ⟨Lagrange.interpolate Finset.univ points values, by
      rw [mem_degreeLT]
      simpa using
        (Lagrange.degree_interpolate_lt values hpoints.injOn :
          (Lagrange.interpolate Finset.univ points values).degree <
            (Finset.univ : Finset ι).card)⟩
  map_add' p q := by
    funext i
    exact eval_add.trans rfl
  map_smul' c p := by
    funext i
    simp
  left_inv p := by
    apply Subtype.ext
    symm
    apply Lagrange.eq_interpolate (s := Finset.univ) (v := points) hpoints.injOn
    have hdegree := p.2
    rw [mem_degreeLT] at hdegree
    simpa using hdegree
  right_inv values := by
    funext i
    exact Lagrange.eval_interpolate_at_node values hpoints.injOn (Finset.mem_univ i)

@[simp]
theorem evaluationEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (points : ι → F) (hpoints : Injective points) (p : degreeLT F (Fintype.card ι)) (i : ι) :
    evaluationEquiv points hpoints p i = p.1.eval (points i) := rfl

/-- A polynomial below the dimension bound is determined by its evaluations. -/
theorem eq_zero_of_eval_eq_zero {ι : Type*} [Fintype ι]
    (points : ι → F) (hpoints : Injective points) (p : F[X])
    (hdegree : p.natDegree < Fintype.card ι)
    (heval : ∀ i, p.eval (points i) = 0) : p = 0 :=
  Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hpoints heval hdegree

/-- Pointwise products of evaluations are evaluations of the product polynomial. -/
theorem eval_mul (p q : F[X]) (x : F) :
    (p * q).eval x = p.eval x * q.eval x := by
  simp

/-- Multiplying two polynomials of degree below `k` produces a polynomial of degree below
`2 * k - 1`.  This is the square-code degree bound used by the Hadamard reduction. -/
theorem natDegree_mul_lt_twice_sub_one {k : ℕ} (hk : 0 < k) (p q : F[X])
    (hp : p.natDegree < k) (hq : q.natDegree < k) :
    (p * q).natDegree < 2 * k - 1 := by
  by_cases hp0 : p = 0
  · simp only [hp0, zero_mul, natDegree_zero]
    omega
  by_cases hq0 : q = 0
  · simp only [hq0, mul_zero, natDegree_zero]
    omega
  rw [natDegree_mul hp0 hq0]
  omega

section Hiding

variable {Data Padding : Type*}
variable [Fintype Data] [Fintype Padding]
variable [DecidableEq Data] [DecidableEq Padding]

/-- Insert padding values after zero-valued data coordinates. -/
def paddingValues : (Padding → F) →ₗ[F] (Data ⊕ Padding → F) where
  toFun padding := Sum.elim (fun _ ↦ 0) padding
  map_add' left right := by
    funext i
    cases i <;> simp
  map_smul' scalar padding := by
    funext i
    cases i <;> simp

@[simp]
theorem paddingValues_data (padding : Padding → F) (i : Data) :
    paddingValues padding (Sum.inl i) = 0 := rfl

@[simp]
theorem paddingValues_padding (padding : Padding → F) (i : Padding) :
    paddingValues (Data := Data) padding (Sum.inr i) = padding i := rfl

/-- Interpolate a polynomial whose data coordinates are zero and whose remaining base-domain
coordinates contain the supplied padding. -/
noncomputable def polynomialFromPadding (base : Data ⊕ Padding → F)
    (hbase : Injective base) :
    (Padding → F) →ₗ[F] degreeLT F (Fintype.card (Data ⊕ Padding)) :=
  (evaluationEquiv base hbase).symm.toLinearMap.comp paddingValues

@[simp]
theorem polynomialFromPadding_eval_data (base : Data ⊕ Padding → F)
    (hbase : Injective base) (padding : Padding → F) (i : Data) :
    (polynomialFromPadding base hbase padding).1.eval (base (Sum.inl i)) = 0 := by
  have h := congrFun ((evaluationEquiv base hbase).apply_symm_apply (paddingValues padding))
    (Sum.inl i)
  exact h

@[simp]
theorem polynomialFromPadding_eval_padding (base : Data ⊕ Padding → F)
    (hbase : Injective base) (padding : Padding → F) (i : Padding) :
    (polynomialFromPadding base hbase padding).1.eval (base (Sum.inr i)) = padding i := by
  have h := congrFun ((evaluationEquiv base hbase).apply_symm_apply (paddingValues padding))
    (Sum.inr i)
  exact h

/-- Evaluate a bounded polynomial at the queried output-domain points. -/
def evaluateQueries (queries : Padding → F) :
    degreeLT F (Fintype.card (Data ⊕ Padding)) →ₗ[F] (Padding → F) where
  toFun p i := p.1.eval (queries i)
  map_add' p q := by
    funext i
    exact eval_add.trans rfl
  map_smul' scalar p := by
    funext i
    simp

/-- The linear contribution of the random padding to the queried codeword coordinates. -/
noncomputable def paddingToQueries (base : Data ⊕ Padding → F)
    (hbase : Injective base) (queries : Padding → F) :
    (Padding → F) →ₗ[F] (Padding → F) :=
  (evaluateQueries queries).comp (polynomialFromPadding base hbase)

@[simp]
theorem paddingToQueries_apply (base : Data ⊕ Padding → F)
    (hbase : Injective base) (queries : Padding → F) (padding : Padding → F)
    (i : Padding) :
    paddingToQueries base hbase queries padding i =
      (polynomialFromPadding base hbase padding).1.eval (queries i) := rfl

private theorem dataQueries_injective (base : Data ⊕ Padding → F)
    (hbase : Injective base) (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q) :
    Injective (Sum.elim (fun d ↦ base (Sum.inl d)) queries) := by
  intro left right h
  cases left with
  | inl leftData =>
      cases right with
      | inl rightData =>
          congr 1
          exact Sum.inl_injective (hbase h)
      | inr rightPadding =>
          exact False.elim (hdisjoint leftData rightPadding h)
  | inr leftPadding =>
      cases right with
      | inl rightData =>
          exact False.elim (hdisjoint rightData leftPadding h.symm)
      | inr rightPadding =>
          congr 1
          exact hqueries h

/-- Random padding perfectly masks the same number of queried coordinates.  The map from padding
values to queries is invertible whenever the query points are distinct and outside the data
coordinates of the interpolation domain. -/
theorem paddingToQueries_injective (base : Data ⊕ Padding → F)
    [Nonempty Padding] (hbase : Injective base) (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q) :
    Injective (paddingToQueries base hbase queries) := by
  intro left right heq
  let difference := left - right
  let polynomial := polynomialFromPadding base hbase difference
  have hquery : paddingToQueries base hbase queries difference = 0 := by
    dsimp only [difference]
    rw [map_sub, heq, sub_self]
  have hpolynomial : polynomial.1 = 0 := by
    apply eq_zero_of_eval_eq_zero
      (Sum.elim (fun d ↦ base (Sum.inl d)) queries)
      (dataQueries_injective base hbase queries hqueries hdisjoint)
    · have hdegree := polynomial.2
      rw [mem_degreeLT] at hdegree
      by_cases hzero : polynomial.1 = 0
      · have hcard : 0 < Fintype.card (Data ⊕ Padding) := Fintype.card_pos
        simpa [hzero] using hcard
      · exact (natDegree_lt_iff_degree_lt hzero).mpr hdegree
    · intro i
      cases i with
      | inl data =>
          exact polynomialFromPadding_eval_data base hbase difference data
      | inr query =>
          change paddingToQueries base hbase queries difference query = 0
          rw [hquery]
          rfl
  funext i
  have hpadding := polynomialFromPadding_eval_padding base hbase difference i
  rw [hpolynomial, eval_zero] at hpadding
  exact sub_eq_zero.mp (by simpa [difference] using hpadding.symm)

/-- The padding-to-query map is a linear equivalence.  Consequently uniform padding induces a
uniform distribution on the queried coordinates. -/
noncomputable def paddingQueryEquiv (base : Data ⊕ Padding → F)
    [Nonempty Padding] (hbase : Injective base) (queries : Padding → F) (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q) :
    (Padding → F) ≃ₗ[F] (Padding → F) :=
  LinearEquiv.ofBijective (paddingToQueries base hbase queries)
    ⟨paddingToQueries_injective base hbase queries hqueries hdisjoint,
      LinearMap.surjective_of_injective
        (paddingToQueries_injective base hbase queries hqueries hdisjoint)⟩

@[simp]
theorem paddingQueryEquiv_apply (base : Data ⊕ Padding → F)
    [Nonempty Padding] (hbase : Injective base) (queries : Padding → F)
    (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q)
    (padding : Padding → F) :
    paddingQueryEquiv base hbase queries hqueries hdisjoint padding =
      paddingToQueries base hbase queries padding := rfl

/-- Uniform Reed--Solomon padding induces an exactly uniform vector at the
same number of distinct, off-data query points. -/
theorem paddingQueries_uniform [Fintype F] [DecidableEq F]
    (base : Data ⊕ Padding → F) [Nonempty Padding]
    (hbase : Injective base) (queries : Padding → F)
    (hqueries : Injective queries)
    (hdisjoint : ∀ d q, base (Sum.inl d) ≠ queries q) :
    (PMF.uniformOfFintype (Padding → F)).map
        (paddingToQueries base hbase queries) =
      PMF.uniformOfFintype (Padding → F) := by
  change (PMF.uniformOfFintype (Padding → F)).map
      (paddingQueryEquiv base hbase queries hqueries hdisjoint).toEquiv =
    PMF.uniformOfFintype (Padding → F)
  exact VeiledFlock.Probability.uniform_map_equiv
    (paddingQueryEquiv base hbase queries hqueries hdisjoint).toEquiv

end Hiding

/-- If a nonzero polynomial is evaluated at distinct points, at most its degree-many
coordinates can vanish. -/
theorem card_zero_evaluations_le_natDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq F]
    (points : ι → F) (hpoints : Injective points) (p : F[X]) (hp : p ≠ 0) :
    (Finset.univ.filter fun i ↦ p.eval (points i) = 0).card ≤ p.natDegree := by
  classical
  let roots : Finset F := p.roots.toFinset
  calc
    (Finset.univ.filter fun i ↦ p.eval (points i) = 0).card
        = ((Finset.univ.filter fun i ↦ p.eval (points i) = 0).image points).card := by
            symm
            exact Finset.card_image_iff.mpr fun _ _ _ _ h ↦ hpoints h
    _ ≤ roots.card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      simpa [roots, Polynomial.mem_roots', hp, IsRoot.def] using hi.2
    _ ≤ p.natDegree :=
      (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)

end VeiledFlock.AdditiveReedSolomon

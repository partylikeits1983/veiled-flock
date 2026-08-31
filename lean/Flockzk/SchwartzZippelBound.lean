import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
The generic Schwartz-Zippel supplier consumed by Flock's generated symbolic
artifacts. Rust emits one nonzero determinant evaluation and a component-wise
degree budget. This theorem turns exactly those two facts into the probability
bound used by the masking bad-set argument.
-/
namespace FlockZk

open Finset

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-- A nonzero polynomial with emitted per-variable degree bounds vanishes on
at most the corresponding Schwartz-Zippel budget over a product set. -/
-- @audit:FlockZk.schwartz_zippel_degree_budget
theorem schwartz_zippel_degree_budget {n : Nat}
    {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (degreeBudget : Fin n -> Nat)
    (hdegree : forall i, p.degreeOf i <= degreeBudget i)
    (S : Fin n -> Finset R) :
    #{x ∈ Fintype.piFinset S | MvPolynomial.eval x p = 0} /
          Finset.prod univ (fun i => (#(S i) : ℚ≥0))
      <= Finset.sum univ (fun i => (degreeBudget i / #(S i) : ℚ≥0)) := by
  calc
    _ <= Finset.sum univ (fun i => (p.degreeOf i / #(S i) : ℚ≥0)) :=
      MvPolynomial.schwartz_zippel_sum_degreeOf hp S
    _ <= Finset.sum univ (fun i => (degreeBudget i / #(S i) : ℚ≥0)) := by
      gcongr with i
      exact_mod_cast hdegree i
-- @audit:end

end FlockZk

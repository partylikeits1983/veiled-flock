import Mathlib

/-!
The masking theorem behind the earlier zk-FLOCK masking construction.

At fixed verifier challenges, every value Flock's zk prover reveals is an
affine function of the prover's secret mask bits `u` and the witness `w`:

    transcript(u, w) = A u + f w

over F₂ (where F₂-linear maps are exactly the additive maps, so `A` is an
`AddMonoidHom`). The rank audits in the Rust code check, per instance,
exactly the two hypotheses used here:

  * affinity — unit-probe differencing extracts `A` exactly, which is only
    possible if the map is affine (`pcs/zk_audit.rs`,
    `tests/zk_piop_audit.rs`);
  * coverage — every witness-difference direction (restricted to the kernel
    of the public claim functionals) lies in `Image A`.

This file proves that those hypotheses imply honest-verifier
zero-knowledge, in the strongest sense available at fixed challenges:

  * `transcript_witness_indep` — for witnesses with equal public inputs,
    the transcript distributions are **identical** (stated as exact fiber
    counts under uniform masks, i.e. pointwise equality of the two
    distributions);
  * `simulator_exact` — any public coset representative yields a simulator
    whose output distribution equals the honest prover's;
  * `fiber_card_const` / `fiber_card_off_coset` — the transcript is
    uniform on its coset (each attainable value has the same probability
    `|ker A| / |U|`, everything else has probability 0);
  * `pmf_transcript_witness_indep` — the same independence statement in
    `PMF` form (`Mathlib`'s probability-mass-function API).

Everything is over an arbitrary finite mask group `U` and value group `V`;
zk-Flock instantiates `U = F₂^{randomizer bits} × F₂^{128·(mask+g slots)}`
and `V = F₂^{128·(revealed values)}`.
-/
namespace FlockZk

open Finset

variable {U V W P : Type*} [Fintype U] [DecidableEq V]
variable [AddCommGroup U] [AddCommGroup V]

/-- **Fiber translation.** If two offsets `t, t'` differ by an element of
`Image A`, then for every transcript value `y` the fibers
`{u | A u + t = y}` and `{u | A u + t' = y}` have the same size — the
translation `u ↦ u + d` (with `A d = t - t'`) is a bijection between them.
With `u` uniform, this is exactly "the two transcript distributions are
pointwise equal". -/
theorem card_fiber_shift (A : U →+ V) {t t' : V} (y : V)
    (h : t - t' ∈ Set.range A) :
    (univ.filter fun u => A u + t = y).card
      = (univ.filter fun u => A u + t' = y).card := by
  obtain ⟨d, hd⟩ := h
  have key : ∀ u : U, A (u + d) + t' = A u + t := by
    intro u
    rw [map_add, hd]
    abel
  refine Finset.card_equiv (Equiv.addRight d) fun u => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, key]

/-- **The masking theorem (witness independence).** If every pair of
witnesses with equal public inputs has its transcript-offset difference
covered by the mask image, then conditioned on the public inputs the
transcript distribution under uniform masks is independent of the witness:
for every value `y`, the number of mask assignments producing `y` is the
same for `w` and `w'`. -/
theorem transcript_witness_indep (A : U →+ V) (f : W → V) (pub : W → P)
    (hcov : ∀ w w', pub w = pub w' → f w - f w' ∈ Set.range A)
    {w w' : W} (hpub : pub w = pub w') (y : V) :
    (univ.filter fun u => A u + f w = y).card
      = (univ.filter fun u => A u + f w' = y).card :=
  card_fiber_shift A y (hcov w w' hpub)

/-- **Simulation.** A simulator that knows only a public representative `r`
of the transcript coset (any point with `f w - r ∈ Image A`, e.g. one
honest transcript published for the statement, or a canonical solution of
the public consistency equations) and samples `A u + r` with uniform `u`
produces **exactly** the honest prover's transcript distribution — without
the witness. -/
theorem simulator_exact (A : U →+ V) (f : W → V) (r : V)
    (hrep : ∀ w, f w - r ∈ Set.range A) (w : W) (y : V) :
    (univ.filter fun u => A u + f w = y).card
      = (univ.filter fun u => A u + r = y).card :=
  card_fiber_shift A y (hrep w)

/-- On its coset, the transcript is **uniform**: every attainable value has
fiber size `|{u | A u = 0}| = |ker A|`. -/
theorem fiber_card_const (A : U →+ V) (t y : V) (hy : y - t ∈ Set.range A) :
    (univ.filter fun u => A u + t = y).card
      = (univ.filter fun u => A u = 0).card := by
  have h : (univ.filter fun u => A u + t = y).card
      = (univ.filter fun u => A u + y = y).card := by
    refine card_fiber_shift A y ?_
    obtain ⟨d, hd⟩ := hy
    exact ⟨-d, by rw [map_neg, hd]; abel⟩
  rw [h]
  congr 1
  ext u
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h'
    have := congrArg (fun v => v - y) h'
    simpa using this
  · intro h'
    rw [h']
    abel

/-- Off its coset, the transcript value is never produced. -/
theorem fiber_card_off_coset (A : U →+ V) (t y : V)
    (hy : y - t ∉ Set.range A) :
    (univ.filter fun u => A u + t = y).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ h
  exact hy ⟨u, eq_sub_of_add_eq h⟩

section PMF

open scoped ENNReal

variable [Nonempty U]

omit [AddCommGroup U] [AddCommGroup V] in
/-- Helper: the probability that an affine transcript takes the value `y`
is `(fiber size) / |U|`. -/
theorem pmf_map_affine_apply (g : U → V) (y : V) :
    (PMF.uniformOfFintype U).map g y
      = (univ.filter fun u => g u = y).card * (Fintype.card U : ℝ≥0∞)⁻¹ := by
  classical
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  have h : ∀ u : U, (if y = g u then (Fintype.card U : ℝ≥0∞)⁻¹ else 0)
      = if g u = y then (Fintype.card U : ℝ≥0∞)⁻¹ else 0 := fun u => by
    simp [eq_comm]
  rw [Finset.sum_congr rfl fun u _ => h u, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]

/-- `transcript_witness_indep`, in `PMF` form: the transcript
**distributions** of two witnesses with equal public inputs are equal. -/
theorem pmf_transcript_witness_indep (A : U →+ V) (f : W → V) (pub : W → P)
    (hcov : ∀ w w', pub w = pub w' → f w - f w' ∈ Set.range A)
    {w w' : W} (hpub : pub w = pub w') :
    (PMF.uniformOfFintype U).map (fun u => A u + f w)
      = (PMF.uniformOfFintype U).map (fun u => A u + f w') := by
  ext y
  rw [pmf_map_affine_apply, pmf_map_affine_apply,
    transcript_witness_indep A f pub hcov hpub y]

/-- `simulator_exact`, in `PMF` form: the simulator's output distribution
equals the honest prover's. -/
theorem pmf_simulator_exact (A : U →+ V) (f : W → V) (r : V)
    (hrep : ∀ w, f w - r ∈ Set.range A) (w : W) :
    (PMF.uniformOfFintype U).map (fun u => A u + f w)
      = (PMF.uniformOfFintype U).map (fun u => A u + r) := by
  ext y
  rw [pmf_map_affine_apply, pmf_map_affine_apply, simulator_exact A f r hrep w y]

end PMF

end FlockZk

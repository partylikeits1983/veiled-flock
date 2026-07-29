import Flockzk.MaskingMixture

/-!
The triangular (quotient) composition theorem — the load-bearing masking
statement for the unamended zk-Flock transcript.

At fixed verifier challenges the full Flock transcript is a function
`T(w, u₁, b)` of the witness `w`, an **inner** mask vector `u₁` (the `u_A`
randomizer bits, the PCS mask `μ`, the blinder `g`, and the committed mask
polynomial `P` — all of which act affinely once the outer masks are fixed)
and an **outer** mask `b` (the `u_B` randomizer bits together with the mask
polynomial `Q`). Fixing `(w, b)` the transcript is affine in `u₁`:

    T(w, u₁, b) = A w b u₁ + g w b,

with a *family* of linear parts `A w b : U₁ →+ V` that may depend on both
the witness and the outer mask (bilinear cross terms), and offsets
`g w b : V`.

The flat mixture theorem (`Flockzk.MaskingMixture`) asked for all offsets
of claim-equal witnesses to lie in **one** coset of the inner image. That
hypothesis is *disproved on the real transcript* by the exact WS-0
certificate `final_b_breaks_full_mixture_hcoset`
(`crates/flock-prover/tests/zk_leakage_certificate.rs`): the b̂-side final
evaluation `final_b_eval` has an identically-zero `u₁`-derivative yet
varies with `b` (and, through the layout, with `w`), so cross-`b` offset
differences provably leave the inner image. The companion certificate
`final_b_covered_by_b_stage` shows the escape directions *are* covered by
the outer (`u_B`) stage — the composition is triangular, not flat.

The repair formalized here quotients out the inner image and pushes the
escaped directions to an outer stage:

  * **H1 (`hrange`, constant inner image)** — every inner slice map has
    the same image `(A w b).range = V₀`. Certified per instance by the
    within-slice rank audits (`zk_piop_audit.rs`, and the within-slice
    image measurements of `zk_affinity_probe.rs`, which survive the
    mixture counterexample).
  * **H2 (`hquot`, residual outer affinity)** — in the quotient `V ⧸ V₀`
    the offset is affine in the outer mask with a *witness-independent*
    linear part: `π (g w b) = Bq b + d w`. This is exactly what the
    outer-stage unit-probe differencing certifies (differencing in `b` at
    fixed `w` always extracts the same `Bq`).
  * **H3 (`hcover`, claim coverage of the residue)** — claim-equal
    witnesses' outer offsets differ by an element of `Image Bq`
    (`final_b_covered_by_b_stage` / the residual-mod-`R(ker L)` coverage
    checks: the only un-covered direction is the public claim itself).

Main results:

  * `triangular_witness_indep` — under H1–H3 the joint transcript
    distribution over uniform `(u₁, b)` is **identical** for claim-equal
    witnesses (exact fiber counts on `U₁ × B`);
  * `triangular_simulator_exact` — running the honest prover on any fixed
    public representative `w₀` of the claim reproduces the honest
    distribution exactly, without the witness;
  * `pmf_triangular_witness_indep` / `pmf_triangular_simulator_exact` —
    the same statements in `PMF` form (map of the uniform PMF on
    `U₁ × B`).

Proof shape: split the joint count over `b` (`card_filter_prod_eq_sum`);
H3 provides an outer shift `β` with `Bq β = d w − d w′`; H2 makes the
slice offsets `g w b` and `g w′ (b + β)` congruent mod `V₀`, so H1 plus
the single-slice comparison `fiber_card_eq_of_range_eq` (first
isomorphism theorem: equal images force equal kernel sizes) equates the
slice counts; re-indexing the `b`-sum by the translation `b ↦ b + β`
finishes. This is the counting form of "quotient by the inner stage, then
run the affine masking theorem on the outer stage".
-/
namespace FlockZk

open Finset

variable {U₁ B W P V : Type*} [Fintype U₁] [Fintype B] [DecidableEq V]
variable [AddCommGroup U₁] [AddCommGroup B] [AddCommGroup V]

/-- **The triangular masking theorem (joint witness independence).** For a
transcript `T(w, (u₁, b)) = A w b u₁ + g w b` that is affine in the inner
mask `u₁` at each fixed outer mask `b`, with

  * H1 (`hrange`): constant inner image `(A w b).range = V₀` across the
    witness and the outer mask,
  * H2 (`hquot`): quotiented offsets affine in `b` with a
    witness-independent linear part, `π (g w b) = Bq b + d w` for
    `π = QuotientAddGroup.mk' V₀`,
  * H3 (`hcover`): claim-equal witnesses' outer offsets differing by an
    element of `Image Bq`,

the joint transcript distribution under uniform `(u₁, b)` is independent
of the witness: for every value `y`, the number of joint mask assignments
producing `y` is the same for `w` and `w'`. -/
theorem triangular_witness_indep
    (A : W → B → (U₁ →+ V)) (g : W → B → V) (pub : W → P)
    (V₀ : AddSubgroup V) (Bq : B →+ V ⧸ V₀) (d : W → V ⧸ V₀)
    (hrange : ∀ w b, (A w b).range = V₀)
    (hquot : ∀ w b, QuotientAddGroup.mk' V₀ (g w b) = Bq b + d w)
    (hcover : ∀ w w', pub w = pub w' → d w - d w' ∈ Set.range Bq)
    {w w' : W} (hpub : pub w = pub w') (y : V) :
    ((univ : Finset (U₁ × B)).filter fun ub => A w ub.2 ub.1 + g w ub.2 = y).card
      = ((univ : Finset (U₁ × B)).filter fun ub => A w' ub.2 ub.1 + g w' ub.2 = y).card := by
  -- H3: an outer-mask shift β aligning the two witnesses' outer offsets.
  obtain ⟨β, hβ⟩ := hcover w w' hpub
  -- Slice comparison: the `w`-slice at `b` matches the `w'`-slice at `b + β`.
  have hslice : ∀ b : B,
      (univ.filter fun u => A w b u + g w b = y).card
        = (univ.filter fun u => A w' (b + β) u + g w' (b + β) = y).card := by
    intro b
    refine fiber_card_eq_of_range_eq (A w b) (A w' (b + β))
      (by rw [hrange, hrange]) ?_ y
    -- The offsets agree in the quotient (H2 + the choice of β), hence
    -- differ by an element of the common inner image V₀ (H1).
    rw [hrange w b, ← QuotientAddGroup.ker_mk' V₀, AddMonoidHom.mem_ker, map_sub,
      hquot w b, hquot w' (b + β), map_add, hβ]
    abel
  calc ((univ : Finset (U₁ × B)).filter fun ub => A w ub.2 ub.1 + g w ub.2 = y).card
      = ∑ b : B, (univ.filter fun u => A w b u + g w b = y).card :=
        card_filter_prod_eq_sum (fun u b => A w b u + g w b) y
    _ = ∑ b : B, (univ.filter fun u => A w' (b + β) u + g w' (b + β) = y).card :=
        Finset.sum_congr rfl fun b _ => hslice b
    _ = ∑ b : B, (univ.filter fun u => A w' b u + g w' b = y).card :=
        Fintype.sum_equiv (Equiv.addRight β) _ _ fun b => rfl
    _ = ((univ : Finset (U₁ × B)).filter fun ub => A w' ub.2 ub.1 + g w' ub.2 = y).card :=
        (card_filter_prod_eq_sum (fun u b => A w' b u + g w' b) y).symm

/-- **Simulation for the triangular prover.** A simulator that knows any
public representative `w₀` of the claim (`pub w = pub w₀`) and runs the
honest prover on it — sampling both mask stages uniformly — produces
**exactly** the honest prover's transcript distribution, without access
to `w`. Immediate from `triangular_witness_indep`. -/
theorem triangular_simulator_exact
    (A : W → B → (U₁ →+ V)) (g : W → B → V) (pub : W → P)
    (V₀ : AddSubgroup V) (Bq : B →+ V ⧸ V₀) (d : W → V ⧸ V₀)
    (hrange : ∀ w b, (A w b).range = V₀)
    (hquot : ∀ w b, QuotientAddGroup.mk' V₀ (g w b) = Bq b + d w)
    (hcover : ∀ w w', pub w = pub w' → d w - d w' ∈ Set.range Bq)
    {w w₀ : W} (hpub : pub w = pub w₀) (y : V) :
    ((univ : Finset (U₁ × B)).filter fun ub => A w ub.2 ub.1 + g w ub.2 = y).card
      = ((univ : Finset (U₁ × B)).filter fun ub => A w₀ ub.2 ub.1 + g w₀ ub.2 = y).card :=
  triangular_witness_indep A g pub V₀ Bq d hrange hquot hcover hpub y

section PMF

open scoped ENNReal

variable [Nonempty U₁] [Nonempty B]

/-- `triangular_witness_indep`, in `PMF` form: the joint transcript
**distributions** of two claim-equal witnesses, over uniform `(u₁, b)`,
are equal. -/
theorem pmf_triangular_witness_indep
    (A : W → B → (U₁ →+ V)) (g : W → B → V) (pub : W → P)
    (V₀ : AddSubgroup V) (Bq : B →+ V ⧸ V₀) (d : W → V ⧸ V₀)
    (hrange : ∀ w b, (A w b).range = V₀)
    (hquot : ∀ w b, QuotientAddGroup.mk' V₀ (g w b) = Bq b + d w)
    (hcover : ∀ w w', pub w = pub w' → d w - d w' ∈ Set.range Bq)
    {w w' : W} (hpub : pub w = pub w') :
    (PMF.uniformOfFintype (U₁ × B)).map (fun ub => A w ub.2 ub.1 + g w ub.2)
      = (PMF.uniformOfFintype (U₁ × B)).map (fun ub => A w' ub.2 ub.1 + g w' ub.2) := by
  ext y
  rw [pmf_map_affine_apply, pmf_map_affine_apply,
    triangular_witness_indep A g pub V₀ Bq d hrange hquot hcover hpub y]

/-- `triangular_simulator_exact`, in `PMF` form: the simulator's output
distribution — the honest prover run on a public representative `w₀` —
equals the honest prover's on `w`. -/
theorem pmf_triangular_simulator_exact
    (A : W → B → (U₁ →+ V)) (g : W → B → V) (pub : W → P)
    (V₀ : AddSubgroup V) (Bq : B →+ V ⧸ V₀) (d : W → V ⧸ V₀)
    (hrange : ∀ w b, (A w b).range = V₀)
    (hquot : ∀ w b, QuotientAddGroup.mk' V₀ (g w b) = Bq b + d w)
    (hcover : ∀ w w', pub w = pub w' → d w - d w' ∈ Set.range Bq)
    {w w₀ : W} (hpub : pub w = pub w₀) :
    (PMF.uniformOfFintype (U₁ × B)).map (fun ub => A w ub.2 ub.1 + g w ub.2)
      = (PMF.uniformOfFintype (U₁ × B)).map (fun ub => A w₀ ub.2 ub.1 + g w₀ ub.2) :=
  pmf_triangular_witness_indep A g pub V₀ Bq d hrange hquot hcover hpub

end PMF

end FlockZk

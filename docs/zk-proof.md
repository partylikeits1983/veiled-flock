# Zero-knowledge for Flock (amended protocol A1′): proof document

This document states and proves the zero-knowledge property of the `zk` mode
for **BLAKE3 batch statements**, under the amendment A1′ (a degree-2 committed
mask channel for the zerocheck round messages). It is written to be checkable:
each claim is marked with how it is established —

- **[P]** closed-form proof in this document;
- **[L]** machine-checked in Lean 4 (`lean/Flockzk/`, no `sorry`, standard
  axioms only);
- **[C]** certified by exact computation on the real prover
  (`crates/flock-prover/tests/zk_leakage_certificate.rs` — exact F₂
  image-coverage, not sampled rank);
- **[A]** an explicit assumption;
- **[S]** standard result, cited.

It is honest about scope and status: this is a **candidate / experimental**
result. See §12 for the disposition of every external-review item and §0 for
what is not yet done.

---

## 0. Status and what is not proven here

- The amendment A1′ is **implemented end to end, reference-correct, and
  verifying**: `prover::prove_r1cs_zk_a1` / `verify_r1cs_zk_a1` run the full
  amended pipeline on a real 256-block BLAKE3 zk statement — commit witness +
  fresh `P,Q` hidingly, bind all roots before any challenge, masked zerocheck
  `â·b̂+γ·P·Q` (`zerocheck::prove_packed_padded_zk`/`verify_zk`), lincheck,
  and hiding openings of the witness and `P,Q` at ρ (leakage `L={P(ρ),Q(ρ)}`).
  Tested: honest roundtrip verifies; fresh masks ⇒ different verifying
  transcript; tampering `σ_z`,`P(ρ)`,`Q(ρ)`, or a masked round message is
  rejected (`prove_verify_r1cs_zk_a1_roundtrip`). This is a self-contained
  reference path; the optimized fused prover is a differential-tested
  follow-up (the shipped `prove_fast_zk` still runs the un-amended zerocheck).
- **Complete-transcript coverage: ESTABLISHED at the certified fixture.**
  The joint conditional certificate runs the COMPLETE A1' pipeline on the real
  prover, with every coordinate located through the canonical transcript
  schema, the complete mask-only leakage set conditioned on, every public
  claim the verifier learns conditioned on, and a genuinely linear
  witness-difference family. Measured over three challenge tuples at the
  16-block fixture (121,861 probes each): 548 witness-dependent coordinates,
  394 mask-only, field-channel subspace rank 124, inner image 52,864 bits,
  joint image 53,024, claim space saturated at 384 bits, and
  rank[residual | dclaim] = 384 = rank(dclaim) at every tuple - no
  claim-preserving witness direction escapes the joint image.

  Supporting results on the round-pair class: H1 (the inner mask image is the
  same subspace at different witnesses) holds with the degree-2 channel and
  fails without it (384 of 2560 bits); the inner-stage deficit is exactly one
  F128 direction and it is exactly `final_b`, supplied by the outer (u_B)
  stage; a constant Q collapses the channel image from 2305 to 1153 bits,
  delimiting the bad-mask set. The negative controls fire, including a canary
  that appends a raw witness functional.

  Four corrections were needed to get an interpretable verdict, each of which
  had made earlier results uninterpretable rather than wrong-in-the-safe-
  direction: (i) the coverage criterion is capped by the number of sampled
  witness directions, so below the claim dimension it passes for free - the
  earlier certificate used 40 against a 128-bit claim; (ii) the witness family
  must be genuinely linear; (iii) mu and g are FIELD-valued, so probing one
  bit per slot samples 1/128 of that channel (an earlier "the fixture is 2.8x
  under-budgeted" diagnosis was a consequence of this and is RETRACTED -
  counted correctly the fixture is over-budgeted); (iv) `s_hat_v` binds the
  randomizer sizing at `blocks x A-chunks >= 128` per bit-residue WITH MARGIN,
  and the residual concentrated in exactly that class at 1.5x margin and
  vanished at 3x. Production BLAKE3 runs at ~12x.
- The earlier joint conditional coverage was verified at
  the zerocheck layer only (`full_conditional_coverage_zk_zerocheck`,
  `L={P(ρ),σ_z}`, at a **single fixed `Q`** — so conditioning on `Q(ρ)` in that
  experiment is vacuous — and with the randomizer channels held at zero).
  **Correction:** the affine and PCS layers do *not* compose with the
  round-pair channel via `MaskingSurjective.coprod_covers` — that lemma
  requires both channels to be additive maps into the transcript space, and
  the randomizer channel is certified *bilinear* on the round-pair coordinates
  (L4). The valid composition is triangular/conditional (fix `u_B,Q`; the
  remaining channels are affine) — see the correction in §4. What remains:
  the complete-transcript joint certificate over the integrated prover for an
  explicit parameter set, and a machine-checked triangular composition lemma.
- The bad-mask probability bound previously stated in §8 (Schwartz–Zippel over
  the mask entries) is **withdrawn**: the implemented `P,Q` are Boolean — one
  bit per cube entry (`prover.rs::sample_mask_bits`) — so the bound's
  uniform-`F₂₁₂₈`-entries hypothesis is false for the shipped prover, and
  Schwartz–Zippel over `{0,1}` is vacuous at these degrees. See §8 for the
  replacement. The Merkle-sibling hiding argument (§7) is closed-form but not
  machine-checked; per-parameter certificate gating is not yet wired.
- Out of scope entirely: SHA-256/Keccak encoders, the hash-chain statement,
  QROM *soundness*, side-channel resistance, and independent cryptographic
  review.

---

## 1. The exact security claim (review item #1)

Let $\mathcal{R}$ be a BLAKE3 batch relation: a fixed R1CS
$Az\circ Bz = z$ over $\mathbb{F}_2$ ($C=I$) for $2^{n}$ compressions sharing
per-block matrices, with the amended zk layout (randomizer rows + the $P,Q$
mask columns). Write $\pi\leftarrow \mathsf{P}(x,w)$ for the honest zk prover's
proof on statement $x$ and witness $w$, and $\mathrm{View}$ for the transcript
plus verifier coins.

**Claim (Z1, interactive — TARGET; evidence status per component, see §0 and
§12).** There is a PPT simulator
$\mathsf{S}$ taking only $x$ such that for every $x$ and every valid witness
$w$,
$$\Delta\big(\mathrm{View}\langle \mathsf{P}(x,w),\mathsf{V}(x)\rangle,\ \mathsf{S}(x)\big)\ \le\ \varepsilon_{\mathrm{rank}} + \varepsilon_{\mathrm{hash}},$$
where the transcript is *identically* distributed conditioned on the challenge
tuple avoiding a bad set of probability $\varepsilon_{\mathrm{rank}}$
(§8), and $\varepsilon_{\mathrm{hash}}$ (§9) is the computational
sibling-hiding term. The verifier is **honest** (public-coin); aborts and
malformed challenges are not a separate case.

**Claim (Z2, NIZK in the ROM, [P]+[S]).** After Fiat–Shamir, the same
$\mathsf{S}$ is a NIZK simulator in the classical ROM, with the same error.
The lift is unconditional given Z1 because $\mathsf{S}$ is *non-programming*
(§2).

**Claim (Z3, QROM — NOT CLAIMED; conjecture only).** $\mathsf{S}$ programs
nothing and rewinds nothing, which makes a QROM ZK statement *plausible*
(heuristically $\varepsilon_{\mathrm{hash}} \to O(q\cdot 2^{-k_{\min}/2})$ by
generic quantum search / O2H), but no precise theorem is written and none is
claimed. **QROM soundness is likewise not claimed.**

**Multi-proof.** Masks are drawn fresh per proof (§10); $k$ proofs compose
with error $k(\varepsilon_{\mathrm{rank}}+\varepsilon_{\mathrm{hash}})$.

The statistical parts (Z1 conditional equality) carry the explicit
$\varepsilon_{\mathrm{rank}}$; sibling hiding is computational under the hash
assumption of §9.

---

## 2. The reduction to witness-indistinguishability, and the explicit simulator (items #1, #2)

**Lemma L1 (no public input; [P], code-checked).** For a BLAKE3 *batch*
statement, the Fiat–Shamir transcript binds only the statement digest (the
matrices + layout: `r1cs.rs::statement_digest`) and the commitment root
(`proof.rs::bind_statement`). Verification (`verifier.rs::verify_ligerito`)
consumes no caller-supplied value beyond the setup and the proof bytes, and
compares the accepted claim values (`R1csClaim`) against nothing. The only
pinned wire is the constant-one wire, pinned to the constant $1$ via the
lincheck $\beta$-fold (`lincheck.rs`), not to any caller value. In particular
there is **no public-input vector and no I/O binding** (unlike the chain
statement, which binds endpoints).

*Consequence.* A valid witness is efficiently self-generatable: pick arbitrary
compressions $(cv,m,\text{ctr},\ell,\text{flags})$, run the honest compression
trace, set the constant wire. Every such witness satisfies the same statement.

**The simulator $\mathsf{S}(x)$.** Read $x$ = the batch size $n$ (all a batch
statement carries). Pick arbitrary compressions; build the witness $z$; run
the honest zk prover `prove_fast_zk` with fresh OS-entropy masks; output its
transcript. $\mathsf{S}$:
- receives no witness and no witness-derived hidden value;
- generates the commitment root, the zerocheck/lincheck/ring-switch messages,
  every Ligerito opened row and Merkle path, the residual $y_r$, the blinder
  value $y_g$, and the reduced claim $v=\hat z(r)$ — because it *is* the honest
  prover on a witness it knows, so these are all ordinary values of its own
  run (in particular $v$ is simulated **jointly** with the rest, not treated as
  a public input);
- makes no random-oracle query it does not answer honestly, and never rewinds.

This is realized and checked: `tests/zk_simulator.rs`
(`simulator_produces_accepting_proof_without_a_witness`) runs $\mathsf{S}$ on
$n=256$ and verifies its output under the unchanged verifier; a second run with
fresh randomness gives a different, still-accepting transcript.

**Status caveat.** The realized simulator test currently drives
`prove_fast_zk`, whose zerocheck is **un-amended** — a path for which the
round-pair hiding argument of this document does not apply (and whose fallback
mixture hypothesis is disproved, `final_b_breaks_full_mixture_hcoset`). The ZK
claim of this document attaches to the A1′ reference path
(`prove_r1cs_zk_a1`); the simulator and its test are being moved onto that
path.

**Reduction.** Since $\mathsf{S}(x)$ is the honest prover on *some* valid
witness $w_0$, proving $\Delta(\mathsf{View}(w),\mathsf{S}(x))\le\varepsilon$
is exactly proving $\Delta(\mathsf{View}(w),\mathsf{View}(w_0))\le\varepsilon$
for all valid $w$ — **full-transcript witness-indistinguishability (WI)**.
Everything below proves WI.

---

## 3. Transcript decomposition (item #5)

Fix the verifier challenges. Write the transcript as a function of the masks
$u=(\text{randomizer bits},\mu,g,P,Q)$ and the witness $w$. WI is a statement
about the **joint** distribution of the whole transcript vector, not
message-by-message; we prove it by covering the joint witness-difference with
the joint mask image.

**Lemma L2 (structure; [P], regression-[C]).** At fixed challenges every
revealed value is affine in $u$ with a witness-independent linear part,
**except** the zerocheck round messages $(G_j(1),G_j(\infty))$. Proof sketch:
the lincheck, ring-switch, and all PCS-opened values are $\mathbb{F}_{2^{128}}$-
linear in the committed data; the randomizer rows enter the $a,b,z$ cubes
additively. The round messages are the one nonlinearity — see L3, L4.
Regression: the affinity gate in `zk_leakage_certificate.rs`
(`affine_classes_exactly_covered`) asserts a zero bilinear defect on exactly
the affine coordinates.

**Lemma L3 (round-1 alignment; [P], assert-[C]).** The 64-point
univariate-skip interpolation groups are 64 consecutive rows; every
randomizer / mask / padding region is 128-bit aligned, so no group mixes
A-rows, B-rows, and real rows. Hence the round-1 vectors $P^{AB},P^{C}$ are
affine in $u$. **Verified** (`l3_round1_region_alignment_holds`): on the real
BLAKE3 zk layout the A-species occupies 12 whole skip groups and the B-species
2, and the two sets of groups are disjoint — so no univariate-skip fold group
mixes the species or straddles a region boundary, which is exactly what the
proof relies on. This closes review item L3, previously asserted with a
runtime check the audit could not locate.

**Lemma L4 (the round messages are bilinear, and why; [P], [C]).** A round
sends $(G(1),G(\infty))$ where $G$ is degree 2 in the fold variable and
$G(\infty)$ is its leading coefficient (verifier reconstruction
`zerocheck.rs`: $G(\rho)=G(0)(1{+}\rho)+G(1)\rho+G(\infty)\rho(1{+}\rho)$).
$G(\infty)=\sum_x \mathrm{eq}(r,x)\,\Delta\hat a(x)\,\Delta\hat b(x)$ (product
of the fold slopes). A-randomizers enter $\Delta\hat a$, B-randomizers enter
$\Delta\hat b$, so $G$ carries genuine $u_A\!\cdot\!u_B$ cross terms once a
fold group spans the A/B region boundary — **not** affine in $u$.
Certified: `zk_leakage_certificate.rs` measures a nonzero affinity defect on
exactly the round-pair coordinates, and the (superseded) mixture certificate's
blind spot — the $\hat b$-side final evaluation has an identically-zero
$u_A$-derivative — is shown by `final_b_breaks_full_mixture_hcoset`.

A degree-1 mask cannot reach $G(\infty)$ (its leading coefficient is zero); in
characteristic 2 the classical separable mask $\sum_i g_i(x_i)$ additionally
vanishes over the cube. This forces the degree-2 channel of §5.

---

## 4. The masking theorem (item #3, [L])

For the affine part, image coverage *is* exact distribution equality.

**Theorem (masking; `Masking.lean`, [L]).** Let $A:U\to V$ be additive, $U$
finite. If for all witness pairs with equal public inputs
$f(w)-f(w')\in\mathrm{Im}\,A$, then for every value $y$ the fiber counts under
$w$ and $w'$ are equal (`transcript_witness_indep`), the transcript is uniform
on its coset with multiplicity $|\ker A|$ (`fiber_card_const`), and the
simulator $u\mapsto Au+r$ from any public representative $r$ reproduces the
honest distribution exactly (`simulator_exact`); PMF forms `pmf_*`.

**Corollary (surjective case; `MaskingSurjective.lean`, [L]).** If $A$ is
surjective, the coset condition is vacuous: WI holds for *every* pair
(`transcript_witness_indep_of_surjective`, `pmf_*`). This is used for the
round-pair block under A1′.

**Composition (`MaskingSurjective.lean`, [L]) — CORRECTION: does not apply as
previously instantiated.** For two independent mask channels
$g_1:U_1\to V$, $g_2:U_2\to V$ that are **additive homomorphisms**, the
coproduct $g_1\boxplus g_2$ has range $=\mathrm{Im}\,g_1+\mathrm{Im}\,g_2$
(`mem_range_coprod`, `coprod_covers`). An earlier revision of this document
instantiated $g_1$ = the existing masks and $g_2$ = the $P\cdot Q$ channel and
concluded the whole amended transcript reduces to the single-map theorem.
That instantiation is **invalid**: the existing-mask channel is not additive
on the round-pair coordinates — it carries certified $u_A\!\cdot\!u_B$
bilinear cross terms (L4, `zk_affinity_probe.rs`), so `coprod_covers`'s
hypothesis fails on exactly the class it was needed for.

The correct composition is **triangular/conditional**: fix the outer masks
$(u_B, Q)$; the transcript is then affine in the remaining (inner) channels
$(u_A,\mu,g,P)$, whose joint image must cover the claim-conditioned
witness-difference directions on the kernel of the leakage map; the
$u_B$-dependent coordinates (e.g. the $\hat b$-side final evaluation) are
handled by the outer stage on the quotient; mixing over $Q$ carries an
explicit bad-set term. The abstract lemma (`MaskingTriangular.lean`, with a
bad-set mixture bound `MaskingMixtureBadSet.lean`) and the corresponding
full-transcript certificate are the load-bearing replacements — see §0 status.
`MaskingMixture.lean` (the flat fixed-$u_B$ mixture) is retained only as a
stepping stone: its `h_coset` hypothesis is **disproved on the full
transcript** (`final_b_breaks_full_mixture_hcoset`).

---

## 5. The amendment A1′ (item #4)

Run the zerocheck AB sumcheck on $\hat a\hat b + \gamma\,P Q$, where:
- $P,Q$ are two fresh **full-support** random multilinears drawn from the
  prover DRBG, carrying **no witness**, committed in the initial commitment
  (bound before any challenge);
- after committing, the prover observes the mask sum
  $\sigma=\sum_x\mathrm{eq}(r,x)P(x)Q(x)$ and the verifier samples $\gamma$;
- each round message becomes $G_j+\gamma M_j$ ($M_j$ = the round pair of the
  $P\cdot Q$ product sumcheck); the running target is shifted by the mask's
  contribution; the final AB check becomes
  $\hat a(\rho)\hat b(\rho)+\gamma\,P(\rho)Q(\rho)$, with $P(\rho),Q(\rho)$
  opened at the zerocheck point through the batched opening.

Round-1 is left unmasked (it is already affine and covered, L3); only the
multilinear round pairs receive the channel.

**Why it hides (the design's core).** Because $P,Q$ are witness-free, the mask
contribution's distribution is witness-independent by construction. But the
checkable statement is the **joint, conditional** one, not the marginal one.
The same $P$ that masks the round pairs is also revealed through $P(\rho)$,
$\sigma$, and every other $P$-functional the verifier sees (including the
values inside $P$'s own hiding opening); revealing those constrains $P$ and
can un-blind the round messages. The load-bearing condition is therefore:

> **(★′)** For a uniform $Q$, the map $P\mapsto(\text{round-pair coordinates
> of } P\cdot Q)$, **restricted to the kernel of the map $L$ collecting every
> other revealed $P$-functional** ($P(\rho)$, $\sigma$, opening-internal
> values), covers every claim-conditioned witness-difference direction of the
> round-pair block: $d\in R(\ker L)$.

Marginal surjectivity of $P\mapsto\text{round pairs}$ (the earlier (★)) is
*necessary but not sufficient*; the measured facts are that conditioning on
$P(\rho)$ removes exactly one $\mathbb{F}_{2^{128}}$-direction (the internal
ab-claim direction, itself hidden by the affine channel) and conditioning on
$\{P(\rho),\sigma\}$ removes two, with the residuals determined by the claim
(`full_conditional_coverage_zk_zerocheck`, `conditional_coverage_p_rho`).
Given (★′) at fixed $(u_B,Q)$: the inner map is affine in $P$ with the
required conditional image, so the combined round pair $G_j+\gamma M_j$ is
uniform on the claim-conditioned space — exact distribution equality on the
slice. Mixing over $Q$ carries the explicit bad-set term of §8, and
composition with the affine classes is the **triangular** argument of §4
(correction), *not* the coproduct lemma.

---

## 5b. The amendment A2: a committed mask channel for the lincheck

A1′ masks the zerocheck's round messages. It does not touch the lincheck,
which is covered only by the randomizer witness rows — and on a real BLAKE3
statement those rows are ~5.5% of the witness, against ~81% on the synthetic
fixture. Measurement (`tests/zk_blake3_certificate.rs`) localized a
claim-preserving witness direction escaping on `lincheck.rounds` and
`lincheck.z_partial`, and six candidate explanations were eliminated
experimentally before the construction was changed; the record is in
`docs/lincheck-mask-channel.md`.

**The construction.** The lincheck proves $\sum_i \mathrm{comb}(i)\,z(i)=T$
by a product sumcheck in which $\mathrm{comb}$ is **public** and the $z$-slot
enters **linearly**. That is a stronger structure than the zerocheck's, and
it admits a strictly simpler repair than the degree-2 $S\cdot T$ channel A1′
needed: mask the $z$-slot additively.

1. Draw a witness-free cube $S$ from the prover DRBG (fork `a2-S`), zero its
   padding rows, and commit it hidingly (`commit_zk`). Its root is bound with
   $P$'s and $Q$'s, before any challenge of the run.
2. After $\alpha$ and the const-pin $\beta$ fix `comb`, absorb
   $\sigma_{lc}=\sum_i \mathrm{comb}(i)\,S_{\mathrm{vec}}(i)$, then draw
   $\gamma_{lc}$.
3. Run the sumcheck on $z+\gamma_{lc}S$ with initial claim
   $T+\gamma_{lc}\sigma_{lc}$.
4. Recover the output claim as $w = w_{\text{sent}} + \gamma_{lc}\hat S(\rho)$
   (char 2), with $\hat S(\rho)$ opened against $S$'s commitment at the
   lincheck's own output point.

**Why it hides.** Every message of the layer — the round pairs and
`z_partial` — is a deterministic function of the shifted table
$z+\gamma_{lc}S$ at fixed public `comb` and fixed challenges. So the masked
transcript is *exactly the honest transcript of a shifted witness*. This is a
different and stronger situation than A1′'s: there the mask had to cover a
witness-difference direction inside a quadratic form, and coverage was a
rank condition to be certified. Here the shift acts on the layer's input.
The remaining question is only how much of $\mathbb{F}_{2^{128}}^k$ the
reachable shifts $\gamma_{lc}\cdot\mathrm{fold}_{x_{\text{outer}}}(S)$ span,
since $S$ is a **Boolean** cube: $\mathrm{fold}(S)[i]=\sum_j
\mathrm{eq}_j S[j,i]$ ranges over the $\mathbb{F}_2$-span of the eq-table
entries, one independent draw per $i$. That span is full whenever the eq
table $\mathbb{F}_2$-spans $\mathbb{F}_{2^{128}}$ — a property of the
challenges, so it is **measured, not assumed**, by the same joint coverage
certificate that covers the rest of the transcript.

**Completeness.** Structural: the masked run *is* an honest run of the
existing prover on $z+\gamma_{lc}S$ with the initial claim shifted by
$\gamma_{lc}\sigma_{lc}$. Pinned end-to-end by
`masked_roundtrip_recovers_the_unmasked_claim`, which also checks that
$\hat S(\rho)$ carries exactly the PCS's evaluation semantics — the
statement the opening will be asked to certify.

**Soundness of the batching (Lemma L6, transplanted).** Let
$\delta = \sum\mathrm{comb}\cdot z - T$ and
$\delta' = \sigma_{lc} - \sum\mathrm{comb}\cdot S$. Both are fixed before
$\gamma_{lc}$ is drawn ($z$ and $S$ by their commitments, $\sigma_{lc}$ by
absorption). The combined initial claim is correct iff
$\delta+\gamma_{lc}\delta'=0$, so a prover with $(\delta,\delta')\neq(0,0)$
succeeds for at most one $\gamma_{lc}$: probability $2^{-128}$, and the
Fiat–Shamir ordering denies the choice. Constructive check:
`masked_verify_rejects_sigma_tamper`.

**Why $\hat S(\rho)$ must be opened, not merely claimed.** This is the step
the amendment's own spec flagged as most likely to go wrong, and it is a real
attack rather than a formality. The verifier reconstructs
$w = w_{\text{sent}}+\gamma_{lc}\hat S(\rho)$. If $\hat S(\rho)$ were an
unbound scalar, a prover could pick it *after* $\rho$ is known and set it to
$w_{\text{sent}} - \hat z(\rho)$ for whatever $\hat z(\rho)$ the witness
commitment forces — absorbing an arbitrary defect and leaving the output
claim unconstrained. Binding it to $S$'s commitment removes the freedom.
`a1_tamper_matrix_rejected` covers `lincheck.s_eval`, `lincheck.sigma_lc`,
`comm_s.root`, and the open_s/comm_s substitutions.

**Knowledge soundness is unchanged.** $S$ enters no R1CS constraint; it is a
term added to a claim, and the extractor still recovers $z$ from the witness
commitment, whose opening is checked at the un-shifted claim $w$.

---

## 6. Completeness and knowledge preservation (item #18, [P]+[C])

**Completeness [P].** The mask rows (randomizer + $P,Q$ columns) are
unconstrained-but-satisfiable; the honest running target starts at
$\gamma\sigma$ and the combined sumcheck telescopes exactly (checked:
`a1_prime_combined_completeness_and_soundness` builds the combined transcript
from the real prover and verifies
$\text{running}=\hat a(\rho)\hat b(\rho)+\gamma P(\rho)Q(\rho)$; tampering a
masked round pair breaks it).

**Lemma L6 (γ-batching: completeness and soundness of the amendment;
[P]+[C]).** The amendment replaces the zerocheck claim
$\sum_x \mathrm{eq}\cdot\hat a\hat b = \mathsf{ab\_init}$ by the random
linear combination
$\sum_x \mathrm{eq}\cdot(\hat a\hat b + \gamma PQ)
 = \mathsf{ab\_init} + \gamma\sigma_z$.

*Completeness.* For an honest prover both sides telescope through the same
round schedule (the round messages are $G_j+\gamma M_j$ and the running
target carries $\gamma$ times the mask sumcheck's), so the final check
$\text{running} = \hat a(\rho)\hat b(\rho) + \gamma P(\rho)Q(\rho)$ holds
identically.

*Soundness.* Fix all prover messages. The verifier's final residual
$R(\sigma_z) = \text{running} + \hat a(\rho)\hat b(\rho) + \gamma
P(\rho)Q(\rho)$ is **affine in $\sigma_z$** over $\mathbb{F}_{2^{128}}$,
with slope $\gamma\cdot\prod_j (1+\rho_j)/(1+r_{\mathrm{eq},j})$. Writing
$\delta$ for the $\hat a\hat b$-side defect and $\delta'$ for the mask-side
defect, acceptance requires $\delta + \gamma\delta' = 0$: for
$(\delta,\delta')\neq(0,0)$ at most **one** $\gamma$ satisfies it, so a
prover who must fix $(\delta,\delta')$ before seeing $\gamma$ is accepted
with probability $\le 2^{-128}$, on top of the unchanged sumcheck error.
The ordering is what supplies "before": the $P,Q$ commitment roots and
$\sigma_z$ are absorbed into the transcript *before* $\gamma$ is sampled
(`prove_r1cs_zk_a1` absorbs both roots; `prove_packed_padded_zk` observes
$\sigma_z$ then samples $\gamma$).

*Constructive check [C]* (`zerocheck.rs::zk_gamma_cancellation_unique_and_fs_ordering`):
on an invalid witness the test measures the affine response, **solves** for
the unique $\sigma^\star$ that cancels the defect, and shows (i) the patched
proof is accepted by the real verifier when challenges are fixed in advance
— i.e. the ordering attack genuinely works if $\sigma_z$ may be chosen after
$\gamma$ — and (ii) the same proof is rejected under Fiat–Shamir, and at 100
further challenge tuples. This exhibits the accept-set in $\gamma$ having
size exactly one, which is the content of the $2^{-128}$ bound, on the real
code. A small-field exhaustive port is **descoped**: $\mathbb{F}_{2^{128}}$
is load-bearing throughout the kernels (GHASH, 128-bit packing, the $\varphi_8$
skip basis), so a small-field variant would be an idealized duplicate of the
protocol rather than the shipped one; the constructive test establishes the
same fact on the real prover (review item #17).

**Knowledge soundness UNCHANGED [P].** Every valid original witness extends to
a valid randomized witness (fill the mask columns with any bits), and every
accepting extended witness restricts to a valid original witness (the mask
columns feed no real constraint; A-rows meet only the constant-1 wire on the
$b$-side, B-rows only on the $a$-side; $C=I$ has explicit zero rows at mask
slots). The knowledge extractor runs on the real-wire sub-witness unchanged.
The constant-one wire is genuinely constrained to 1 (lincheck $\beta$-fold,
$\beta$ sampled after the round-1 message). Randomizer/padding rows cannot
carry witness-dependent data that satisfies a real constraint. This is a
statement change absorbed into `statement_digest`, not a change to the
knowledge claim on the hash wires.

Privacy (this document) and soundness are proven separately and neither is
used to justify the other (item #7).

---

## 7. PCS hiding (items #8, #9)

**Low-mask interpolation lemma L9 ([P], encoder-checked [C]).** The additive-
NTT (LCH) basis is degree-graded: basis polynomial $j$ has degree $j$. The
mask $\mu$ occupies the low $t$ coefficient slots
(`commit.rs::replicate_message_fill_zk`, positions $p<\text{mask\_positions}$),
which span all polynomials of degree $<t$; evaluation of $\{\deg<t\}$ at any
$t$ distinct domain positions is a bijection (Vandermonde over distinct
points), so the mask-to-symbol map is surjective at every query set, at every
recursive level, **identically in the challenges** ($\varepsilon_\mu=0$). A
top-half mask would be multiplied by a subspace-vanishing polynomial and
contribute nothing on half the domain — hence the low placement. (An
encoder-vs-math test should pin the concrete slot order against this map.)

**Blinder coverage L10 ([P], regression-[C]).** The full-support blinder $g$,
uniform over the doubled message space, is folded as $F=m'+c\,g$; every opened
row, internal sumcheck message, and $y_r$ is $\mathbb{F}_{2^{128}}$-linear in
$F$, so $g$ masks them at every level. $y_g=\langle g_{\text{top}},b\rangle$ is
uniform (linear in $g$). This upgrades the PCS rank audit's premise from
sampled to structural.

**Unopened-sibling hiding, and the hash assumption (item #8) [A].** Collision
resistance gives binding, not hiding. We state the hiding assumption
explicitly: model SHA-256 as a random oracle (or assume it is a PRF /
one-way over high-min-entropy inputs). Each level-0 leaf carries its 64
$g$-lane symbols — $\ge 8192$ bits of fresh DRBG entropy; deeper leaves are
encodings of $g$-blinded folds. Condition on **all** revealed data (opened
rows across every level, $y_g$, the sumcheck messages, $y_r$): the linear
functionals of $g$ that are revealed number at most $128\cdot(\#\text{revealed
values})$, spread across leaves, so each unopened leaf retains conditional
min-entropy $k_{\min}\ge 8192-512$ (conservative). An unopened sibling hash is
then the RO image of a $k_{\min}$-min-entropy preimage, distinguishable from
uniform with advantage $\le q\cdot 2^{-k_{\min}}$ over $q$ queries
($\varepsilon_{\mathrm{hash}}$). In the QROM this becomes
$O(q\cdot 2^{-k_{\min}/2})$.

---

## 8. The bad-mask bound (items #3, #10)

$\varepsilon_{\mathrm{rank}}=\Pr_{P,Q}[\neg(\star)]$: the probability the
mask draw fails to cover the round-pair block.

**Lemma L7 ([P], witness-[C]).** (★) holds iff a covering minor $D(Q)$ of the
matrix $[P\mapsto \text{round-pairs}(P\cdot Q)]$ is nonzero. $D$ is a
polynomial in the entries of $Q$ (and the challenges); it is **not identically
zero** because a specific uniform $Q$ makes the map surjective — and that
witness is exhibited by `a1_prime_masks_round_pairs` (full rank $2304$ at
$m=15$, over multiple uniform draws, including the $G(\infty)$ coordinates). A
constant $Q$ (measure $\approx 0$) gives $\Delta Q\equiv 0$ and covers only the
$G(1)$ half — the test records exactly this, delimiting the bad set.

**Lemma L8 — WITHDRAWN.** An earlier revision bounded
$\varepsilon_{\mathrm{rank}}$ by Schwartz–Zippel: entries of degree
$d^\star\lesssim 90$ over "uniform mask entries in $\mathbb{F}_{2^{128}}$"
giving $d^\star/2^{128}$. That argument is unsound for the shipped prover, for
three independent reasons. (i) **Wrong domain**: the implemented $P,Q$ are
Boolean — `prover.rs::sample_mask_bits` draws one *bit* per cube entry — so
the mask entries range over $\{0,1\}$, where Schwartz–Zippel gives
$\deg/2 \ge 1$: vacuous. (ii) **Wrong degree object**: $d^\star$ bounds a
single matrix *entry*; the covering minor $D$ is a determinant whose degree is
the sum over rows (~$2304\times$ larger). (iii) **Mixed variable sets**: the
degree count is over the challenge variables while the probability is taken
over the mask entries.

**Replacement (per-proof fail-closed self-check).** The map
$P\mapsto(\text{round pairs}\,|\,L)$ at the prover's actual $(Q,\text{
challenges})$ is $\mathbb{F}_2$-linear; the reference prover verifies the
required conditional coverage for its own draw by an exact $\mathbb{F}_2$ rank
computation (random-probe spanning through the real fold kernels + Gaussian
elimination) and **aborts and resamples $P,Q$ on failure**. The failure event
depends only on $(Q,\text{challenges})$ — both witness-independent — so
resampling leaks nothing. Consequence: $\varepsilon_{\mathrm{rank}} = 0$ for
every *emitted* proof; the unproven quantity becomes the resample probability,
which affects liveness, not privacy (measured 0 across all recorded runs; a
closed-form bound over Boolean $Q$ remains open). Note: masking a value
"needs 128 bits" is only a heuristic unless the induced map has full rank;
here rank is what is *checked per proof*, not inferred from bit-count.

---

## 9. Fiat–Shamir (item #6, [P]+[S])

The interactive argument is public-coin and $\mathsf{S}$ is non-programming
(§2), so the classical-ROM NIZK simulator is $\mathsf{S}$ itself: at any fixed
oracle, the compiled transcript distribution equals the honest one whenever
Z1's conditional equality holds; averaging over the oracle gives Z2 with error
$\varepsilon_{\mathrm{rank}}+\varepsilon_{\mathrm{hash}}$. No rewinding, no
programming. Challenge derivation, the PoW grind (SHA-256 leading-zeros,
absorbed before the dependent challenge), and retries are all reflected in the
transcript the simulator itself produces, so they need no separate treatment.
QROM: §1 Z3.

---

## 10. Repeated-proof security and randomness (items #12, #13)

`ZkRng::from_entropy()` is called **per proof** (BLAKE3 XOF keyed from
`getrandom`; panics if entropy is unavailable — fail-closed). Domain-separated
forks feed the witness randomizers, $\mu$, $g$, and $P,Q$ independently; the
fork counter + label prevent collisions even under a reused parent. The DRBG
never touches the Fiat–Shamir transcript (mask randomness reaches it only
through committed data). Deterministic seeding exists only on explicitly
test-facing entry points. Hence $k$ proofs of the same or related witnesses use
independent masks and compose by a hybrid with error
$k(\varepsilon_{\mathrm{rank}}+\varepsilon_{\mathrm{hash}})$; there is no
linear-cancellation across proofs. (Zeroization of mask buffers and a
fork-collision test are hardening items tracked separately.)

---

## 11. Leakage boundary (item #11)

The transcript is allowed to reveal, and reveals only: the statement digest
(matrices + zk layout), batch size, proof size and parameter selection, the
Fiat–Shamir challenges, PoW nonces, query positions, and the accepted claim
*as a constrained quantity* (the opening proves $\hat z(r)=v$, so the
consistency relations determine $\gamma v + c\,y_g$ from revealed values — this
is why WI conditions on the public claim, not a weakening). Everything else —
every masked field element, every unopened sibling — is proven
witness-independent (§4–§8) or computationally hidden (§7). No timing,
retry-count, memory-access, failure-message, or witness-dependent
sparsity/layout channel is claimed to be closed; those are side channels, out
of scope (§0).

---

## 12. Comparison (item #20) and the disposition table (item #22)

**Comparison.** The randomizer rows are the ethSTARK randomizer-trace idea
transplanted to a batch-R1CS PIOP; the hiding opening is Ligero/Ligerito
masking; the degree-2 $P\cdot Q$ channel is the Chiesa–Forbes–Spooner
masking-polynomial idea rebuilt for characteristic 2 (where the separable mask
vanishes). Diamond (ePrint 2025/1015) gives a ZK polynomial commitment over
binary fields; whether it could *replace* the hiding opening (removing $\mu$
and $g$) is open and worth settling. What is genuinely new here is the
reduction (no public input ⇒ honest-prover simulator ⇒ WI) plus the exact
image-coverage certification methodology and the degree-2 channel's
witness-free surjectivity argument.

**Disposition of the 22 review items.**

| # | Item | Status |
|---|------|--------|
| 1 | Exact claim | **[P]** §1 |
| 2 | Explicit simulator | **[P]+[C]** §2, `zk_simulator.rs` |
| 3 | Replace sampled audits | partial **[C]** — exact image extraction, but witness-difference coverage is sampled and the full-transcript joint certificate is remaining §3/§8 |
| 4 | Bilinear zerocheck | **[P]+[C]** §5 (`a1_prime_*`); the Lean surjective corollary applies only once (★′) is certified — its hypothesis is a Rust measurement, not Lean |
| 5 | Joint hiding | **open** — zerocheck-layer conditional certificate only (single fixed Q, randomizers zeroed); composition lemma invalid as previously instantiated (§4 correction); full-transcript certificate + triangular lemma remaining |
| 6 | Fiat–Shamir ROM | **[P]+[S]** §9 |
| 7 | Separate ZK/soundness | **[P]** §6 (separated theorems) |
| 8 | Hash assumptions | **[A]** §7 (stated explicitly) |
| 9 | Low-mask interpolation | **[P]**, encoder-test remaining §7 |
| 10 | Mask entropy = rank | partial — rank certified at sampled draws; closed-form bound **withdrawn** (§8), per-proof self-check is the replacement |
| 11 | Leakage boundary | **[P]** §11 |
| 12 | Repeated-proof | **[P]** §10 |
| 13 | Randomness lifecycle | **[P]**, zeroization/fork-test remaining §10 |
| 14 | Protocol↔code audit | partial (this doc cites sites); full correspondence doc remaining |
| 15 | Adversarial tests | partial (negative controls + tamper); systematic suite remaining |
| 16 | Leakage-search framework | the exact image-cover harness is a start; polynomial-feature search remaining |
| 17 | Small exhaustive models | the F₂ image certificate is the feasible exact analogue (F₂₁₂₈ blocks brute force); small-field port remaining |
| 18 | Completeness/witness semantics | **[P]+[C]** §6 |
| 19 | Every circuit family | **scoped out** — BLAKE3 batch only |
| 20 | Compare prior work | **[P]** §12 (this section) |
| 21 | Benchmarks | separate; median/variance/component breakdown remaining |
| 22 | Release criteria | **not met** — candidate/experimental; needs the amendment wired, machine-checked bounds, and independent review |

**Bottom line.** For BLAKE3 batch statements, ZK reduces to full-transcript
WI (proven, L1). The affine transcript classes are hidden exactly
(Masking.lean + exact certificates); the round messages are the hard class,
targeted by the degree-2 $P\cdot Q$ channel with the *conditional* coverage
condition (★′). Still open before the WI theorem is established: the
complete-transcript joint certificate, the triangular composition lemma, and
the per-proof rank self-check replacing the withdrawn Schwartz–Zippel bound.
Sibling hiding is computational under a stated hash assumption; the FS lift
is unconditional via the non-programming simulator *given* WI. The result is
a candidate ZK mode with a proven partial core, pending those closures and
independent review.

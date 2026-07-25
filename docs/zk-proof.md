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
- The joint conditional coverage is verified on the **real amended prover** at
  the zerocheck layer (`full_conditional_coverage_zk_zerocheck`, `L={P(ρ),σ_z}`
  — no claim-preserving witness direction leaks); the affine and PCS layers
  reuse the existing exact certificates, composing by the independent-channel
  lemma (`MaskingSurjective.coprod_covers`, Lean). What remains: assembling
  these into **one** complete-transcript certificate over the integrated
  prover, for a small explicit parameter set (currently one fixture per
  layer).
- The bad-mask probability bound (§8) and the Merkle-sibling hiding argument
  (§9) are closed-form but **not machine-checked** with an explicit numerical
  constant; per-parameter certificate gating is not yet wired.
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

**Claim (Z1, interactive, [P]+[L]+[C]+[A]).** There is a PPT simulator
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

**Claim (Z3, QROM, [P]+[A]).** $\mathsf{S}$ programs nothing and rewinds
nothing, so the ZK property survives quantum oracle access verbatim except
$\varepsilon_{\mathrm{hash}} \to O(q\cdot 2^{-k_{\min}/2})$ (generic quantum
search / O2H). **QROM soundness is not claimed.**

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
affine in $u$. (A runtime layout assertion enforces the alignment the proof
relies on.)

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

**Composition (`MaskingSurjective.lean`, [L]).** For two independent mask
channels $g_1:U_1\to V$, $g_2:U_2\to V$, the coproduct
$g_1\boxplus g_2$ has range $=\mathrm{Im}\,g_1+\mathrm{Im}\,g_2$
(`mem_range_coprod`), so if the witness-difference splits as
$d_1+d_2$ with $d_i\in\mathrm{Im}\,g_i$ then it is covered by the joint map
(`coprod_covers`). Under A1′: $g_2$ = the $P\cdot Q$ channel (round-pair
block), $g_1$ = the existing masks (affine classes).

This is why the *whole* amended transcript reduces to the single-map masking
theorem; `MaskingMixture.lean` (the fixed-$u_B$ conditional argument) is
retained only as the fallback for the un-amended, bilinear protocol.

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
contribution's distribution is witness-independent by construction. Hiding of
the round pairs reduces to a clean, checkable statement:

> **(★)** For a uniform $Q$, the map $P\mapsto(\text{round-pair coordinates of
> } P\cdot Q)$ is surjective onto the round-pair coordinate space.

Given (★): at any fixed $Q$ the map is affine in $P$ with full image, so the
combined round pair $G_j+\gamma M_j$ is uniform over the round-pair space
regardless of the witness-dependent $G_j$ — exact distribution equality
(Theorem 4, surjective corollary). Mixing over $Q$ preserves it (WI is a
per-$Q$ property, and $Q$ is witness-free). Composition (Theorem 4) with the
affine classes covers the whole transcript.

---

## 6. Completeness and knowledge preservation (item #18, [P]+[C])

**Completeness [P].** The mask rows (randomizer + $P,Q$ columns) are
unconstrained-but-satisfiable; the honest running target starts at
$\gamma\sigma$ and the combined sumcheck telescopes exactly (checked:
`a1_prime_combined_completeness_and_soundness` builds the combined transcript
from the real prover and verifies
$\text{running}=\hat a(\rho)\hat b(\rho)+\gamma P(\rho)Q(\rho)$; tampering a
masked round pair breaks it).

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

**Lemma L8 (Schwartz–Zippel [P]/[S]).** Each matrix entry is a product of
$\le m$ eq-factors (degree $\le 1$ per challenge variable) and the
univariate-skip Lagrange factors (degree $\le 63$ in the round-1 challenge),
so $\deg D \le d^\star$ with $d^\star = 63 + (m-7) + \dots = O(m)$
(concretely $d^\star \lesssim 90$ at $m=22$). Over the uniform mask entries in
$\mathbb{F}_{2^{128}}$, $\varepsilon_{\mathrm{rank}}\le d^\star/2^{128}$ per
covered dimension — negligible ($\ll 2^{-100}$) at production sizes. (Mathlib
carries a Schwartz–Zippel lemma; formalizing this instantiation is optional
future work.) Note: masking a value "needs 128 bits" is only a heuristic
unless the induced map has full rank; here rank is what is certified, and L8
bounds the failure probability rather than inferring hiding from bit-count.

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
| 3 | Replace sampled audits | **[C]+[P]** exact image cert §3/§8; full-rank on the amended prover is remaining |
| 4 | Bilinear zerocheck | **[P]+[C]+[L]** §5, `a1_prime_*`, surjective corollary |
| 5 | Joint hiding | **[P]+[L]+[C]** §3–§5 |
| 6 | Fiat–Shamir ROM | **[P]+[S]** §9 |
| 7 | Separate ZK/soundness | **[P]** §6 (separated theorems) |
| 8 | Hash assumptions | **[A]** §7 (stated explicitly) |
| 9 | Low-mask interpolation | **[P]**, encoder-test remaining §7 |
| 10 | Mask entropy = rank | **[C]+[P]** §8 |
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
WI (proven, L1); the affine transcript is hidden exactly (Masking.lean +
exact certificate); the round messages are hidden by the degree-2 $P\cdot Q$
channel (surjective corollary + certificate), with a Schwartz–Zippel bad-mask
bound; sibling hiding is computational under a stated hash assumption; the FS
lift is unconditional via the non-programming simulator. The result is a
candidate ZK mode with a proven core, pending the amendment's production wiring
and independent review.

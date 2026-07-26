# Making Flock Zero-Knowledge — research note (v5.1)

A candidate zero-knowledge mode for BLAKE3 batch statements in Flock, a
hash-based SNARK for batch R1CS over F₂.

**Decision label: B — experimental candidate with a proven partial core.**
Not production zero-knowledge, and not independently reviewed. The
complete-transcript coverage certificate now **passes** at the certified
fixture — over all 548 witness-dependent coordinates, at three challenge
tuples, conditioned on the complete mask-only leakage set and on every public
claim the verifier learns, no claim-preserving witness direction escapes the
joint mask image. Measured *at* the production configuration (m=22): the degree-2 channel spans
the round-pair block in full (4096/4096 bits), a degenerate Q spans exactly
half, the per-proof coverage self-check passes with no resampling and its
proof verifies, and the randomizer margin binding `s_hat_v` is 12× the
requirement versus 3× at the fixture. What keeps this at label B: run directly on a *real* BLAKE3 statement
(m=20, PIOP classes), one F128 direction of claim-preserving witness
difference is still unaccounted for — a specific measured lead, not a proven
leak. Plus the ROM assumption and the absence of independent review.

**What changed in v5.1 — amendment A2.** v5 stated the lincheck's transcript
classes were covered by the randomizer witness rows. Measurement refuted that,
so the construction gained a second mask channel: a committed additive shift
`z ↦ z + γ_lc·S` for the lincheck. It is a different kind of channel from the
zerocheck's on purpose — the zerocheck masks a *product* of witness-dependent
multilinears and needs a degree-2 mask, while the lincheck's multiplier is
*public* and its z-slot *linear*, so an additive shift makes that layer's
transcript equal to the honest transcript of a shifted witness. Measured: the
lincheck classes go from 9,728/10,240 bits with 128 escaping to 10,240/10,240
with nothing escaping.

With A2 in, the residual on the unrestricted real-statement run is attributed
to **one** class, `zerocheck.round1_c` — down from three. That class is the
univariate-skip C-side message, linear in the witness, sitting outside the
degree-2 channel by design (a mask there would not vanish on the constraint
domain and would break the zerocheck assumption). The escape there is *joint,
not marginal*: `round1_c` passes in isolation at 8,192/8,192, and only fails
when it must be covered simultaneously with everything else. The repair is
specified in `docs/round1c-mask-channel.md` and not made.

The label does not move on partial progress: one of the two measured gaps is
closed with a built, tested, soundness-argued amendment; the other is open.

## The claim, exactly

For an explicitly enumerated set of certified BLAKE3 *batch* configurations
that bind no externally supplied message, chaining value, or hash output:

> the algebraic transcript of the **reference** amended prover is statistically
> witness-indistinguishable up to an explicit rank-failure term ε_rank, and the
> complete protocol is **computational** zero-knowledge in the classical
> random-oracle model — because hiding of unopened Merkle siblings is
> computational, not statistical.

Not claimed: SHA-256, Keccak, hash chains, externally bound hashes, recursive
composition, QROM security, side channels, and the optimized prover (which runs
the un-amended zerocheck).

## Claims at a glance

| Claim | Scope | Basis | Status |
|---|---|---|---|
| Completeness | reference prover, certified configs | telescoping identity; roundtrip tests | proved; tested |
| Zerocheck soundness (γ batching) | amended zerocheck | Lemma L6 + adversarial suite | proved; constructively checked |
| Algebraic-transcript WI | certified configs | Lean + exact certificates | **established at the certified fixture** |
| Merkle sibling hiding | all hiding openings | k_min-min-entropy leaves, ROM | assumed (computational) |
| ZK after Fiat–Shamir | BLAKE3 batch, certified configs | reduction + rows above | conditional on those rows |
| QROM | — | — | not claimed |
| Optimized prover | excluded | — | benchmark only; no ZK claim |

## What is new relative to v4

The security label was corrected (statistical HVZK → computational ZK in the
classical ROM); the claim was narrowed to the reference prover; the
Schwartz–Zippel bound on ε_rank was **withdrawn** (the implemented masks are
Boolean, so its hypothesis is false) and replaced by a per-proof coverage check;
the image-addition composition step was replaced by a triangular composition
machine-checked in Lean; and the certified configurations are enumerated with a
fail-closed API. Full list in `CHANGES.md`.

## Performance

Two pipelines, not comparable. Optimized (no ZK claim): 2.24/3.16/3.95× prove,
0.98–1.03× verify, 1.65–1.82× proof size versus non-zk, at batches 2¹⁰/2¹²/2¹⁴.
Reference amended prover at 2⁸ compressions (m=22): 22.8 ms prove, 4.5 ms
verify, versus 3.8 ms for the non-zk fused prover — a reference-implementation
artefact, not a cost of zero-knowledge.

Amendment A2 costs 20.0 → 22.8 ms proving and 4.3 → 4.5 ms verification: one
more full-size commitment and opening. That is more than the channel needs —
`S` only masks the length-2^k_log folded table (4,096 entries here, against
2²²), so a commitment over that domain would be some three orders of magnitude
smaller. Left unoptimized on purpose: correctness first, cost second.

## Building the paper

```sh
pdflatex zk-flock.tex && pdflatex zk-flock.tex   # or: tectonic zk-flock.tex
```

## Reproduction

Implementation, certificates, and Lean development live in the Flock repository
on the branch this note was written from; see the paper's Appendix B for exact
commands and `docs/review-dossier.md` for the full evidence index, exact bounds,
test inventory, and unresolved assumptions.

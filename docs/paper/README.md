# Making Flock Zero-Knowledge — research note (v5)

A candidate zero-knowledge mode for BLAKE3 batch statements in Flock, a
hash-based SNARK for batch R1CS over F₂.

**Decision label: B — experimental candidate with a proven partial core.**
Not production zero-knowledge, and not independently reviewed. The
complete-transcript coverage certificate now **passes** at the certified
fixture — over all 548 witness-dependent coordinates, at three challenge
tuples, conditioned on the complete mask-only leakage set and on every public
claim the verifier learns, no claim-preserving witness direction escapes the
joint mask image. What keeps this at label B is that the certificate is
per-fixture: transfer to the production shape rests on structural identity of
the maps, and the ROM assumption and independent review remain.

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

Two pipelines, not comparable. Optimized (no ZK claim): 2.2–3.6× prove,
~1.0× verify, 1.65–1.82× proof size versus non-zk, at batches 2¹⁰–2¹⁴.
Reference amended prover at 2⁸ compressions (m=22): 20.0 ms prove, 4.3 ms
verify, versus 4.3 ms for the non-zk fused prover — a reference-implementation
artefact, not a cost of zero-knowledge.

## Building the paper

```sh
pdflatex zk-flock.tex && pdflatex zk-flock.tex   # or: tectonic zk-flock.tex
```

## Reproduction

Implementation, certificates, and Lean development live in the Flock repository
on the branch this note was written from; see the paper's Appendix B for exact
commands and `docs/review-dossier.md` for the full evidence index, exact bounds,
test inventory, and unresolved assumptions.

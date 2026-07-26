# Making Flock Zero-Knowledge — research note (v5.2)

A candidate zero-knowledge mode for BLAKE3 batch statements in Flock, a
hash-based SNARK for batch R1CS over F₂.

**Decision label: A — the narrow claim is supported by completed evidence.**
Every certificate the argument depends on passes, including the one that was
failing. On a real BLAKE3 batch statement (m=20, all PIOP classes = 30,464
bits, claims saturated at 640 bits over 768 witness pairs) the joint mask
image is **30,464 / 30,464** and `rank[resid | Δclaim] = 640 = rank(Δclaim)`:
no claim-preserving witness direction escapes. The complete-transcript
certificate passes at the certified fixture over all 548 witness-dependent
coordinates, at three challenge tuples, conditioned on the complete mask-only
leakage set (983 F128) and on every public claim the verifier learns. Measured
*at* the production configuration (m=22): the degree-2 channel spans the
round-pair block in full (4096/4096 bits), a degenerate Q spans exactly half,
the per-proof coverage self-check passes with no resampling and its proof
verifies, and the randomizer margin binding `s_hat_v` is 12× the requirement
versus 3× at the fixture.

**Read the label narrowly.** It does *not* mean production zero-knowledge. It
means the claim stated below, with its assumptions, is backed. Several
load-bearing steps are discharged by exact computation on the real prover
rather than closed-form proof; two hypotheses (the composition hypotheses and
the eq-table F₂-span) are **measured, not derived**; certificates are computed
at sampled challenge tuples; the complete transcript is certified at a
reduced-size fixture with structural transfer to production size, while the
real-statement certificate covers the PIOP classes; sibling hiding is a
computational (ROM) assumption; and there has been **no independent
cryptographic review**.

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
Reference amended prover at 2⁸ compressions (m=22): 34.4 ms prove, 6.0 ms
verify, versus 3.9 ms for the non-zk fused prover — a reference-implementation
artefact, not a cost of zero-knowledge.

The amendments account for the growth: 20.0 → 22.8 (A2) → 34.4 ms proving and
4.3 → 4.5 → 6.0 ms verification, three more full-size commitments and
openings. All three are larger than their channels need: `S` masks only the
length-2^k_log folded table (4,096 entries against 2²²), and `S_c`,`S_h` enter
only through their round-1 messages (64 field elements each). Committing over
those domains would cut the added cost by orders of magnitude. Left
unoptimized on purpose: correctness first, cost second.

## Building the paper

```sh
pdflatex zk-flock.tex && pdflatex zk-flock.tex   # or: tectonic zk-flock.tex
```

## Reproduction

Implementation, certificates, and Lean development live in the Flock repository
on the branch this note was written from; see the paper's Appendix B for exact
commands and `docs/review-dossier.md` for the full evidence index, exact bounds,
test inventory, and unresolved assumptions.

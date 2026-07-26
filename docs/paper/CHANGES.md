# Paper change summary (v4 → v5)

A reader who knows v4 can read this instead of diffing. Weakenings are listed
before strengthenings on purpose.

## Headline deltas

1. **The security label changed.** v4 led with "Statistical honest-verifier
   zero-knowledge". v5 says: the *algebraic* transcript is statistically
   witness-indistinguishable up to ε_rank, and the *complete protocol* is
   **computational** zero-knowledge in the classical ROM, because sibling
   hiding is computational. v4's own §6 already admitted the latter; the
   headline and the body now agree.
2. **The object of the claim narrowed.** The claim attaches to the reference
   amended prover only. The optimized prover runs the un-amended zerocheck and
   is now explicitly excluded, in the abstract, the claim table, and the
   limitations.
3. **The ε_rank bound was withdrawn, not weakened.** v4 bounded ε_rank by
   Schwartz–Zippel over "uniform mask entries in F₂¹²⁸". The implemented masks
   are Boolean (one bit per cube entry), so the hypothesis is false for the
   shipped prover, and SZ over {0,1} at these degrees is vacuous; the bound also
   conflated an entry's degree with a determinant's and mixed two variable sets.
   Replacement: a per-proof rank check with resample-on-failure, giving
   ε_rank = 0 for emitted proofs, with the resample probability stated as open.
4. **QROM was demoted from a hedged claim to "not claimed".**
5. **The composition argument was replaced.** v4 composed the mask channels by
   adding their images (a coproduct lemma). That step is invalid — it needs both
   channels to be additive, and the randomizer channel is certifiably bilinear on
   exactly the coordinates it was needed for. v5 uses a triangular (quotient)
   composition, machine-checked in Lean.
6. **The "public ab-claim" language is gone.** The direction the inner stage
   cannot reach is an internal claim direction carried by the outer stage, not a
   public value; it is never relabelled public to make a theorem pass.
7. **Certified configurations are enumerated and the API fails closed.**

## Claims weakened

- Statistical HVZK for the whole protocol → computational ZK in the classical ROM.
- Whole-protocol claim → reference-prover-only claim.
- ε_rank ≤ deg/2¹²⁸ → ε_rank = 0 per emitted proof, closed form open.
- "exact certificate, not a sampled rank audit" → exact in image extraction;
  witness directions are a structured spanning family plus random draws;
  challenge tuples are sampled.
- QROM statement → not claimed.
- Coprod composition → triangular composition (different, and narrower).
- Any parameter set → the enumerated certified configurations.

## Claims strengthened

- γ-batching soundness is now a stated lemma with a constructive check that
  exhibits the accept-set in γ having size exactly one, on the real code.
- The composition hypotheses (H1 constant inner image; conditional coverage) are
  measured on the complete pipeline, not on the zerocheck layer alone.
- The transcript is enumerated and classified by a canonical schema with
  compile-time, bijectivity, wire-order, and pinned-hash tripwires.
- Simulator exactness is constructive: a solved mask translation makes two
  witnesses' transcripts bit-identical on the covered block.
- Two new Lean theorems (triangular composition; bad-set mixture), with an axiom
  audit script making the "standard axioms only" claim mechanically checked.

## Structural changes

| v4 | v5 |
|---|---|
| §1 Scope + status (with test inventory) | §1 Scope/claim/status (test names moved to Appendix A) |
| — | §2 Relation, definitions, reduction **with proof** |
| — | §3 Claim-at-a-glance table |
| §2 What Flock reveals | §4 Numbered protocol overview + figure + notation table |
| §3 Transcript split | §5 (condensed; char-2 obstruction stated once) |
| §4 + §5 (duplicated ab-claim argument) | §6 (single reconciled account; toy example first) |
| §5 certificates | §7 certificates + certified-configuration table + honest ε_rank |
| §6 assumptions | §9 soundness (new), §10 assumptions |
| — | §8 theorem dependency roadmap |
| §7 comparison + limitations | §11 related work, §13 limitations (itemized) |
| — | Appendix A implementation map, Appendix B reproduction |

## Defects fixed

| Defect | Resolution |
|---|---|
| Headline label contradicted §6 | §1 restated |
| ab-claim argument duplicated in §4 and §5 with contradicting direction counts (one vs two) | single account in §6 |
| "exact, not sampled" overbroad for the PCS layer | scope of exactness stated precisely in §7 |
| No relation, no ZK/WI definitions | §2 |
| Δ overloaded (statistical distance vs witness difference) | `\Dsd` vs `d` |
| k_min, k_skip, ε_hash, μ, g, σ_z undefined | notation table |
| Lemma 1 and Theorem 1 unproved, uncited | Lemma 1 proved; theorems cite their Lean files |
| "8 KiB" of leaf entropy | 8192 bits (1 KiB) |
| §1 "implemented end to end" vs §7 "not yet wired" | superseded text removed |
| `\bibitem{Flock}` never cited | cited in §11 |
| Dead `\shatv` macro | removed |
| No tables, figure, appendix, roadmap | all added |
| Scope/status repeated 3–4× | §1 and §13 only |
| Certificate config vs claim config unreconciled | §7 configuration table |
| No benchmark table despite a measured 2.2–3.8× overhead | §12, two labelled panels |
| No version identifier | date line carries version + source revision |

## Numbers and their provenance

Every measured number in the paper comes from a named test at the release
revision; the commands are in Appendix B and the mapping test-to-claim is in
`docs/review-dossier.md` §8. Numbers not yet measured at the release revision
are marked in the source with `SYNC` placeholders and must not be published
while those placeholders remain.

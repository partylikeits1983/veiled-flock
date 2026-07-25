# Research: joint full-transcript coverage — findings and implementation plan

This responds to the reviewer's requirement that the certificate cover the
**joint transcript** (`d ∈ R(ker L)`, not `d ∈ Im R`), and turns their 18
points into a prioritized, correctness-first plan. It leads with a decisive
experiment that answers the one question everything else hinges on.

## 0. The decisive finding (measured, not argued)

The reviewer's central point is correct: marginal (per-coordinate)
surjectivity is **not** joint zero-knowledge, because the same mask `P`
appears both in the round messages `M_j(P)` and in the opened evaluation
`P(ρ)`. Revealing `P(ρ)` constrains `P`, which can un-blind the round
messages. The correct condition is
$$d_{\text{witness}} \in R(\ker L),$$
where `R` is the round-map and `L` is the map to every *other* revealed
`P`-dependent coordinate.

We measured this exactly on the real prover
(`tests/zk_leakage_certificate.rs::conditional_coverage_p_rho`):

| quantity | value | meaning |
|---|---|---|
| `rank(R)` | 2304 / 2304 | round-map marginally surjective |
| `rank([R;L])`, `L={P(ρ)}` | 2304 | **`P(ρ)` is a linear function of the round messages** (the sumcheck telescoping) |
| `dim R(ker L)` | 2176 | conditioning on `P(ρ)` removes **exactly one F128** direction |
| `rank([residual \| Δclaim])` | `= rank(Δclaim)` | the un-covered direction is **exactly the public ab-claim** |

**Verdict.** The one round direction `P(ρ)` un-covers is precisely the
public ab-claim value `final_a·final_b` — which the WI definition already
conditions on (the opening proves it). So A1′ **does** achieve joint
conditional coverage of the round messages — *under one load-bearing
condition*:

> **`P` and `Q` must be opened via the HIDING opening (the existing μ/g
> machinery), so that only `P(ρ)`/`Q(ρ)` leak — not the opened codeword
> rows.** A plain (non-hiding) opening reveals ~`queries × rows` additional
> `P`-functionals; those enlarge `L` well beyond the single claim direction
> and, by the same `dim R(ker L)` accounting, would un-cover
> claim-preserving witness directions — a real leak.

This is the single most important design consequence of the reviewer's
analysis, and it is now backed by measurement, not intuition.

## 1. What this changes in the design and the paper

1. **Open `P,Q` hidingly.** Route the `P,Q` openings through `commit_zk` /
   the blinded opening, not a plain Ligerito open. (Previously unspecified;
   now required.)
2. **The certificate must be the joint conditional form**, over the *entire*
   `P`-dependent transcript (round messages, `P(ρ)`, and — if any `P`
   material is ever revealed elsewhere — those coordinates too), checking
   `d ∈ R(ker L)` with `d` restricted to the kernel of the public-claim
   functionals. The per-coordinate `affine_classes_exactly_covered` check is
   replaced/augmented by a single joint-image check.
3. **The paper's claim is unchanged in form but now correctly scoped**:
   statistical WI *conditioned on the public claim*, with the explicit note
   that `P,Q` hiding openings are what make the joint coverage hold.

## 2. Prioritized plan (correctness-first), mapping the 18 points

### Tier 1 — correctness blockers (must hold or the scheme is not ZK)

- **T1.1 Joint conditional certificate (reviewer #3, #13, #5).** Extract the
  joint map (all masks → the *entire* algebraic transcript) from the real
  prover and check `f(w)−f(w') ∈ Im A_full` restricted to `ker(claim
  functionals)`. For the round pairs specifically, check `d ∈ R(ker L)` with
  `L` = all revealed `P`-functionals. *Status: methodology proven on the
  round/`P(ρ)` slice (§0); generalize to the full transcript.*
- **T1.2 Hiding `P,Q` openings (new, from §0).** Wire `P,Q` through the
  hiding opening; add a negative control that a plain opening fails the joint
  certificate.
- **T1.3 A1′ integrated into the optimized prover/verifier (reviewer #2 of
  the minimum standard).** The combined masked sumcheck (σ, γ, combined
  messages, final `+γP(ρ)Q(ρ)`), with the transcript order and verifier
  rejections the reviewer lists (§2 of their note). *Validated
  (`a1_prime_combined_completeness_and_soundness`); not yet wired.*
- **T1.4 Canonical transcript interface (reviewer #1, #10).** A single
  `TranscriptItem` enum + `AlgebraicTranscript` through which *every*
  prover→verifier value passes, with a `LeakageClass` classification
  required per coordinate; CI fails on any unclassified/uncertified
  coordinate. This is what makes T1.1 exhaustive rather than best-effort.
- **T1.5 PCS conditioning made joint (reviewer #13).** Extract and certify
  the joint `μ,g` → (all opened rows, `(u0,u2)`, `y_r`, `y_g`, batched
  targets) map, not per-stage marginals.

### Tier 2 — soundness & universality of the certificate

- **T2.1 Challenge-dependent rank (reviewer #6).** A nonzero-minor
  certificate: pick a full-rank square minor, represent entries as
  polynomials/SLPs in the challenges, an explicit degree bound `D`, and one
  evaluation with nonzero determinant. Checker verifies the evaluation;
  Schwartz–Zippel gives `ε_rank ≤ D/2^128`. Replace the `O(m)` prose bound
  with a machine-generated `D`.
- **T2.2 Per-parameter certificates (reviewer #5).** A `ZkParameterCertificate`
  per supported `(circuit_digest, layout_digest, batch_log, params,
  version)`; runtime rejects uncertified configs; no silent fallback.
- **T2.3 `P·Q` batching soundness (reviewer #16).** Order attacks (`σ`/`P,Q`
  after `γ`), cross-proof commitments, altered `P(ρ)`/`Q(ρ)`; small-field
  enumeration of `γ` bounding false-accept by `1/|F| +` sumcheck error.

### Tier 3 — implementation assurance

- **T3.1 Witness-difference basis generator (reviewer #9).** A basis of legal
  witness differences (message/CV/state/padding/residue directions); certify
  the whole basis, not random pairs.
- **T3.2 Toy exhaustive models (reviewer #8, #17).** Small-field port where
  all masks/challenges/witnesses enumerate; exact real-vs-real and
  real-vs-simulated transcript equality; the full negative-control matrix
  (disable `P`, constant `Q`, drop `g`/`μ`/A/B rows, reuse masks, `μ` high,
  misalign, omit `P(ρ)`/`Q(ρ)` checks, `γ` before commit). Note: F₂₁₂₈
  blocks true brute force; the exact F₂ image certificate is the feasible
  analogue at production field size, the small-field port is the true
  exhaustive check.
- **T3.3 Layout assertions (reviewer #12).** 128-bit alignment, region
  disjointness, non-aliasing, constant-one constrained — as checked
  invariants, hashed into the statement + certificate id.
- **T3.4 Randomness lifecycle (reviewer #11).** One-proof seed, irreversible
  domain-separated forks (A/B/μ/g/P/Q/salt/grind), statement+version+nonce in
  each derivation, zeroization, fail-closed, retry/concurrency/clone tests,
  no deterministic seeds in production builds.
- **T3.5 Merkle-leaf domain separation + entropy budget (reviewer #14).**
  Labeled leaf hash, runtime `fresh_blinder_bits ≥ MIN`; optional per-leaf
  salt to reduce reliance on correlated-codeword entropy estimates (still an
  assumption).

### Tier 4 — formalization & API

- **T4.1 Lean certificate checker + full-WI theorem (reviewer #15).** Lean
  defs for the algebraic transcript, affine channels, `conditional coverage`
  (`R(ker L)`), the `P·Q` mixture, composition, rank-failure distance, and
  the simulator reduction; a checker that consumes the Rust-generated
  certificates; CI rejects `sorry`/axioms/mismatch. *We already have
  `Masking`/`MaskingSurjective`/`MaskingMixture`; add `ConditionalCoverage`
  and `CertificateChecker`.*
- **T4.2 Narrow API + simulator restriction (reviewer #7, #18).**
  `prove_blake3_batch_zk_experimental`; the simulator asserts the statement
  binds no external hash output (fails for chain/SHA-256/Keccak/pinned-IO).
  *Simulator exists (`zk_simulator.rs`); add the guard.*
- **T4.3 Release-blocking CI gates (reviewer #17) + independent review.** The
  full gate list; label computational-ZK-in-ROM (Merkle hiding is
  computational), not statistical-ZK-for-the-whole-protocol.

## 3. Sequencing

1. T1.4 (transcript interface) + T1.1 (joint certificate on the current
   transcript) — makes coverage exhaustive and catches any T1.2 regression.
2. T1.3 + T1.2 (integrate A1′ with hiding `P,Q` openings) — then re-run T1.1
   on the integrated prover; this is the real proof-carrying artifact.
3. T2.* (universality: challenge-rank minor, per-parameter certs, batching
   soundness).
4. T3.* (assurance) and T4.* (Lean + API + CI gates), then independent
   review.

## 3b. Implementation progress (minimum path)

- **DONE — Z1: reference-correct A1′ combined masked zerocheck**
  (`zerocheck::prove_packed_padded_zk` / `verify_zk`, committed). Runs the AB
  sumcheck on `â·b̂ + γ·P·Q`; combined round messages `G_j+γM_j`, initial
  claim `+γσ_z`, final check `â(ρ)b̂(ρ)+γP(ρ)Q(ρ)`. Tested: FsChallenger
  roundtrip (completeness, m=13..16) + tamper rejection of `σ_z`, `P(ρ)`,
  `Q(ρ)`, round messages, `final_a` (soundness). Reference-quality (naive
  round-pair kernels + skip fold); the fused optimized variant is a
  differential-tested follow-up. Returns `P(ρ),Q(ρ)` for PCS authentication.

- **DONE — Z2: hiding `P,Q` commitment + authenticated opening at ρ**
  (`pcs::tests::zk_pq_hiding_open_roundtrip`, committed). `commit_zk` per
  polynomial (hiding — codeword rows blinded by `g`); roots observed before
  the zerocheck so `γ`/`ρ` bind them; opened at ρ=(z, mlv_challenges) as RS
  claims authenticating `final_p_eval`/`final_q_eval`. Point convention
  verified (`final_p_eval == zhat_skip_reference` at forward `mlv_challenges`).
  Two openings derived from a forked+domain-tagged post-zerocheck challenger
  (independent, both transcript-bound). Honest roundtrip verifies; tampered
  `P(ρ)` rejected. Keeps the joint-coverage leakage `L = {P(ρ),Q(ρ)}`.

- **DONE — Z4 (zerocheck layer): full joint coverage on the REAL prover**
  (`full_conditional_coverage_zk_zerocheck`). Runs
  `prove_packed_padded_zk`; with the complete `P`-leakage `L={P(ρ),σ_z}`,
  conditioning removes 2 F128 directions but the witness residuals stay
  determined by the public ab-claim — no claim-preserving witness direction
  leaks. Lincheck/ring-switch coords are affine (existing
  `affine_classes_exactly_covered`); `μ,g` by the PCS audit; compose by
  `MaskingSurjective.coprod_covers`.

- **NEXT — end-to-end wiring** (the gating remainder for a ZK shipped
  prover): thread Z1+Z2 into `prove_fast_ligerito_from_witness_zk`
  (commit P,Q; observe roots before `bind_statement`; swap the zerocheck for
  `prove_packed_padded_zk` — add `s_hat_v_c` capture for the c-claim; open
  P,Q at ρ) + the verifier mirror + the proof-struct extension. Components
  de-risked (Z1, Z2 tested); this is a large soundness-critical integration.

- **THEN — Z6/Z7/Z8/Z9**: explicit nonzero-minor rank bound; per-parameter
  certificates + runtime gating; written WI theorem + deterministic
  certificate format + reproducible checker; minimal test set (small-field
  exact equality, real-vs-sim, negative controls); fresh-masks enforcement +
  narrow API. Paper v4 published (secret gist) with the implemented-amendment
  status.

## 4. Honest status after this research

- The **methodology gap the reviewer identified is real** and is now fixed
  in principle: we check joint conditional coverage, and we have the exact
  measurement showing what `P(ρ)` does.
- The **design is sound under a newly-identified condition** (hiding `P,Q`
  openings); without it, A1′ would leak — a concrete, testable requirement.
- Everything in Tier 1–4 above is engineering + formalization on top of a
  now-settled design question. Until Tier 1 lands on the integrated prover
  and an independent cryptographer reviews it, the correct label remains
  **experimental / candidate, computational-ZK-in-the-ROM**, BLAKE3 batch
  only.

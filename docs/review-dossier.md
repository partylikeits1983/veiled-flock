# External review dossier — Flock zero-knowledge mode (A1′)

> **Superseded review dossier.** This file indexes the withdrawn Boolean
> $P\cdot Q$ protocol and is retained only as design history. It is not an
> entry point for reviewing `flock-zk-fv-v3`. Review the current paper and the
> S2, S3, simulator-game, and knowledge-extraction artifacts instead.

This document is the entry point for an independent cryptographic review. It
indexes what is claimed, what establishes each claim, how to reproduce it, and
what is knowingly unresolved. It is not itself evidence.

**Status label: B — experimental candidate with a proven partial core.**

---

## 1. Scope and exact claim

For an explicitly enumerated set of BLAKE3 *batch* statement configurations
(§6) that bind no externally supplied message, chaining value, or hash output,
the **reference** amended prover is claimed to be:

> computational zero-knowledge in the classical random-oracle model, with the
> algebraic transcript statistically witness-indistinguishable up to an
> explicit rank-failure term ε_rank, and hiding of unopened Merkle siblings
> computational under the hash assumption of §7.

The witness-indistinguishability step is **established at the certified
fixture**: over all 548 witness-dependent coordinates of the complete A1′
transcript, at three challenge tuples, conditioned on the complete mask-only
leakage set and on every public claim the verifier learns, with the claim space
saturated, no claim-preserving witness direction escapes the joint mask image.
What keeps the overall label at B is §10 — the certificate is per-fixture, the
ROM assumption is assumed, and no independent review has been done — plus one
process fact: a prior revision promoted the label to A, and the promotion was
withdrawn when the certificate *pipeline* was found to overstate itself (a
runner that did not fail on the flagship certificate's failure, three gates
whose `--exact` filters matched zero tests, a substring-matched evidence
registry, and advertised negative controls that did not exist). The pipeline
is repaired; re-promotion waits on one green end-to-end run of the hardened
`scripts/zk-certify.sh` at the pinned revision.

Explicitly **not** claimed: SHA-256, Keccak, hash chains, Merkle-path
statements, externally bound hashes, recursive composition, arbitrary Flock
statements, QROM security (soundness or ZK), side-channel resistance, and the
optimized `prove_fast_zk` prover (which runs the un-amended zerocheck).

Paper: `docs/paper/zk-flock.tex` §1–§2. Proof document: `docs/zk-proof.md`.

## 2. Protocol specification

`docs/paper/zk-flock.tex` §4 (numbered protocol + figure) and `docs/zk-proof.md`
§5. The two ordering invariants a reviewer should check first, because
everything else rests on them:

1. All six hiding commitments (witness, `P`, `Q`, `S`, `S_c`, `S_h`) and the
   mask sum `σ_z` are absorbed into the Fiat–Shamir transcript **before** `γ`
   is sampled.
2. Amendment A2: `σ_lc` is absorbed after the const-pin `β` fixes `comb` and
   **before** `γ_lc` is sampled; and `Ŝ(ρ)` is checked against `S`'s
   commitment rather than taken on the prover's word. The second is
   load-bearing — an unbound `Ŝ(ρ)` can be chosen after `ρ` and absorb an
   arbitrary defect into the lincheck's output claim.
3. Amendment A3: the round-1 mask pair must satisfy `M_ab + M_c = V_S·h`, so
   the *combined* polynomial still vanishes on `S`. That is the load-bearing
   condition — it is what preserves the zerocheck assumption the AB
   reconstruction (and hence soundness) rests on. `M_c(z)` and `h(z)` are
   bound by openings at the c-claim point; unbound they could be chosen after
   `z`. Note A3 needs no batching challenge, because it adds no
   prover-claimed sum.
4. Inside the PCS opening, `y_g` is observed and the proof-of-work is priced
   **before** the blinder-combination challenge `c` is sampled.

Canonical transcript definition: `crates/flock-prover/src/transcript_schema.rs`
(`A1_FIELD_MANIFEST` is the reviewable classification list).

## 3. Theorem dependency map

| Result | Feeds | Established by | Location |
|---|---|---|---|
| Masking theorem | affine transcript classes | Lean 4 | `lean/Flockzk/Masking.lean` |
| Surjective corollary | round-pair block | Lean 4 | `lean/Flockzk/MaskingSurjective.lean` |
| Triangular composition | joint WI | Lean 4 | `lean/Flockzk/MaskingTriangular.lean` |
| Bad-set mixture | ε_rank accounting | Lean 4 | `lean/Flockzk/MaskingMixtureBadSet.lean` |
| H1 (constant inner image) | hypothesis of the above | exact certificate | `tests/zk_joint_certificate.rs` |
| Conditional coverage `d ∈ R(ker L)` | hypothesis of the above | exact certificate | `tests/zk_joint_certificate.rs` |
| γ-batching soundness (L6) | amendment soundness | paper proof + constructive test | `zerocheck.rs` |
| γ_lc-batching soundness (A2) | lincheck amendment soundness | paper proof + constructive test | `lincheck.rs` (`masked_verify_rejects_sigma_tamper`) |
| A2 output-claim recovery | PCS binding to ẑ survives the mask | test | `lincheck.rs` (`masked_roundtrip_recovers_the_unmasked_claim`) |
| eq-table F₂-span (A2) | Boolean mask reaches all of F₂¹²⁸ per slot | **measured, not derived** | `tests/zk_blake3_certificate.rs` |
| A3 round-1 mask pair | round1_c coverage without breaking the zerocheck assumption | paper proof + staged test | `zerocheck.rs` (`prove_verify_zk_round1_mask_roundtrip`) |
| A3 un-shift correctness | C-claim and AB running claim recovered exactly | proved; tested end to end | `zerocheck.rs` |
| No-public-input reduction (L1) | simulator validity | paper proof + code inspection | `docs/zk-proof.md` §2 |
| Sibling hiding | ε_hash | **assumed** | `docs/zk-proof.md` §7 |
| Classical-ROM ZK | headline claim | proved conditional on the above | `docs/zk-proof.md` §9 |

Superseded and retained only as a stepping stone: `lean/Flockzk/MaskingMixture.lean`
(its coset hypothesis is **disproved** on the full transcript by
`final_b_breaks_full_mixture_hcoset`).

## 4. Implementation map

| Component | Location |
|---|---|
| Reference ZK prover / verifier | `crates/flock-prover/src/prover.rs` — `prove_r1cs_zk_a1`, `verify_r1cs_zk_a1` |
| Gated API (the claim's entry point) | `r1cs_hashes/blake3.rs` — `Blake3Setup::prove_zk_a1`, `verify_zk_a1` |
| Masked zerocheck | `crates/flock-core/src/zerocheck.rs` — `prove_packed_padded_zk`, `verify_zk` |
| Hiding commitment | `crates/flock-core/src/pcs/commit.rs` — `commit_zk` |
| Hiding opening | `crates/flock-core/src/pcs.rs` — `open_zk_blinded` |
| Randomizer rows | `crates/flock-core/src/zk.rs` — `ZkBlockLayout`; `r1cs_hashes/common.rs` — `write_zk_randomizers` |
| Mask DRBG | `crates/flock-core/src/zk.rs` — `ZkRng` (BLAKE3 XOF, OS-seeded, domain-separated forks) |
| Mask channel plumbing | `prover.rs` — `A1MaskSources`, `A1MaskForks` |
| Transcript schema | `crates/flock-prover/src/transcript_schema.rs` |
| Certificate gate | `crates/flock-prover/src/zk_certificate.rs` |
| Serialization | `crates/flock-prover/src/proof_io.rs` — flavor 4 |

### Most security-sensitive functions

Ranked by what breaks if they are wrong:

1. `zerocheck::prove_packed_padded_zk` / `verify_zk` — the amendment itself;
   the σ_z-before-γ ordering lives here.
2. `prover::prove_r1cs_zk_a1` — commitment ordering, mask fork derivation,
   and the hiding P/Q openings.
3. `pcs::open_zk_blinded` — `y_g` before the grind before `c`.
4. `pcs::commit::commit_zk` — mask/blinder placement (low-half μ, full-support g).
5. `zk::ZkRng::{from_entropy, fork}` — mask independence; fails closed if the
   OS entropy source is unavailable.
6. `zk_certificate::require_certified` — the fail-closed API gate.
7. `r1cs::statement_digest` — binds matrices, layout, and the zk layout.
8. `challenger::FsChallenger` — tagged-duplex Fiat–Shamir.

## 5. Certificate format and reproduction

A certificate is a registered `ZkCertificate` (in `zk_certificate.rs`) binding:
protocol version, circuit digest (`statement_digest`), layout digest,
transcript-schema version, field representation, fold order, endianness, PCS
parameters, batch size, generator revision, and the list of evidence tests. A
test asserts the evidence list matches exactly what `scripts/zk-certify.sh`
runs, so the gate cannot vouch for tests that never execute.

```sh
cargo test --release --workspace --features zk        # fast suite (all tripwires)
scripts/zk-certify.sh                                 # exact certificates (hours)
cd lean && lake exe cache get && lake build
scripts/lean-axioms.sh                                # axiom audit
```

## 6. Supported parameter set

See `CERTIFIED` in `crates/flock-prover/src/zk_certificate.rs`. Anything else
returns `ZkGateError`, including every non-BLAKE3 encoder and every statement
family that binds public I/O.

## 7. Exact bounds

| Quantity | Value | Basis |
|---|---|---|
| γ-batching false accept | ≤ 2⁻¹²⁸ (+ sumcheck error) | Lemma L6, `docs/zk-proof.md` §6 |
| ε_rank | 0 per emitted proof | per-proof rank check with resample-on-failure |
| ε_rank closed form | **open** | Boolean masks; Schwartz–Zippel inapplicable |
| ε_hash | ≤ q · 2^(−k_min), k_min ≥ 8192 − 512 bits | assumption, `docs/zk-proof.md` §7 |
| Multi-proof (k proofs) | k(ε_rank + ε_hash) | fresh masks per proof |

## 8. Test inventory

| Test | Certifies | Cost |
|---|---|---|
| `zk_transcript_schema.rs` | field classification, bijectivity, FS wire order, pinned schema hash | fast |
| `zk_a1_soundness.rs` | e2e tamper matrix, commitment/params substitution, opening swaps, gate refusal | fast |
| `zerocheck::zk_invalid_witness_rejected` | false statements rejected on the amended path | fast |
| `zerocheck::zk_gamma_cancellation_unique_and_fs_ordering` | γ-uniqueness; the ordering attack works without FS and fails with it | fast |
| `zk_joint_certificate::h1_inner_image_witness_independent_on_round_block` | H1, and that P is what discharges it | ~25 s |
| `zk_joint_certificate::p_channel_image_requires_nondegenerate_q` | bad-Q set delimitation (2561 → 1281 bits) | ~20 s |
| `zk_joint_certificate::joint_certificate_smoke` | triangular coverage on the round block | ~40 s |
| `zk_joint_certificate::joint_certificate_negative_controls` | detector non-vacuity (honest baseline passes, added unmasked leakage fails) | ~20 s |
| `zk_joint_certificate::mask_reuse_across_proofs_is_a_leak` | reused masks leak a deterministic witness functional; fresh-per-proof masks are load-bearing | fast |
| `zk_joint_certificate::joint_conditional_coverage_full_transcript` | complete-transcript joint coverage — **passes** at 3 tuples | offline, ~13 min/tuple |
| `zk_blake3_certificate::blake3_witness_difference_lies_in_the_mask_image` | real-statement (m=20) coverage over the PIOP classes — **passes**, 30,464/30,464 | offline, ~15 min/class scope |
| `zk_production_config.rs` | **at m=22**: channel surjectivity on the round-pair block (4096/4096), degenerate-Q control (2048/4096), per-proof self-check + verify, randomizer margin 12× | ~15 s |
| `zk_simulator.rs` | simulator on the A1′ path; constructive translation exactness | mixed |
| `zk_leakage_certificate.rs` | affine-class exact coverage; A1′ round-pair image | offline |
| `pcs/zk_audit.rs` | PCS-layer image containment; no-g negative control | fast |

## 9. Known limitations

Mirrors `docs/paper/zk-flock.tex` §13. In brief: unsupported statement families
and parameters; ε_rank closed form open; full-transcript certificate computed at
a reduced fixture with structural transfer to production size; certificates at
sampled challenge tuples; optimized-prover equivalence not established; ROM
assumption; no independent review; side channels and QROM out of scope.

## 10. Unresolved assumptions

1. **Sibling hiding** is assumed (ROM / hash pseudorandomness), not derived.
2. **Challenge-tuple genericity**: certificates hold at the tuples tested; no
   argument covers all tuples.
3. **RESOLVED — the former principal open item (`round1_c`), closed by
   amendment A3.** On a real BLAKE3 batch statement (m=20, 64 blocks,
   triangular probing, claim space saturated at 640 bits) one F128 direction
   of claim-preserving witness difference escaped the mask image, attributed
   to `zerocheck.round1_c`. Amendment A2 removed the lincheck's share
   (9728/10240 with 128 bits escaping → 10240/10240 with none); amendment A3
   (the round-1 mask pair, `docs/round1c-mask-channel.md` — the cheap
   diagonal design was first ruled out by measurement) closed the remainder:
   `blake3_witness_difference_lies_in_the_mask_image` now **passes** at
   30,464/30,464 bits with `rank[resid | Δclaim] = 640 = rank(Δclaim)`
   (`docs/zk-proof.md` §0). It stays in this section because two findings
   from the failure outlast the fix and bind how every other result here
   must be read:

   - **The escape was joint, not marginal.** `round1_c` passed in isolation
     at 8192/8192 the entire time; the failure appeared only when it had to
     be covered simultaneously with every other coordinate. A reviewer
     should note that per-class coverage results are therefore not
     composable, here or anywhere else in this development.
   - **The assumption that broke was never written down as an assumption.**
     The randomizer rows were *believed* to cover the affine classes — true
     on the synthetic fixture (~81% randomizer rows) and false on a real
     witness (~5.5%). A certificate run only on the vehicle would have
     reported success indefinitely.

4. **The fixture certificate.** The complete-transcript certificate passes at
   the reduced fixture (m=16) chosen so exact probing is feasible. Measured
   *at* the production configuration: channel surjectivity on the round-pair
   block (4096/4096), its degenerate-Q control (2048/4096), the per-proof
   self-check (passes, 0 resamples, proof verifies), and the s_hat_v margin
   (12× versus the fixture's 3×).

## 11. Revision hashes

| Artifact | Revision |
|---|---|
| Branch | `ajl/zk-flock-gaps` (stacked on `ajl/zk-flock-lean`) |
| Paper | `docs/paper/zk-flock.tex`, see its date line |
| Lean toolchain | `leanprover/lean4:v4.32.1`, Mathlib `v4.32.1` |
| Rust toolchain | stable (1.97.1 at time of writing) |

## 12. Suggested review order

1. §2 ordering invariants — the cheapest way to break the construction.
2. Lemma L6 and its constructive test — soundness of the amendment.
3. The no-public-input reduction (L1) — validity of the simulator.
4. The transcript schema — is any verifier-visible value missing or
   misclassified? The certificates are only as complete as this list.
5. `h1_inner_image_witness_independent_on_round_block` and the joint
   certificate — the hypotheses of the triangular theorem.
6. The ε_rank replacement (per-proof check) — is the resample event really
   witness-independent?

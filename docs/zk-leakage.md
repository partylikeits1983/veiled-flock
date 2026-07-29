# Zero-knowledge Flock: leakage map, masking design, and ZK evidence

This document is the **leakage map and evidence index**; the scoped
zero-knowledge **proof** (exact security claim, the reduction to
witness-indistinguishability + explicit simulator, the amendment A1′, the
separated soundness/hiding theorems, the assumptions, and the disposition
of every external-review item) is in [`zk-proof.md`](zk-proof.md). It
classifies every prover→verifier message, states what is claimed and what is
machine-checked, and records the soundness accounting. Scope of the current
implementation: **batch R1CS statements with the BLAKE3 encoder**
(`Blake3Setup::with_zk` / `prove_fast_zk`); other encoders and the hash-chain
statement are future work (see the end).

**Status: candidate / experimental.** The exact leakage certificate
(`tests/zk_leakage_certificate.rs`) proves the affine transcript classes are
hidden exactly and validates the degree-2 `P·Q` mask channel (amendment A1′)
that closes the zerocheck round pairs; A1′ is validated but not yet wired
into the optimized single-pass prover. See `zk-proof.md` §0.

## 1. Design summary

Two mask species, both committed in the initial commitment — so every mask is
bound by the Fiat–Shamir transcript **before any challenge that could depend
on it** (the ordering requirement is structural, not a discipline):

1. **Randomizer witness rows** (`flock_core::zk::ZkBlockLayout`). Each R1CS
   block gets extra rows of two shapes, on fresh witness columns filled with
   uniform bits from a prover-secret DRBG (`ZkRng`, BLAKE3-XOF, seeded from
   OS entropy):
   - A-type `u·1 = u`: the A row is a self-loop on the random column, the B
     row selects the constant-1 wire; `C = I` makes the row's c/z-slot the
     same bit. Randomness enters the a-cube, the product cube, and the
     z-cube. In the cube itself products are pointwise and A/B rows are
     disjoint, so no `u_A·u_B` cross terms exist **in the cube** — but
     zerocheck *round messages* multiply folded â·b̂ values, so cross terms
     do enter the round pairs once a fold group spans an A/B region
     boundary. The masking claim for that class is the conditional one of
     §3; every other class is jointly affine in the masks.
   - B-type `1·u′ = u′`: symmetric, masking the b̂-side.
   The rows are satisfied by any bit assignment, so completeness and the
   knowledge claim about the real witness wires are unchanged. The optimized
   zerocheck/lincheck kernels are untouched — they just process a witness
   that contains random bits. The rows live **inside** `useful_bits` (the
   padded kernels skip regions declared zero), and the layout is bound into
   `statement_digest`.

2. **Hiding PCS** (`pcs::commit_zk` + the blinded opening). The committed
   message becomes `message′ = [mask ‖ z_packed]` with a uniform low-half
   mask block (the low novel-basis slots `X̂_0..X̂_{t−1}` span all degrees
   < t, so any t distinct opened positions receive a surjective mask→symbol
   map — no dead zones; a top-block mask would vanish on the low subspace,
   half the query domain at rate ½). A **full-support blinder** `g`, uniform
   over the doubled message space, is committed alongside in shared wide
   Merkle leaves (`leaf = [f′ lanes ‖ g lanes]`, one root). The opening runs
   the unchanged Ligerito recursion on `F = message′ + c·g`, where the
   prover first observes `y_g = ⟨g_top, b_combined⟩`, grinds
   `fold_grinding_bits[0]+1` PoW bits, and only then samples `c`
   (observing `y_g` after `c` would let a cheating prover shift the combined
   target — the order is soundness-critical). The low-half mask hides the
   raw f′ rows opened at L0; `g` hides everything downstream: all recursive
   rows, every internal sumcheck message `(u_0, u_2)` including the pre-glue
   ones, and the final residual `yr`. (Low-half masks alone provably leak:
   the combined basis `b′ = [0 ‖ b_combined]` is zero on the mask half and
   the LSB-first folds preserve the half split, so the first `initial_k+1`
   sumcheck messages and the top half of `yr` would be clear witness
   functionals — the PCS rank audit's negative control demonstrates exactly
   this.)

Why not the classical Chiesa–Forbes–Spooner / Libra masking-polynomial
sumcheck: over F₂₁₂₈ the standard additive mask `g(x) = Σᵢ gᵢ(xᵢ)` has
`Σ_cube g = 2^{m−1}(…) = 0` — characteristic 2 annihilates it — and Flock
has no shared sumcheck seam (zerocheck, lincheck, and the PCS sumchecks are
independently hand-optimized kernels). The randomizer-witness design achieves
the same effect with zero kernel changes.

## 2. Leakage map

Every transcript `observe` site and clear-text proof field, classified.
"Masked by" names the species that makes the value's conditional
distribution witness-independent.

| # | Message | Site | Masked by |
|---|---------|------|-----------|
| L1 | Commitment root | `proof.rs::bind_statement` | hiding commit (mask + g + randomizers in the committed message) |
| L2 | `round1_ab`, `round1_c` (2×64 F128) | `zerocheck.rs:307-308` | randomizer rows |
| L3 | zerocheck round pairs `(G(1),G(∞))` | `zerocheck.rs:349-350,412-413` | randomizer rows |
| L4 | `final_a_eval`, `final_b_eval`, `final_c_eval` | `zerocheck.rs:437-438`, proof field | A-side / B-side randomizer rows |
| L5 | lincheck rounds `(e1,einf)`, `z_partial`, claim `w` | `lincheck.rs:1311-1312,1338` | randomizer rows |
| L6 | chain-shift rounds + `g_at_point` | `chain.rs:200-202` | **future work** (chain statements are not zk yet) |
| L7a | `s_hat_v` (128 F128 per RS claim) | `ring_switch.rs:2222` | randomizer rows (needs ≥128 bits per bit-residue — see §4) |
| L7b | Ligerito opened rows, all levels | `RecursiveProof.opened_rows` | low-half mask (L0 f′ rows) + blinder `g` (all levels) |
| L7c | PCS sumcheck `(u_0,u_2)`; final `yr` | `sumcheck_transcript`, `FinalProof.yr` | blinder `g` (via the `c`-combination) |
| L7d | Unopened Merkle siblings | `merkle.rs` | computational: every L0 leaf carries ≥8 KiB of fresh `g` entropy; deeper leaves are rows of `g`-blinded folds (no leaf salting — see §5) |
| — | `y_g` | `BatchOpeningProofLigerito.zk_blind` | uniform by construction (linear in `g`) |

Public, no treatment: statement digest (includes the zk layout), batch size,
matrix structure, FS challenges, PoW nonces, query positions, and the claim
values *as constrained quantities* (see §3).

## 3. The precise HVZK claim

- **Model:** honest-verifier; the interactive argument is public-coin and
  compiled by the existing Fiat–Shamir transform, so HVZK lifts to NIZK in
  the ROM as usual.
- **Claim:** statistical witness-indistinguishability of the transcript
  distribution, conditioned on the public inputs, for all revealed field
  elements; **computational** (SHA-256 preimage) hiding for unopened Merkle
  siblings. At fixed challenges the revealed values split in two
  (structure measured by `tests/zk_affinity_probe.rs`):
  - **Affine classes** (everything except the zerocheck round pairs —
    round-1 vectors are saved by the 128-bit region alignment; lincheck,
    ring-switch, and all PCS values are F₂₁₂₈-linear in the committed
    data): affine in `(randomizer bits, mask, g)` with witness-independent
    linear part. With the budgets of §4 the witness-dependent offsets lie
    inside the mask image; the masking theorem gives identical
    distributions and an exact simulator.
  - **Zerocheck round pairs** `(G(1), G(∞))`: bilinear across the two
    randomizer species with witness-dependent linear coefficients — but
    affine in `u_A` at any fixed `u_B` (no within-species cross terms:
    A-rows only meet the constant-1 wire on the b̂-side). *Superseded by
    amendment A1′* (`zk-proof.md` §5): a degree-2 committed mask channel
    `γ·P·Q` (two witness-free full-support random multilinears) makes this
    class **surjectively** masked — `G(∞)`, the degree-2 leading
    coefficient no degree-1 mask can reach, included — so it too reduces to
    the single-map masking theorem. The mixture argument below is retained
    only as the fallback for the un-amended protocol; note the exact
    certificate found that its `h_coset` hypothesis is false for the full
    transcript (the b̂-side final evaluation has an identically-zero
    `u_A`-derivative), which A1′ avoids.

  Both up to the statistical error of the budget margins (~2^{-64} per the
  slack term).
- **Conditioning on public inputs is necessary, not a caveat:** the PCS
  opening *proves* `ẑ(point) = v`; the consistency equations genuinely
  determine `γ·v + c·y_g` from the revealed values. The audits therefore
  probe witness directions in the kernel of the public claim functionals
  (PCS audit) / compare witnesses for the same statement (PIOP audit).

## 4. Machine-checked evidence (the "prove it" deliverable)

All evidence is re-runnable; the negative controls prove the detectors would
catch an unwired or missing mask.

1. **PCS rank audit** — `flock-core/src/pcs/zk_audit.rs`
   (`cargo test -p flock-core --features zk zk_audit`). With a fixed
   challenger, the map `(mask, g) → all revealed PCS values` is affine over
   F₂₁₂₈; 192 unit probes extract it exactly at m=13, and Gaussian
   elimination checks `Image(witness|_{ker claims}) ⊆ Image(masks)`.
   Negative control: withholding `g` must fail (it does — the pre-glue
   messages / `yr` leak class).
2. **PIOP rank audit** — `flock-prover/tests/zk_piop_audit.rs`
   (`cargo test -p flock-prover --features zk --test zk_piop_audit`).
   Certifies **k-wise joint uniformity**: for random 6-value subsets drawn
   across every message class (round-1 vectors, round pairs, final evals,
   `z_partial`, both `s_hat_v` vectors), the restricted randomizer image is
   the full 768-dim space. Full joint uniformity of all ~460 revealed values
   needs ≈59k probe runs and is not run in CI; k-wise uniformity catches any
   leaked or under-masked value in a sampled class. Negative control:
   withholding the A-group must fail (it does). Scope: mixed-species probes
   make this a valid *uniformity* certificate for the affine classes only;
   for the bilinear round-pair class it is a detector, and the valid
   certificate is item 2b.
2b. **Conditional PIOP certificate** — `flock-prover/tests/zk_affinity_probe.rs`
   (`cargo test -p flock-prover --features zk --test zk_affinity_probe`).
   First measures the affinity structure: the joint F₂ affinity defect and
   the mask-map witness-dependence are confined to the zerocheck round
   pairs; no within-species defects; at fixed `u_B` the transcript is
   affine in `u_A` everywhere. Then the fixed-`u_B` rank certificate:
   random `u_A` probes (genuinely affine deltas) reach full 768-dim rank on
   per-class subsets **and** on a subset drawn entirely from the round-pair
   class, at multiple `u_B` draws, with witness deltas and cross-`u_B`
   offsets contained in the `u_A`-image — exactly the constant-image and
   coset-coverage hypotheses of the mixture masking theorem.
3. **Transcript differentials** — same statement, two DRBG seeds ⇒
   essentially every masked value changes (asserted ≥90%); zeroed masks ⇒
   byte-identical deterministic transcripts (the leak being closed).
   End-to-end at the BLAKE3 level: `prove_fast_zk_ligerito_roundtrip`
   asserts fresh seeds change the commitment root, `final_a_eval`, and
   `z_partial`, while the proof still verifies.
4. **Roundtrips + tamper rejection** — zk proofs verify via the unchanged
   verifier entry points; tampering `z_partial`, round messages, final
   evals, `s_hat_v`, `y_g`, a mask cell, or stripping `zk_blind` is
   rejected (`pcs_zk_roundtrip_and_negatives`,
   `r1cs_prove_verify_roundtrip_ligerito_zk`,
   `prove_fast_zk_ligerito_roundtrip`).
5. **Formal masking theorems** — `lean/` holds a Lean 4 + Mathlib proof
   (no `sorry`) that the audited hypotheses imply zero-knowledge, in two
   forms matching the two transcript classes of §3. `Masking.lean` (the
   affine classes): an affine transcript with mask-covered witness
   directions is witness-independent, uniform on its coset, and exactly
   simulatable from a public coset representative
   (`transcript_witness_indep`, `simulator_exact`, `pmf_*`).
   `MaskingMixture.lean` (the round-pair class): for a family of affine
   maps indexed by `(witness, u_B)` with constant image and coset-covered
   offsets, the joint distribution over uniform `(u_A, u_B)` is
   witness-independent and exactly simulatable
   (`mixture_witness_indep`, `pmf_mixture_*`). Item 2 checks the first
   theorem's hypotheses, item 2b the second's; see `lean/README.md` for
   the two-layer argument and its limits.

**Budget rules** (`ZkConfig::sized_for` errs high; the audits are ground
truth): masking one revealed F128 needs ≥128 bits of randomizer entropy
reaching it; the `s_hat_v` bit-slices additionally need ≥128 bits **per
bit-residue** (slice r only sees witness bits at position r mod 128), i.e.
`blocks × A-chunks-per-block ≥ 128` with margin. BLAKE3: 2 A-chunks + 1
B-chunk + the 512-bit chain-mask pair (also A-type) per block ⇒ ≥6 A-type
bits per residue per block × ≥256 blocks ≥ 1,536 per residue, and ~229k
total randomizer bits against a ~72k-bit budget at m=22.

## 5. Soundness accounting

- **Statement change:** randomizer rows are unconstrained-but-satisfiable;
  the knowledge claim on the hash wires is unchanged. The zk layout (and the
  `useful_bits` extension) is absorbed into `statement_digest`.
- **PCS shape change:** zk commits the (m+1)-dimensional message, so the
  opening transparently uses the existing, audited `(m+1)` config ladder
  (`configs/ligerito/m{m+1}_*.toml`); the proximity/UDR analysis is literally
  the (m+1) analysis. The mask block and `g` are ordinary code dimensions.
- **The `c` combination** is one extra interleave-fold round (the L0 word
  has `2^{initial_k+1}` rows folded by `c` then the lane challenges): +1 bit
  on the worst row-union term, priced by the mandatory
  `fold_grinding_bits[0]+1` PoW grind before `c` is sampled. `y_g` is
  observed before the grind.
- **Merkle siblings:** not salted. Every L0 leaf contains its 64 `g`-lane
  symbols (≥8,192 bits of fresh DRBG entropy); level ≥1 leaves are rows of
  encodings of `g`-blinded folds. Unopened sibling hashes are therefore
  hashes of high-min-entropy strings: computational hiding in the plain
  model, statistical in the ROM. Salting would add bytes and a `merkle.rs`
  fork for no gain in this model.
- **DRBG:** `ZkRng` = BLAKE3 XOF keyed from `getrandom` OS entropy,
  domain-separated forks for the witness randomizers and the PCS masks; it
  never touches the FS transcript (mask randomness reaches the transcript
  only through committed data).

## 6. Measured cost (see `benches/zk_vs_baseline.rs`)

zk mode costs, by construction: L0 commit ≈4× (message dim ×2, leaf width
×2), the opening's lane-fold phase ≈2× (doubled `F`/`b′`), one extra
`(m+1)`-ladder step in the recursion, ~2× L0 opened-row bytes in the proof,
a few percent on the PIOP phases (extended useful region), and the DRBG fill.
Measured end-to-end (BLAKE3 batch, 8 threads, min of 5, idle machine,
`ZKB_RUNS=5 cargo bench --features zk --bench zk_vs_baseline`):

| batch | m | baseline prove | zk prove | prove × | verify × | proof size × |
|---:|---:|---:|---:|---:|---:|---:|
| 1,024 | 24 | 5.6 ms | 12.1 ms | 2.15 | 0.96 | 1.82 (288→524 KiB) |
| 4,096 | 26 | 12.1 ms | 36.0 ms | 2.97 | 1.05 | 1.72 |
| 16,384 | 28 | 34.1 ms | 130.1 ms | 3.82 | 1.00 | 1.64 |

Size and verify ratios are stable; prove times are load-sensitive. The
ratio grows toward the 4× L0 commit factor as m grows (the commit is a
larger fraction of the total). Future-work optimization: shrink the mask
block below a full half (jagged-style basis gating) to cut the commit
factor.

## 7. Future work

- sha2 / keccak / keccak3 randomizer sections (keccak's walker circuits need
  the randomizer comb terms added to `fold_alpha_batched`).
- Chain statements: the shift argument folds only the In/Out slots
  (`chain_common.rs::fold_in_out`), so its messages are unmasked witness
  functionals. Design (worked out, unimplemented): fold the committed
  chain-mask slot pair (already allocated in the BLAKE3 zk layout) like
  In/Out into a table `m(y,s₀)`; prover observes `σ = Σ m`, verifier samples
  `γ`; run the sumcheck on `W·g + γ·m`; final check gains `γ·m_at_point`;
  one extra packed-direct claim through the existing batched opening.
- Batch-major zk witness generation (currently row-major only).
- Full-rank (not k-wise) PIOP certificate as an offline job; a constructive
  transcript simulator on top of the audits.
- Cut the 2× mask-block overhead via jagged/partial mask blocks.

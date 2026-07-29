# Amendment A2: a committed mask channel for the lincheck

**Status: implemented.** The security argument lives in `docs/zk-proof.md`
§5b; this file is the diagnostic record — why the amendment was needed, what
was ruled out before the construction was touched, and how the built design
differs from the one first specified here.

## Why it was needed

The A1′ amendment masks the zerocheck round messages with a degree-2
committed channel `γ·P·Q`. It did not touch the lincheck, which was covered
only by the randomizer witness rows. Measured on a real BLAKE3 statement
(`tests/zk_blake3_certificate.rs`, m=20, 64 blocks, triangular probing, claim
space saturated):

| Classes under test | Mask image | Verdict |
|---|---|---|
| `zerocheck.round1_c` alone | 8192 / 8192 bits | passes |
| `lincheck.*` alone | 9728 / 10240 bits | **128 bits escape** |
| both together | 21632 / 30464 bits | **128 bits escape** |

One F128 direction of *claim-preserving* witness difference was uncovered, on
`lincheck.rounds` and `lincheck.z_partial`.

Why the fixture passed and BLAKE3 did not: the fixture's witness is ~81%
randomizer rows, a real BLAKE3 witness ~5.5%. Both results were correct.

### What was excluded first

The construction was changed only after every cheaper explanation failed
under measurement. Each of these was a real experiment, not a review:

- **The harness.** The identical procedure on the synthetic fixture gives
  `rank[resid | Δclaim] = 384 = rank(Δclaim)`
  (`control_same_procedure_on_the_passing_fixture`).
- **The zerocheck classes.** `zerocheck.round1_c` alone spans 8192/8192 — the
  A1′ channel does its job on the classes it targets.
- **Region alignment.** Lemma L3 is verified on the real layout: the A-species
  occupies 12 whole univariate-skip groups, the B-species 2, disjoint
  (`l3_round1_region_alignment_holds`).
- **The constant-wire pin.** It shifts the lincheck target by a challenge β
  identically for every valid witness (`lincheck.rs`, `const_pin_col`), so it
  induces no witness-difference direction.
- **The randomizer budget.** Reallocating the block's 896 randomizer bits to
  4 A-chunks + 3 B-chunks (2.3× the entropy in the covering species, spending
  the chain-mask reservation batch statements never use) left the image rank
  **identical** — 9728/10240, same 128 bits. Entropy was not the binding
  constraint; the image was rank-limited by the structure of the map. The
  change was reverted, having bought nothing.
- **The conditioning hypothesis.** The deficit was a suspiciously round 512
  bits = 4 field elements, constant under that 2.3× entropy change, which
  suggested it was not a coverage shortfall at all but the dimension of the
  lincheck transcript's built-in algebraic dependencies — in which case the
  fix would have been to condition on a missing transcript-determined value,
  with no change to the construction. The zerocheck's `a_eval` and `b_eval`
  are exactly such values (the verifier consumes them to form the lincheck's
  target). Adding both to the claim set, saturating at 5 × 128 = 640 bits over
  768 witness pairs, left the result **unchanged**: same image rank, same 128
  bits escaping, same attribution. Refuted.

With every conditioning value the verifier demonstrably learns already
accounted for and the direction still escaping, a mask channel was the
remaining candidate.

## What was built, and how it differs from the first sketch

This file originally specified a degree-2 channel `comb·z + γ_lc·S·T`,
mirroring A1′ one layer down. **The implemented amendment is additive
instead**, and the difference is not a simplification for its own sake — the
two layers are not analogous:

- In the zerocheck, the masked object is a *product* `â·b̂` of two
  witness-dependent multilinears. A mask has to live in the same degree-2
  space to preserve the sumcheck's degree structure, so `P·Q` it is, and
  coverage of a witness-difference direction inside that quadratic form is a
  rank condition that has to be certified.
- In the lincheck, `comb` is **public** and the `z`-slot enters **linearly**.
  Shifting `z ↦ z + γ_lc·S` therefore keeps the degree structure exactly as
  it was, and the entire layer becomes the honest transcript of a shifted
  witness. One committed polynomial, one opening, and the shift acts on the
  layer's *input* rather than having to reach a direction inside a form.

So the built construction is:

1. **Commit** a witness-free cube `S` (DRBG fork `a2-S`), padding rows zeroed,
   hidingly, root bound alongside `P`,`Q` before any challenge.
2. **Absorb** `σ_lc = Σ comb·S_vec` once `comb` is final (after α and the
   const-pin β), then **draw** `γ_lc`.
3. **Run** the existing sumcheck on `z + γ_lc·S`, initial claim
   `target + γ_lc·σ_lc`.
4. **Recover** the output claim `w = w_sent + γ_lc·Ŝ(ρ)`, with `Ŝ(ρ)` opened
   against `S`'s commitment at the lincheck's output point.

`zero_lincheck_padding_rows` keeps the committed cube and the padded fold in
agreement — the fold skips rows `[useful_bits, 2^k_log)` while a commitment
would not, and the fail-closed assert guarding that fired on a partial-block
fixture before it was handled.

### The one thing this does *not* make unconditional

`S` is a Boolean cube (the PCS commits bit-valued data), so the reachable
shift on the folded table is `γ_lc·Σ_j eq_j·S[j,i]` — a random
`F₂`-combination of the eq-table entries, independently per `i`. It spans all
of `F₂¹²⁸` per slot iff the eq table `F₂`-spans the field, which is a
property of the challenges. That is **measured by the coverage certificate**,
not assumed. It is the one place where a field-valued mask would give an
unconditional argument and a Boolean one does not.

### A known, deliberately deferred optimization

`S` is committed as a full `2^m` cube, so it costs a fourth full-size
commitment and opening. It does not need to be: the channel only ever masks
the *folded* `z_vec` of length `2^k_log` (4096 at the certified shape, against
`2^22`), and a commitment over that domain would be some three orders of
magnitude smaller. The obstacle is only that the opening point is then a
`k_log`-variate quirky point with no outer part, which the PCS ladder is not
currently shaped for.

This is left as-is on purpose: correctness first, cost second. The
reference path is certification-oriented, not optimized, and the benchmark
panel reports what it actually costs rather than what a tuned version would.

## How to tell it worked

1. `cargo test --release --workspace --features zk` — completeness, the
   tamper matrix, the γ-ordering tests and the schema tripwires.
2. `ZK_BLAKE3_CLASSES=lincheck` on
   `blake3_witness_difference_lies_in_the_mask_image` — the 128 escaping bits
   must go to zero.
3. The unrestricted run of the same test.
4. `scripts/zk-certify.sh` — the fixture certificate and every negative
   control must still hold; the added-leakage canary must still break
   coverage.
5. Re-run both benchmark panels; the channel adds one commitment and one
   opening, so the reference-path cost moves.

If (2) closes but (1) or (4) regresses, the amendment is unsound — prefer
reverting to shipping it.

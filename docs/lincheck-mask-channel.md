# Amendment A2: a committed mask channel for the lincheck

**Status: specified, not implemented.** This is the single remaining gap
between the current state and a zero-knowledge algebraic transcript on real
BLAKE3 batch statements. It is written so the work can start without
re-deriving the diagnosis.

## Why it is needed

The A1′ amendment masks the zerocheck round messages with a degree-2
committed channel `γ·P·Q`. It does not touch the lincheck, which is covered
only by the randomizer witness rows. Measured on a real BLAKE3 statement
(`tests/zk_blake3_certificate.rs`, m=20, 64 blocks, triangular probing, claim
space saturated at 384 bits):

| Classes under test | Mask image | Verdict |
|---|---|---|
| `zerocheck.round1_c` alone | 8192 / 8192 bits | passes |
| `lincheck.*` alone | 9728 / 10240 bits | **128 bits escape** |
| both together | 21632 / 30464 bits | **128 bits escape** |

One F128 direction of *claim-preserving* witness difference is uncovered, on
`lincheck.rounds` and `lincheck.z_partial`.

### What has been excluded

- **The harness.** The identical procedure on the synthetic fixture gives
  `rank[resid | Δclaim] = 384 = rank(Δclaim)`
  (`control_same_procedure_on_the_passing_fixture`).
- **Region alignment.** Lemma L3 is verified on the real layout: the A-species
  occupies 12 whole univariate-skip groups, the B-species 2, disjoint
  (`l3_round1_region_alignment_holds`).
- **The constant-wire pin.** It shifts the lincheck target by a challenge β
  identically for every valid witness (`lincheck.rs`, `const_pin_col`), so it
  induces no witness-difference direction.
- **The randomizer budget.** Reallocating the block's 896 randomizer bits to
  4 A-chunks + 3 B-chunks (2.3× the entropy in the covering species, spending
  the chain-mask reservation batch statements never use) left the image rank
  **identical** — 9728/10240, same 128 bits, deficit constant at 512 bits.
  Entropy is not the binding constraint; the image is rank-limited by the
  structure of the map.

Why the fixture passes and BLAKE3 does not: the fixture's witness is ~81%
randomizer rows, a real BLAKE3 witness ~5.5%. Both results are correct.

## The construction

Mirror A1′ one layer down. The lincheck proves
`Σ_x comb(x)·z(x) = target` by a degree-2 product sumcheck, so the same
degree-2 channel applies.

1. **Commit** two fresh witness-free multilinears `S,T` over the lincheck's
   domain (`2^{k_log}` after the outer fold), hidingly, alongside the witness
   and `P,Q`. Bind both roots before any challenge.
2. **Bind** `σ_lc = Σ_x eq(·,x)·S(x)·T(x)` into the transcript.
3. **Derive** `γ_lc` by Fiat–Shamir, after those roots and `σ_lc` — the
   ordering that Lemma L6 needs, for the same reason.
4. **Run** the lincheck sumcheck on `comb·z + γ_lc·S·T`; each round message
   becomes `e_j + γ_lc·M_j` and the running target starts at
   `target + γ_lc·σ_lc`.
5. **Send** `z_partial + γ_lc·s_partial` in place of `z_partial`.
6. **Open** `S(ρ_lc), T(ρ_lc)` *hidingly* at the lincheck's final point, so
   the leakage set gains only those two evaluations — a plain opening would
   enlarge `L` with the opened rows and un-cover claim-preserving directions,
   exactly as for `P,Q`.
7. **Verify**: the final check gains `γ_lc·S(ρ_lc)·T(ρ_lc)`, and the output
   claim `w` is recovered by subtracting the mask's contribution from the
   combined `z_partial` using the opened evaluations, so the downstream PCS
   opening is unchanged.

## What must be argued, not assumed

- **Completeness**: the combined claim telescopes, as in A1′ §6.
- **Soundness of the batching**: with all messages fixed, the residual is
  affine in `σ_lc`; a defect pair `(δ, δ')` is accepted iff `δ + γ_lc·δ' = 0`,
  so at most one `γ_lc` works and the ordering denies it. This is Lemma L6
  transplanted — reuse its constructive test
  (`zk_gamma_cancellation_unique_and_fs_ordering`) at the lincheck.
- **Knowledge soundness unchanged**: `S,T` feed no real constraint.
- **The output claim** must be exactly the pre-mask `w`, or the PCS binding
  to `ẑ` breaks. This is the step most likely to go wrong.

## How to tell it worked

1. `cargo test --release --workspace --features zk` — completeness, the
   tamper matrix, and the γ-ordering tests must all still pass.
2. `ZK_BLAKE3_CLASSES=lincheck` on
   `blake3_witness_difference_lies_in_the_mask_image` — the 128 escaping bits
   must go to zero.
3. The unrestricted run of the same test — must pass.
4. `scripts/zk-certify.sh` — the fixture certificate and every control must
   still hold; the added-leakage canary must still break coverage.
5. Re-run both benchmark panels; the lincheck channel adds two commitments
   and two openings, so the reference-path cost will move.

If (2) closes but (1) or (4) regresses, the amendment is unsound — prefer
reverting to shipping it.

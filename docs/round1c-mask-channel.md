# Amendment A3: masking the zerocheck's round-1 C-side

**Status: specified, not implemented.** This is the single remaining gap
between the current state and a covered algebraic transcript on real BLAKE3
batch statements. Written so the work can start without re-deriving the
diagnosis, and — like the A2 spec — written to be falsified cheaply before
anything in the construction is touched.

## Why it is needed

Amendment A2 closed the lincheck. On a real BLAKE3 statement
(`tests/zk_blake3_certificate.rs`, m=20, 64 blocks, claim space saturated at
640 bits) the residual attribution changed from three classes to one:

| Classes under test | Before A2 | After A2 |
|---|---|---|
| `lincheck.*` alone | 9,728 / 10,240 — **128 bits escape** | 10,240 / 10,240 — **passes** |
| `zerocheck.round1_c` alone | 8,192 / 8,192 — passes | 8,192 / 8,192 — passes |
| all PIOP classes | 128 bits escape, on `round1_c` + `lincheck.rounds` + `lincheck.z_partial` | 128 bits escape, on **`zerocheck.round1_c` only** |
| `zerocheck.*` alone | — | 12,032 / 20,224 — **128 bits escape**, on `round1_c` |

So one F128 direction of claim-preserving witness difference is still
uncovered, and it now sits entirely in `round1_c`.

**The gap is inside the zerocheck layer, not a cross-layer interaction.**
Running the certificate on `zerocheck.*` alone reproduces the failure exactly
— same 128 bits, same attribution — so nothing about the lincheck, A2, or the
interaction between the layers is involved. The arithmetic also confirms A2's
channel is clean and complete: the unrestricted joint image is 22,272 bits and
the zerocheck-only joint image is 12,032, and 22,272 − 12,032 = 10,240, the
full lincheck subspace. A2 contributes exactly that subspace and nothing else,
which is what an additive channel on a linear slot should do.

## What `round1_c` is, and why it is unmasked

`round1_c` is the C-side of the univariate-skip round-1 message:
`P^C(λ) = Σ_x eq(r_rest,x)·ĉ(λ,x)` with `ĉ = ẑ` (the relation has `C = I`),
sent as its `2^k_skip = 64` evaluations on Λ. It is **linear in the witness**,
and one scalar of it — `c_eval = P^C(z)` — is a public claim that the PCS
binds. The other 63 field elements are covered only by the randomizer rows.

Round 1 is excluded from the A1′ degree-2 channel deliberately, and the reason
matters for the repair: the verifier reconstructs the AB running claim using
the **zerocheck assumption** `P^AB(λ) + P^C(λ) = 0` for `λ ∈ S`. A mask that
does not vanish on `S` breaks that reconstruction. The `γ·P·Q` channel does
not vanish there, which is why it starts at round 2.

## The escape is joint, not marginal — read this before designing

`ZK_BLAKE3_CLASSES=round1_c` **passes**: the mask image restricted to
`round1_c` is the full 8,192 bits. The failure only appears when `round1_c` is
required to be covered *simultaneously* with every other coordinate. Full
projection onto a class means "for any target on that class there is an image
vector matching it there" — that vector is free to be wrong everywhere else.

This is the same phenomenon as the two-dimensional example in the paper's
conditional-coverage section, and it has a design consequence: **a mask that
merely adds rank to `round1_c` will not necessarily help.** What is needed is
a direction that moves `round1_c` while leaving the other classes fixed (or
moving them in a way the existing channels can undo). Anything else adds
image rank without closing the joint condition.

## Check this first (cheapest falsifiable step)

Before building anything, determine **which** direction escapes and what it
looks like on the other classes:

1. Extract the escaping vector explicitly — reduce a claim-preserving witness
   difference by the joint image and dump the residual by class, not just the
   rank. The harness already attributes by class (`coord_paths`); extend it to
   print the residual's support within `round1_c`.
2. Ask whether that residual is in the span of the *diagonal* directions
   `(M, M)` on `(round1_ab, round1_c)`. If it is, the cheap construction in
   the next section suffices. If it is not — and the current attribution,
   which names `round1_c` and **not** `round1_ab`, suggests it is not — then
   the diagonal design is ruled out before it is built.

The A2 spec's analogous "check this first" step was run and refuted the cheap
fix. Doing the same here is what keeps the effort proportionate.

## Two candidate constructions

### (a) The diagonal mask — cheap, probably insufficient

Add the **same** witness-free mask `γ_c·M` to both `round1_ab` and
`round1_c`. In characteristic 2 the combined vector `round1_ab + round1_c` is
then unchanged, so the zerocheck assumption and the whole AB reconstruction
survive untouched. The verifier un-shifts using one scalar `M(z) = Ŝ_c(z,
r_rest)`, opened against `S_c`'s commitment exactly as A2 opens `Ŝ(ρ)` — and
the C-claim handed to the PCS is `final_c_eval + γ_c·M(z)`.

This is a genuinely small change. Its weakness is stated above: it only
contributes diagonal directions, and the measured residual appears to be
off-diagonal.

### (b) Independent masks with a vanishing constraint — the real design

Use different masks `M_ab`, `M_c`, subject to `M_ab + M_c ≡ 0` on `S` so the
zerocheck assumption still holds. Since `P^C` has degree `< ell` and the
combined polynomial degree `< 2·ell`, the admissible difference `M_ab + M_c`
is any multiple of the vanishing polynomial of `S` of degree `< 2·ell` — an
`ell`-dimensional space. That is enough freedom to move `round1_c`
independently of `round1_ab`.

The work this needs, and it is not small:

- **Where the masks come from.** They must be round-1 messages of *committed*
  witness-free objects, or the verifier cannot bind them. Deriving a pair
  satisfying the vanishing constraint from committed cubes is the crux.
- **The two interpolation conventions.** Round 1 mixes the naive convention
  (`round1_c`, restored `C_s` factor) with the combined-polynomial
  convention used for `interpolate_at_z_combined`. A mask must be expressed
  correctly in both.
- **Soundness.** The vanishing constraint is exactly what a cheating prover
  would want to relax: the assumption `P^AB + P^C = 0` on `S` is what forces
  an honest witness. Any masking that gives the prover freedom on `S` is a
  soundness break, not a privacy improvement. This needs its own argument,
  not an analogy to A2's.

## How to tell it worked

1. `cargo test --release --workspace --features zk` — completeness, the tamper
   matrix, the γ-ordering tests, the schema tripwires.
2. `ZK_BLAKE3_CLASSES=round1_c`, then `=zerocheck`, then unrestricted, on
   `blake3_witness_difference_lies_in_the_mask_image` — the last of these is
   the one that has to go from 768/640 to 640/640.
3. `scripts/zk-certify.sh` — the fixture certificate and every negative
   control still hold; the added-leakage canary still breaks coverage.
4. An explicit false-statement test through the amended round 1
   (`a1_false_statement_rejected_end_to_end` extended), because (b) touches
   the constraint-domain assumption that makes the zerocheck sound.

If (2) closes but (1), (3) or (4) regresses, the amendment is unsound —
prefer reverting to shipping it.

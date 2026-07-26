# Amendment A3: masking the zerocheck's round-1 C-side

**Status: implemented.** The security argument is in `docs/zk-proof.md` §5c;
this file is the diagnostic record and the design rationale.

**Measured outcome.** On the real BLAKE3 statement, restricted to the
zerocheck classes (m=20, 64 blocks, claims saturated at 640 bits), the joint
mask image went from **12,032 of 20,224 bits with 128 escaping** to
**20,224 of 20,224 with `rank[resid | Δclaim] = 640 = rank(Δclaim)`** —
nothing escapes.

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

## Check this first — already answered: the residual is off-diagonal

The cheap question is whether the escaping direction lies in the span of the
*diagonal* directions `(M, M)` on `(round1_ab, round1_c)`, because if it does,
construction (a) below suffices and nothing hard is needed.

**It does not.** The harness already reports which coordinate classes the
excess rows touch, and it lists classes when they apply — in the pre-A2
unrestricted run it named three. In the current run it names exactly one:

```
  residual attribution — which coordinate classes carry it:
    zerocheck.round1_c: 768 row(s) touch it (64 F128)
```

`round1_ab` is absent, so the excess rows have zero support there. A diagonal
mask moves both classes by the same amount and therefore cannot produce a
direction supported on one of them alone. **Construction (a) is ruled out by
measurement already in hand**, before it is built.

What would still be worth extracting, if construction (b) is attempted, is the
escaping vector's support *within* `round1_c` — which of the 64 evaluations it
occupies, and whether that pattern is stable across witness pairs and
challenge tuples. That tells you the shape the mask has to reach.

## Two candidate constructions

### (a) The diagonal mask — cheap, and RULED OUT by the measurement above
### (NOT the design that was built; kept as the record of a dead end)

Add the **same** witness-free mask `γ_c·M` to both `round1_ab` and
`round1_c`. In characteristic 2 the combined vector `round1_ab + round1_c` is
then unchanged, so the zerocheck assumption and the whole AB reconstruction
survive untouched. The verifier un-shifts using one scalar `M(z) = Ŝ_c(z,
r_rest)`, opened against `S_c`'s commitment exactly as A2 opens `Ŝ(ρ)` — and
the C-claim handed to the PCS is `final_c_eval + γ_c·M(z)`.

This is a genuinely small change, and it is recorded here only so nobody
re-derives it and builds it: it contributes diagonal directions only, and the
residual is measurably off-diagonal (see above). It would add image rank,
change the measured numbers, and not close the criterion — the most expensive
kind of wrong answer, because it looks like progress.

### (b) Independent masks with a vanishing constraint — THE IMPLEMENTED DESIGN

Use different masks `M_ab`, `M_c`, subject to `M_ab + M_c ≡ 0` on `S` so the
zerocheck assumption still holds. Since `P^C` has degree `< ell` and the
combined polynomial degree `< 2·ell`, the admissible difference `M_ab + M_c`
is any multiple of the vanishing polynomial of `S` of degree `< 2·ell` — an
`ell`-dimensional space. That is enough freedom to move `round1_c`
independently of `round1_ab`.

How each of the anticipated difficulties actually resolved:

- **Where the masks come from.** Two witness-free cubes `S_c`, `S_h`,
  committed hidingly before any challenge. Their masks are the *round-1
  C-side message* of each cube — the same computation `round1_c` is, applied
  to a mask instead of the witness. That is what makes the two values the
  verifier needs, `M_c(z)` and `h(z)`, equal to `Ŝ_c(z, r_rest)` and
  `Ŝ_h(z, r_rest)`: ordinary PCS evaluations at exactly the c-claim point,
  bound by ordinary openings. (Pinned by
  `round1_c_output_is_independent_of_ab`, since the mask messages are
  obtained by calling the round-1 routine with zero `a`,`b`.)
- **The vanishing constraint imposes nothing.** `M_ab = M_c + V_S·h` and
  `V_S` has no zero on `Λ`, so as `M_c|_Λ` and `h|_Λ` range freely the pair
  `(M_c|_Λ, M_ab|_Λ)` ranges over everything. The constraint that looked
  like the obstacle costs no freedom at all — it only forces the *shape* of
  the pair.
- **The two interpolation conventions.** Both masks are built by the same
  code path as `round1_c`, including the `C_s` restoration, so they are in
  the same convention by construction rather than by argument.
- **Soundness.** The vanishing constraint is exactly what a cheating prover
  would want to relax, and A3 does not relax it: the *combined* polynomial
  still vanishes on `S`, because the masks were chosen so their sum is a
  multiple of `V_S`. The prover gains no freedom on `S`; the two scalars it
  supplies are bound by commitments, and the verifier's derived claims are
  un-shifted exactly. What the prover controls is what it controlled before.

## A note on how the completeness break was found

The first end-to-end run failed with `SumcheckFinalFailed`, and the algebra
above said it should not. Rather than adjust the algebra until the test
passed, the un-shift was bisected over its terms (`none` / `mc` / `V_S·h` /
both) — and *every* variant failed identically, which no error in the
un-shift can produce. That pointed at the code rather than the derivation:
the un-shift edit had never been applied, having been lost when the script
that wrote it aborted midway. The derivation was right the whole time.

The staged completeness test (`prove_verify_zk_round1_mask_roundtrip`, zero /
diagonal / full) exists so that this class of confusion is caught in one run
next time: the zero stage pins that the masked path reduces *exactly* to the
unmasked one.

## How to tell it worked

1. `cargo test --release --workspace --features zk` — completeness, the tamper
   matrix, the γ-ordering tests, the schema tripwires.
2. `ZK_BLAKE3_CLASSES=zerocheck`, then unrestricted, on
   `blake3_witness_difference_lies_in_the_mask_image`.
3. `scripts/zk-certify.sh` — the fixture certificate and every negative
   control still hold; the added-leakage canary still breaks coverage.
4. `a1_false_statement_rejected_end_to_end`, because A3 touches the
   constraint-domain assumption that makes the zerocheck sound.

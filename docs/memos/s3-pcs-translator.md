# S3 conditional replacement for the blinded PCS

Protocol: `flock-zk-fv-v3`

## Translator

Let the committed message be `f' = [mu || z]`, the blinder be
`g = [g_lo || g_top]`, and the post-commitment challenge be nonzero `c`. The
recursive opening uses:

```
F = f' + c*g.
```

For a packed witness delta `d` that preserves every public opening claim, use:

```
delta_g_top = c^-1*d
E_mu(delta_mu)|S = E_z(d)|S
delta_g_lo = c^-1*delta_mu.
```

Here `S` is the set of L0 queried positions and `E` is the exact additive-NTT
encoder. Characteristic two gives both
`delta_mu + c*delta_g_lo = 0` and `d + c*delta_g_top = 0`, so `delta_F = 0`
globally. The middle equation also makes the raw `f'` L0 rows invariant; after
multiplication by `c^-1`, it makes the raw `g` rows invariant. Thus every
post-L0 algebraic value, including recursive rows, induced-basis sumchecks,
OOD values, and `yr`, is unchanged.

`pcs::symbolic_opening::translate_mask_for_queries` solves the middle equation
over F2^128 and verifies the resulting raw rows against the same interleaved
additive NTT used by `commit_zk`. The test includes a nonzero public-claim
kernel direction and rejects `c = 0`.

## Functional closure

`OPENING_FUNCTIONAL_MANIFEST` classifies all twelve proof-field categories.
`assert_proof_fields_classified` exhaustively destructures the proof structs,
so a wire-schema addition fails compilation until classified. The pinned
manifest is `docs/artifacts/s3_opening_functionals.json`.

The `y_g` delta is `c^-1 * <d,b>` and is zero because composition supplies a
claim-kernel `d`. Grinding nonces can be recomputed on the invariant prefix.
Merkle roots and authentication siblings are the random-oracle boundary, not
algebraic field functionals.

## L0 entropy

The low mask subcode has `w / num_ntts` free field symbols per lane. Evaluation
at any smaller set of distinct positions has full row rank in the degree-graded
novel basis. Therefore an additional fresh wide leaf retains two field symbols
per lane, one in `f'` and one in `g`.

For the BLAKE3-256 production fast profile:

```
L0 queries                  218
mask symbols per lane       512
wide lanes                  128
conditional bits per leaf   128 * 128 = 16384
```

The gate and fixture values are pinned in
`docs/artifacts/s3_minentropy_table.json`. No recursive-level sibling entropy
term is needed: `delta_F = 0` makes every recursive codeword, root, and
authentication sibling identical. Only L0 commits to the separately changing
`f'` and `g` rows.

## Bound and scope

The algebraic translator is a measure-preserving translation outside `c = 0`
and the query-solvability bad set. The Lean theorem
`conditional_replacement_tv_bound` composes the algebraic bad-set mass with a
separate hash-boundary term. This memo establishes the PCS algebraic
replacement and L0 entropy input, not the final random-oracle simulation bound
by itself.

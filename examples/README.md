# VEIL examples of FLOCK's own protocols

This package holds three full zero-knowledge examples built on the protocols
of this repository: the FLOCK zerocheck with univariate skip, the FLOCK
lincheck, the hiding Ligerito PCS with ring-switched openings, and the
`veil-f128` constraint layer. The examples take their names and their
two-function structure from the `slop-veil` examples (`root`, `mle_eval`,
`zerocheck`), but they prove FLOCK statements over `GF(2)` witnesses, not the
upstream KoalaBear protocols. There is no transparent backend, because
`SPEC.md` forbids a non-ZK flavor.

```sh
cargo run --release -p veil-examples --example root_zk
cargo run --release -p veil-examples --example mle_eval_zk
cargo run --release -p veil-examples --example zerocheck_zk
cargo test --release -p veil-examples
```

## The three examples

**`mle_eval_zk`** — the smallest FLOCK protocol: one committed witness and
one opening. The prover commits a random `2^22`-bit witness with the hiding
PCS, samples a quirky point, and sends the evaluation of the witness's
multilinear extension, one-time padded. The verify body registers one
ring-switched claim. Nothing else is proved; the example shows the hiding
commitment, the masked ring slices, and the blinded joint opening in
isolation.

**`zerocheck_zk`** — FLOCK's zerocheck with univariate skip on committed
data. The prover commits three random `2^22`-bit vectors `a`, `b`, and
`c = a AND b`, then runs the native zerocheck prover through the masking
context, so every round message is one-time padded. The verify body replays
the univariate-skip interpolation and the fold recurrences as VEIL
constraints, checks the terminal product, and ties the three terminal
evaluations to `a`, `b` at `(z, rho)` and to `c` at `(z, r_rest)` with
ring-switched claims.

**`root_zk`** — a complete FLOCK argument for a Boolean R1CS. The statement
is knowledge of a root of a public degree-50 polynomial over `GF(2^8)`. One
`2^12`-bit block encodes one Horner evaluation as an R1CS with `C = I`, the
circuit convention of this repository; `2^10` copies fill the batch. The
prover commits the packed witness, then runs the native zerocheck and
lincheck provers through the masking context. The verify body is the shifted
FLOCK verifier for this R1CS: zerocheck, lincheck with the constant-wire
pin, and the two ring-switched claims `ab` and `c` on the single commitment.

| Example | Statement | FLOCK layers | Oracles | Masks |
|---|---|---|---|---|
| `mle_eval_zk` | a committed `2^22`-bit witness evaluates to the sent value at a random quirky point | ring-switched opening | 1 | 257 |
| `zerocheck_zk` | three committed `2^22`-bit vectors satisfy `a AND b = c` | zerocheck, three ring-switched openings | 3 | 930 |
| `root_zk` | knowledge of a root of a public degree-50 polynomial over `GF(2^8)`, as a Boolean R1CS with `C = I` | zerocheck, lincheck, two ring-switched openings | 1 | 750 |

The mask count is the number of prover messages: the zerocheck sends two
round-one vectors of 64, `m - 6` round pairs, and two terminal evaluations;
the lincheck sends `k_log - 6` round pairs and a partial vector of 64; every
ring-switched claim sends 128 witness slices and 128 blinder slices.

## The context layer

`src/ctx.rs` keeps the three roles of the upstream compiler traits. A single
`*_verify` body runs on the mask counter, on the prover replay that emits the
constraints, and on the verifier.

The prover context is itself a `Challenger`. Every field value the native
`flock_core` provers observe through it is one-time padded, recorded as a
sent message, and absorbed in masked form. The native zerocheck and lincheck
provers therefore run unchanged. The replay pass returns the recorded
challenges, so the real Fiat--Shamir state stays untouched, exactly as the
upstream replay context does.

`src/flock.rs` holds the verify bodies. They are ports of the production
shifted verifier circuit in `crates/flock-prover/src/succinct_veil.rs`: the
univariate-skip interpolation, the multilinear fold recurrences, the terminal
product, the lincheck rounds and final dot product. Each reads masked values
as affine `LinearCombination`s and emits `assert_zero` and `assert_mul`
constraints.

## Ring-switched openings

A committed object is a Boolean vector packed into `2^(m-7)` `F128` words
under `commit_zk_with_ro`: a uniform low mask block, a full blinder `g`, one
256-bit salt per leaf, and a fresh tree nonce. A claim `ẑ(point) = v` at a
FLOCK quirky point is discharged as in production:

1. The prover sends the 128 witness slices `s(z)` and the 128 blinder slices
   `s(g)` one-time padded.
2. A bounded grind runs and a challenge `c` in `F*` is sampled.
3. The public blinded slices `q = s(z) + c * s(g)` are bound.
4. The shifted circuit checks `q_i = s(z)_i + (c * s(g))_i` for every slice
   over `GF(2)`-linear packed-field scaling, and `v = <weights, s(z)>`.
5. The PCS opens `z + c * g` at the point with `q` as the ring-switch proof,
   on a transcript fork of its own.

The opened data is independent of the witness because `g` is uniform and
`c` is nonzero. This is the mechanism of `docs/ARCHITECTURE.md`, section
"Outer shielded commitment", applied to each committed vector.

## The `root_zk` relation

One `2^12`-bit block holds one instance. Wire 0 is the constant one and is
pinned by the lincheck. Wires 1 to 8 hold the root. Each Horner step spends
64 product rows `t_ij = acc_i * root_j` and 8 reduction rows that XOR the
products of each output bit through the constant wire, with the public
coefficient bits folded in. An OR chain reduces the final accumulator to one
bit, and the row of the constant wire, `1 = (1 + nonzero) * 1`, forces that
bit to zero. The batch tiles `2^10` copies of the block; the copies are
hidden like the rest of the witness.

## Parameters and scope

The hiding PCS uses `PcsParams { m: 22, log_inv_rate: 1, log_batch_size: 6,
profile: Secure, zk: true }`, the production floor. The committed message is
`[mask || z]`, so the Ligerito config is the embedded `m23_secure` profile
and the blind grind uses two bits. The VEIL constraint layer uses
`ConstraintParameters::succinct_flock_secure()` and every circuit passes
`certify_constraint_soundness`.

The examples inherit the production zero-knowledge argument by construction.
Two simplifications are deliberate. The R1CS carries no randomizer rows: the
VEIL one-time pads cover every visible coordinate, and the blinded opening
covers the PCS. The examples carry no witness-free simulator. They make no
standalone security claim; see [`docs/SECURITY.md`](../docs/SECURITY.md) and
[`SPEC.md`](../SPEC.md) for the production scope.

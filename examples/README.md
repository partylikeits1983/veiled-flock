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

**`root_zk`** — a complete FLOCK argument for a Boolean R1CS. The statement is
knowledge of one selected root of a public degree-50 polynomial over
`GF(2^8)`. The polynomial has a public set of valid roots; because the field is
tiny, the example hides which valid root was used, not the root set itself. One
`2^12`-bit block encodes one Horner evaluation as an R1CS with `C = I`, the
circuit convention of this repository; `2^10` copies fill the batch. The block
also carries private randomizer rows that are copied through free constraints
and committed with the witness. The prover commits the packed witness, then
runs the native zerocheck and lincheck provers through the masking context. The
verify body is the shifted FLOCK verifier for this R1CS: zerocheck, lincheck
with the constant-wire pin, and the two ring-switched claims `ab` and `c` on the
single commitment.

| Example | Statement | FLOCK layers | Oracles | Masks |
|---|---|---|---|---|
| `mle_eval_zk` | a committed `2^22`-bit witness evaluates to the sent value at a random quirky point | ring-switched opening | 1 | 257 |
| `zerocheck_zk` | three committed `2^22`-bit vectors satisfy `a AND b = c` | zerocheck, three ring-switched openings | 3 | 930 |
| `root_zk` | knowledge of which public root of a public degree-50 polynomial over `GF(2^8)` was selected, as a Boolean R1CS with `C = I` | zerocheck, lincheck, two ring-switched openings | 1 | 750 |

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
pinned by the lincheck. Wires 1 to 8 hold the selected root. Each Horner step
spends 64 product rows `t_ij = acc_i * root_j` and 8 reduction rows that XOR
the products of each output bit through the constant wire, with the public
coefficient bits folded in. An OR chain reduces the final accumulator to one
bit, and the row of the constant wire, `1 = (1 + nonzero) * 1`, forces that bit
to zero. The block then allocates 256 randomizer rows of the form `u = u * 1`.
Those rows are private, fresh per batch block, included in the committed
witness, and independent of the public polynomial relation. The batch tiles
`2^10` blocks.

## Simulator-backed assurance

The examples include executable simulator-style assurance tests in addition to
roundtrip and mutation tests:

- `mle_eval_zk` and `zerocheck_zk` construct accepted views from independently
  sampled satisfying witnesses for the same public parameter shape.
- `root_zk` constructs accepted proofs for two different valid roots under the
  same public polynomial and R1CS digest.
- all three examples scan the serialized proof for accidentally exposed
  unmasked terminal evaluations or witness ring slices.
- `root_zk` checks that its public polynomial does not encode the selected root
  in the constant coefficient and that its randomizer rows are not fixed zero.

These tests are regression guards for the examples' public view. They are not a
replacement for the production BLAKE3 preimage simulator in `flock-prover`, and
they do not make a standalone pROM theorem for this package.

## Parameters and scope

The hiding PCS uses `PcsParams { m: 22, log_inv_rate: 1, log_batch_size: 6,
profile: Secure, zk: true }`, the production floor. The committed message is
`[mask || z]`, so the Ligerito config is the embedded `m23_secure` profile
and the blind grind uses two bits. `BitPcs::new` runs the production
batch-opening certificate on both configs: the L0 query count must fit in
the mask symbols of one lane, query-phase grinding is not allowed, fold
grinding is bounded per site and in the number of sites, and the blind grind
is in range. `m = 21` fails that certificate (298 queries against a
256-symbol lane) and is rejected; `m = 22` is the smallest accepted shape.
The grind bounds are the production values from `succinct_veil.rs`. The VEIL constraint layer uses
`ConstraintParameters::succinct_flock_secure()` and every circuit passes
`certify_constraint_soundness`.

The examples mirror the production zero-knowledge construction: VEIL one-time
pads cover every visible coordinate, the hiding PCS and blinded openings cover
the committed witnesses, and `root_zk` includes private randomizer rows in its
R1CS witness. The simulator-style tests above are deliberately narrower than
the production witness-free simulator. The examples make no standalone security
claim; see [`docs/SECURITY.md`](../docs/SECURITY.md) and [`SPEC.md`](../SPEC.md)
for the production scope.

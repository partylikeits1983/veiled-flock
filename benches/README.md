# End-to-end proving benchmarks

This directory holds the e2e bench crates. They measure full prove and
verify cycles for hash chains.

- `blake3-bench` — BLAKE3 chains over the two veil-f128 backends. Its lib
  also holds the shared harness.

The micro-benches in `crates/flock-prover/benches/` are different. They
measure raw hash throughput only. These crates are the e2e proving suite.

## How to run

```sh
cargo bench -p blake3-bench
```

Smoke mode shrinks each sweep to one small row with one timing run:

```sh
BENCH_SMOKE=1 cargo bench -p blake3-bench
```

Write the rows as JSON for tracking across commits:

```sh
cargo bench -p blake3-bench -- --json blake3-results.json
```

Sweep overrides (validated, and loud on bad values):

- `BENCH_FRAMED_MAX_LOG` — framed BLAKE3 rows above n = 64. Read the
  memory model in `blake3-bench/blake3_hashchain_e2e.rs` first.

## Backends

| Backend | What it is |
|---|---|
| `veil-framed` | The direct VEIL argument: `VeiledBlake3Setup` over `veil_f128::prove_block_r1cs`. The witness is proven inside the VEIL code itself, with materialized sparse matrices. Largest proofs, no Ligerito layer. |
| `veil-succinct` | The succinct VEIL argument: `Blake3PreimageZkSetup` over `succinct_veil`. The witness stays in FLOCK's hiding Ligerito commitment; a small VEIL circuit proves the additively-masked transcript. This is the path the `veiled_flock` CLI ships. Experimental — see the setup rustdoc. |

## Columns

| Column | Meaning |
|---|---|
| `backend` | Prover label. See the Backends table above. |
| `relation` | What the circuit enforces. See the caveat below. |
| `n_real` / `n_slots` / `util` | Real chain links, padded witness slots, and their ratio. |
| `setup`, `witness`, `prove`, `verify` | Wall time per section. Prove and verify are best-of-N. |
| `bytes` | Proof size. One fixint bincode encoder serves every row. |
| `hash/s` | Proven links per second: `n_real / prove`. |
| `slowdown` | `prove` divided by the native chain time at the same `n_real`. The native rate comes from one warmed, amortized calibration. |
| `params` | The parameter set that produced the row. Rows without equal `params` are not comparable. |

## Relation caveat

Every BLAKE3 row is `public-chain`: each block proves one relation with
public input/output values. The benched verify closure checks linkage
over the public values, not the circuit.

The `public-chain` rows have no secret witness at all: with every digest
public, each block's input is publicly derivable. Those rows measure
batch throughput of independent per-block relations. They do not measure
chain-statement proving.

## Verification behavior

Each bench asserts that `verify` returns Ok. A failed verify aborts the
run — e2e means a broken proof is a bench failure, not a data point.

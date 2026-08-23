# End-to-end proving benchmarks

This directory holds two bench crates. They measure full prove and verify
cycles for hash chains.

- `blake3-bench` — BLAKE3 chains over the two veil-f128 backends. Its lib
  also holds the shared harness.
- `keccak-bench` — keccak-f chains over the native chain prover and the
  succinct-VEIL backend.

The micro-benches in `crates/flock-prover/benches/` are different. They
measure raw hash throughput only. These crates are the e2e proving suite.

## How to run

```sh
cargo bench -p blake3-bench
cargo bench -p keccak-bench
```

Smoke mode shrinks each sweep to one small row with one timing run:

```sh
BENCH_SMOKE=1 cargo bench -p blake3-bench -p keccak-bench
```

Write the rows as JSON for tracking across commits:

```sh
cargo bench -p keccak-bench -- --json keccak-results.json
```

Sweep overrides (validated, and loud on bad values):

- `BENCH_FRAMED_MAX_LOG` — framed BLAKE3 rows above n = 64. Read the
  memory model in `blake3-bench/blake3_hashchain_e2e.rs` first.
- `BENCH_KECCAK_MAX_LOG` — keccak rows above n = 4096 (m = 28). Ligerito
  configs stop at m = 35.

## Columns

| Column | Meaning |
|---|---|
| `backend` | Prover: `veil-framed`, `veil-succinct`, or `native-ligerito`. |
| `relation` | What the circuit enforces. See the caveat below. |
| `n_real` / `n_slots` / `util` | Real chain links, padded witness slots, and their ratio. |
| `setup`, `witness`, `prove`, `verify` | Wall time per section. Prove and verify are best-of-N. |
| `bytes` | Proof size. One fixint bincode encoder serves every row. |
| `hash/s` | Proven links per second: `n_real / prove`. |
| `slowdown` | `prove` divided by the native chain time at the same `n_real`. The native rate comes from one warmed, amortized calibration. |
| `params` | The parameter set that produced the row. Rows without equal `params` are not comparable. |

## Relation caveat

The `relation` column separates two different statements:

- `chain-in-circuit` (native keccak `prove_chain`): the committed witness
  enforces `state_24[i] == state_0[i + 1]`. Only the two endpoints are
  public.
- `public-chain` (all VEIL rows, BLAKE3 and keccak): each block proves one
  relation with public input/output values. The benched verify closure
  checks linkage over the public values, not the circuit.

The `public-chain` rows have no secret witness at all: with every digest
or state public, each block's input is publicly derivable. Those rows
measure batch throughput of independent per-block relations. They do not
measure chain-statement proving. A cross-backend comparison at equal
relation is future work (Part 7 of the plan).

## Verification behavior

Each bench asserts that `verify` returns Ok. A failed verify aborts the
run — e2e means a broken proof is a bench failure, not a data point.

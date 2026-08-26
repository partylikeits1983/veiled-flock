# End-to-end proving benchmarks

Two bench crates measure full prove and verify cycles for hash chains, and
`harness` holds the code that they share. `blake3-bench` proves BLAKE3 chains on
the two veil-f128 backends. `keccak-bench` proves keccak-f chains on the native
chain prover and the succinct-VEIL backend. The micro-benches in
`crates/flock-prover/benches/` are different, because they measure raw hash
throughput only.

## How to run

Use the tuned `bench` profile. A bare `--release` changes the codegen, because
the workspace tunes `[profile.bench]` only.

```sh
cargo run --profile bench -p blake3-bench --bin blake3_e2e             # full sweep
cargo run --profile bench -p keccak-bench --bin keccak_e2e -- --smoke  # one point
cargo run --profile bench -p keccak-bench --bin keccak_e2e -- --json out.json
```

Both bins take `--smoke`, `--runs`, one sweep-bound flag, and `--json`. An
environment variable is a fallback only, and a flag always wins. The README of
each crate holds the full flag table.

`cargo bench -p <crate>` reaches the criterion targets, which ignore
`BENCH_SMOKE`. The bins land in `target/release/`. The `bench` profile also
applies to the dependencies, but `cargo bench` builds them as `release`, so make
a new baseline one time after a change to the layout of this suite.

## Backends

| Backend | What it is |
|---|---|
| `veil-framed` | The direct VEIL argument, BLAKE3 only. `VeiledBlake3Setup` over `veil_f128::prove_block_r1cs`, with materialized sparse matrices. The largest proofs, and no Ligerito layer. |
| `veil-succinct` | The succinct VEIL argument, BLAKE3 and keccak. The witness stays in the hiding Ligerito commitment, and a small VEIL circuit proves the masked transcript. The `veiled_flock` CLI ships this path. Experimental. |
| `native-ligerito` | The native chain prover, keccak only. `KeccakSetup::prove_chain`, with no VEIL layer and no zk mask. It is the in-circuit reference row. |

## Columns

| Column | Meaning |
|---|---|
| `backend`, `relation` | The prover, and what the circuit enforces. |
| `n_real`, `n_slots`, `util` | Real links, padded slots, and their ratio. |
| `setup`, `witness`, `prove`, `verify` | Wall time per section. Prove and verify are the best of N. |
| `bytes` | Proof size from one fixint bincode encoder. |
| `hash/s` | `n_real / prove`. |
| `slowdown` | `prove` divided by the native time at the same `n_real`, from one warmed calibration. |
| `params` | Two rows are comparable only if their `params` are equal. |

## The relation caveat

`chain-in-circuit` means that the committed witness enforces the link
`state_24[i] == state_0[i + 1]`, and only the two endpoints are public.
`public-chain` means that each block proves one relation with public input and
output values, and the verify closure checks the links outside the circuit.

A `public-chain` row has no secret witness, because every digest or state is
public. Such a row measures the batch throughput of independent per-block
relations. It does not measure the proof of a chain statement.

The keccak bench also runs `veil-succinct` at `chain-in-circuit`. That row and
the native row prove the same relation, so a comparison of the two gives the
cost of the zk mask layer. The BLAKE3 rows stay `public-chain` only.

Each bench asserts that verify returns `Ok`. A failed verify stops the run.

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

Both crates are dual mode. The e2e suite is a bin (run under the tuned
`bench` profile — never bare `--release`, which changes codegen); the
`cargo bench` target is a criterion stage-timing complement:

```sh
cargo run --profile bench -p blake3-bench --bin blake3_e2e
cargo run --profile bench -p keccak-bench --bin keccak_e2e
```

Smoke mode shrinks each sweep to one small point with one timing run:

```sh
cargo run --profile bench -p blake3-bench --bin blake3_e2e -- --smoke
cargo run --profile bench -p keccak-bench --bin keccak_e2e -- --smoke
```

Write the rows as JSON for tracking across commits:

```sh
cargo run --profile bench -p blake3-bench --bin blake3_e2e -- --json blake3-results.json
cargo run --profile bench -p keccak-bench --bin keccak_e2e -- --json keccak-results.json
```

Both bins take the same flag shape with env vars as fallbacks
(`--smoke`/`BENCH_SMOKE`, `--runs`, one sweep-bound flag, `--json`); a
flag wins over its env var. The per-crate READMEs carry the full flag
tables. Muscle-memory trap: `BENCH_SMOKE=1 cargo bench -p <crate>` no
longer runs an e2e suite — `cargo bench` reaches the criterion targets,
which ignore that env var.

Sweep overrides (validated, and loud on bad values):

- `--framed-max-log` / `BENCH_FRAMED_MAX_LOG` — framed BLAKE3 rows above
  n = 64. Read the memory model in `blake3-bench/src/blake3.rs`
  first.
- `--max-log` / `BENCH_KECCAK_MAX_LOG` — keccak rows above n = 4096
  (m = 28). Ligerito configs stop at m = 35.

## Backends

| Backend | What it is |
|---|---|
| `veil-framed` | The direct VEIL argument (BLAKE3 only): `VeiledBlake3Setup` over `veil_f128::prove_block_r1cs`. The witness is proven inside the VEIL code itself, with materialized sparse matrices. Largest proofs, no Ligerito layer. |
| `veil-succinct` | The succinct VEIL argument (BLAKE3 and keccak): `Blake3PreimageZkSetup` / `KeccakZkSetup` over `succinct_veil`. The witness stays in FLOCK's hiding Ligerito commitment; a small VEIL circuit proves the additively-masked transcript. Keccak has two relations on this backend: per-block with public states (`public-chain`) and, via `prove_succinct_chain`, in-circuit linkage with endpoints-only publics (`chain-in-circuit`). This is the path the `veiled_flock` CLI ships. Experimental — see the setup rustdoc. |
| `native-ligerito` | FLOCK's native chain prover (keccak only): `KeccakSetup::prove_chain`. No VEIL layer, no zk masking. It enforces chain linkage in-circuit and serves as the in-circuit reference row. |

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
measure chain-statement proving.

The keccak bench also runs `veil-succinct` at `chain-in-circuit`
(`prove_succinct_chain`, Part 7): the succinct backend proving the SAME
relation as the native row. Compare those two rows for the cost of the
zk masking layer at equal relation. The BLAKE3 backends stay
`public-chain` only.

## Verification behavior

Each bench asserts that `verify` returns Ok. A failed verify aborts the
run — e2e means a broken proof is a bench failure, not a data point.

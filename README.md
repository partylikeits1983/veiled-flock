# veiled-flock

Zero-knowledge batched BLAKE3 preimage proofs over binary fields,
combining Succinct's FLOCK and VEIL.

FLOCK provides fast batched hash proving. VEIL adds zero knowledge to
hash-based multilinear proof systems. veiled-flock adapts those ideas
to FLOCK's binary-field setting.

Given an ordered list of BLAKE3 digests, the prover demonstrates that
it has corresponding 64-byte preimages without revealing those
preimages.

## Overview

VEIL-FLOCK is a succinct zero-knowledge FLOCK composition for ordered batches
of 64-byte BLAKE3 preimages. The prover shows knowledge of one private
64-byte message for each public BLAKE3 digest in the same order:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

The proof bundle contains the ordered public digests, the witness commitment,
and the VEIL proof, but never the private messages. The full-ZK path combines
FLOCK's BLAKE3-preimage circuit, masked transcript values, hiding PCS openings,
and the native `GF(2^128)` VEIL backend. See the
[VEIL paper](https://eprint.iacr.org/2026/683) for the wrapper design and
[SECURITY.md](docs/SECURITY.md) for this repository's exact security scope.

## Repository layout

- **[crates/flock-core](crates/flock-core)** - FLOCK field, transcript,
  polynomial, PCS, zerocheck, lincheck, and R1CS building blocks.
- **[crates/flock-prover](crates/flock-prover)** - End-to-end proof systems,
  BLAKE3 preimage relation, proof-bundle IO, CLI, examples, and benchmarks.
- **[crates/veil-f128](crates/veil-f128)** - Native `GF(2^128)` VEIL
  commitment and constraint backend.
- **[examples](examples)** - Full-ZK examples of FLOCK's protocol layers using
  the VEIL context.
- **[tools/formal-proof](tools/formal-proof)** - Cargo wrapper for building the
  Lean formalization and auditing theorem assumptions.

## Performance

The table compares FLOCK and single-column **full-ZK Standard** at a common
**100-bit composed interactive soundness floor**. The benchmark tunes FLOCK's
query and grinding counts while retaining its registered recursion layouts and
rate 1/2. ZK uses the same outer code length relative to the original witness,
except at 256 slots where finite-length soundness requires rate 1/4. Its extra
padding is included in the soundness calculation. FLOCK's normal default is
unchanged. The actual numerical bounds are 100.20–100.48 bits for FLOCK and
100.71–101.27 bits for ZK. The benchmark checks both bounds before measuring.

| Hashes | FLOCK prove | ZK prove | FLOCK verify | ZK verify | FLOCK size | ZK size | Size overhead | Proving ratio |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 4.875 ms | 10.575 ms | 14.000 ms | 9.271 ms | 169,257 B | 289,096 B | 70.8% | 2.17× |
| 128 | 5.383 ms | 10.661 ms | 14.110 ms | 9.282 ms | 301,513 B | 289,256 B | -4.1% | 1.98× |
| 256 | 6.799 ms | 10.843 ms | 13.800 ms | 9.317 ms | 323,953 B | 289,096 B | -10.8% | 1.59× |
| 512 | 7.794 ms | 10.919 ms | 14.155 ms | 9.539 ms | 331,545 B | 383,000 B | 15.5% | 1.40× |
| 1,024 | 10.407 ms | 14.720 ms | 15.043 ms | 10.106 ms | 342,585 B | 395,552 B | 15.5% | 1.41× |
| 2,048 | 16.196 ms | 20.786 ms | 15.423 ms | 11.169 ms | 373,889 B | 405,824 B | 8.5% | 1.28× |
| 4,096 | 27.108 ms | 32.334 ms | 17.229 ms | 13.453 ms | 389,889 B | 421,448 B | 8.1% | 1.19× |

Measured on September 11, 2026, on an Apple M2 Pro with 16 GiB RAM, using
Rust 1.98.0, a release build with `target-cpu=native`, and eight Rayon threads.
Each value is the median of 25 samples after one untimed warm-up per protocol
and batch size. The benchmark alternates which prover runs first, and verifies
every proof. Setup construction, message and digest generation, and
serialization are excluded; the public prove APIs' witness checks are included.
A separate 75-sample run gave 28.679 ms for FLOCK and 34.334 ms for ZK at
4,096 hashes. Those two runs measured 19.3% and 19.7% proving overhead. Earlier
paired runs ranged up to 26%; the machine was also running other work.

Sizes are bincode-serialized proof objects, excluding the separately returned
witness commitment, public digests, and bundle framing. Size overhead is
`(ZK size / FLOCK size - 1) * 100%`; the proving ratio is
`ZK prove time / FLOCK prove time`. Fresh ZK randomness causes small size
variations: the table's 4,096-hash proofs ranged from 419,464 to 423,048 B.

ZK pads batches below 256 hashes to 256 slots. The 64- and 128-hash FLOCK
baselines use smaller circuit shapes and derived schedules below the registry
floor; the benchmark reduces interleaving when necessary to fit distinct
queries. Those rows therefore differ in circuit geometry despite sharing the
soundness floor.

These measurements use the single-column construction. Its Lean update is
pending; the checked-in salted-Merkle/Fiat–Shamir ZK theorem covers the legacy
Secure construction. See the [formal proof scope](lean/README.md).

Reproduce the table with:

```sh
RAYON_NUM_THREADS=8 cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 25
```

## Quickstart

Run commands from the workspace root. The `veiled_flock` binary is gated behind
the `veil` feature.

```sh
cargo run --locked --release -p flock-prover --features veil \
  --bin veiled_flock -- demo
```

To prove and verify a generated sample batch, write one or more concatenated
64-byte messages to a file. This example creates two zero-valued messages:

```sh
dd if=/dev/zero of=messages.bin bs=64 count=2

cargo run --locked --release -p flock-prover --features veil \
  --bin veiled_flock -- \
  prove --message messages.bin --out proof.bin

cargo run --locked --release -p flock-prover --features veil \
  --bin veiled_flock -- \
  verify --in proof.bin
```

`messages.bin` must contain one or more concatenated 64-byte messages. The
proof bundle includes the ordered public digests. Full-ZK batches support up
to 4096 messages and use registered 256/512/1024/2048/4096-slot circuit shapes.

## Examples

Use release builds for the examples. Debug builds are useful for compiler
checks, but the timing output is not meaningful.

The `veil-examples` package contains full zero-knowledge examples for FLOCK's
own protocol layers:

```sh
cargo run --locked --release -p veil-examples --example mle_eval_zk
cargo run --locked --release -p veil-examples --example zerocheck_zk
cargo run --locked --release -p veil-examples --example root_zk
```

- **`mle_eval_zk`** - proves an MLE evaluation against a hiding PCS
  commitment.
- **`zerocheck_zk`** - proves that committed bit vectors satisfy
  `a AND b = c` through FLOCK zerocheck plus ring-switched openings.
- **`root_zk`** - proves knowledge of a selected root of a public polynomial as
  a Boolean R1CS with zerocheck, lincheck, and ring-switched openings.

See [examples/README.md](examples/README.md) for the statements, layers, oracle
counts, and masking scope of those examples.

The `flock-prover` crate also has benchmark and development examples:

| Example | Command | Notes |
|---|---|---|
| `preimage_scaling` | `cargo run --locked --release -p flock-prover --features veil --example preimage_scaling -- 5` | Reproduces the canonical ZK versus non-ZK performance table with five samples. |
| `mle_eval_bench` | `cargo run --locked --release -p flock-prover --example mle_eval_bench` | Compares naive and Remark 1.7 MLE folding. |
| `chain_bench` | `cargo run --locked --release -p flock-prover --features unsound-challenger --example chain_bench` | Isolates hash-chain shift sumcheck cost with the insecure test challenger. |
| `keccak_mid_density` | `cargo run --locked --release -p flock-prover --example keccak_mid_density` | Reports midpoint Keccak R1CS row density. |
| `linear_sha_verifier` | `cargo run --locked --release -p flock-prover --example linear_sha_verifier` | Compares the fused SHA-256 verifier walk with sparse matrix folding. |
| `keccak_chain_bench` | `cargo run --locked --release -p flock-prover --example keccak_chain_bench` | Runs full Keccak chain proofs and can take many minutes and gigabytes of memory. |
| `gen_ligerito_configs` | `cargo run --locked --release -p flock-prover --example gen_ligerito_configs` | Regenerates embedded Ligerito configs; review the generated diff before committing. |

The native hash-chain baselines are Cargo benchmarks:

```sh
cargo bench --locked -p flock-prover --features veil --bench blake3_native_chain
cargo bench --locked -p flock-prover --features veil --bench keccak_native_chain
```

## Building and testing

```sh
make test
make formal-proof
```

`make test` runs the locked release workspace checks, formatting check, clippy,
the x86 clippy pass, and the BLAKE3 preimage smoke tests. `make formal-proof`
builds the Lean proof libraries and audits the main theorem chain for
non-standard axioms. See [SECURITY.md](docs/SECURITY.md) for the precise
theorem and implementation scope.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)
- [Full-ZK examples of FLOCK's protocols](examples/README.md)

## Papers and credits

- [Flock: Fast Proving for Batch Boolean Computations](https://arxiv.org/pdf/2607.27491)
  by Benedikt Bünz, Ron D. Rothblum, and William Wang.
- [VEIL: Lightweight Zero-Knowledge for Hash-Based Multilinear Proof Systems](https://eprint.iacr.org/2026/683.pdf)
  by Rahul Dalal, Tamir Hemo, Eugene Rabinovich, and Ron Rothblum.

## License

Apache-2.0 or MIT.

## Status

Unaudited. The Lean update for the single-column Standard construction is
pending. The checked-in ZK theorem covers the legacy Secure construction.
See the [formal proof scope](lean/README.md).

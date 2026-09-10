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

| Hashes | FLOCK prove | FLOCK verify | FLOCK size | Full-ZK prove | Full-ZK verify | Full-ZK size | Size overhead vs. non-ZK FLOCK |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 4.944 ms | 13.123 ms | 274,609 B | 19.350 ms | 11.454 ms | 801,705 B | 191.9% |
| 128 | 5.140 ms | 13.544 ms | 283,537 B | 18.987 ms | 11.338 ms | 801,865 B | 182.8% |
| 256 | 6.447 ms | 13.467 ms | 377,697 B | 19.485 ms | 11.534 ms | 802,185 B | 112.4% |
| 512 | 7.961 ms | 14.042 ms | 385,081 B | 24.723 ms | 12.499 ms | 811,281 B | 110.7% |
| 1,024 | 10.381 ms | 14.460 ms | 398,657 B | 32.597 ms | 11.974 ms | 847,489 B | 112.6% |
| 2,048 | 15.925 ms | 15.033 ms | 433,425 B | 49.119 ms | 13.442 ms | 863,857 B | 99.3% |
| 4,096 | 23.917 ms | 16.476 ms | 451,937 B | 81.780 ms | 15.662 ms | 885,585 B | 96.0% |

Measured on an Apple M2 Pro with 16 GiB RAM, using Rust 1.98.0,
commit `9a369670ba5ad3d9a450b859572760b179085666`, a release build with
`target-cpu=native`, and the benchmark's default thread pool. Each value is
the median of five samples after one untimed warm-up per protocol and batch
size. Every generated proof is verified. Setup construction, message and
digest generation, and serialization are excluded from the timings; the
public prove APIs' witness checks are included.

Sizes are the bincode-serialized proof objects, excluding the separately
returned witness commitment, public digests, and bundle framing. Size overhead
is `(full-ZK size / FLOCK size - 1) * 100%`. Fresh ZK randomness causes small
size variations: the five 4,096-hash proofs ranged from 882,737 to 887,089 B.

Both setups select the Secure profile at rate 1/2 (`log_inv_rate = 1`). The
full-ZK path uses registered PCS configurations and pads batches below 256
hashes to 256 slots. The 64- and 128-hash non-ZK baselines use smaller circuit
shapes with ad hoc PCS schedules below the registry floor, so those rows do
not compare identical circuit geometry or registered security budgets.

The ZK PCS doubles the committed message dimension with `[mask || witness]`
and doubles the initial Merkle leaf width with a same-length blinding vector
`g`. VEIL constraint and ring-linkage proofs add further overhead. These
measurements establish a baseline for future size and proving-time experiments.

Reproduce the benchmark with:

```sh
cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 5
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
| `preimage_scaling` | `cargo run --locked --release -p flock-prover --features veil --example preimage_scaling -- 5` | Reproduces the performance table with five samples. |
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

Experimental and unaudited. The Lean proof covers statistical zero knowledge
for the formal model; production Rust expands an OS seed with BLAKE3 XOF, and
Rust-to-Lean correspondence remains future work.

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

The table compares non-ZK FLOCK using the Secure profile at rate 1/2 with
**full-ZK Standard** at rate 1/8. Standard enforces 100-bit PCS and
composed interactive numerical bounds. The public ZK constructor, CLI, simulator, and
ZK examples select it by default. Non-ZK FLOCK keeps its existing configuration.
These profiles have different soundness budgets, so this comparison does not
isolate the intrinsic cost of ZK. The concrete Lean tables still describe the
legacy Secure ZK configuration; porting them is pending.

| Hashes | FLOCK prove | ZK prove | FLOCK verify | ZK verify | FLOCK size | ZK size | Size overhead | Proving ratio |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 4.515 ms | 20.772 ms | 13.458 ms | 11.880 ms | 274,609 B | 436,001 B | 58.8% | 4.60× |
| 128 | 5.136 ms | 20.039 ms | 13.871 ms | 11.465 ms | 283,537 B | 436,769 B | 54.0% | 3.90× |
| 256 | 6.375 ms | 20.311 ms | 13.940 ms | 11.483 ms | 377,697 B | 435,937 B | 15.4% | 3.19× |
| 512 | 8.143 ms | 26.301 ms | 14.248 ms | 11.712 ms | 385,081 B | 446,929 B | 16.1% | 3.23× |
| 1,024 | 10.836 ms | 37.788 ms | 14.989 ms | 12.455 ms | 398,657 B | 477,585 B | 19.8% | 3.49× |
| 2,048 | 15.554 ms | 63.120 ms | 15.342 ms | 13.122 ms | 433,425 B | 490,569 B | 13.2% | 4.06× |
| 4,096 | 23.842 ms | 106.233 ms | 16.985 ms | 14.940 ms | 451,937 B | 505,633 B | 11.9% | 4.46× |

Measured on an Apple M2 Pro with 16 GiB RAM, using Rust 1.98.0,
implementation commit `fc47c3a18847beb7bfd97d0f7da10159c3d8ca15` (before the
profile rename to `Standard`), a release build with `target-cpu=native`,
and the benchmark's default thread pool. Each value
is the median of five samples after one untimed warm-up per protocol and
batch size. Every generated proof is verified. Setup construction, message
and digest generation, and serialization are excluded from the timings;
the public prove APIs' witness checks are included.

Sizes are bincode-serialized proof objects, excluding the separately returned
witness commitment, public digests, and bundle framing. Size overhead is
`(ZK size / FLOCK size - 1) * 100%`; the proving ratio is
`ZK prove time / FLOCK prove time`. Fresh ZK randomness causes small size
variations: the five 4,096-hash proofs ranged from 503,137 to 505,985 B.

ZK pads batches below 256 hashes to 256 slots. The 64- and 128-hash non-ZK
baselines use smaller circuit shapes with ad hoc PCS schedules below the
registry floor, so those rows also differ in circuit geometry.

Reproduce the table with:

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

Unaudited. The Lean proof covers the legacy Secure parameter model;
porting it to Standard is pending. Production Rust expands an
OS seed with BLAKE3 XOF, and Rust-to-Lean correspondence remains future work.

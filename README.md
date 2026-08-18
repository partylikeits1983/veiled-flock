# zk-FLOCK with VEIL

This repository is an experimental implementation of FLOCK with VEIL to make
FLOCK zero knowledge.

It proves knowledge of one or more 64-byte BLAKE3 preimages without revealing
the preimages. The public statement is the ordered list of BLAKE3 digests.

> This code is experimental, unaudited, and not suitable for production
> secrets.

## Design

The implementation keeps FLOCK's succinct zerocheck, lincheck, and Ligerito
pipeline.

- FLOCK commits to a randomized witness using a hiding Ligerito commitment.
- Zerocheck and lincheck messages are masked over `GF(2^128)`.
- The masks are committed before dependent Fiat--Shamir challenges.
- VEIL proves that the masked FLOCK transcript is valid.
- The VEIL output claims and Ligerito opening refer to the same commitment.

The upstream VEIL code uses a two-adic prime field. This repository implements
the required VEIL dot-product, Hadamard-product, and constraint protocols over
`GF(2^128)` using additive Reed--Solomon codes. See
[`crates/veil-f128`](crates/veil-f128) and
[`succinct_veil.rs`](crates/flock-prover/src/succinct_veil.rs).

## Simulator

The repository includes a programmable-random-oracle simulator. It accepts
public digests, a random seed, and an oracle. It does not accept messages or
preimages.

The test `succinct_veil_public_only_simulator_is_accepted` verifies that the
simulator can produce an accepted proof for arbitrary digest targets. This is
useful implementation evidence, but it is not a formal zero-knowledge proof.
See [the security audit](docs/SECURITY.md) and
[formal verification plan](docs/FORMAL_VERIFICATION.md).

## Benchmark

Batch 256, release build, median of 10 runs. Setup time and public digests are
excluded from the measurements.

| Mode | Prove | Verify | Proof size |
|---|---:|---:|---:|
| FLOCK | 7.59 ms | 13.52 ms | 272,013 bytes |
| zk-FLOCK with VEIL | 11.74 ms | 5.21 ms | 579,999 bytes |

In this run, zk-FLOCK proving was 1.55x slower and its proof was 2.13x larger.
Short batches use the same 256-slot hiding-PCS floor, so their proof size is
also about 580 KB.

Reproduce the benchmark with:

```sh
VEIL_BENCH_BATCH=256 VEIL_BENCH_RUNS=10 \
  cargo bench -p flock-prover --features veil --bench veil_vs_flock
```

## Run

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo
```

To prove and verify a file of concatenated 64-byte messages:

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  prove --message messages.bin --out proof.bin

cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  verify --in proof.bin
```

The proof file contains the public digests, commitment, and proof. It does not
contain the messages or raw witness.

## Documentation

- [Architecture](docs/ARCHITECTURE.md)
- [Security audit](docs/SECURITY.md)
- [Formal verification plan](docs/FORMAL_VERIFICATION.md)
- [Transcript](docs/TRANSCRIPT.md)

## License

Apache-2.0 or MIT.

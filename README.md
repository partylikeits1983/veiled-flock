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

This comparison matches the circuit shape, witness-column count, outer code
length, and recursion layout, with a common **100-bit composed interactive
soundness floor**. Both use 32 witness columns; ZK adds one random column and
query-sized padding. Query counts are calculated separately to include the
extra ZK polynomial dimension. Non-ZK production defaults are unchanged.

| Hashes | FLOCK prove | ZK prove | FLOCK verify | ZK verify | FLOCK size | ZK size | Size overhead | Proving ratio |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 6.018 ms | 9.864 ms | 13.898 ms | 8.600 ms | 152,649 B | 289,288 B | 89.5% | 1.64× |
| 512 | 6.982 ms | 10.609 ms | 14.965 ms | 9.434 ms | 214,841 B | 383,256 B | 78.4% | 1.52× |
| 1,024 | 10.589 ms | 14.637 ms | 14.592 ms | 10.016 ms | 246,513 B | 395,712 B | 60.5% | 1.38× |
| 2,048 | 15.490 ms | 19.133 ms | 15.785 ms | 10.748 ms | 264,865 B | 405,568 B | 53.1% | 1.24× |
| 4,096 | 24.962 ms | 30.330 ms | 17.599 ms | 12.672 ms | 281,145 B | 421,128 B | 49.8% | 1.22× |

Measured September 11, 2026, on an Apple M2 Pro with 16 GiB RAM, Rust 1.98.0,
a release build with `target-cpu=native`, and eight Rayon threads. Values are
medians of 25 samples after one warm-up per protocol and size. Prover order
alternates and every proof is verified. Timings exclude setup, message/digest
generation, and serialization; public prove API witness checks are included.
A separate 75-sample run at 4,096 hashes measured 25.050 ms for FLOCK and
30.235 ms for ZK, or 20.7% proving overhead.

Sizes count serialized proof objects, excluding the separately returned witness
commitment, public digests, and bundle framing. Fresh ZK randomness causes small
size differences: the 4,096-hash proofs ranged from 419,880 to 423,656 B.
Size overhead is `(ZK size / FLOCK size - 1) * 100%`; proving ratio is
`ZK prove time / FLOCK prove time`.

The earlier comparison retained FLOCK's 64-column layout while ZK used 32
witness columns, giving different costs for the initial openings. At 256 hashes,
ZK also used a larger outer encoded domain. Those choices could make the ZK
proof smaller overall; they do not isolate the cost of adding ZK. With matched
layouts, the current 4,096-hash proof-size overhead is about **50%**, above the
10–20% target.

Batches below 256 hashes are omitted here because ZK pads them to 256 slots
while non-ZK FLOCK uses smaller circuit shapes. The `stock` comparison retains
FLOCK's existing layouts and includes those smaller batches; it still retunes
soundness to the same floor.

```sh
RAYON_NUM_THREADS=8 cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 25 all matched
# Compare against FLOCK's existing layouts instead:
RAYON_NUM_THREADS=8 cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 25 all stock
```

The Lean update for the single-column construction is pending; the checked-in
salted-Merkle/Fiat–Shamir ZK theorem covers the legacy Secure construction.
See the [formal proof scope](lean/README.md).

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

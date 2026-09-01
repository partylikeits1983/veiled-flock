# zk-FLOCK

> **Warning:** This is draft work. No code review has been performed. Use at
> your own risk. Do not use this repository for production secrets.

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
| 64 | 5.402 ms | 12.705 ms | 274,676 B | 21.898 ms | 15.549 ms | 803,764 B | 192.6% |
| 128 | 6.086 ms | 13.121 ms | 283,604 B | 21.832 ms | 15.189 ms | 805,556 B | 184.0% |
| 256 | 7.685 ms | 13.192 ms | 377,764 B | 21.804 ms | 14.940 ms | 809,364 B | 114.3% |
| 512 | 10.003 ms | 13.578 ms | 385,148 B | 26.817 ms | 16.263 ms | 828,412 B | 115.1% |
| 1,024 | 10.280 ms | 14.698 ms | 398,724 B | 39.577 ms | 16.389 ms | 880,364 B | 120.8% |
| 2,048 | 14.888 ms | 14.599 ms | 433,492 B | 78.313 ms | 17.229 ms | 929,468 B | 114.4% |
| 4,096 | 23.771 ms | 17.193 ms | 452,004 B | 134.793 ms | 19.671 ms | 1,017,308 B | 125.1% |

Measured on an AMD Ryzen 7 7840HS.

The [VEIL paper](https://eprint.iacr.org/2026/683) reports 12% proof-size
overhead for a much larger `2^29`-element trace over a 31-bit prime field. These
benchmarks use smaller instances over `GF(2^128)`, so the results are not
directly comparable. Wider field elements increase serialized size, but they
are not the only source of overhead. The ZK PCS doubles the committed message
dimension with `[mask || witness]` and doubles the initial Merkle leaf width
with a same-length blinding vector `g`. The smaller instances also provide less
opportunity to amortize these costs. Separate VEIL constraint and ring-linkage
proofs, plus the public digest list, add more bytes.

Reproduce the benchmark with:

```sh
make preimage-scaling
```

## Quickstart

Run commands from the workspace root. The Makefile targets wrap the locked
Cargo invocation and the `veil` feature required by the `veiled_flock` binary.

```sh
make quickstart-demo
```

To prove and verify a generated sample batch:

```sh
make quickstart-roundtrip
```

`make quickstart-roundtrip` writes two zero-valued 64-byte messages to
`messages.bin`, writes the proof bundle to `proof.bin`, and verifies it. Use
`QUICKSTART_MESSAGES`, `QUICKSTART_PROOF`, and `QUICKSTART_COUNT` to override
those defaults.

For an existing message file:

```sh
make quickstart-prove QUICKSTART_MESSAGES=messages.bin QUICKSTART_PROOF=proof.bin
make quickstart-verify QUICKSTART_PROOF=proof.bin
```

`QUICKSTART_MESSAGES` must point to one or more concatenated 64-byte messages.
The proof bundle includes the ordered public digests. Full-ZK batches support
up to 4096 messages and use registered 256/512/1024/2048/4096-slot circuit
shapes.

## Examples

Use release builds for the examples. Debug builds are useful for compiler
checks, but the timing output is not meaningful. The Makefile targets below
wrap the required Cargo package, feature, and example flags.

To run the regular non-mutating examples:

```sh
make examples
```

The `veil-examples` package contains full zero-knowledge examples for FLOCK's
own protocol layers:

```sh
make veil-examples
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

| Target | Example | Notes |
|---|---|---|
| `make preimage-scaling` | `preimage_scaling` | Reproduces the performance table with `EXAMPLE_SAMPLES ?= 5`. |
| `make mle-eval-bench` | `mle_eval_bench` | Compares naive and Remark 1.7 MLE folding. |
| `make chain-bench` | `chain_bench` | Isolates hash-chain shift sumcheck cost with the insecure test challenger. |
| `make keccak-mid-density` | `keccak_mid_density` | Reports midpoint Keccak R1CS row density. |
| `make linear-sha-verifier` | `linear_sha_verifier` | Compares the fused SHA-256 verifier walk with sparse matrix folding. |
| `make keccak-chain-bench` | `keccak_chain_bench` | Runs full Keccak chain proofs and can take many minutes and gigabytes of memory. |
| `make gen-ligerito-configs` | `gen_ligerito_configs` | Regenerates embedded Ligerito configs; review the generated diff before committing. |

The native hash-chain baselines are Cargo benchmarks:

```sh
make native-hash-benches
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

## License

Apache-2.0 or MIT.

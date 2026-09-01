# zk-FLOCK

VEIL-FLOCK is a succinct zero-knowledge FLOCK composition for ordered batches
of 64-byte BLAKE3 preimages.

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Draft status

This is draft work. No code review has been performed. Use at your own risk.
Do not use this repository for production secrets.

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

To prove and verify your own batch, write one or more concatenated 64-byte
messages to a file. This example creates two zero-valued messages:

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

## Running examples

Use release builds for the examples. Debug builds are useful for compiler
checks, but the timing output is not meaningful.

The `veil-examples` package contains full zero-knowledge examples for FLOCK's
own protocol layers:

```sh
cargo run --locked --release -p veil-examples --example mle_eval_zk
cargo run --locked --release -p veil-examples --example zerocheck_zk
cargo run --locked --release -p veil-examples --example root_zk
```

See [examples/README.md](examples/README.md) for the statements, layers, oracle
counts, and masking scope of those examples.

The `flock-prover` crate also has benchmark and development examples:

| Example | Command | Notes |
|---|---|---|
| `preimage_scaling` | `cargo run --locked --release -p flock-prover --features veil --example preimage_scaling -- 5` | Reproduces the performance table with five samples. |
| `mle_eval_bench` | `cargo run --locked --release -p flock-prover --example mle_eval_bench` | Compares naive and Remark 1.7 MLE folding. |
| `chain_bench` | `cargo run --locked --release -p flock-prover --features unsound-challenger --example chain_bench` | Isolates hash-chain shift sumcheck cost with the insecure test challenger. |
| `keccak_chain_bench` | `cargo run --locked --release -p flock-prover --example keccak_chain_bench` | Runs full Keccak chain proofs and can take many minutes and gigabytes of memory. |
| `keccak_mid_density` | `cargo run --locked --release -p flock-prover --example keccak_mid_density` | Reports midpoint Keccak R1CS row density. |
| `linear_sha_verifier` | `cargo run --locked --release -p flock-prover --example linear_sha_verifier` | Compares the fused SHA-256 verifier walk with sparse matrix folding. |
| `gen_ligerito_configs` | `cargo run --locked --release -p flock-prover --example gen_ligerito_configs` | Regenerates embedded Ligerito configs; review the generated diff before committing. |

The native hash-chain baselines are Cargo benchmarks:

```sh
cargo bench --locked -p flock-prover --features veil --bench blake3_native_chain
cargo bench --locked -p flock-prover --features veil --bench keccak_native_chain
```

## Verification

```sh
make test
make formal-proof
```

`make formal-proof` builds the Lean proof libraries and audits the main theorem
chain for non-standard axioms. See [SECURITY.md](docs/SECURITY.md) for the
precise theorem and implementation scope.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)
- [Full-ZK examples of FLOCK's protocols](examples/README.md)

## License

Apache-2.0 or MIT.

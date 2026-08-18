# zk-FLOCK

Experimental integration of VEIL with FLOCK to add zero knowledge.

The implemented relation proves knowledge of 64-byte BLAKE3 preimages for a
public list of digests. Preimages and FLOCK witness wires are not included in
the proof.

This code is unaudited and not suitable for production secrets.

## Benchmark

Batch 256, release build, median of 10 runs:

| Mode | Prove | Verify | Proof size |
|---|---:|---:|---:|
| FLOCK | 7.59 ms | 13.52 ms | 272,013 bytes |
| zk-FLOCK with VEIL | 11.74 ms | 5.21 ms | 579,999 bytes |

```sh
VEIL_BENCH_BATCH=256 VEIL_BENCH_RUNS=10 \
  cargo bench -p flock-prover --features veil --bench veil_vs_flock
```

## Usage

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo

cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  prove --message messages.bin --out proof.bin

cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  verify --in proof.bin
```

`messages.bin` must contain one or more concatenated 64-byte messages.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Security status](docs/SECURITY.md)
- [Formal verification plan](docs/FORMAL_VERIFICATION.md)

## License

Apache-2.0 or MIT.

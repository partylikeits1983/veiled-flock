# zk-FLOCK

Experimental succinct VEIL wrapper for FLOCK.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

The implementation has completeness, mutation, serialization, and simulator
tests. It does not have end-to-end zero-knowledge, soundness, or knowledge
proofs. It is unaudited and unsuitable for production secrets. See
[SECURITY.md](docs/SECURITY.md).

## Usage

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo
```

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  prove --message messages.bin --out proof.bin

cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  verify --in proof.bin
```

`messages.bin` must contain one or more concatenated 64-byte messages. The
proof bundle includes the ordered public digests.

## Benchmarks

Raw hash-throughput micro-benches:

```sh
cargo bench -p flock-prover --bench blake3_native_chain
cargo bench -p flock-prover --bench keccak_native_chain
```

End-to-end proving benchmarks (full prove + verify cycles, both veil-f128
backends and the native chain prover) live in [`benches/`](benches/README.md):

```sh
cargo bench -p blake3-bench
cargo bench -p keccak-bench
```

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)

## License

Apache-2.0 or MIT.

# zk-FLOCK

Succinct end-to-end zero-knowledge VEIL composition for FLOCK.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

The implemented claim is multi-theorem zero knowledge in the classical
programmable random-oracle model, plus completeness and concrete soundness for
the pinned 64-byte BLAKE3-preimage relation. It is not a claim that concrete
SHA-256 is a random oracle, does not cover quantum random-oracle queries, and
does not claim argument-of-knowledge extraction. The code remains unaudited;
see [SECURITY.md](docs/SECURITY.md) for the exact theorem boundary.

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

```sh
cargo bench -p flock-prover --bench blake3_native_chain
cargo bench -p flock-prover --bench keccak_native_chain
```

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)

## License

Apache-2.0 or MIT.

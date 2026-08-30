# zk-FLOCK

Succinct VEIL composition for making FLOCK zero knowledge.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

The implementation targets multi-theorem zero knowledge in the classical
programmable random-oracle model, plus completeness and concrete soundness for
the pinned 64-byte BLAKE3-preimage relation. The end-to-end composition is
under active audit and formalization and must not yet be treated as an audited
zero-knowledge implementation. It is not a claim that concrete SHA-256 is a
random oracle, does not cover quantum random-oracle queries, and does not claim
argument-of-knowledge extraction. See [SECURITY.md](docs/SECURITY.md) for the
exact theorem boundary.

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
proof bundle includes the ordered public digests. Full-ZK batches support up
to 2048 messages and use registered 256/512/1024/2048-slot circuit shapes.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)
- [Full-ZK examples of FLOCK's protocols](examples/README.md)

## License

Apache-2.0 or MIT.

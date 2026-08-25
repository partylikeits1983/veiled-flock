# VEIL + FLOCK

Succinct VEIL wrapper for FLOCK.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

VEIL covers the masked zerocheck and lincheck verifier equations. The witness
commitment and opening, together with the explicit AB/C evaluation claims,
use a hiding PCS and randomized witness rows. The implementation has
completeness, mutation, serialization, algebraic-invariant, and simulator
tests. It does not have end-to-end zero-knowledge, soundness, or knowledge
proofs and is unsuitable for production secrets. See
[SECURITY.md](docs/SECURITY.md) for the component audit and remaining proof
obligations.

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

# zk-FLOCK

Experimental succinct VEIL wrapper for FLOCK, with a separate Lean
formalization of the production protocol model.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

The Lean development proves statistical zero knowledge for the formal
production protocol model. The main theorem is
`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126` in
`lean/VeiledFlock/Production/Security/FormalZK.lean`, with concrete distance
bound `< 2^-126` in the finite classical programmable-random-oracle model.

That theorem is about the formal model. The Rust implementation remains
experimental and unaudited, and this repository does not include a full
mechanized Rust-to-Lean correspondence proof, concrete SHA-256-as-random-oracle
theorem, QROM theorem, argument-of-knowledge extraction theorem, or
side-channel audit. See [SECURITY.md](docs/SECURITY.md).

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

## Lean Verification

```sh
cd lean
lake build VeiledFlock
cd ..
scripts/lean-axioms.sh
```

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)

## License

Apache-2.0 or MIT.

# zk-FLOCK

VEIL wrapper for FLOCK, with provable zero knowledge via a Lean
formalization of the production protocol model.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

The Lean development proves that the VEIL-FLOCK protocol is statistically zero
knowledge in the formal production protocol model: every valid public
statement and witness satisfying the pinned relation has a real adversary view
within `< 2^-126` statistical distance of a witness-free simulated view. The
main theorem is
`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126` in
`lean/VeiledFlock/Production/Security/FormalZK.lean`, with concrete distance
bound `< 2^-126` in the finite classical programmable-random-oracle model.

This theorem is about the formal model. The Rust implementation has been kept
aligned with the Lean logic as closely as possible, but this repository does
not yet include a mechanized Rust-to-Lean correspondence proof for every
executable code path. See [SECURITY.md](docs/SECURITY.md).

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

A first build on a cold Lake/Mathlib cache can take 30+ minutes on an M-series
MacBook. Incremental rebuilds are usually much faster.

```sh
make formal-proof
```

This downloads the pinned Mathlib cache, builds the Lean proof with a progress
bar, and audits the resulting theorems for non-standard axioms.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)

## License

Apache-2.0 or MIT.

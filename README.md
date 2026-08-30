# zk-FLOCK

VEIL-FLOCK is a succinct zero-knowledge FLOCK composition for batched
64-byte BLAKE3 preimage statements.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

This PR contains the full-ZK Rust path, canonical proof bundle/CLI, and a
machine-checked Lean proof endpoint for the formal protocol model. The main
Lean theorem is
`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126` in
`lean/VeiledFlock/Production/Security/FormalZK.lean`; it proves statistical
zero knowledge with concrete distance bound `< 2^-126` in the finite classical
programmable-random-oracle model, under the reviewed query and serialization
envelope. The same Lean layer also records a witness-free simulator efficiency
certificate.

That theorem is about the formal model. The PR does not claim an independent
audit of the Rust implementation, a full mechanized Rust-to-Lean
correspondence proof for every code path, concrete SHA-256-as-random-oracle
security, quantum random-oracle security, argument-of-knowledge extraction, or
side-channel privacy. See [SECURITY.md](docs/SECURITY.md) for the theorem
boundary and operational caveats.

## What this PR adds

- Full-ZK BLAKE3-preimage proving, verifying, and witness-free simulation via
  `Blake3PreimageZkSetup::{new, prove, verify, simulate}`.
- Registered 256/512/1024/2048-slot circuit shapes for batches of 1-2048
  concatenated 64-byte messages.
- Fresh OS-sampled prover/simulator coins, typed transcript framing, tree
  nonces, leaf salts, and the reviewed random-oracle path.
- A reorganized `lean/VeiledFlock` development grouped into `Core`, `Algebra`,
  `Oracle`, `Concrete`, and `Production/*` subdirectories.

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

## Verification

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo
```

```sh
cd lean
lake build VeiledFlock
cd ..
scripts/lean-axioms.sh
```

`scripts/zk-certify.sh` runs the full executable certificate suite: Rust tests,
Lean build, axiom audit, formal-ZK theorem audit, and random-oracle surface
checks.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)

## License

Apache-2.0 or MIT.

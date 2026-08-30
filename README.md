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

The implementation contains the full-ZK Rust path, canonical proof bundle/CLI,
and witness-free simulator. It targets statistical zero knowledge in the
finite classical programmable-random-oracle model. The Lean theorem for the
formal protocol model is maintained separately from this Rust implementation.

This is not an independent audit, a mechanized Rust-to-Lean correspondence
proof, concrete SHA-256-as-random-oracle security, quantum random-oracle
security, argument-of-knowledge extraction, or side-channel privacy. See
[SECURITY.md](docs/SECURITY.md) for the exact boundary and operational
caveats.

## Supported Surface

- Full-ZK BLAKE3-preimage proving, verifying, and witness-free simulation via
  `Blake3PreimageZkSetup::{new, prove, verify, simulate}`.
- Registered 256/512/1024/2048/4096-slot circuit shapes for batches of 1-4096
  concatenated 64-byte messages.
- Fresh OS-sampled prover/simulator coins, typed transcript framing, tree
  nonces, leaf salts, and the reviewed random-oracle path.

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
to 4096 messages and use registered 256/512/1024/2048/4096-slot circuit shapes.

## Verification

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo
```

`scripts/zk-certify.sh` runs the executable Rust certificate suite and
random-oracle surface checks.

To build and audit the Lean formalization:

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

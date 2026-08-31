# zk-FLOCK

VEIL-FLOCK is a succinct zero-knowledge FLOCK composition for batched
64-byte BLAKE3 preimage statements, with a Lean proof of statistical zero
knowledge for its formal production protocol model.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

The Lean development proves that the formal production protocol model is
statistically zero knowledge: every valid statement and witness has a real
adaptive adversary view within `< 2^-126` statistical distance of a
witness-free simulated view. The main endpoint is
`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126`.

The Rust implementation is kept aligned with that model, but the repository
does not yet contain a mechanized Rust-to-Lean correspondence proof for every
executable path. This is also not an independent audit, a concrete
SHA-256-as-random-oracle theorem, a QROM theorem, an argument-of-knowledge
theorem, or a side-channel audit. See [SECURITY.md](docs/SECURITY.md).

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

### Lean formal proof

A cold Lake/Mathlib build can take 30 minutes or more. Incremental builds are
usually much faster.

```sh
make formal-proof
```

This downloads the pinned Mathlib cache, builds all Lean proof libraries with
a progress bar, and audits the main theorem chain for non-standard axioms.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)
- [Full-ZK examples of FLOCK's protocols](examples/README.md)

## License

Apache-2.0 or MIT.

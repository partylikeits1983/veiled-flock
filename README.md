# VEIL + FLOCK

Experimental succinct VEIL wrapper for FLOCK. This is a research prototype,
not a production-ready zero-knowledge system.

The prover shows knowledge of one 64-byte BLAKE3 preimage for each public
digest in an ordered batch:

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Security status

VEIL covers the masked zerocheck and lincheck verifier equations. The witness
commitment/opening and the explicit AB/C evaluation claims still require the
active hiding-PCS and witness-randomizer mechanisms. The implementation has
completeness, mutation, serialization, algebraic-invariant, and simulator
tests, but it does not yet have end-to-end zero-knowledge, soundness, or
knowledge proofs. It is unaudited and unsuitable for production secrets. See
[SECURITY.md](docs/SECURITY.md) for the component audit and release gates.

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

The comparison benchmark proves the same batch-256 relation in ordinary FLOCK
and VEIL+FLOCK, then emits median/MAD timings and a JSON proof-size breakdown:

```sh
VEIL_BENCH_BATCH=256 VEIL_BENCH_RUNS=10 \
  cargo bench --locked -p flock-prover --features veil --bench veil_vs_flock
```

For commitment-plus-proof serialization (excluding the public digest list and
setup), the current sample measured ordinary FLOCK at 271,814 bytes and
VEIL+FLOCK at 580,526 bytes. Roughly 76% of the increase is the hiding witness
PCS and 24% is the inner VEIL proof. See the security audit for the exact
component table and commitment geometry.

Native hash-chain microbenchmarks remain available:

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

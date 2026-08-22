# zk-FLOCK

Research implementation of a succinct VEIL wrapper for FLOCK.

The active relation is:

```text
public:   ordered BLAKE3 digests y[0..b]
private:  exactly 64-byte messages x[0..b]
claim:    BLAKE3(x[i]) = y[i] for every i
```

One proof covers the whole batch. The serialized bundle contains the public
digests, commitments, masked protocol messages, openings, and a VEIL proof; it
does not contain the messages or the raw FLOCK witness. Batch size, order,
padded circuit shape, proof length, timing, and memory behavior remain public.

## Current security status

This is a real protocol implementation, not a feature-name wrapper around
ordinary FLOCK. The active prover commits to a randomized witness, masks each
exposed zerocheck and lincheck field element, and uses the native `veil-f128`
compiler to prove that the hidden transcript satisfies a shifted FLOCK
verifier circuit. The verifier checks that circuit, the hiding PCS opening,
and the verifier-derived public digest claim.

It is nevertheless **not yet justified as a zero-knowledge argument**. The
repository has executable completeness, mutation, and public-input-only
simulator tests, but no end-to-end proof that the real and simulated views have
the same distribution. The additive-code lemmas, AB/C output-claim masking,
hiding Ligerito composition, transcript fork, and classical-ROM composition
still have open proof obligations. The current review also found transcript
and commitment-framing gaps that must be resolved before a production claim.

Consequently:

- it is reasonable to experiment with candidate batch preimage arguments;
- absence of raw preimages from the bundle is established by its data shape;
- cryptographic zero knowledge, a complete argument-of-knowledge theorem, and
  production soundness are not yet established; and
- this code is unaudited and must not protect real secrets.

See the [security scope](docs/SECURITY.md) for the precise findings and
release gates.

## Proof-size comparison

Recorded batch-256 release measurement on an Apple M2 Pro using eight worker
threads. Setup time and public digests are excluded. Times and proof sizes are
medians of 10 runs after one warm-up:

| Mode | Prove | Verify | Proof size |
|---|---:|---:|---:|
| regular FLOCK | 6.26 ms | 13.45 ms | 272,013 bytes |
| succinct zk-FLOCK with VEIL | 12.20 ms | 4.09 ms | 579,999 bytes |

The current zk proof is **not smaller than regular FLOCK**: it is about
2.13 times as large. It is smaller than the historical A1/custom-mask zk path,
whose checked-in batch-256 artifact is about 2.51 MB. The reduction comes from
proving only FLOCK's 242-value algebraic verifier transcript inside VEIL and
reusing one hiding FLOCK opening, instead of proving or separately committing
large parts of the original relation. Regular FLOCK has none of that privacy
machinery and remains smaller.

The measured prover overhead is about 1.95x at batch 256, 2.24x at batch
1,024, and 2.44x at batch 4,096 on this machine. The VEIL paper's reported
~3% prover overhead is for its own large-trace proof of concept and baseline;
it is not a universal bound. This port compares a complete regular FLOCK proof
with a randomized `GF(2^128)` witness, hiding PCS, masked FLOCK transcript, and
native VEIL proof. The growing ratio points to the randomized witness and
hiding PCS as important remaining costs, not only the small VEIL verifier
circuit.

Reproduce the current comparison with:

```sh
VEIL_BENCH_BATCH=256 VEIL_BENCH_RUNS=10 \
  cargo bench -p flock-prover --features veil --bench veil_vs_flock
```

Benchmark numbers are measurements, not security estimates. The older A1
artifact uses a different implementation and benchmark environment, so it is
only an architectural comparison. The table's size is the serialized
commitment and proof; it excludes the ordered public digest list. The CLI
bundle also stores those 32-byte digests plus its header.

## Try the batched preimage proof

The demo proves two private messages, pads the circuit to 256 slots, and
verifies the result:

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo
```

For your own batch, concatenate one or more 64-byte messages:

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  prove --message messages.bin --out proof.bin

cargo run --release -p flock-prover --features veil --bin veiled_flock -- \
  verify --in proof.bin
```

The proof bundle carries the ordered public digest list. Verification means
that the experimental argument accepts for every digest in that list; it does
not reveal the corresponding message bytes. Inputs of any length other than
64 bytes are outside the implemented relation.

The focused end-to-end regression test also mutates the statement and proof
components and requires rejection:

```sh
cargo test -p flock-prover --features veil \
  r1cs_hashes::blake3_preimage::tests::succinct_veil_preimage_roundtrip_and_mutations \
  -- --exact
```

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Design decisions](docs/DECISIONS.md)
- [Upstream source pins](docs/SOURCES.md)

## License

Apache-2.0 or MIT.

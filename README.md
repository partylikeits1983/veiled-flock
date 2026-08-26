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
proof bundle includes the ordered public digests. Full-ZK batches support up
to 2048 messages and use registered 256/512/1024/2048-slot circuit shapes.

## Benchmarks

```sh
cargo bench -p flock-prover --bench blake3_native_chain
cargo bench -p flock-prover --bench keccak_native_chain
cargo run --release -p flock-prover --features veil --example preimage_scaling -- 5
```

The scaling benchmark compares non-ZK FLOCK and full-ZK VEIL-FLOCK on the
same pinned relation using the Secure unique-decoding Ligerito profile. These
release-mode results were measured on an Apple M4 Pro (`arm64`, macOS 26.2,
`rustc 1.98.0`). Each value is the median of five independent proofs after one
untimed warm-up; setup construction, digest generation, and compilation are
excluded.

| Hashes | FLOCK prove | FLOCK verify | FLOCK bundle | Full-ZK prove | Full-ZK verify | Full-ZK bundle | Size overhead |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 4.384 ms | 9.846 ms | 377,764 B | 17.400 ms | 8.567 ms | 809,372 B | 114.3% |
| 512 | 5.368 ms | 9.807 ms | 385,492 B | 23.273 ms | 9.110 ms | 828,732 B | 115.0% |
| 1,024 | 6.439 ms | 10.615 ms | 398,548 B | 37.705 ms | 9.317 ms | 879,484 B | 120.7% |
| 2,048 | 9.806 ms | 10.898 ms | 433,012 B | 61.272 ms | 9.783 ms | 928,812 B | 114.5% |

The canonical full-ZK bundle includes the ordered public digest list, while
the historical non-ZK `R1csProofBundleLigerito` does not. Adding the same
`32 * hashes` public bytes to the non-ZK wire total reduces the normalized
overhead to 109.7%, 106.2%, 103.9%, and 86.3%, respectively. It does not
remove the main approximately twofold proof difference.

### Is proof growth logarithmic?

The PCS proof grows logarithmically in the committed trace length for a fixed
query-security target: each doubling adds Merkle depth and occasionally a
recursive level. The finite-length Secure schedule also changes query counts
and grinding, so growth is stepwise rather than a smooth `a + b log N` curve.
The complete wire bundle is not asymptotically logarithmic because it includes
all `N` public 32-byte digests, an `O(N)` statement term.

Across the measured 8x batch increase, the non-ZK bundle grows 14.6% and the
full-ZK bundle grows 14.8%. After subtracting the linear public digest list,
the full-ZK proof core grows 7.8%.

### Where the proof-size difference comes from

At 256 hashes, the median bundles break down as follows:

| Component | Full-ZK | Comparable non-ZK |
| --- | ---: | ---: |
| Shielded/batched PCS opening | 692,569 B | 373,769 B |
| VEIL constraint proof | 96,184 B | — |
| Masked FLOCK PIOP | 3,912 B | 3,928 B |
| Masked ring linkage | 8,256 B | — |
| Public digest statement | 8,200 B | not bundled |
| Commitment + freshness/nonces | 197 B | 61 B |
| Protocol IDs + file header | 54 B | 6 B |

Of the 431,608-byte canonical difference, 318,800 bytes (73.9%) come from the
shielded PCS and 96,184 bytes (22.3%) from the live VEIL constraint proof.
Ring linkage and the bundled public statement contribute about 8.2 KB each.

The PCS dominates because this FLOCK instantiation has one packed witness
object. ZK mode commits the doubled coefficient message `[mask || witness]`
and adds a same-shape full random blinder `g`. The blinder doubles the initial
Merkle leaf width, while the mask prefix adds a codeword-depth bit. VEIL's one
masking row is amortized in protocols with many committed witness rows; here
it is paired with one packed witness row, so it is not.

The official VEIL result reports 12% proof-size overhead, alongside 3% prover
and 22% verifier overhead, for a `2^29`-element trace over a 31-bit prime
field. Its fixed inner proof and masking row are much more heavily amortized
than in this small `GF(2^128)` FLOCK instance with a 120-bit Secure UDR PCS
schedule. See the [VEIL paper](https://eprint.iacr.org/2026/683) and
[Succinct's announcement](https://blog.succinct.xyz/veil/).

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)

## License

Apache-2.0 or MIT.

# zk-FLOCK

VEIL-FLOCK is a succinct zero-knowledge FLOCK composition for ordered batches
of 64-byte BLAKE3 preimages.

```text
public:   ordered BLAKE3 digests y[0..b)
private:  64-byte messages x[0..b)
claim:    BLAKE3(x[i]) = y[i] for 0 <= i < b
```

## Performance

| Hashes | FLOCK prove | FLOCK verify | FLOCK size | Full-ZK prove | Full-ZK verify | Full-ZK size | Size overhead vs. non-ZK FLOCK |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 5.402 ms | 12.705 ms | 274,676 B | 21.898 ms | 15.549 ms | 803,764 B | 192.6% |
| 128 | 6.086 ms | 13.121 ms | 283,604 B | 21.832 ms | 15.189 ms | 805,556 B | 184.0% |
| 256 | 7.685 ms | 13.192 ms | 377,764 B | 21.804 ms | 14.940 ms | 809,364 B | 114.3% |
| 512 | 10.003 ms | 13.578 ms | 385,148 B | 26.817 ms | 16.263 ms | 828,412 B | 115.1% |
| 1,024 | 10.280 ms | 14.698 ms | 398,724 B | 39.577 ms | 16.389 ms | 880,364 B | 120.8% |
| 2,048 | 14.888 ms | 14.599 ms | 433,492 B | 78.313 ms | 17.229 ms | 929,468 B | 114.4% |
| 4,096 | 23.771 ms | 17.193 ms | 452,004 B | 134.793 ms | 19.671 ms | 1,017,308 B | 125.1% |

Measured on an AMD Ryzen 7 7840HS.

The [VEIL paper](https://eprint.iacr.org/2026/683) reports 12% proof-size
overhead for a `2^29`-element trace over a 31-bit prime base field, so it is not
directly comparable to these small `GF(2^128)` proof files. The 128-versus-31-bit
field width contributes (the issue is element width, not binary versus prime by
itself), but it is not the whole gap. This one-packed-witness PCS has little
opportunity to amortize VEIL's additions: ZK commits `[mask || witness]` and a
same-size blinder `g`, doubling both the message dimension and initial Merkle
leaf width, then adds VEIL constraint and ring-linkage proofs. The serialized
Full-ZK format also carries the public digest list.

Reproduce the benchmark with:

```sh
cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 5
```

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
make test
make formal-proof
```

`make formal-proof` builds the Lean proof libraries and audits the main theorem
chain for non-standard axioms. See [SECURITY.md](docs/SECURITY.md) for the
precise theorem and implementation scope.

## Documentation

- [Protocol specification](SPEC.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Transcript](docs/TRANSCRIPT.md)
- [Security scope](docs/SECURITY.md)
- [Upstream source pins](docs/SOURCES.md)
- [Full-ZK examples of FLOCK's protocols](examples/README.md)

## License

Apache-2.0 or MIT.

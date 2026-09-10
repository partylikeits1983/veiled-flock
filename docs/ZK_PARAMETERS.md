# Canonical 100-bit ZK PCS

The full-ZK prover, verifier, simulator, CLI, and ZK examples use the `Standard`
profile at rate 1/8 (`log_inv_rate = 3`). Non-ZK FLOCK retains its existing
profiles and defaults; the preimage benchmark baseline uses Secure at rate 1/2.

## Run

```sh
cargo run --locked --release -p flock-prover --features veil \
  --example preimage_scaling -- 5
```

Library callers use `Blake3PreimageZkSetup::new(n)`.

## Security scope

Before proving, simulation, or verification, the ZK setup checks the profile,
rate, circuit geometry, query schedule, and computed PCS and composed
interactive soundness bounds. Both numerical bounds must be at least 100 bits.
Prover and verifier load the same registered `m23_standard` through `m27_standard`
configs. Legacy Secure proofs and proofs from the former experimental
transcript domain must be regenerated for this configuration.

The schedule uses unique decoding and includes the hiding L0 combination
error in the additive PCS bound. The simulator and `rom_soundness_bound`
operate on the canonical configuration. These are Rust implementations and
numerical bounds under the repository's soundness analysis, not a mechanized
security certificate for these parameters.

**Lean coverage is pending.** The concrete Lean model still uses the legacy
rate-1/2 Secure tables, positive fold-grinding schedules, and larger L0 query
counts. Its concrete statistical-ZK theorem must not be attributed to Standard.
Porting it requires updating the code domains and handling an empty
fold-grinding schedule in the formal sampling state machine. Rust-to-Lean
correspondence and the seeded-XOF instantiation also remain unproved.

All Standard levels disable query grinding, fold grinding, tapering, and OOD
sampling. The separate L0 blind-combination challenge uses one grinding bit.

| Slots | Committed m | Queries by level | PCS bits | Composed interactive bits |
| ---: | ---: | --- | ---: | ---: |
| 256 | 23 | 121, 114, 111 | 100.078561 | 100.071942 |
| 512 | 24 | 121, 113, 110 | 100.054817 | 100.048305 |
| 1,024 | 25 | 121, 113, 109, 109 | 100.007687 | 100.001384 |
| 2,048 | 26 | 121, 113, 109, 108 | 100.041422 | 100.034970 |
| 4,096 | 27 | 121, 113, 109, 107 | 100.032426 | 100.026015 |

At 256 slots, the earlier 121/114/110 schedule has a PCS bound of 100.004730
bits but a composed bound of 99.998439 bits. One additional final-level query
closes that additive error budget. It is not an extra query required by ZK
hiding.

ZK hiding requires enough independent random mask elements to cover the
opened positions; it does not inherently require increasing the query count
or lowering the code rate. This implementation still uses the existing
`[mask || witness]` layout and full-length blinder. Its hiding-budget check
requires the L0 query count to fit within the mask symbols per lane.
Replacing full-half padding with query-sized blinding is a separate
construction change, not implemented here.

The rate/query tradeoff also exists without ZK. For example, the
[upstream m27 Secure config](https://github.com/succinctlabs/flock/blob/af7fa628fde250b862747521d79f721a501d1131/crates/flock-core/configs/ligerito/m27_secure.toml)
uses 290 initial queries at rate 1/2 and targets 120 bits per round. Under the
same finite-length UDR query formula at 14 message-column bits, 121 queries
provide approximately 50.18 query-error bits at rate 1/2 and 100.43 at rate
1/8. The 121-query schedule cannot simply be moved to rate 1/2 while retaining
that bound.

## Measurements

Results correspond to implementation commit
`fc47c3a18847beb7bfd97d0f7da10159c3d8ca15`, before the profile was renamed
from `Zk100` to `Standard`. The raw CSV retains its original protocol labels;
the rename leaves parameters and binary proof encoding unchanged.

Measured on an Apple M2 Pro with 16 GiB RAM, Rust 1.98.0, release mode,
`target-cpu=native`, and the benchmark's default thread pool. Values are
independent medians of five samples after one warm-up per protocol and size.
Every proof is verified. Setup, message/digest generation, and serialization
are excluded from timings; public API witness checks remain included.

Sizes count bincode-serialized proof objects, excluding commitments, public
digests, and bundle framing. The two protocols prove the same public batch,
but full ZK pads batches below 256 to 256 slots. The 64/128-hash non-ZK
baselines use smaller shapes and ad hoc below-registry PCS schedules. The
Secure baseline and Standard profile have different soundness budgets;
this is an implementation comparison, not a security-matched measurement of
the intrinsic cost of ZK.

| Hashes | FLOCK prove | ZK prove | FLOCK verify | ZK verify | FLOCK size | ZK size | Size overhead | Proving ratio |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 4.515 ms | 20.772 ms | 13.458 ms | 11.880 ms | 274,609 B | 436,001 B | 58.8% | 4.60× |
| 128 | 5.136 ms | 20.039 ms | 13.871 ms | 11.465 ms | 283,537 B | 436,769 B | 54.0% | 3.90× |
| 256 | 6.375 ms | 20.311 ms | 13.940 ms | 11.483 ms | 377,697 B | 435,937 B | 15.4% | 3.19× |
| 512 | 8.143 ms | 26.301 ms | 14.248 ms | 11.712 ms | 385,081 B | 446,929 B | 16.1% | 3.23× |
| 1,024 | 10.836 ms | 37.788 ms | 14.989 ms | 12.455 ms | 398,657 B | 477,585 B | 19.8% | 3.49× |
| 2,048 | 15.554 ms | 63.120 ms | 15.342 ms | 13.122 ms | 433,425 B | 490,569 B | 13.2% | 4.06× |
| 4,096 | 23.842 ms | 106.233 ms | 16.985 ms | 14.940 ms | 451,937 B | 505,633 B | 11.9% | 4.46× |

[Raw samples summary](benchmarks/standard.csv) includes the minimum
and maximum proof sizes. At 4,096 hashes, Standard proof sizes ranged
from 503,137 to 505,985 B. Fresh ZK randomness accounts for that variation.

## Implementation improvement

The salted Merkle builder previously assembled all `salt || leaf` payloads
into one extra allocation before hashing. For the 4,096-slot ZK configuration that
buffer occupied 260 MiB and was populated serially. The new builder gathers
four salted leaves at a time in reusable task-local buffers, keeps native
hashing parallel, and preserves external-oracle query order. Tests compare
every tree node and the complete recorded oracle trace against the old
materialized construction, including SHA padding boundaries and short trees.

In the earlier five-sample experimental runs on the same machine, the
4,096-hash proving median decreased from 133.450 ms to 107.718 ms (19.3%). See the
[before-change results](benchmarks/zk-before-merkle-streaming.csv)
and [after-change results](benchmarks/zk-after-merkle-streaming.csv), measured before
the canonical profile/domain switch.
The hashing inputs and proof format are unchanged. This implementation
improvement is retained by the canonical ZK path.

The remaining rate-1/8 encoding is larger by construction: at 4,096 hashes the
initial codeword occupies 256 MiB, versus 64 MiB for full-ZK Secure and 16 MiB
for non-ZK FLOCK. These results recover approximately 12–20% proof-size
overhead for batches of at least 256 hashes, with substantially higher
proving-time overhead.

The initial codeword expansion relative to non-ZK FLOCK is 16×: 2× for the
full low-half mask, 2× for the blinder lanes, and 4× for the lower code rate.
This increases encoding and hashing work; it is not a phase-time attribution.
Query-sized blinding may reduce that expansion, but requires a separate
construction analysis and implementation. No 10–20% proving-time overhead
is established by these measurements.

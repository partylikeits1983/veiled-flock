# Experimental 100-bit ZK PCS

This opt-in experiment trades a larger Reed–Solomon codeword for smaller
proofs. It uses rate 1/8 (`log_inv_rate = 3`) and a distinct
`ExperimentalZk100` profile. The normal `Blake3PreimageZkSetup::new` constructor
and CLI continue to select the registered rate-1/2 Secure profile.

## Run

```sh
cargo run --locked --release -p flock-prover --features experimental-zk \
  --example preimage_scaling -- 5 --experimental-100
```

Both the Cargo feature and benchmark selector are required. Enabling the
feature alone does not change the default benchmark or CLI. Library callers
can explicitly use `Blake3PreimageZkSetup::experimental_100_bit(n)`.

## Security scope

Before proving or verifying, the experimental setup checks the selected rate,
circuit geometry, query schedule, and computed PCS and composed interactive
soundness bounds. Both numerical bounds must be at least 100 bits. Prover and
verifier derive the same fixed schedule, with an experimental Fiat–Shamir
domain. Secure verifiers reject experimental commitments and proofs, including
proofs whose commitment parameters have been relabeled as Secure.

The schedule uses unique decoding and includes the hiding L0 combination
error in the additive PCS bound. These are Rust numerical calculations under
the repository's soundness analysis. The experimental profile is outside the
registered Lean tables and the production protocol specified in `SPEC.md`.
The simulator and public ROM certificate API return `Uncertified` for it;
this PR does not establish a new end-to-end noninteractive security theorem.
The default Secure floors remain 114-bit PCS / 106-bit composed interactive.

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
`5ee114573ae08f91a5c0f04769171658d78763a2`.

Measured on an Apple M2 Pro with 16 GiB RAM, Rust 1.98.0, release mode,
`target-cpu=native`, and the benchmark's default thread pool. Values are
independent medians of five samples after one warm-up per protocol and size.
Every proof is verified. Setup, message/digest generation, and serialization
are excluded from timings; public API witness checks remain included.

Sizes count bincode-serialized proof objects, excluding commitments, public
digests, and bundle framing. The two protocols prove the same public batch,
but full ZK pads batches below 256 to 256 slots. The 64/128-hash non-ZK
baselines use smaller shapes and ad hoc below-registry PCS schedules. The
Secure baseline and experimental profile have different soundness budgets;
this is an implementation comparison, not a security-matched measurement of
the intrinsic cost of ZK.

| Hashes | FLOCK prove | Experimental prove | FLOCK verify | Experimental verify | FLOCK size | Experimental size | Size overhead | Proving ratio |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 4.660 ms | 21.741 ms | 13.458 ms | 11.858 ms | 274,609 B | 435,873 B | 58.7% | 4.67× |
| 128 | 5.095 ms | 19.893 ms | 13.931 ms | 11.313 ms | 283,537 B | 436,577 B | 54.0% | 3.90× |
| 256 | 6.321 ms | 20.544 ms | 13.588 ms | 11.474 ms | 377,697 B | 435,585 B | 15.3% | 3.25× |
| 512 | 8.178 ms | 27.003 ms | 14.020 ms | 12.208 ms | 385,081 B | 446,801 B | 16.0% | 3.30× |
| 1,024 | 10.556 ms | 38.587 ms | 14.799 ms | 12.324 ms | 398,657 B | 477,585 B | 19.8% | 3.66× |
| 2,048 | 15.631 ms | 63.440 ms | 15.413 ms | 12.857 ms | 433,425 B | 491,657 B | 13.4% | 4.06× |
| 4,096 | 23.728 ms | 107.718 ms | 17.007 ms | 14.797 ms | 451,937 B | 505,121 B | 11.8% | 4.54× |

[Raw samples summary](benchmarks/experimental-zk100.csv) includes the minimum
and maximum proof sizes. At 4,096 hashes, experimental proof sizes ranged
from 504,513 to 507,041 B. Fresh ZK randomness accounts for that variation.

## Implementation improvement

The salted Merkle builder previously assembled all `salt || leaf` payloads
into one extra allocation before hashing. For the 4,096-slot experiment that
buffer occupied 260 MiB and was populated serially. The new builder gathers
four salted leaves at a time in reusable task-local buffers, keeps native
hashing parallel, and preserves external-oracle query order. Tests compare
every tree node and the complete recorded oracle trace against the old
materialized construction, including SHA padding boundaries and short trees.

In the five-sample runs on the same machine, the 4,096-hash experimental
proving median decreased from 133.450 ms to 107.718 ms (19.3%). See the
[before-change results](benchmarks/experimental-zk100-before-merkle-streaming.csv).
The hashing inputs and proof format are unchanged. This implementation
improvement also applies to the default Secure path.

The remaining rate-1/8 encoding is larger by construction: at 4,096 hashes the
initial codeword occupies 256 MiB, versus 64 MiB for full-ZK Secure and 16 MiB
for non-ZK FLOCK. These results recover approximately 12–20% proof-size
overhead for batches of at least 256 hashes, with substantially higher
proving-time overhead.

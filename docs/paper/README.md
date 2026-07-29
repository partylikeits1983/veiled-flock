# Zero Knowledge for Flock's BLAKE3 Prover

The active paper is `zk-flock.tex`. It states the covered relation and
zero-knowledge experiment on the first page, presents the proof as two
distribution-preserving translations, and gives the concrete simulator bound
in one equation. `zk-flock-cheat-sheet.tex` is a separate plain-language
companion covering the protocol algorithms, security models, recurring
symbols, and reader-facing terminology.

## Result

For the registered BLAKE3 circuit-batch and 64-byte fixed-digest profiles, the
result is **computational zero knowledge in the classical programmable-random-
oracle model**, subject to the paper's explicit assumptions. The first profile
has no public digest binding and preserves the benchmark circuit shape. The
second binds 256 secret 64-byte messages to 256 public 32-byte BLAKE3 digests.
At `Q = 2^64` oracle
queries, the dominant ZK term is `720 / 2^128` (118.508 bits) and the explicit
listed union bound is 118.502 bits.

Knowledge is separate. One term caps the available standalone Fiat-Shamir
reduction over `F2^128` at 55.994 bits for `Q = 2^64`, before other
knowledge-error terms are added. The deployment target is
labelled **100-bit conjectured classical knowledge security**; it is not a
100-bit theorem of the paper. This loss is present in the classical reduction;
the paper has no QROM reduction and makes no post-quantum knowledge claim.

At the certified batch size of 256, the current unoptimized ZK prover is 6.78
times slower than the current non-ZK prover on twelve threads and 3.55 times
slower on one thread. Its encoded proof is 9.21 times larger. The paper keeps
these matched measurements separate from the original Flock paper's
large-batch, less-than-250-times-native headline.

## Registered implementation shape

- 256 BLAKE3 instances
- `m = 22`
- Ligerito rate `1/2`, batch log 6
- fixed digest messages are exactly 64 bytes
- proof I/O format 6, transcript schema 5

Every other statement family or parameter set fails closed.

## Implementation identity

- wire protocol: `flock-zk-fv-v3`
- BLAKE3 batch circuit digest:
  `4a398ca2e73d9d1f70611bd6a2a408b0404aabddcf6cf75c29cfa412f72f8423`
- BLAKE3 fixed-digest circuit digest:
  `e71bde2b053b1b697412d2d30c2e2e57f7b5f1822484fcbcc15c89ea202890d5`

The paper uses **Flock-ZK** as the reader-facing protocol name. The wire
identifier remains versioned because it is absorbed into the transcript and
changing it would intentionally make proofs incompatible.

## Evidence map

- PIOP coverage: `docs/artifacts/s2_mask_coverage.json`
- PCS opening functionals: `docs/artifacts/s3_opening_functionals.json`
- PCS conditional entropy: `docs/artifacts/s3_minentropy_table.json`
- simulator hybrid ledger: `docs/artifacts/sim_game_error_table.json`
- knowledge ledger: `docs/artifacts/knowledge-ledger.json`
- Lean scope and exclusions: `lean/README.md`

## Reproduction

```sh
scripts/zk-certify.sh
cargo test --release --workspace --features zk,symbolic
cargo clippy --workspace --all-targets --features zk,symbolic -- -D warnings
cd lean && lake build
ZK_BENCH_THREADS=12 ZK_BENCH_RUNS=10 scripts/zk-benchmark.sh
```

Build the paper with `tectonic zk-flock.tex` and the companion with
`tectonic zk-flock-cheat-sheet.tex`, or use two `pdflatex` passes for each.
The old fixed-digest filename is a compatibility wrapper for the active paper.
Git history records earlier designs and claims.

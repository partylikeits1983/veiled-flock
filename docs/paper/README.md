# Zero Knowledge for Flock's BLAKE3 Prover

The active paper is `zk-flock.tex`. It states the covered relation and
zero-knowledge experiment on the first page, presents the proof as two
distribution-preserving translations, and gives the concrete simulator bound
in one equation. `zk-flock-cheat-sheet.tex` is a separate plain-language
companion covering every acronym, protocol label, recurring symbol, and unit.

## Result

For the registered BLAKE3 batch and 64-byte fixed-digest profiles, the result
is **computational zero knowledge in the classical programmable-random-oracle
model**, subject to the paper's explicit assumptions. At `Q = 2^64` oracle
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

## Certified production shape

- 256 BLAKE3 instances
- `m = 22`
- Ligerito rate `1/2`, batch log 6
- fixed digest messages are exactly 64 bytes
- proof I/O format 6, transcript schema 5

Every other statement family or parameter set fails closed.

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

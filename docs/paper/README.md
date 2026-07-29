# Zero Knowledge for Flock's BLAKE3 Prover (v7.1)

The active paper is `zk-flock.tex`. Version 7.1 is an editorial revision of
the v7 result: it states the covered relation and zero-knowledge experiment on
the first page, presents the proof as two distribution-preserving
translations, and gives the concrete simulator bound in one equation. The
protocol and certified parameter sets are unchanged.

## Result

For the registered BLAKE3 batch and 64-byte fixed-digest profiles, the result
is **computational zero knowledge in the classical programmable-random-oracle
model**, subject to the paper's explicit assumptions. At `Q = 2^64` oracle
queries, the dominant ZK term is `720 / 2^128` (118.508 bits) and the explicit
listed union bound is 118.502 bits.

Knowledge is separate. The available standalone Fiat-Shamir reduction over
`F2^128` gives 55.994 bits at `Q = 2^64`. The shipped deployment target is
labelled **100-bit conjectured classical knowledge security**; it is not a
100-bit theorem of the paper.

## Certified production shape

- 256 BLAKE3 instances
- `m = 22`
- Ligerito rate `1/2`, batch log 6
- fixed digest messages are exactly 64 bytes
- proof I/O version 6, transcript schema 5

Every other statement family or parameter set fails closed.

## Reproduction

```sh
scripts/zk-certify.sh
cargo test --release --workspace --features zk,symbolic
cargo clippy --workspace --all-targets --features zk,symbolic -- -D warnings
cd lean && lake build
```

Build the paper with `tectonic zk-flock.tex` or two `pdflatex` passes. The v6
and v7 change records are retained for history, while the old fixed-digest
filename is a compatibility wrapper for the active paper. Earlier Boolean P/Q
and knowledge-security claims are superseded.

# Making Flock Zero-Knowledge (v7)

The active paper is `zk-flock.tex`. It describes the implemented
field-valued-mask protocol `flock-zk-fv-v3`, the fixed-digest BLAKE3 simulator,
the symbolic PIOP coverage bound, the PCS replacement translator, recording
extractor, and the exact certificate registry.

## Result

For the registered BLAKE3 batch and 64-byte fixed-digest profiles, the result
is **computational zero knowledge in the classical programmable-random-oracle
model**, subject to the paper's explicit assumptions. At `Q = 2^64` oracle
queries, the dominant ZK term is `720 / 2^128` (118.508 bits) and the explicit
listed union bound is 118.502 bits.

Knowledge is separate. The shipped standalone `F2^128` profile has about
55.994 bits of currently provable knowledge security after Fiat-Shamir and is
labelled **100-bit conjectured classical knowledge security**. Its standalone
theorem column remains 55.994 bits at `Q = 2^64`.

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
change record is retained for history, while the old fixed-digest filename is
a compatibility wrapper for v7. Earlier Boolean P/Q and knowledge-security
claims are superseded.

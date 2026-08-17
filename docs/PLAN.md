# zk-FLOCK with VEIL: implementation plan and status

## Current milestone: working end-to-end reference

The repository now has an experimental proof mode that:

- proves a FLOCK pinned BLAKE3-64 Boolean R1CS over `GF(2^128)`;
- binds a public digest and hides the 64-byte preimage;
- uses native characteristic-two VEIL dot-product and Hadamard protocols;
- uses additive-domain base and square Reed--Solomon codes;
- proves Booleanity, R1CS satisfaction, constant pins, and public outputs;
- serializes and verifies through a CLI;
- rejects changed statements and mutated proofs; and
- includes a statement-only programmable-RO simulator accepted by the same
  algebraic verifier.

The working release command is:

```sh
cargo run --release -p flock-prover --features veil --bin veiled_flock -- demo
```

The current proof is a direct proof of FLOCK's R1CS, not yet a VEIL compilation
of FLOCK's succinct zerocheck/lincheck/Ligerito verifier.

## Completed phases

### 1. Fixed statement and native relation

- Reused the `RootHash64` parameter pinning and fixed-digest output layout.
- Added a one-item relation constructor that bypasses only the normal lincheck
  batch floor; the matrices and statement digest remain the FLOCK relation.
- Reused FLOCK's optimized packed generator for `z`, `A z`, and `B z`.

### 2. Characteristic-two VEIL kernel

- Implemented affine additive LCH NTTs.
- Implemented a disjoint-coset RS code, product code, decoding, and reduction.
- Implemented row-Merkle commitments with nonce/role/channel framing.
- Implemented VEIL ZK dot-product and Hadamard protocols.
- Implemented a generic arithmetic constraint compiler for small circuits.

### 3. Memory-linear FLOCK compiler

- Combined R1CS and Booleanity into one Hadamard instance.
- Kept the six VEIL multiplication-padding values private.
- Batched `A^T q`, `B^T q`, padding links, constant pins, and digest equalities
  into one dot proof against the same extended witness.
- Avoided the failed >10 GB generic-matrix expansion.

### 4. Simulator and executable artifact

- Added a straight-line statement-only simulator.
- Programmed only fresh framed Merkle leaf/node points.
- Verified simulated proofs through the shared programmable oracle.
- Confirmed simulated proofs fail under native SHA-256.
- Added a CLI and canonical proof bundle.

## Hardening still required before any production claim

1. Write or cite full proofs for the additive code's MDS projection,
   multiplicative reduction, proximity generator, and concrete soundness.
2. Register a reviewed 100-bit profile; the current memory-oriented profile is
   about 53 bits in its basic proximity term.
3. Audit transcript distribution correspondence against VEIL's paper and Lean
   trusted base, especially the characteristic-two six-value bijection.
4. Add exact small-domain real/simulated distribution enumeration and larger
   witness-pair distinguishing experiments.
5. Replace remaining proof `Vec` decoding with explicit size caps before parsing
   untrusted multi-megabyte bundles.
6. Obtain an independent cryptographic and implementation audit.

## Performance phase: succinct VEIL-FLOCK

The next research implementation should recover FLOCK-like proof size and batch
throughput by compiling the existing succinct verifier rather than the full hash
R1CS.

### A. Typed verifier transcript

Refactor one verifier program so it can verify, emit arithmetic constraints,
count masks, and drive simulation. Classify every zerocheck, lincheck,
ring-switch, and Ligerito value as public, shielded, or exposed.

### B. Partially ZK Ligerito commitment

Apply constrained-interleaved-code padding per CFW26/VEIL, resolve recursive
query accounting, mask the terminal residual, and retain the framed Merkle
simulator. Prove the exact query projection rank for every round.

### C. VEIL transcript compiler

Mask the exposed vector `v` with committed `h`, send `v+h`, and prove the shifted
verifier decision `C(v+h-h)=0` using the native inner system. The direct R1CS
mode remains the correctness oracle.

### D. Benchmarks and profiles

Re-run FLOCK's parameter search with ZK padding costs, benchmark batches from
`2^10` through `2^18`, and compare against both normal FLOCK and this direct
reference proof.

## Release gate

An experimental release is complete when formatting, unit tests, release
prove/verify, release simulation, CLI demo, mutation tests, and documentation all
pass from a clean checkout. Publishing to GitHub is a separate user-approved
mutation.

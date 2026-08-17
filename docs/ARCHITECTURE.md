# Architecture of the working experiment

## What is implemented

The current end-to-end mode proves the fixed-digest statement

```text
public:  BLAKE3 digests y_0, ..., y_(b-1)
private: 64-byte messages x_0, ..., x_(b-1)
claim:   BLAKE3(x_i) = y_i for every i
```

It reuses FLOCK's pinned BLAKE3 Boolean R1CS and optimized witness generator,
but replaces FLOCK's zerocheck/lincheck/Ligerito proof with a direct native
`F128` VEIL proof. This is the memory-linear reference implementation. Compiling
FLOCK's existing succinct verifier transcript through VEIL is the next
performance phase, not something the current artifact claims to have done.

## Proof flow

```text
64-byte messages
      |
FLOCK BLAKE3 generator -> Boolean z, a = A z, b = B z
      |
      +-- Hadamard vector 1: [a | z | r | r+1]
      +-- Hadamard vector 2: [b | z | s | t]
      +-- Hadamard vector 3: [z | z | rs | (r+1)t]
      |                      proves R1CS and z^2 = z
      |
      +-- extended witness: [z | r | s | rs | r+1 | t | (r+1)t]
                             (the six padding values remain private)
      |
VEIL Hadamard proof + VEIL dot-product proof
      |
public digest equalities, constant pin, and A/B transpose links are batched
into one random linear dot claim against the same extended witness commitment
```

The two commitments use an additive-domain Reed--Solomon code over
`GF(2^128)`. Each message has 128 random padding symbols, the verifier opens 128
positions, and Merkle leaves/nodes are domain-separated by channel and a fresh
per-proof nonce.

## Why the specialized compiler exists

FLOCK's substituted BLAKE3 matrices contain roughly 21 million nonzero column
indices. Expanding every index into a generic `(usize, F128)` linear-combination
term exceeded 10 GB for the smallest padded experiment. The specialized compiler
computes `A^T q` and `B^T q` directly from the sparse binary matrices, so proof
memory is linear in the 16,384 witness slots plus the existing matrix storage.

## Native characteristic-two VEIL crate

`crates/veil-f128` contains:

- affine additive LCH NTTs over `F128`;
- the base and square Reed--Solomon codes and reduction map;
- framed row-Merkle commitments;
- VEIL dot-product and Hadamard protocols;
- a generic arithmetic-constraint compiler used by unit tests;
- the specialized FLOCK block-R1CS compiler; and
- the statement-only programmable-RO simulator.

Upstream VEIL's Rust implementation is two-adic/prime-field-specific. This crate
ports the protocol structure to an additive code; it does not pretend the
KoalaBear implementation can be instantiated over a binary field.

## Simulator

The simulator receives the public matrices, public equalities, public statement,
simulator coins, and a programmable random oracle. It never receives `z`, a
message, or a preimage.

It samples random commitment roots, algebraic messages from their VEIL masking
distributions, and queried code rows conditioned on the two verifier equations.
It then programs only fresh framed Merkle leaf/node points so those rows open to
the already sampled roots. The ordinary algebraic verifier accepts through the
external oracle. Native SHA-256 rejects the same transcript, as required: a ROM
simulator is not a real-hash proof forgery.

## User-facing entry points

- `VeiledBlake3Setup::{prove,verify}`: real native-SHA proof path.
- `VeiledBlake3Setup::{simulate,verify_with_oracle}`: executable ROM game.
- `veiled_flock demo`: prove and verify one 64-byte BLAKE3 preimage.
- `veiled_flock prove/verify`: file-based proof bundle workflow.

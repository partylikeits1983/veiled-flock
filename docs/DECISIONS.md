# Decision log

## D001 — Fork the working zk-FLOCK branch

The experiment is a FLOCK fork rather than a thin integration repository. This
keeps the fixed-digest relation, programmable oracle, field implementation, and
witness generator available in one build while the new VEIL path remains behind
the `veil` feature.

## D002 — Use `F128` directly

FLOCK's algebraic values already live in `GF(2^128)`. The new crate uses an
additive-domain Reed--Solomon code because binary extension fields have no
two-adic multiplicative subgroup. Upstream VEIL Rust is reference material, not
a reusable backend for this field.

## D003 — Ship a direct block-R1CS reference before a succinct compiler

The first working mode proves FLOCK's Boolean R1CS directly. It is larger than
FLOCK's normal proof but isolates the new code, Hadamard, dot-product, and
simulation machinery. The optimized follow-up will compile the existing
zerocheck/lincheck/Ligerito verifier transcript.

## D004 — Keep sparse binary matrices native

Generic `F128` linear combinations expanded the BLAKE3 matrices beyond 10 GB.
The specialized compiler computes transpose challenges directly from the sparse
column lists and uses FLOCK's fast generator for `z`, `A z`, and `B z`.

## D005 — Make VEIL's six padding values private

Sending `(r,s,rs,r+1,t,(r+1)t)` in the clear would reveal the unpadded Hadamard
claims after subtraction. They are appended to the privately committed witness;
the Hadamard proof enforces the two products and the dot link enforces
`r + (r+1) = 1`.

## D006 — Use framed programmable-RO simulation

The simulator samples the hidden transcript distribution and programs fresh
Merkle points. It does not force degenerate Fiat--Shamir challenges and does not
claim to forge a native-SHA proof. Real and simulated transcripts use the same
algebraic verifier with different random-oracle backends.

## D007 — Label the rate-1/2 profile experimental

The 128-query rate-1/2 profile is an iteration profile with roughly a 53-bit
basic proximity term. A reviewed 100-bit parameter registration is future work.

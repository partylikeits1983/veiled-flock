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

That follow-up is now complete (D009). The direct compiler remains only as a
correctness and regression oracle.

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

**Status:** the active path frames PCS and VEIL commitments with one nonce and
distinct channels, but programs only Fiat--Shamir challenges.

## D007 — Keep the square code below rate one

The original direct-reference rate-1/2 base profile made the square/product
code rate one and therefore gave it no useful proximity gap. That reference
now uses a rate-1/4 base code and rate-1/2 square code. With 128 queries its
basic square-code unique-decoding term is roughly 53 bits. The succinct path
uses the stronger D012 profile.

## D008 — Exclude degenerate masking challenges

Dot/Hadamard mask coefficients are sampled from `F \ {0}` and the R1CS
six-value batching point from `F \ {0,1}`. This makes the masking maps
invertible for every accepted transcript instead of tolerating a negligible
challenge on which a mask disappears.

**Status:** both active compilers follow this decision.

## D009 — Compile only FLOCK's algebraic verifier transcript

The usable mode keeps one hiding Ligerito opening, masks every observed
zerocheck/lincheck `F128` value, and proves the shifted verifier decision with
a 242-input VEIL circuit at batch 256. This removes four auxiliary mask
commitments from the older custom path and avoids a proof linear in the R1CS.

## D010 — Precommit VEIL masks in two phases

The mask root is absorbed before FLOCK samples any masked-transcript
challenge. The circuit is built only after those challenges exist, then proved
against the same root. This path uses asserted products with linear outputs, so
no challenge-dependent materialized witness variable is needed.

## D011 — Fork the inner proof before the terminal PCS protocol

FLOCK's historical Ligerito prover and verifier accept the same terminal proof
but do not promise identical challenger states afterward. The VEIL inner proof
forks immediately before PCS, after the statement, commitment roots, masked
PIOP, output claims, and digest challenge are bound. PCS and VEIL independently
link to those same roots and claims.

## D012 — Use a 160-query inverse-rate-8 inner profile

The shifted verifier has one real multiplication plus two dummy mask rows. At
inverse rate 8 its square code has rate at most 1/4; 160 queries put the basic
unique-decoding miss term near 108 bits. This remains experimental pending a
complete composed soundness proof.

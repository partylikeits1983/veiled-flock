# Security scope of the experiment

This code is experimental, unaudited, and not production-safe.

## Public and private data

Public data consists of the ordered BLAKE3 digest vector, actual batch size,
padded power-of-two shape, pinned circuit digest, proof profile, and proof nonce.
Private data consists of the 64-byte messages and every FLOCK witness wire.
Circuit shape, proof length, timing, and memory behavior are not hidden.

## Zero-knowledge claim being tested

The construction follows VEIL's bounded-query code masking over `F128`:

- 128 random message symbols cover 128 non-adaptive code queries;
- one random masking codeword hides each revealed linear combination;
- a product-code mask hides the Hadamard reduction;
- two private tautological multiplication triples make the three Hadamard dot
  claims uniform when the batching challenge is neither 0 nor 1; and
- every Merkle tree uses a fresh nonce and disjoint leaf/node/channel framing.

The executable simulator is straight-line in the programmable random-oracle
model and aborts on the negligible bad challenges or a programming collision.
Its API accepts no witness. The simulator test also checks that its transcript
fails against native SHA-256.

This is engineering evidence, not a completed cryptographic proof. In particular,
the additive-code instantiation and correspondence to VEIL's formal statements
need independent human review.

## Soundness profile

The currently registered `experimental()` parameters use a rate-1/2 code and
128 queries to keep the one-block reference proof small enough to iterate on.
The basic unique-decoding proximity term is only about 53 bits. This is not a
100-bit production profile. Fiat--Shamir knowledge soundness, QROM security,
adaptive-query ZK, and post-quantum knowledge extraction are not claimed.

The fixed statement is nevertheless bound fail-closed in the implementation:

- changing a public digest rejects;
- changing the circuit digest, proof nonce, parameters, or batch shape rejects;
- mutating the Hadamard reduction or a Merkle opening rejects; and
- non-Boolean witnesses and unsatisfied R1CS rows are rejected by the prover and
  enforced by the proof.

## Code assumptions still requiring review

1. The additive NTT evaluates the interpolating polynomial on the intended
   disjoint affine coset for all registered dimensions.
2. Any 128 queried coordinates have full-rank projection from the 128 random
   message symbols (the Reed--Solomon/MDS argument).
3. The square code, decode, and restriction map implement VEIL's required
   multiplicative code and reduction property.
4. Query selection is non-adaptive and never exceeds the padding dimension.
5. The six-private-value bijection and all conditioned simulator distributions
   match the real transcript, including the characteristic-two signs.

Tiny exhaustive/rank and multiplicativity tests cover regressions, but do not
replace proofs of these statements.

## Current measured reference point

On the development machine, a one-item release build measured approximately:

- prove: 0.35 seconds;
- verify: 0.30 seconds;
- serialized proof: 2.98 MB;
- statement-only simulation plus verification: 3.2 seconds.

These are smoke-test measurements, not benchmark claims.

# VEIL-FLOCK transcript

All labels below are stable, unversioned protocol domains. Every operation is
typed and length-framed.

1. Absorb the VEIL-FLOCK protocol, pinned BLAKE3-preimage relation, Secure-UDR
   parameter suite, and ordered public statement.
2. Sample a fresh 256-bit proof nonce and independent 256-bit nonces for the
   outer witness, VEIL-linear, and VEIL-Hadamard initial trees. Commit to the
   randomized FLOCK witness and to the VEIL mask inputs using their respective
   tree contexts. Bind the circuit shape, proof nonce, all tree nonces, witness
   root, and mask root under `veil-flock-tree-nonces` and
   `veil-flock-mask-root` before any PIOP challenge.
3. Run FLOCK zerocheck. Observe and serialize every prover field value as
   `value + fresh_mask`, preserving scalar/vector framing. Equality
   coordinates are sampled from the exact production rejection domain.
4. Run lincheck with the same one-time-pad treatment for every round pair and
   the final partial vector.
5. Mask and absorb the witness and blinder ring slices under
   `veil-flock-ring-masks`. Build the sole public packed-direct functional from
   the digest statement and absorb its blinder evaluation.
6. Perform the bounded outer grind and sample the nonzero folding challenge.
   Form the committed fold and absorb its masked AB/C slices.
7. Fix the canonical claim manifest and batch AB, C, and the public digest
   functional into one opening.
8. Fork the fully bound prefix under `veil-flock-pcs-fork` and
   `veil-flock-inner-fork`. The PCS branch performs the sole shielded
   ring-switch/Ligerito opening. The VEIL branch proves the shifted verifier,
   including the Hadamard and ring-link constraints.

At the pinned batch-256 shape, the affine mask layout is:

```text
128  zerocheck round-one coordinates
 32  zerocheck multilinear coordinates
  2  zerocheck terminal coordinates
 16  lincheck round coordinates
 64  lincheck partial-vector coordinates
512  two pairs of witness/blinder ring slices
---
754  independently sampled F128 masks
```

The witness, VEIL-linear, and VEIL-Hadamard initial Merkle trees use distinct
channels and independently sampled 256-bit tree nonces. Every initial leaf
payload is framed as a fresh 256-bit salt followed by the row payload; internal
nodes use a disjoint tag. The proof carries the public tree nonces and only the
salts for queried leaves.

Fiat--Shamir squeezes use exact SHA-256 block semantics. Two `F128` challenges
sharing one digest block are programmed jointly, unused halves are uniform,
and rejection-sampled values retain every rejected block in the transcript.
No mask, preimage, witness bit, code padding, or unmasked PIOP value is
serialized.

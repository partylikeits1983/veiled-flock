# VEIL-FLOCK Transcript

All transcript inputs are typed and length-framed. The labels below are stable
protocol domains.

1. Absorb the ordered public statement under the VEIL-FLOCK BLAKE3-preimage
   Fiat-Shamir domain.
2. Sample a 256-bit proof nonce and independent 256-bit nonces for the witness,
   VEIL-linear, and VEIL-Hadamard initial trees. Commit to the randomized FLOCK
   witness and VEIL mask inputs under those tree contexts.
3. Bind the circuit shape, proof nonce, tree nonces, witness root, and mask
   root before any PIOP challenge.
4. Run FLOCK zerocheck. Every prover field value is serialized as
   `value + fresh_mask`, with scalar/vector framing preserved. Equality
   coordinates are drawn from the production rejection domain.
5. Run lincheck with the same one-time-pad treatment for each round pair and
   final partial vector.
6. Mask and absorb the witness and blinder ring slices. Build the public
   packed-direct digest functional and absorb its blinder evaluation.
7. Perform the bounded outer grind, sample the nonzero folding challenge, form
   the committed fold, and absorb the masked AB/C slices.
8. Fix the claim manifest and batch AB, C, and the public digest functional
   into one opening.
9. Fork the bound prefix. The PCS branch performs the shielded
   ring-switch/Ligerito opening. The VEIL branch proves the shifted verifier,
   including Hadamard and ring-link constraints.

At the pinned 256-slot shape, the affine mask layout is:

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
channels and independent 256-bit tree nonces. Each initial leaf is framed as a
fresh 256-bit salt followed by row data. Internal nodes use a separate tag. The
proof carries the public tree nonces and the salts for queried leaves.

Fiat-Shamir squeezes use SHA-256 block semantics. Two `F128` challenges can
share one digest block; unused halves are uniform. Rejection-sampled values
keep rejected blocks in the transcript.

No mask, preimage, witness bit, code padding, or unmasked PIOP value is
serialized.

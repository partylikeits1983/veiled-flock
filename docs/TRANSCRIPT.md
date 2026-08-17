# Implemented transcript (version 0)

All observations below are absorbed in order by FLOCK's duplex SHA-256
challenger. Merkle hashing is separately framed by role, channel, position, and
the proof nonce.

1. Top-level label, batch size, pinned R1CS digest, commitment nonce, and public
   digest vector.
2. Block-R1CS label, extended-witness commitment root, and Hadamard commitment
   root.
3. Batching challenge for the R1CS and Booleanity multiplication triples.
4. Hadamard label and root; evaluation challenge; `gamma`; product-mask
   challenge; `phi`.
5. Hadamard dot vector; three claimed dot products; additive-mask dot product;
   root; linear-combination challenge; revealed masked vector and random message
   padding; 128 derived query positions and one framed Merkle multiproof.
6. Link batching challenge. The verifier computes `A^T q`, `B^T q`, the private
   six-value links, the `r + (r+1) = 1` equality, constant pins, and public digest
   equalities.
7. Dot-product label; computed link vector; expected claim; mask dot product;
   extended-witness root; linear-combination challenge; revealed masked vector
   and random message padding; 128 derived query positions and one framed Merkle
   multiproof.

No message bytes, witness bits, `A z`, `B z`, or the six multiplicative padding
values are serialized directly. The three Hadamard dot claims are masked by the
private tautological triples.

The current mode does not serialize FLOCK zerocheck, lincheck, ring-switching, or
Ligerito transcripts: it proves FLOCK's native block R1CS directly. Those phases
re-enter the transcript only in the future succinct-verifier compilation.

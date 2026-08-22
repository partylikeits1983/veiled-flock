# Security status

This implementation is experimental, unaudited, and unsuitable for production
secrets.

## Claim status

| Property | Current status |
|---|---|
| Exact 64-byte BLAKE3 relation | Implemented and differentially tested |
| Honest prove/verify completeness | Implemented and tested at batch 256 |
| Raw messages absent from proof types | Checked by serialization tests and code review |
| Mutation rejection | Tested for statement and major proof components |
| Public-input-only simulated acceptance | Implemented for programmed Fiat--Shamir challenges |
| Distributional zero knowledge | Not proved |
| Composed adversarial soundness | Not proved; only component evidence and estimates |
| Argument of knowledge/extraction | Partial components exist; no active end-to-end theorem |
| Classical-ROM composition | Not proved; current simulator is not a single-oracle model |
| QROM security | Not claimed |

## Active path

`Blake3PreimageZkSetup::prove_succinct` commits to a randomized witness, masks
the FLOCK PIOP transcript, and proves the shifted verifier with `veil-f128`.
Verification checks the shifted circuit, hiding PCS opening, and public digest
claim. The proof type omits messages, witness values, masks, and private
padding. It includes public digests, masked messages, evaluation claims,
commitments, openings, and the VEIL certificate.

## Simulator boundary

`simulate_succinct` accepts public digests without a preimage and produces a
proof accepted by the generic verifier. It programs Fiat--Shamir challenges
only. PCS and inner VEIL hashing bypass its programmable oracle. The test does
not model one random oracle for the full protocol or prove that simulated and
real transcripts have the same distribution.

## Open requirements

1. Exclude 0 and 1 from the constraint compiler's multiplication batching
   challenge, as required by decision D008.
2. Use framed, nonce-separated, and channel-separated inner VEIL commitments.
3. Use one programmable random oracle for Fiat--Shamir, PCS, and VEIL hashing.
4. Prove the additive-code properties, AB/C masking rank, hiding Ligerito,
   transcript fork, and ROM composition for the active path.
5. Bound allocations before decoding attacker-controlled proof vectors.
6. Audit side channels, randomness, and secret erasure.

Do not describe or deploy this implementation as a zero-knowledge argument
until these requirements are resolved and independently reviewed.

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
| Public-input-only simulated acceptance | Implemented with one programmable oracle for Fiat--Shamir, PCS, and VEIL hashing |
| Distributional zero knowledge | Not proved |
| Composed adversarial soundness | Not proved; only component evidence and estimates |
| Argument of knowledge/extraction | Partial components exist; no active end-to-end theorem |
| Classical-ROM composition | Not proved; the executable harness uses one oracle, but no composition theorem is claimed |
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
proof accepted by the generic verifier. Fiat--Shamir, PCS, and inner VEIL
hashing all query the same programmable oracle under disjoint encodings. This
executable check does not prove that simulated and real transcripts have the
same distribution.

## Input bounds

The CLI accepts at most 256 public digests and decodes proof bundles with a
640 KiB resource limit. The limit is enforced while reading and by the bincode
decoder before proof vectors are constructed.

## Open requirements

1. Prove the additive-code properties, AB/C masking rank, hiding Ligerito,
   transcript fork, and ROM composition for the active path.
2. Audit side channels, randomness, and secret erasure.

Do not describe or deploy this implementation as a zero-knowledge argument
until these requirements are resolved and independently reviewed.

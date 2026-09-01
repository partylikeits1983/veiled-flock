# veiled-flock

Zero-knowledge batched BLAKE3 preimage proofs over binary fields,
combining Succinct's FLOCK and VEIL.

FLOCK provides fast batched hash proving. VEIL adds zero knowledge to
hash-based multilinear proof systems. veiled-flock adapts those ideas
to FLOCK's binary-field setting.

Given an ordered list of BLAKE3 digests, the prover demonstrates that
it has corresponding 64-byte preimages without revealing those
preimages.

### Headline benchmark

For 4,096 64-byte BLAKE3 preimages:

- Prove: ~135 ms
- Verify: ~20 ms
- Full proof bundle: 1,017,308 bytes
- Machine: AMD Ryzen 7 7840HS

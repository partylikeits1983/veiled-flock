# v6 to v7

v7 replaces the Boolean `P * Q` design with a field-valued `P` on a translated
subcube and a fixed public affine `Q-star`. The obsolete Q commitment, opening,
evaluation, and randomness streams are removed.

The transcript now binds a per-proof nonce before every challenge. Merkle
leaves, internal nodes, recursion levels, commitment channels, and proof of
work all use injective role-separated random-oracle frames. Native and
recording/programming backends are byte-identical when unprogrammed.

The distribution argument no longer rests on sampled Boolean-rank evidence:

- a generic symbolic kernel emits a nonzero production minor with total-degree
  bound 720, giving a PIOP bad-set bound of `720 / 2^128`;
- a closed-form PCS translator preserves the combined opening vector and all
  queried L0 wide rows;
- the production L0 conditional entropy is 16,384 bits per fresh leaf;
- recursive codewords are identical under the translation;
- a sealed, one-pass simulator receives only the public statement and programs
  at most 18 fresh oracle points.

The recording-oracle extractor and fresh-prefix weak simulation-extractability
gate are executable. The decoder is accurately scoped as an exact-word and
candidate validator, not a complete arbitrary-error Reed-Solomon decoder.

The security labels are corrected. Computational ZK is separate from
knowledge security. At `Q = 2^64`, the standalone `F2^128` knowledge theorem is
about 55.994 bits and the deployment label is **100-bit conjectured classical
knowledge security**. The standalone theorem column remains 55.994 bits.

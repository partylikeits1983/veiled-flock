# v7 to v7.1

Version 7.1 is an editorial revision. It does not change the protocol,
certificate registry, concrete bounds, or security labels.

- The abstract and first section now state the covered relations, simulator
  interface, model, and result before describing the implementation.
- The proof is organized around two distribution-preserving translations:
  conditioned PIOP masking and opening-preserving PCS blinding.
- The conditioned-rank theorem and PCS translation lemma include short proof
  sketches.
- The explicit simulator error is collected in one equation:
  `723 / 2^128 + 18 Q_H / 2^256 + Q_H / 2^16384`.
- The 118.502-bit figure is explicitly separated from the ordinary 256-bit
  random-oracle collision term.
- Knowledge-security reduction bounds, deployment labels, and unimplemented
  profiles are separated in both prose and the summary table.
- Bibliography entries and inline citations have been completed.

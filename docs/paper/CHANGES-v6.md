# v5.2 to v6: historical change record

This file records the v6 transition and is superseded by `CHANGES-v7.md`.
Its P/Q construction and security wording are not the active protocol or claim.

## The headline change

v5.2 and everything before it concerned the BLAKE3 **batch** statement, whose
public input is the batch size. v6 concerns the **fixed-digest** statement:
public digests, private preimages, `BLAKE3(x_i) = y_i`.

This is not a strengthening of the old claim — it is a different relation, and
the old evidence does not carry over. Stated plainly because the distinction is
easy to blur: **witness-indistinguishability is vacuous for a unique-witness
relation**, so every coverage certificate in v5.2, all of which measure exactly
that, could not be reused even in principle.

## Claims added

- **A simulator for the fixed-digest relation.** Receives only the public
  digests; the unmodified verifier accepts. v5.2 had no such object and could
  not have: its simulator is the honest prover on a self-chosen witness.
- **Distribution evidence in claim-kernel form.** The `P·Q` channel spans the
  zerocheck round-pair block in full (4096/4096 at m=22) on the fixed-digest
  circuit, with a degenerate-mask control at exactly 2048.
- **A knowledge extractor.** v5.2 had none, and asserted base knowledge
  soundness by proximity to the Ligerito theorems. v6 implements the
  system-specific half and cites the ROM-observation half (BCS).
- **An executable ROM game.** A programmable oracle whose unprogrammed
  behaviour is byte-identical to the real challenger.

## Claims corrected or retired

- **"The zk mode is zero-knowledge"** now means something different and must be
  read with its statement. The batch-statement result stands as it stood; it is
  simply about a weaker assertion than most readers assume.
- **The label scheme is superseded** for this relation. v6 states the property,
  the evidence for each component, and the conditions, rather than a letter.

## Findings that changed the design

- **Padding digests are not zero.** Under a pinning, padding slots must satisfy
  the pinned rows, so their output region holds `BLAKE3(0^64)`. A statement
  assuming zero padding rejects honest proofs. The padding rule is now part of
  the statement hash.
- **Pinning a bit to zero must keep the constant wire on the b-side.**
  `0·0 = z_s` pins correctly and satisfies the R1CS while breaking every honest
  proof, because the lincheck checks the matrix–vector products and the witness
  generator emits `b[s]=1`.
- **Naive coset sampling is distinguishable.** Sampling every revealed value
  from the coset the verifier's equations cut out lands outside the honest
  support: deep-level opened rows satisfy code-parity relations the verifier
  never checks. The simulator therefore *computes* the opening.
- **Oracle programming is necessary, not decorative.** The final round's
  `G(∞)` must be solved against a challenge sampled after the message
  preceding it. Plain Fiat–Shamir cannot supply it.
- **A desynchronised proof-of-work nonce.** The harness absorbed it raw where
  the real challenger tags it; six unit tests passed because none grind. Caught
  by the control requiring an unprogrammed oracle to reproduce Fiat–Shamir.

## Evidence-pipeline repairs carried in from the v5.2 branch

The certificate runner could not fail (it recorded a flagship failure and
exited 0); three end-to-end gates matched **zero tests** because module-scoped
tests were addressed by bare name under `--exact`; the registry's evidence
check was a substring match. All fixed, with a matched-zero-tests guard. The
label was walked back from A to B at that time for exactly this reason.

## Still open

Simulation-extractability; a quantitative extraction bound; an executable
ROM-observation step; all-tuple coverage; messages longer than 64 bytes; QROM;
independent review.

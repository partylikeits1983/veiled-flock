# Lean proofs

This directory contains the generic Flock masking lemmas and the formal
VEIL-FLOCK protocol model. The production endpoint is the theorem
`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126`, implemented in
`VeiledFlock/Production/Security/FormalZK.lean`.

The filesystem is grouped by proof area:

- `Flockzk/`: legacy masking and probability lemmas.
- `VeiledFlock/Core/`: finite probability, bad-event, and bookkeeping lemmas.
- `VeiledFlock/Algebra/`: fields, coding, masks, zerocheck, and algebraic
  protocol reductions.
- `VeiledFlock/Oracle/`: programmable-oracle, adaptive query, freshness, and
  simulator machinery. `AdaptiveHiddenInput.lean` lives here.
- `VeiledFlock/Concrete/`: concrete parameters, framing, transcripts, grinding,
  and random-tape ledgers.
- `VeiledFlock/Production/Algebra/`: production algebraic translation,
  masking, padding, compiler, and VEIL layers.
- `VeiledFlock/Production/Merkle/`: Merkle transport, equality sampling, and
  tree samplers.
- `VeiledFlock/Production/Nizk/`: adversary, proof, experiment, and coupling
  model.
- `VeiledFlock/Production/Operational/`: operational tape, causal transport,
  hidden-salt, and good-event bridge.
- `VeiledFlock/Production/Outer/`: outer PCS/code definitions.
- `VeiledFlock/Production/Sampling/`: sampling schedule and bad-event
  probability chain.
- `VeiledFlock/Production/Security/`: statistical-distance, statistical-ZK,
  concrete-failure, and final formal-ZK theorem files.

Namespaces intentionally remain stable across the directory refactor. For
example, the main theorem is still named
`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126`.

```sh
cd lean
lake exe cache get
lake build
cd ..
scripts/lean-axioms.sh
```

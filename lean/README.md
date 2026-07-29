# Lean support for Flock-ZK

This directory proves reusable masking and probability lemmas used by the
Flock-ZK paper. It does not contain an end-to-end formalization of the Rust
protocol, its transcript, or its random-oracle simulation.

## What Lean proves

| Module | Result | Role in the paper |
|---|---|---|
| `Masking.lean` | Affine transcripts with witness differences inside the mask image have witness-independent distributions and exact simulators. | Generic masking argument. |
| `MaskingSurjective.lean` | Surjectivity is a sufficient condition for full mask coverage. | Reusable coverage corollaries. |
| `MaskingTriangular.lean` | Two dependent masking stages compose under triangular coverage hypotheses. | Generic staged-composition argument. |
| `MaskingMixtureBadSet.lean` | Conditional equality outside a bad challenge set gives a statistical-distance bound by the bad-set mass. | Adds the exceptional rank set to the ZK ledger. |
| `SchwartzZippelBound.lean` | A nonzero multivariate polynomial with supplied per-variable degree bounds has the stated Schwartz-Zippel zero-set bound. | Converts the symbolic determinant certificate into a probability bound. |
| `ConditionalReplacement.lean` | Algebraic replacement distance and a separate commitment boundary add. | Generic PIOP/PCS composition rule. |

The files contain no `sorry`. The axiom audit permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

## What Rust supplies

The current field-valued Flock-ZK instantiation is protocol-specific and is
not encoded directly in Lean. The executable certificate suite supplies:

- the exact zerocheck mask-functional matrix for the registered parameters;
- a nonzero 32 by 32 minor evaluation and its degree vector;
- the rank-two leakage check and conditioned-image calculation;
- the exact additive-NTT PCS mask translation on the registered query fixture;
- the opening-field manifest, entropy ledger, simulator acceptance tests, and
  concrete hybrid-error ledger.

The paper composes these checked facts with the generic Lean theorems. See
`docs/paper/zk-flock.tex`, `docs/memos/s2-piop-coverage.md`, and
`docs/memos/s3-pcs-translator.md`.

## What is not proved in Lean

- equality between every Rust execution trace and a Lean protocol model;
- the registered determinant and translator calculations themselves;
- random-oracle programming, Merkle hiding, or the Fiat-Shamir transform;
- the complete simulator theorem as one Lean declaration;
- the extractor's general noisy Reed-Solomon decoding step;
- QROM or post-quantum security.

`MaskingMixture.lean` and some auxiliary modules are retained because they are
useful generic results and record earlier proof paths. They should not be read
as the current protocol instantiation.

## Build and audit

```sh
cd lean
lake exe cache get
lake build
cd ..
scripts/lean-axioms.sh
```

The toolchain and Mathlib revision are pinned by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.

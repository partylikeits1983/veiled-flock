# Formal verification plan for succinct VEIL-FLOCK

## Objective

The target theorem is zero knowledge for the fixed-digest BLAKE3 relation:
for every valid public statement and any two satisfying witnesses, the real
verifier views are identically distributed in the interactive model. After
Fiat--Shamir, the target becomes computational/statistical zero knowledge in
the classical random-oracle model with an explicit bad-event bound.

The proof must cover the active succinct implementation, not the older direct
whole-R1CS or A1 reference paths.

## Proof boundary

The formal model will include:

- the exact masked zerocheck and lincheck transcript geometry;
- the shifted VEIL verifier circuit and its AB/C output claims;
- additive-domain Reed--Solomon base and square codes over `GF(2^128)`;
- VEIL dot-product and Hadamard-product protocols;
- the hiding Ligerito opening and its query budget;
- the public digest opening and batch-padding rule; and
- the programmable-random-oracle simulator.

Initially trusted components will be BLAKE3 collision resistance, Merkle
binding, the `GF(2^128)` implementation, the random sampler, and Rust/Lean
conformance. Each must be listed explicitly in the final theorem statement.

## Phase 1: freeze an executable specification

1. Define a versioned transcript manifest containing every observed byte,
   field element, label, challenge, and fork in order.
2. Generate mask counts and proof-shape checks from that manifest instead of
   maintaining parallel handwritten counts.
3. Add a Rust trace exporter for honest and simulated executions.
4. Make CI compare those traces against a small executable Lean model.

**Exit condition:** changing a transcript field or challenge order breaks a
conformance test until the formal model and manifest are updated.

## Phase 2: formalize the native VEIL code

In Lean 4, prove for the registered additive RS dimensions:

1. encoding linearity and injectivity;
2. minimum distance and the unique-decoding radius used by the soundness
   calculation;
3. MDS projection: any at-most-`k` queried coordinates are uniform when the
   `k` message-padding coordinates are uniform;
4. closure of products in the square code;
5. correctness and linearity of `square_to_base`; and
6. nonzero proximity-generator coefficients.

The proofs should be dimension-generic, with the concrete inverse-rate-8,
160-query profile discharged as a corollary.

**Exit condition:** Lean derives the hiding and distance facts currently
stated informally by `veil-f128::code`.

## Phase 3: formalize VEIL over `GF(2^128)`

Model the Rust protocols in this order:

1. `ZkDotProduct`;
2. `ZkHadamard` and its product-code reduction;
3. the six-value/two-dummy-product padding map; and
4. the two-phase arithmetic-constraint compiler.

Prove completeness, verifier equivalence, perfect honest-verifier ZK under
the hard query budget, and the concrete soundness-error expression. Prove
that committing in phase one and supplying the challenge-dependent shifted
circuit in phase two is equivalent to the single-phase VEIL statement.

**Exit condition:** a Lean theorem covers
`commit_constraint_inputs`/`prove_constraints_from_commitment` and
`verify_constraints` at the succinct profile.

## Phase 4: formalize the shifted FLOCK verifier

1. Encode every zerocheck and lincheck recurrence in
   `shifted_verifier_circuit`.
2. Prove that adding the private mask vector to the public masked messages
   reconstructs the ordinary accepting FLOCK transcript.
3. Prove the circuit accepts if and only if all PIOP recurrences and the
   terminal `a*b`, AB, and C claims hold.
4. Prove the two-phase mask commitment occurs before every challenge whose
   distribution depends on a masked value.

**Exit condition:** Lean establishes shifted-verifier equivalence and exact
mask-accounting for every supported batch shape.

## Phase 5: close the FLOCK commitment layer

This is the most important protocol-specific milestone.

1. Derive the exact linear map from FLOCK's randomizer rows to the AB and C
   evaluation claims.
2. Prove rank two for all non-degenerate supported challenge tuples and bound
   the exceptional set rather than relying on sampled tests.
3. Prove hiding of every Ligerito recursive opening under the aggregate hard
   query budget, including the terminal residual.
4. Reconcile the result explicitly with the constrained-interleaved-code
   theorem used for the PCS layer.
5. Prove that the public digest claim and the two VEIL output claims refer to
   the same committed witness.

**Exit condition:** a simulator can replace the committed witness and both
output claims without changing the verifier-view distribution, except for a
stated bad-event probability.

## Phase 6: prove composition and simulation

Construct a single Lean `RealView` and `SimView` for the interactive protocol.
Prove, in order:

1. transcript one-time-pad replacement;
2. VEIL inner-proof replacement;
3. hiding-PCS witness replacement;
4. AB/C claim replacement; and
5. equality of the final interactive views.

Reuse the generic masking, bad-set, Schwartz--Zippel, and conditional
replacement lemmas already in `lean/Flockzk`, but instantiate them with the
active succinct transcript rather than the legacy A1 certificate.

**Exit condition:** one top-level declaration states interactive ZK with all
assumptions and error terms visible.

## Phase 7: Fiat--Shamir in the classical ROM

1. Model `OracleChallenger` and `FsChallenger` as implementations of one
   domain-separated transcript interface.
2. Formalize the simulator's 17 programmed zerocheck challenges at the
   batch-256 geometry.
3. Prove freshness or account for programming collisions.
4. Justify the pre-PCS inner-VEIL transcript fork as a composition boundary.
5. Apply an appropriate classical-ROM Fiat--Shamir theorem and report the
   complete distinguishing advantage.

QROM zero knowledge is a separate project and is not a release requirement
for the first formally justified experimental version.

**Exit condition:** the public-input-only simulator is connected to a
classical-ROM ZK theorem, rather than only an acceptance test.

## Phase 8: implementation correspondence and review

1. Differential-test Rust and Lean transcript traces across all supported
   batch profiles.
2. Add property/fuzz tests for decoding, malformed shapes, query uniqueness,
   and transcript framing.
3. Run the Lean no-`sorry` and axiom audit in CI.
4. Have a cryptographer review the mathematical statement and a separate
   reviewer audit the Rust correspondence.

**Release condition:** the top-level theorem, exact source revision,
parameter profile, trusted assumptions, and audit reports are published
together. Until then the repository remains experimental.

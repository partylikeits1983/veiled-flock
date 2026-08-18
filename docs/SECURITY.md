# Security scope of succinct VEIL-FLOCK

This implementation is experimental, unaudited, and not production-safe.

## Audit verdict

The active CLI path is genuinely wired through the native VEIL compiler:

```text
veiled_flock
  -> Blake3PreimageZkSetup::prove_succinct
  -> prove_succinct_veil_r1cs
  -> veil_f128::commit_constraint_inputs
  -> veil_f128::prove_constraints_from_commitment
```

Verification reconstructs the shifted circuit, verifies the same hiding PCS
claims, and calls `veil_f128::verify_constraints`. The `veil` Cargo feature is
therefore functional, not a label around ordinary FLOCK.

The audit found no message, raw witness, transcript mask, or VEIL private
witness in the serialized `Bundle`/`SuccinctVeilProof` types. The proof does
contain public digests, randomized evaluation claims, Merkle commitments and
openings, masked PIOP messages, and the VEIL certificate, as intended.

This is an implementation audit, not a cryptographic proof or independent
review. In particular, executable simulator acceptance does not establish
distributional equality.

## What is hidden

The 64-byte BLAKE3 messages and all ordinary FLOCK witness wires are private.
The proof contains neither raw witness data nor an unmasked zerocheck/lincheck
message.

The digest list, actual batch count, padded shape, circuit, parameter profile,
proof length, timing, and memory behavior are public.

## Why the composition is intended to be zero knowledge

1. Every exposed algebraic PIOP coordinate is additively one-time-padded by an
   independent `GF(2^128)` mask committed before its challenge is sampled.
2. VEIL proves the shifted verifier identity without opening those masks. Its
   code padding hides queried coordinates, its additive/product masks hide
   revealed combinations, and two dummy product rows hide the three Hadamard
   linkage claims.
3. The witness PCS uses FLOCK's hiding commitment: a random low message half,
   a full-support blinder codeword, and the existing hiding recursive opening.
4. The two output evaluation claims are linked on both sides: the shifted
   circuit derives them from the hidden PIOP, while Ligerito checks them against
   the witness commitment. FLOCK's zk randomizer rows move those claim values.

At batch 256, VEIL masks 242 transcript values. Its profile uses inverse rate
8 and 160 random padding symbols for 160 non-adaptive queries. With three
product rows, the square code has rate at most 1/4; the basic unique-decoding
miss term `(5/8)^160` is about 108 bits. This is a parameter calculation, not a
complete soundness proof.

## Executable simulator

`simulate_succinct` receives arbitrary public digests and no preimage. It
constructs a randomized pseudo-witness whose public digest cells are patched,
simulates zerocheck in the programmable ROM, and then runs the production
lincheck, hiding PCS opening, and VEIL proof. The ordinary succinct verifier
accepts the result using the same programmed oracle.

This establishes executable simulator acceptance. Distributional equality
additionally relies on:

- uniform transcript masks and the VEIL code-projection property;
- FLOCK's hiding-PCS lemmas/query budget;
- the zk randomizer rows covering the AB/C output claim kernel; and
- freshness of the programmed Fiat--Shamir points.

The existing fixed-digest certificates show that fresh randomizers move the
terminal evaluations, and the succinct tests check that both output claims
move across fresh draws. A full all-challenge rank proof for this exact
two-claim kernel is still required before a formal ZK claim.

The simulator uses `OracleChallenger`, not the production deterministic
`FsChallenger`, because a random-oracle simulator must program challenge
answers. Both challengers exercise the same generic succinct verifier. The
formal ROM argument must still bound programming collisions and prove that
the programmed view has the real view's distribution.

## Soundness checks implemented

- Verifier-owned PCS and VEIL parameters are pinned exactly.
- The mask commitment is bound before every masked PIOP challenge.
- The shifted circuit checks C interpolation, every zerocheck recurrence, the
  final `a*b` product, every lincheck recurrence, and both PCS output values.
- The public digest claim is verifier-derived and shares the same opening.
- Mutations of the statement, nonce, witness root, masked zerocheck,
  masked lincheck, AB claim, VEIL dot proof, VEIL Hadamard reduction, or
  Ligerito opened rows are rejected.
- Proof decoding is canonical in the CLI.

## Remaining review obligations

1. Prove the additive-code MDS projection, multiplicative reduction, and
   proximity-generator properties for the registered dimensions.
2. Prove the exact AB/C randomizer claim-kernel rank for every supported shape.
3. Review the hiding-Ligerito recursion and its final residual against VEIL/CFW
   assumptions, including the hard query budget.
4. Prove the Fiat--Shamir compilation's ZK statement in the classical ROM;
   QROM security is not claimed.
5. Audit that the pre-PCS transcript fork used by the inner certificate is a
   valid composition boundary.
6. Add allocation limits before deserializing attacker-controlled vectors.
7. Obtain independent cryptographic and implementation audits.

The staged proof plan and proposed Lean theorem boundaries are in
[`FORMAL_VERIFICATION.md`](FORMAL_VERIFICATION.md).

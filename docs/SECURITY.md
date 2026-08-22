# Security scope of succinct VEIL-FLOCK

This implementation is experimental, internally reviewed, not independently
audited, and not suitable for production secrets.

## Claim status

| Property | Current status |
|---|---|
| Exact 64-byte BLAKE3 relation | Implemented and differentially tested |
| Honest prove/verify completeness | Implemented and tested at batch 256 |
| Raw messages absent from proof types | Confirmed by serialization/code review |
| Mutation rejection | Tested for statement and major proof components |
| Public-input-only simulated acceptance | Implemented for programmed Fiat--Shamir challenges |
| Distributional zero knowledge | Not proved |
| Composed adversarial soundness | Not proved; only component evidence and estimates |
| Argument of knowledge/extraction | Partial components exist; no active end-to-end theorem |
| Classical-ROM composition | Not proved; current simulator is not a single-oracle model |
| QROM security | Not claimed |

The correct current description is “an implementation intended to be a
zero-knowledge argument,” not an unqualified “zero-knowledge proof.”

## Implementation wiring

The active CLI path reaches the native VEIL compiler:

```text
veiled_flock
  -> Blake3PreimageZkSetup::prove_succinct
  -> prove_succinct_veil_r1cs
  -> veil_f128::commit_constraint_inputs
  -> veil_f128::prove_constraints_from_commitment
```

Verification reconstructs the shifted circuit, checks the hiding PCS opening,
derives the public digest claim, and calls `veil_f128::verify_constraints`.
The `veil` feature is therefore functional, not a label around an ordinary
FLOCK proof.

The serialized `Bundle` and `SuccinctVeilProof` types contain no message, raw
witness, transcript mask, PCS blinding witness, or VEIL private padding. They
do contain the public digest list, randomized evaluation claims, Merkle roots
and openings, masked PIOP messages, and the VEIL certificate.

This establishes data-flow facts, not semantic privacy. A proof can omit the
witness and still leak a function of it through its transcript; ruling that
out is the purpose of the unfinished ZK proof.

## Private and public information

Intended private information:

- the exact 64-byte message for each public digest;
- ordinary FLOCK witness wires and ZK randomizer rows;
- the 242 transcript masks at batch 256;
- FLOCK PCS blinding data; and
- VEIL code padding, additive/product masks, and six compiler pad values.

Public information:

- the ordered digest list and actual batch count;
- the padded power-of-two shape, which is at least 256 slots;
- circuit and parameter profile, proof nonce, roots, and proof length;
- masked zerocheck and lincheck messages;
- explicit randomized AB and C evaluation values;
- PCS and VEIL openings; and
- timing, memory use, and access-pattern side channels.

## Intended privacy argument

1. Every exposed algebraic FLOCK PIOP coordinate is additively padded with an
   independent `GF(2^128)` mask committed before the dependent challenge.
2. VEIL proves the shifted verifier identity without opening those masks. Code
   padding is intended to hide queried coordinates, while additive/product
   masks and two dummy product rows hide the revealed combinations.
3. The witness uses FLOCK's hiding commitment and recursive opening rather
   than its ordinary PCS path.
4. The shifted circuit and PCS both check the same explicit AB and C values.
   FLOCK's randomizer rows are intended to hide those two values. The public
   digest value is verifier-derived and checked in the same PCS opening.

At batch 256, the inner VEIL profile uses inverse rate 8, 160 random padding
symbols, and 160 distinct non-adaptive queries. With three product rows, the
square-code unique-decoding miss expression `(5/8)^160` is about 108 bits.
This is one component estimate, not the protocol's final soundness level.

## Simulator boundary

`simulate_succinct` takes arbitrary public digests, a seed, a programmable
oracle, and no preimage. It constructs a pseudo-witness for unrelated random
messages, patches its public digest cells, programs zerocheck challenges, and
then runs production lincheck, PCS, and VEIL code. The generic verifier accepts
the result under the same programmed `OracleChallenger`.

The current harness programs Fiat--Shamir squeezes only. The succinct prover
and verifier instantiate a native `RoContext` for PCS, and the active VEIL
constraint compiler uses unframed native Merkle hashing. Those calls do not
pass through the shared `ProgrammableOracle`. The test therefore demonstrates
Fiat--Shamir programming acceptance, but not one executable random-oracle game
covering every protocol hash call.

Even after that wiring is fixed, acceptance alone is insufficient. A ZK proof
must establish the distribution of the real and simulated views, account for
programming collisions, and compose the transcript masks, VEIL proof, hiding
PCS, and AB/C claim replacement.

## Soundness evidence and limits

Implemented checks include:

- verifier-owned PCS and VEIL parameters;
- mask-root binding before masked PIOP challenges;
- every zerocheck and lincheck recurrence, terminal `a*b`, and AB/C linkage in
  the shifted circuit;
- a verifier-derived public digest claim in the common witness opening;
- canonical CLI encoding with rejection of trailing bytes; and
- rejection tests for mutations to the statement, nonce, roots, masked
  messages, AB/C values, PCS rows, and VEIL dot/Hadamard data.

No forged false statement was found by these tests. Mutation tests do not
model an adaptive malicious prover, however. A complete soundness statement
must combine at least the FLOCK PIOP error, random digest-equality test, PCS
error, VEIL linear/Hadamard batching and proximity errors, Merkle binding, and
Fiat--Shamir transform.

## Known active deviations and obligations

The current release-blocking items are:

1. The active constraint compiler samples the six-value multiplication
   batching point from all of `GF(2^128)` instead of excluding 0 and 1 as
   required by decision D008. This adds an exceptional event of probability
   at most `2^-127` under ideal sampling and invalidates the claimed
   always-invertible masking argument on those challenges.
2. Inner VEIL commitments use the legacy unframed Merkle APIs even though
   framed, nonce- and channel-separated variants exist.
3. The simulator and commitment layers do not yet use one shared programmable
   random oracle.
4. Additive-code MDS/projection/product properties, AB/C rank, hiding
   Ligerito, the transcript fork, and the complete ROM composition remain
   unproved for the active path.
5. CLI decoding is canonical but not allocation-bounded before deserializing
   attacker-controlled vectors.
6. Timing, cache behavior, memory access, randomness quality, and secret
   erasure have not been audited.

These obligations must be resolved, tested, and independently reviewed before
the implementation is described or deployed as a zero-knowledge argument.

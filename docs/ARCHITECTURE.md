# Architecture

This document describes how the active implementation adds zero knowledge to
FLOCK with VEIL. The normative protocol is defined in [`../SPEC.md`](../SPEC.md).

## Components

The implementation has three proof layers.

| Layer | Purpose | Implementation |
|---|---|---|
| FLOCK PIOP | Reduce Boolean R1CS satisfaction to two witness-evaluation claims | `flock-core` zerocheck and lincheck |
| FLOCK PCS | Commit to the randomized witness and open the AB, C, and digest claims | hiding ring-switch and Ligerito |
| VEIL | Prove that the masked PIOP transcript is an accepting FLOCK transcript | `veil-f128` constraint, dot-product, and Hadamard protocols |

The public API is `Blake3PreimageZkSetup::{prove_succinct,
verify_succinct,simulate_succinct}`. The CLI uses these methods. The older
direct whole-R1CS implementation in `veiled_preimage.rs` is not on the active
path.

## Baseline FLOCK flow

For witness `z`, FLOCK computes `a = A z`, `b = B z`, and `c = z`. It commits
only to `z`.

```text
z --commit--> Com(z)

(a, b, c)
    |
    +-- zerocheck --> evaluations of a, b, c
    |
    +-- lincheck  --> AB evaluation claim on z

AB claim + C claim + public digest claim
    |
    +-- ring-switch/Ligerito opening against Com(z)
```

Ordinary FLOCK sends the zerocheck and lincheck messages directly. Those
messages depend on the witness, so ordinary FLOCK is not zero knowledge.

## Step 1: randomize and hide the witness

`Blake3PreimageZkSetup::new_succinct` builds the pinned BLAKE3 R1CS with FLOCK
ZK randomizer rows. Batches are padded to at least 256 slots.

`prove_succinct` validates every supplied preimage, samples fresh randomizer
rows for every slot, and generates:

```text
z, A z, B z, lincheck(z)
```

`prove_succinct_veil_r1cs` commits to `z` with `commit_zk_with_ro`. This is
FLOCK's hiding commitment, not the ordinary commitment. It adds a random low
message half and a full-support blinder codeword before Ligerito encoding.

The public digest claim is a random multilinear evaluation of the digest cells
inside `z`. The verifier computes its expected value from the public digest
list. The claim is included in the same opening as the PIOP claims.

## Step 2: mask every exposed PIOP value

The prover samples a uniform `GF(2^128)` vector `h`. Its length is exactly the
number of zerocheck and lincheck values observed by the FLOCK challenger. At
batch 256 this is 242 values.

`MaskingChallenger` wraps the normal FLOCK challenger. Whenever FLOCK observes
a field value `v_i`, the wrapper observes:

```text
v'_i = v_i + h_i
```

It preserves FLOCK's labels, scalar framing, vector framing, challenge
sampling, and proof-of-work methods. The serialized zerocheck and lincheck
proofs contain the same masked values that were absorbed by Fiat--Shamir.

Masking the messages alone is insufficient: the verifier cannot check FLOCK's
equations without the original values, and revealing `h` would remove the
privacy. VEIL solves this problem.

## Step 3: commit to the masks before challenges

The shifted FLOCK verifier depends on Fiat--Shamir challenges derived from the
masked transcript. The mask commitment must therefore precede those
challenges, while the final shifted circuit cannot be constructed until after
they exist.

The VEIL compiler is split into two phases:

1. `commit_constraint_inputs` commits to `h` and six private multiplication
   pads using an empty placeholder circuit with the final input count.
2. `prove_constraints_from_commitment` receives the completed shifted circuit
   and proves it against the same commitment.

The outer transcript absorbs the commitment root under
`veil-flock-mask-root-v0` before zerocheck starts. This removes the circular
dependency without allowing the prover to choose masks after seeing the
challenges.

## Step 4: construct the shifted verifier

`shifted_verifier_circuit` replays the public masked transcript and derives the
same challenges as the prover. Each original value is represented inside the
circuit as:

```text
v_i = public(v'_i) + private(h_i)
```

The circuit checks:

1. the round-one C interpolation;
2. every zerocheck folding equation;
3. the final `a_eval * b_eval` relation;
4. every lincheck folding equation;
5. the final lincheck dot product;
6. the AB evaluation value; and
7. the C evaluation value.

The shifted circuit has one multiplication from the FLOCK decision. The
remaining checks are linear over `GF(2^128)`.

The AB and C values are public proof fields. The shifted circuit proves that
they are the outputs of the hidden FLOCK transcript. The PCS independently
proves that the same values are evaluations of `Com(z)`. This is the binding
edge between VEIL and FLOCK.

## Step 5: prove the shifted circuit with VEIL

The upstream VEIL Rust implementation uses multiplicative-subgroup codes over
a two-adic prime field. `GF(2^128)` has no two-adic multiplicative subgroup, so
`veil-f128` implements the same required interfaces with additive-domain
Reed--Solomon codes.

`AdditiveRsCode` represents a message as evaluations on an additive subspace,
interpolates it, and evaluates it on a disjoint affine subspace. Pointwise
products lie in a square code with twice the degree. `square_to_base` is the
VEIL reduction from the square-code message to the base message positions.

The constraint compiler reduces the shifted circuit to:

- one Hadamard proof for multiplication constraints; and
- one dot-product proof for the batched linear constraints and links to the
  Hadamard claims.

It appends private values:

```text
(r, s, r*s, r+1, t, (r+1)*t)
```

The products `r*s` and `(r+1)*t` add two dummy Hadamard rows. Together with
`r + (r+1) + 1 = 0`, they randomize the three dot-product claims exposed by
the Hadamard proof. These values are committed but never serialized.

Both VEIL code layers use inverse rate 8 and 160 random padding rows. The
Fiat--Shamir transcript selects 160 distinct non-adaptive query positions.

## Step 6: link VEIL, PCS, and the public statement

After lincheck, the prover has:

```text
AB = (point_ab, value_ab)
C  = (point_c,  value_c)
D  = public digest evaluation claim
```

The transcript absorbs `value_ab` and `value_c` under
`veil-flock-output-claims-v0`. The public digest batching challenges are then
sampled.

The prover creates one hiding Ligerito opening for `AB`, `C`, and `D`. The
shifted circuit checks `value_ab` and `value_c`; Ligerito checks all three
claims against `Com(z)`. The verifier, not the prover, derives the value for
`D` from the digest list.

FLOCK randomizer rows change `value_ab` and `value_c` between proofs of the
same witness. These rows are the privacy mechanism for the two values that are
not covered by the transcript one-time pad. A formal all-challenge rank proof
for this two-value map remains required.

## Step 7: separate the terminal transcripts

The Ligerito prover and verifier agree on acceptance but do not guarantee an
identical challenger state after the terminal opening. The implementation
therefore clones the transcript before PCS and labels the clone
`veil-flock-inner-fork-v0`.

The original branch verifies Ligerito. The fork verifies VEIL. The fork occurs
only after the statement, commitment roots, masked PIOP, AB/C values, and
digest challenge are fixed. Both branches are linked through the same roots
and AB/C claims.

This fork is an explicit experimental composition boundary and still requires
a formal proof.

## Verification path

`verify_succinct_veil_r1cs` performs the reverse process:

1. check the registered PCS and VEIL parameters;
2. bind the statement, nonce, and witness commitment;
3. absorb the VEIL mask root;
4. reconstruct the shifted circuit from the masked proofs;
5. derive the AB, C, and public digest claims;
6. create the same transcript fork;
7. verify the hiding Ligerito opening; and
8. verify the VEIL constraint proof.

Acceptance requires both proof systems to verify. Mutation tests cover the
statement, nonce, witness root, masked zerocheck, masked lincheck, AB claim,
VEIL dot proof, VEIL Hadamard proof, and Ligerito rows.

## Simulator

`simulate_succinct` takes public digests and no preimage. It constructs a valid
FLOCK witness for unrelated random messages, replaces the public digest cells
with the requested targets, and commits to the resulting pseudo-witness.

The pseudo-witness does not satisfy the hash R1CS. `RomZerocheckSimulator`
therefore samples the zerocheck messages, programs the zerocheck challenges,
and solves the final quadratic coefficient so the transcript ends at the
pseudo-witness's actual terminal evaluations. Production lincheck, PCS, and
VEIL code then complete the proof.

The generic verifier accepts the simulated proof when driven by the same
programmed oracle. At batch 256, the simulator programs 17 challenges.

This demonstrates that an accepting transcript can be generated from the
public statement alone. Proving that its distribution matches a real proof
requires the remaining arguments listed in `docs/SECURITY.md`.

## Private and public data

Private data:

- 64-byte messages;
- FLOCK witness wires and randomizer rows;
- transcript mask vector `h`;
- FLOCK PCS blinding data; and
- VEIL code padding, additive masks, product masks, and six private pads.

Public proof data:

- digest list and padded shape;
- proof nonce and commitment roots;
- masked zerocheck and lincheck messages;
- AB and C evaluation values;
- hiding Ligerito opening; and
- VEIL dot-product and Hadamard proofs.

The proof does not hide batch size, circuit shape, parameter profile, proof
length, timing, or memory access patterns.

## Diagrams

Sequence and class diagrams for the three crates are in [`../SPEC.md`](../SPEC.md), section 15.

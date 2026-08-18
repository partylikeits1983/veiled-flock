# zk-FLOCK with VEIL specification

## 1. Status

This document specifies the active succinct zk-FLOCK implementation. The
protocol is experimental. It has executable tests and a simulator, but it does
not yet have an end-to-end formal zero-knowledge proof.

The words **MUST**, **MUST NOT**, **SHOULD**, and **MAY** are normative.

## 2. Relation

Let `b >= 1` be the public batch length.

- Public input: ordered digests `Y = (y_0, ..., y_(b-1))`, where each `y_i` is
  32 bytes.
- Private witness: messages `X = (x_0, ..., x_(b-1))`, where each `x_i` is
  exactly 64 bytes.
- Relation: `BLAKE3(x_i) = y_i` for every `i`.

Each hash is one BLAKE3 root compression with:

```text
chaining value = BLAKE3 IV
counter        = 0
block length   = 64
flags          = CHUNK_START | CHUNK_END | ROOT
```

The circuit MUST pin these values. It MUST leave the 64 message bytes private.

## 3. Batch shape and padding

The circuit uses `N = 2^n` slots, where:

```text
n = max(8, ceil(log2(b)))
```

Therefore `N >= 256`. Slots `0..b` contain the requested instances. Remaining
slots contain the valid pinned compression of the all-zero 64-byte message.
The corresponding padding digest is public and fixed.

The statement MUST bind:

- the ordered digest list and its length;
- the padded batch size;
- the digest layout and padding rule; and
- the FLOCK circuit and PCS parameters.

Changing the digest order, count, padding rule, or shape MUST invalidate the
proof.

## 4. Algebra and parameters

FLOCK's Boolean R1CS is over `GF(2)`. Its PIOP and VEIL transcript values are
over `F = GF(2^128)`.

The active PCS parameters are:

```text
Ligerito profile = Fast
PCS inverse rate = 2
batch log        = 6
zk               = true
```

The active VEIL parameters are:

```text
linear padding   = 160 field elements
Hadamard padding = 160 field elements
inverse rate     = 8
queries          = 160 distinct non-adaptive positions
```

The verifier MUST reject proofs containing different PCS or VEIL parameters.

## 5. Witness commitment

The prover constructs the pinned FLOCK witness `z`, the row evaluations
`a = A z` and `b = B z`, and the lincheck representation of `z`.

Every padded block receives fresh FLOCK ZK randomizer rows. The prover then
commits to `z` with `commit_zk_with_ro`. The commitment uses:

- a random low message half;
- a full-support random blinder codeword;
- a fresh 32-byte proof nonce; and
- the `Witness` random-oracle channel.

The nonce, circuit statement, PCS parameters, and commitment root MUST be
bound before the PIOP transcript is processed.

## 6. Masked FLOCK transcript

Let `v` be the ordered list of all `F` values observed from FLOCK zerocheck and
lincheck. The prover samples an independent uniform mask vector
`h in F^s`, commits to it with VEIL, and sends:

```text
v_masked = v + h
```

Addition and subtraction are identical in characteristic two.

The mask commitment root MUST be absorbed before any Fiat--Shamir challenge
that depends on `v_masked`. Scalar and vector transcript framing MUST match
ordinary FLOCK.

For the current circuit:

```text
s = 2 * 2^K_SKIP
  + 2 * (m - K_SKIP)
  + 2
  + 2 * (k_log - k_skip)
  + 2^k_skip
```

At batch 256, `K_SKIP = k_skip = 6`, `m = 22`, and `k_log = 14`, so
`s = 242`.

The ordered fields are:

1. 64 zerocheck `round1_ab` values;
2. 64 zerocheck `round1_c` values;
3. two values for each remaining zerocheck round;
4. terminal zerocheck `a` and `b` values;
5. two values for each lincheck round; and
6. 64 lincheck `z_partial` values.

`final_c_eval` is not an observed FLOCK message. It stores the explicit C
opening claim. The shifted circuit reconstructs the same value from masked
`round1_c`.

## 7. Shifted verifier circuit

The verifier derives all FLOCK challenges from the public masked transcript.
It then constructs an arithmetic circuit `C_shifted` whose private inputs are
the mask vector `h`.

For each public masked value `v_masked[i]`, the circuit reconstructs:

```text
v[i] = v_masked[i] + h[i]
```

`C_shifted` MUST enforce:

1. interpolation of the zerocheck C claim;
2. every zerocheck recurrence;
3. the terminal relation `a_eval * b_eval = running_claim`;
4. every lincheck recurrence;
5. the final lincheck dot-product identity;
6. equality between the lincheck result and the AB PCS claim; and
7. equality between the reconstructed C result and the C PCS claim.

The circuit produces the same AB and C evaluation points that ordinary FLOCK
would open. The prover MUST abort if the circuit-derived claims differ from
the prover's claims.

## 8. VEIL proof

VEIL proves that the committed mask vector satisfies `C_shifted` without
revealing the masks.

The implementation uses additive-domain Reed--Solomon codes over `GF(2^128)`
because this field has no two-adic multiplicative subgroup. The code evaluates
the interpolating polynomial on a disjoint affine subspace. Its square code
contains pointwise products of base-code words.

The VEIL compiler appends six private values:

```text
(r, s, r*s, r+1, t, (r+1)*t)
```

It adds two dummy multiplication constraints and the linear constraint
`r + (r+1) + 1 = 0`. These rows mask the three Hadamard linkage claims. The
six values MUST remain private.

The VEIL proof consists of:

- a Hadamard proof for the real and dummy multiplication rows; and
- a dot-product proof for a random linear combination of all linear
  constraints and multiplication-link constraints.

Both proofs MUST use 160 random code-padding symbols and at most 160 distinct
query positions.

## 9. PCS linkage

The proof contains explicit AB and C evaluation values. These values are not
one-time-padded. FLOCK's randomizer rows are intended to make them independent
of the private witness.

The verifier derives three openings from one witness commitment:

1. the AB claim from lincheck;
2. the C claim from zerocheck; and
3. the public digest claim computed from `Y`.

The AB and C values MUST be checked by both `C_shifted` and the PCS opening.
The digest value MUST be computed by the verifier. The prover MUST NOT supply
the expected digest-opening value independently.

The three claims MUST be verified in one hiding ring-switch/Ligerito opening.

## 10. Transcript order

The transcript order is:

1. absorb the public digest statement;
2. bind the witness commitment, proof nonce, circuit, and PCS shape;
3. absorb the VEIL mask commitment under `veil-flock-mask-root-v0`;
4. process the masked zerocheck transcript;
5. process the masked lincheck transcript;
6. absorb AB and C values under `veil-flock-output-claims-v0`;
7. derive the public digest claim;
8. fork the transcript under `veil-flock-inner-fork-v0`;
9. verify the hiding PCS opening on the original branch; and
10. verify the VEIL constraint proof on the fork.

The fork occurs before the terminal PCS protocol. All roots, masked PIOP
messages, output claims, and the public digest challenge are bound before the
fork.

## 11. Proof format

The CLI bundle uses magic `VFLK0003` and contains:

```text
public digest list
witness commitment
proof nonce
masked zerocheck proof
masked lincheck proof
AB evaluation value
C evaluation value
hiding Ligerito opening
VEIL constraint proof
```

The bundle MUST NOT contain messages, raw FLOCK witness data, unmasked PIOP
messages, the mask vector, or VEIL private padding values.

The CLI transcript domain is `veiled-flock-cli-succinct-v0`. Decoding MUST be
canonical and MUST reject trailing data.

## 12. Verification

The verifier MUST:

1. reject an empty digest list or invalid bundle magic;
2. reconstruct the padded setup from the digest count;
3. reject mismatched commitment or proof parameters;
4. reconstruct `C_shifted` from the masked proof;
5. derive the AB, C, and digest claims;
6. verify the hiding Ligerito opening;
7. verify the VEIL Hadamard and dot-product proofs; and
8. accept only if every check succeeds.

Any mutation to the statement, nonce, commitment root, masked PIOP messages,
AB/C values, PCS opening, or VEIL proof MUST cause rejection except with the
protocol's soundness error.

## 13. Simulator

`simulate_succinct` is the protocol simulator. Its input is:

```text
public digest list
simulator seed
programmable random oracle
transcript domain
```

It MUST NOT receive a preimage.

The simulator:

1. creates unrelated random 64-byte messages;
2. constructs their valid FLOCK witness;
3. replaces only the public digest cells with the target digests;
4. commits to this pseudo-witness with the normal hiding PCS;
5. samples masked zerocheck messages;
6. programs the zerocheck challenges and solves the final coefficient so the
   transcript reaches the pseudo-witness's terminal evaluations; and
7. runs the production lincheck, PCS opening, VEIL prover, and generic
   verifier.

At batch 256 it programs 17 scalar challenges. Programming collisions or
degenerate challenges MUST cause simulation failure.

Simulator acceptance is required, but it is not sufficient to establish zero
knowledge. A complete proof must also show equality, or a bounded statistical
distance, between real and simulated verifier views.

## 14. Security scope

The intended privacy argument has three parts:

1. uniform VEIL masks hide the algebraic FLOCK transcript;
2. the hiding PCS hides the committed witness and its openings; and
3. FLOCK randomizer rows hide the explicit AB and C values.

The current implementation does not formally prove the complete composition.
The following remain required:

- a proof of the additive RS projection, distance, and product-code
  properties for the registered dimensions;
- an all-challenge rank proof for the AB/C randomizer map;
- a hiding proof for recursive Ligerito, including its terminal residual;
- a proof that the pre-PCS transcript fork is a valid composition boundary;
  and
- a classical random-oracle proof for Fiat--Shamir and simulator programming.

No QROM or production-security claim is made.

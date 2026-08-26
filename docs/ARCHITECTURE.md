# Architecture

VEIL-FLOCK has one zero-knowledge path and three linked proof layers.

| Layer | Role |
|---|---|
| FLOCK PIOP | Reduce the pinned Boolean R1CS to witness evaluations |
| Shielded FLOCK PCS | Commit once and batch-open AB, C, and public digest claims |
| VEIL | Prove the masked affine and nonlinear verifier relations |

The public entry point is
`Blake3PreimageZkSetup::{new,prove,verify,simulate}`. There is no alternate ZK
proof flavor or legacy masking API.

## Pinned relation

The public statement is an ordered list of BLAKE3 digests. The private witness
contains one 64-byte message per digest. The circuit pins the BLAKE3 IV,
counter zero, block length 64, and `CHUNK_START|CHUNK_END|ROOT` flags. A
short list is padded deterministically to the next registered power-of-two
shape, with a 256-slot production floor and a 2048-slot ceiling. The verifier
pins each exact circuit digest and its Secure PCS parameters.

## Outer shielded commitment

The witness is packed over `GF(2^128)` and committed with the blinded additive
RS encoder. Per lane, the coefficient message is `[mu || z]`: `mu` is a
uniform degree-`<k` low block and `z` occupies the next `k` novel-basis
coefficients. The image is the registered `RS[N,2k]` code. Evaluation of the
low block on any union of at most `k` distinct positions is a full-row-rank
Vandermonde map, so those opened rows are uniform for fixed `z`.

One additional full random row enters the nonzero shielded linear combination.
The implementation certificate couples this uniform fold jointly with every
opened initial column and ring slice. Subtracting the padding contribution
leaves the virtual full message `[mu || z] + c*g`, which is uniform. Its claim
basis is `[0 || b]`, so it proves exactly the original claims about `z`.
Recursive Ligerito therefore runs unchanged after this boundary.

The outer witness, VEIL-linear, and VEIL-Hadamard initial trees each have an
independently sampled 256-bit tree nonce and a fresh 256-bit salt per leaf.
The separate Fiat--Shamir proof nonce and all three tree nonces are bound into
the transcript. Recursive trees need no privacy salt because their complete
inputs are already witness-independent.

## Masked FLOCK verifier

At the 256-slot floor, the PIOP exposes 242 field coordinates and its two
ring-switch claims expose 512 more. Each of the 754 coordinates receives a
distinct uniform field mask. Every circuit-size doubling adds two sumcheck
coordinates, so the registered 512/1024/2048-slot shapes use 756/758/760
masks. The mask layout is derived from the exact circuit and checked against
the registered count; proving and verification fail if the transcript consumes
a different number or order.

At fixed challenge history the visible affine transcript has the form

```text
Y = A*w + B*r + d(public).
```

The production certificate constructs the translation witness for
`image(A) <= image(B)`. The active layout makes the mask block surjective.
Adaptive composition follows by conditioning on each already-independent
prefix before sampling the next verifier challenge.

Ring switching is certified over `GF(2)`: the 128 by 128 matrix for a field
challenge is built from the production basis decomposition and multiplication
routine, then checked on all basis vectors. The masked witness, blinder, and
folded slices obey the same committed `q = z + c*g` relation.

## VEIL nonlinear linkage

The mask commitment is made before FLOCK derives challenges. Once the masked
transcript is known, the shifted verifier circuit reconstructs each hidden
value from its public masked coordinate and private pad. It checks every
zerocheck and lincheck recurrence, the terminal multiplication, AB/C linkage,
ring-switch linkage, and public-functional linkage.

VEIL uses additive-domain Reed--Solomon codes over `GF(2^128)`. Operand and
product codes have separately certified ZK projection, distance, and query
budgets. Pointwise products lie in `RS[N,2K-1]`. The exact reduction function
is checked on every pair of basis vectors, which suffices by bilinearity.

The initial VEIL linear and Hadamard trees each use their own channel, tree
nonce, and independent 256-bit leaf salts. Simulation constructs a shifted
circuit genuinely satisfied by simulator-owned masks, so the ordinary ZK VEIL
prover is never invoked on an unsatisfied assignment.

## Single batched opening

The exact claim manifest is formed and absorbed before batching challenges.
One fresh witness commitment produces exactly one opening containing AB, C,
and the public digest functional. Claim identifiers are canonical and
duplicates are rejected. The union of distinct initial positions is checked
against the code-padding budget.

The public digest functional is derived only from the public statement. Its
raw evaluation is safe because equal public statements induce witness
differences in the functional's kernel; the joint PCS certificate checks this
condition.

## Simulator boundary

Before the uniform-fold boundary, the simulator uses algebraic FLOCK and VEIL
simulators with challenges sampled from the honest distributions. It creates
an arbitrary representative of the public affine fiber only to evaluate the
linear post-processing needed to form the same joint distribution. This
representative is not asserted to satisfy BLAKE3.

After the joint fold is uniform, the simulator runs ordinary recursive
Ligerito and deterministic/randomized post-processing honestly. All
Fiat--Shamir programming follows the production 256-bit block layout,
including rejection sampling and uniform unused halves.

## Random-oracle compilation

One lazy classical random oracle serves Fiat--Shamir, Merkle, VEIL, and
grinding under injective role-separated encodings. The simulator shares one
table across adaptive proofs and programs only undefined points. Fresh proof
nonces, tree channels, leaf salts, and masks make sequential composition
independent even for correlated witnesses. The exact pROM bound and
limitations are stated in [SECURITY.md](SECURITY.md).

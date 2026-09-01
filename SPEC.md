# VEIL-FLOCK specification

The words **MUST**, **MUST NOT**, **SHOULD**, and **MAY** are normative for the
Rust protocol. Statements about Lean describe its formal model.

## 1. Relation

For `1 <= b <= 4096` public ordered digests `Y=(y_0,...,y_(b-1))`, the private
witness is `X=(x_0,...,x_(b-1))` with each `x_i` exactly 64 bytes, and
`BLAKE3(x_i)=y_i`. The circuit MUST pin the BLAKE3 IV, counter zero, block
length 64, and `CHUNK_START|CHUNK_END|ROOT` flags.

The circuit has `N=2^n` slots with `n=max(8,ceil(log2(b)))`. Unused slots MUST
contain the fixed valid compression of the all-zero message. Digest order,
length, padding, layout, circuit digest, and protocol parameters are public and
transcript-bound.

The library verifier receives the expected digest list separately from the
proof. The canonical bundle also carries a copy for transport; applications
MUST compare it with the verifier-controlled statement.

## 2. Algebra and profiles

FLOCK's R1CS is over `GF(2)`; PIOP, PCS, and VEIL values are over
`F=GF(2^128)`. Production MUST use the Secure unique-decoding Ligerito profile
in ZK mode. The outer PCS uses inverse-rate log 1 and batch log 6. Fast and Slim
profiles MUST be rejected.

| Slots | R1CS `m` | Secure config | PIOP / total masks | L0 queries / blind bits |
| ---: | ---: | --- | ---: | ---: |
| 256 | 22 | `m23_secure` | 242 / 754 | 294 / 2 |
| 512 | 23 | `m24_secure` | 244 / 756 | 292 / 3 |
| 1,024 | 24 | `m25_secure` | 246 / 758 | 291 / 4 |
| 2,048 | 25 | `m26_secure` | 248 / 760 | 290 / 5 |
| 4,096 | 26 | `m27_secure` | 250 / 762 | 290 / 6 |

The VEIL constraint layer uses 160 operand/linear padding elements, 160
Hadamard padding elements, inverse rate 8, and 160 distinct queries. The
verifier MUST reject any proof-carried parameter mismatch.

## 3. ZK encoders

For packed witness lane `z` and a random degree-`<k` low block `mu`, the outer
witness code MUST implement `C(z,mu) = Eval_D(mu + X_k*z)`.

Here `X_k*X_j=X_(k+j)` in the production novel polynomial basis. Consequently,
the random projection is evaluation of every degree-`<k` polynomial and every
set of at most `k` distinct opened positions is uniform for fixed `z`. The
implementation MUST canonicalize positions, count a duplicate once, and reject
a union larger than `k`. The claim basis MUST be embedded as `[0 || b]`, so the
shifted coefficient layout proves the original witness functional.

For a VEIL code with logical length `L`, 160 random padding elements are added
and the result is zero-padded to interpolation length
`K=next_power_of_two(L+160)`. The code length is `N=8K`, and the Hadamard
product code MUST accept exactly `RS_D[N,2K-1]`. In production the linear and
Hadamard code lengths are 8192 and 2048. Their padding and query budgets MUST
be checked separately.

## 4. Freshness and Merkle framing

Every proof MUST sample fresh independent:

- witness randomizer rows and code padding;
- the PCS blinder and all PIOP/ring masks;
- VEIL operand and product padding;
- proof nonce, tree nonces, and one 256-bit salt per initial leaf.

The public full-ZK prover and simulator MUST draw these coins directly from the
OS random source. Their public APIs MUST NOT accept deterministic seeds. The
deterministic sampler is test-only and MUST remain unreachable from the public
full-ZK entry point.

Leaf and internal-node hash inputs MUST use disjoint tags and injective length
framing. Witness, VEIL-linear, and VEIL-Hadamard trees MUST use distinct
channels. Initial leaf payloads are `salt || row`. Recursive Ligerito trees MAY
be unsalted only after their complete input is witness-independent.

A commitment MUST NOT be reused across proofs. One fresh commitment MUST have
exactly one batched PCS opening.

## 5. Masked FLOCK transcript

The prover MUST one-time-pad every verifier-visible affine private coordinate.
The five shapes have 242-250 PIOP coordinates. Every shape also has 512 ring
coordinates: two claims, each with 128 witness and 128 blinder coordinates.
The resulting 754-762 masks MUST be independent and MUST never later be
revealed unmasked.

Lean proves that every witness-dependent direction in
`visible = A*w + B*r + public_constant` is covered by the random mask map.

Ring linkage MUST be certified over `GF(2)`. For field challenge `c`, the
production matrix is `M_c=S o mul_c o S^-1`, and the verifier MUST bind masked
witness, blinder, and folded slices to the same committed vectors.

## 6. VEIL shifted verifier

The mask-input commitment MUST precede all FLOCK challenges it affects. The
shifted circuit MUST reconstruct hidden values from public masked values and
private pads and enforce:

1. every zerocheck interpolation and fold recurrence;
2. the terminal multiplication relation;
3. every lincheck recurrence and final dot product;
4. AB and C equality with the PCS claims;
5. exact ring-switch linkage;
6. all live nonlinear relations through the VEIL Hadamard proof.

The public digest functional is not part of this shifted circuit. The verifier
adds it as the packed-direct claim in the PCS opening. VEIL adds six private
mask values, two dummy products, and one linear relation before proving the
shifted circuit.

In the simulation experiment, the shifted VEIL circuit MUST be genuinely
satisfied by simulator-owned masks. The implementation MUST NOT run an honest
nonlinear prover on an unsatisfied assignment.

## 7. Joint shielded opening

The outer fold coefficient multiplying the full random row MUST be sampled
from `F*`. For each fresh commitment, the joint distribution of the fold,
every opened initial column, all exposed ring slices, and public direct
functionals MUST be independent of the private witness.

After removing the padding contribution, the ordinary Ligerito input is
uniform and witness-independent. Recursive Ligerito MAY then run honestly,
including its recursive commitments and clear terminal residual.

Production MUST batch exactly two ring-switched claims, AB and C, followed by
one packed-direct public digest claim. Their order is fixed before the batching
challenges. The verifier MUST compute the digest target from the public
statement.

## 8. Fiat--Shamir and grinding

One typed, role-separated random oracle serves transcript challenges, Merkle
hashing, VEIL, and grinding. `F128` decoding is bijective. `F*` and
`F\{0,1}` samplers MUST use exact rejection sampling. Two field elements in
one 256-bit output MUST be sampled/programmed jointly; unused bytes MUST remain
uniform.

The outer blind grind uses 2-6 bits and an 8192-trial limit. Each live Ligerito
fold grind uses at most 5 bits and a 4096-trial limit. Lean stops each search at
its limit. Rust currently finds the first successful nonce and checks its bound
afterward, so the Rust search itself is not yet bounded.

## 9. Simulator

`Blake3PreimageZkSetup::simulate` receives only public digests and a shared
programmable oracle; its randomness comes from the OS and its transcript
domain is pinned internally. It MUST sample challenges from their honest
distributions before programming them and MUST abort if any programmed point
was already defined inconsistently.

Before the uniform-fold boundary it MUST use algebraic FLOCK and VEIL
simulation. It MAY construct an arbitrary representative of the public affine
fiber for linear evaluation, but MUST NOT assume that representative satisfies
BLAKE3. After the uniform-fold boundary it MAY execute ordinary recursive
Ligerito honestly.

Across adaptive proofs the simulator MUST retain one shared oracle table and
fresh per-proof randomness. Correlated witnesses are permitted; commitment
reuse is not.

## 10. Proof format and verification

The canonical bundle contains the public digest list, the outer witness
commitment, and a `SuccinctVeilProof`. The nested proof contains the proof
nonce, three initial-tree nonces, masked zerocheck and lincheck messages, two
masked ring claims, one public-direct blinder value, the blind-grinding nonce,
one batched Ligerito opening, and one VEIL constraint proof. It MUST NOT contain
messages, raw witness data, private masks, code padding, or unmasked PIOP
messages.

The byte format is the five-byte `FLOCK` magic, flavor byte 5, and a bincode
payload using fixed-width integer encoding. The payload contains bounded
vectors and is not itself fixed-width. Decoding MUST enforce a 1 MiB limit,
exact parameter shapes, no trailing bytes, and bounded vector lengths.

The verifier MUST reconstruct the pinned statement and shifted circuit, derive
all claims itself, verify the one PCS opening and the VEIL proof, and reject any
mutation except with the stated soundness error.

Public proving and verification MUST instantiate the pinned SHA-256
Fiat--Shamir domain internally. Generic or test-only challengers MUST NOT be
selectable through the public full-ZK API.

The prover and simulator use the first successful grinding nonce. The verifier
checks the predicate and applies the 8192 outer limit or 4096 Ligerito limit; it
does not check minimality for a positive-bit grind. The pROM ledger MUST include
the geometric failure tail for every live site.

## 11. Security claim

Lean proves statistical distance below `2^-126` for the five registered shapes
in a finite classical programmable-random-oracle model. Its relation checks the
padded public projection, not BLAKE3 or R1CS satisfaction, and its proof object
is a privacy projection rather than the serialized Rust proof. Establishing the
same claim for Rust requires the end-to-end correspondence described in
`docs/SECURITY.md`.

Rust composes its interactive soundness errors additively and reports about 107
bits for the pinned profiles. Noninteractive soundness requires the explicit
classical Fiat--Shamir/ROM assumption.

No argument-of-knowledge, concrete-SHA theorem, QROM theorem, side-channel
security, or production-readiness claim is made.

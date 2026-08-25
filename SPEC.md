# VEIL-FLOCK specification

The words **MUST**, **MUST NOT**, **SHOULD**, and **MAY** are normative.

## 1. Relation

For public ordered digests `Y=(y_0,...,y_(b-1))`, the private witness is
`X=(x_0,...,x_(b-1))` with each `x_i` exactly 64 bytes, and
`BLAKE3(x_i)=y_i`. The circuit MUST pin the BLAKE3 IV, counter zero, block
length 64, and `CHUNK_START|CHUNK_END|ROOT` flags.

The circuit has `N=2^n` slots with `n=max(8,ceil(log2(b)))`. Unused slots MUST
contain the fixed valid compression of the all-zero message. Digest order,
length, padding, layout, circuit digest, and protocol parameters are public and
transcript-bound.

## 2. Algebra and profiles

FLOCK's R1CS is over `GF(2)`; PIOP, PCS, and VEIL values are over
`F=GF(2^128)`. Production MUST use the Secure unique-decoding Ligerito profile,
inverse-rate log 1, batch log 6, and ZK mode. Fast and Slim profiles MUST be
rejected.

The VEIL constraint layer uses 160 operand/linear padding elements, 160
Hadamard padding elements, inverse rate 8, and 160 distinct queries. The
verifier MUST reject any proof-carried parameter mismatch.

## 3. ZK encoders

For packed witness lane `z` and a random degree-`<k` low block `mu`, the outer
witness code MUST implement the linear encoder

```text
C(z,mu) = Eval_D(mu + X_k*z).
```

Here `X_k*X_j=X_(k+j)` in the production novel basis. Consequently, the
random projection is evaluation of every degree-`<k` polynomial and every set
of at most `k` distinct opened positions is uniform for fixed `z`. The
implementation MUST canonicalize positions, count a duplicate once, and
reject a union larger than `k`. The claim basis MUST be embedded as
`[0 || b]`, so the shifted coefficient layout proves the original witness
functional.

The operand code has dimension `K=n+k`. The Hadamard product code MUST accept
exactly `RS_D[N,2K-1]`; its reduction to the intended multiplication rows MUST
be the production bilinear map. Product commitments that use additional
padding MUST certify that padding and query budget separately.

## 4. Freshness and Merkle framing

Every proof MUST sample fresh independent:

- witness randomizer rows and code padding;
- full masking row and all PIOP/ring masks;
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
The pinned layout has 242 PIOP and 512 ring coordinates. Masks MUST be
independent and MUST never later be revealed unmasked.

At every accepted challenge history, the implementation certificate MUST
establish `image(A)<=image(B)` for

```text
visible = A*w + B*r + public_constant.
```

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
6. public digest-functional linkage; and
7. all live nonlinear relations through the VEIL Hadamard proof.

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

The exact AB, C, and public digest claims MUST form one canonical manifest
before batching challenges. Duplicate claim identifiers MUST be rejected. The
digest target MUST be computed by the verifier from the public statement.

## 8. Fiat--Shamir and grinding

One typed, role-separated random oracle serves transcript challenges, Merkle
hashing, VEIL, and grinding. `F128` decoding is bijective. `F*` and
`F\{0,1}` samplers MUST use exact rejection sampling. Two field elements in
one 256-bit output MUST be sampled/programmed jointly; unused bytes MUST remain
uniform.

The active outer grind is the canonical first nonce satisfying a two-bit
predicate, capped at 1024 trials. Proving and simulation MUST fail closed if
no nonce succeeds.

## 9. Simulator

`Blake3PreimageZkSetup::simulate` receives only public digests, a simulator
seed, a shared programmable oracle, and a transcript domain. It MUST sample
challenges from their honest distributions before programming them and MUST
abort if any programmed point was already defined inconsistently.

Before the uniform-fold boundary it MUST use algebraic FLOCK and VEIL
simulation. It MAY construct an arbitrary representative of the public affine
fiber for linear evaluation, but MUST NOT assume that representative satisfies
BLAKE3. After the uniform-fold boundary it MAY execute ordinary recursive
Ligerito honestly.

Across adaptive proofs the simulator MUST retain one shared oracle table and
fresh per-proof randomness. Correlated witnesses are permitted; commitment
reuse is not.

## 10. Proof format and verification

The canonical bundle contains protocol, relation, and parameter-suite IDs,
public digests, one witness commitment, proof nonce, three initial-tree nonces,
masked FLOCK transcript, masked ring claims, one batched Ligerito opening, and
one VEIL constraint proof. It MUST NOT contain messages, raw witness data,
private masks, code padding, or unmasked PIOP messages.

Decoding MUST enforce a 1 MiB limit, canonical fixed-width encoding, exact IDs,
exact parameter shapes, no trailing bytes, and bounded vector lengths.

The verifier MUST reconstruct the pinned statement and shifted circuit, derive
all claims itself, verify the one PCS opening and the VEIL proof, and reject any
mutation except with the stated soundness error.

Public proving and verification MUST instantiate the pinned SHA-256
Fiat--Shamir domain internally. Generic or test-only challengers MUST NOT be
selectable through the public full-ZK API.

Every outer and recursive grinding site MUST use the canonical first-success
nonce and MUST reject a nonce outside the first 1024 trials. The pROM ledger
MUST include the geometric failure tail for every live site.

## 11. Security claim

Subject to the certified RS proximity assumptions and the classical
programmable-random-oracle model, the protocol is multi-theorem zero knowledge.
Its algebraic transcript is perfectly witness-independent; the remaining ZK
error is the pROM abort/collision bound in `docs/SECURITY.md`.

Completeness and interactive soundness are composed additively. The pinned
interactive soundness is approximately 107 bits. Noninteractive soundness is
stated only with the explicit classical Fiat--Shamir/ROM assumption.

No argument-of-knowledge, concrete-SHA theorem, QROM theorem, side-channel
security, or production-readiness claim is made.

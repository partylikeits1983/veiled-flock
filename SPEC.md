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
`F=GF(2^128)`. The full-ZK API MUST use the Standard unique-decoding Ligerito
profile with 32 witness columns and one random column. Its outer code length
is twice the original witness height, except at 256 slots where it is four
times that height. Other profiles MUST be rejected by this API. Non-ZK FLOCK profiles and defaults are unchanged.
The PCS aggregate and composed interactive numerical bounds MUST each clear
100 bits before proving, simulation, or verification.

| Slots | R1CS `m` | Standard config | PIOP / total masks | L0 queries / blind bits |
| ---: | ---: | --- | ---: | ---: |
| 256 | 22 | `m22_standard` | 242 / 763 | 163 / 1 |
| 512 | 23 | `m23_standard` | 244 / 765 | 299 / 1 |
| 1,024 | 24 | `m24_standard` | 246 / 767 | 269 / 1 |
| 2,048 | 25 | `m25_standard` | 248 / 769 | 257 / 1 |
| 4,096 | 26 | `m26_standard` | 250 / 771 | 252 / 1 |

The VEIL constraint layer uses 160 operand/linear padding elements, 160
Hadamard padding elements, inverse rate 8, and 160 distinct queries. The
verifier MUST reject any proof-carried parameter mismatch.

All Standard fold-grinding widths are zero; the L0 blind-combination grind uses
one bit. Query schedules are registered in the [PCS configs](crates/flock-core/configs/ligerito/).
The Lean update for this setup is pending. The checked-in end-to-end pROM
theorem retains its legacy Secure construction and parameters.

## 3. ZK encoders

For each witness column `w` of height `n`, the prover MUST sample `q` random
padding coefficients, where `q` is the number of distinct L0 queries. The
outer encoder is

```text
C(w,p) = Eval_D(w + (X_n + shift) p)
shift = X_n(beta_log_code)
```

Here `X_n` is the normalized subspace polynomial of degree `n` in the novel
polynomial basis, and `beta_log_code` lies outside the full code domain `D`.
The factor MUST be nonzero at every code position, including the original
witness domain. Multiplying the degree-`<q` padding evaluation by this factor
preserves full rank on any `q` distinct positions. Unshifted `X_n*p` is invalid:
it vanishes on the original witness domain and exposes those rows.

The witness and padding polynomials have degrees below `n` and `q`,
respectively. Their sum has degree below `n+q`, which MUST be used in the
outer soundness calculation. The claim basis applies to the original witness.
One independent random column of `n+q` coefficients MUST use the same encoder
and be authenticated jointly with all witness columns in one Merkle tree.

For a VEIL code with logical length `L`, 160 random padding elements are added
and the result is zero-padded to interpolation length
`K=next_power_of_two(L+160)`. The code length is `N=8K`, and the Hadamard
product code MUST accept exactly `RS_D[N,2K-1]`. In production the linear and
Hadamard code lengths are 8192 and 4096. Their padding and query budgets MUST
be checked separately.

## 4. Freshness and Merkle framing

Every proof MUST sample fresh independent:

- witness randomizer rows and code padding;
- the PCS blinder and all PIOP/ring masks;
- VEIL operand and product padding;
- proof nonce, tree nonces, and one 256-bit salt per initial leaf.

The public full-ZK prover and simulator MUST draw one fresh seed from the OS
random source for each proof or simulation and expand it with the prover-side
DRBG. Their public APIs MUST NOT accept deterministic seeds. The deterministic
sampler is test-only and MUST remain unreachable from the public full-ZK entry
point.

Leaf and internal-node hash inputs MUST use disjoint tags and injective length
framing. Witness, VEIL-linear, and VEIL-Hadamard trees MUST use distinct
channels. Initial leaf payloads are `salt || row`. Recursive Ligerito trees MAY
be unsalted only after their complete input is witness-independent.

A commitment MUST NOT be reused across proofs. One fresh commitment MUST have
exactly one batched PCS opening.

## 5. Masked FLOCK transcript

The prover MUST one-time-pad every verifier-visible affine private coordinate.
The five shapes have 242-250 PIOP coordinates. Every shape also masks two
128-element transposed ring slices, ten lane-sumcheck coordinates, one
blinder evaluation, and 254 intermediate ring-conversion values. The resulting
763-771 masks MUST be independent and MUST never be revealed unmasked.

The bit transpose MUST be checked as a GF(2)-linear map, not treated as an
F128-linear map. The circuit implements each weighted transpose using a
linearized polynomial; every intermediate square has its own committed mask.

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

The verifier MUST derive the public digest functional and include its target
in the batched PCS reduction checked by this circuit. VEIL adds six private
mask values, two dummy products, and one linear relation before proving the
shifted circuit.

In the simulation experiment, the shifted VEIL circuit MUST be genuinely
satisfied by simulator-owned masks. The implementation MUST NOT run an honest
nonlinear prover on an unsatisfied assignment.

## 7. Joint shielded opening

The prover MUST mask the lane-sumcheck messages before sampling their fold
challenges. After reducing the witness columns, it MUST bind a masked evaluation
of the independent random column, sample a nonzero blinding coefficient, and
combine that column with the folded witness. The shifted circuit MUST bind this
reduction to the public PCS target.

Initial Merkle openings MUST authenticate every witness column and the random
column. The prover MUST reveal the combined padding and bind it before sampling
queries. The verifier subtracts its encoding from the authenticated weighted
row combination. Recursive Ligerito then checks the original unpadded code.
The combined padding and folded witness are jointly uniform because the
independent random column has a nonzero coefficient; recursive Ligerito MAY
use unsalted commitments and a clear terminal residual.

The VEIL transcript MUST bind the masked reduction, its nonces and target, and
the auxiliary ring-conversion messages before its proof challenges are sampled.

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

The outer blind grind uses one bit and an 8192-trial limit. Each live Ligerito
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
masked transposed ring claims, masked lane-fold messages, a masked blinder
evaluation, combined padding, grinding nonces, ring-conversion messages, one
batched Ligerito opening, and one VEIL constraint proof. It MUST NOT contain
private preimages, raw witness data, individual masks or padding, or unmasked
PIOP messages.

The byte format is the five-byte `FLOCK` magic, flavor byte 6, and a bincode
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

The checked-in Lean salted-Merkle/pROM bound below `2^-126` covers the legacy
full-matrix-blinder model. The Lean update for the single-column construction
is pending; see `lean/README.md` for theorem scope.

Rust adds the PIOP, public-digest binding, VEIL constraint, and PCS errors
and enforces a 100-bit interactive floor for the pinned profiles. This is a
numerical ledger under the adopted soundness analysis. Noninteractive
soundness requires the explicit
classical Fiat--Shamir/ROM assumption.

No argument-of-knowledge, concrete-SHA theorem, QROM theorem, side-channel
security, or production-readiness claim is made.

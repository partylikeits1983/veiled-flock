# Security theorem and scope

VEIL-FLOCK implements a zero-knowledge succinct argument for the pinned
64-byte BLAKE3-preimage relation. The zero-knowledge theorem is in the
classical programmable random-oracle model (pROM). The implementation is
unaudited and should not yet protect production secrets.

## Claimed properties

| Property | Scope |
|---|---|
| Relation | Ordered batch of 1–2048 64-byte BLAKE3 preimages, padded to a registered 256/512/1024/2048-slot shape |
| Completeness | Honest proofs verify |
| Zero knowledge | Multi-theorem, adaptive classical pROM |
| Algebraic privacy | Perfect, conditioned on the public statement and accepted challenge history |
| Noninteractive privacy loss | Random-oracle prequery, collision, nonce-collision, and bounded-grinding events |
| Interactive soundness | Additive bound from FLOCK PIOP, VEIL constraints, and Secure Ligerito |
| Fiat--Shamir soundness | Classical-ROM assumption/reduction boundary |
| Argument of knowledge | Not claimed |
| QROM/post-quantum ZK | Not claimed |
| Concrete SHA-256 theorem | Not claimed; SHA-256 instantiates the modeled oracle |

## Zero-knowledge theorem

For every valid public statement `x`, every witness `w` satisfying the pinned
relation, every adaptive classical adversary making at most `Q_H` oracle
queries, and every sequence of fresh proofs, the real verifier view is
indistinguishable from `Blake3PreimageZkSetup::simulate(x)`, which receives no
preimage. One shared lazy oracle table is used across all proofs. The simulator
programs only undefined points and aborts if a point was queried first.

For `P` proofs, `J` programmed points per proof, and the implementation cap
`Q_P` on protocol oracle calls per proof, the executable conservative bound is

```text
P*J*Q_H/2^256
+ P*Q_P*Q_H/2^256
+ (Q_H + P*Q_P)^2/2^257
+ 4*P*(P-1)/2^257
+ P*((31/32)^4096 + 16*(15/16)^4096).
```

The terms respectively cover challenge prequeries, hidden initial-Merkle
inputs, oracle collisions, collisions in any of the four nonce domains (one
Fiat--Shamir proof nonce plus three initial-tree nonces), and failure of the
bounded outer or Ligerito grinds. `ClassicalPromZkBound` computes this sum.

The theorem requires fresh independent proof nonces, witness-code padding,
masking rows, PIOP masks, ring masks, VEIL padding, tree nonces, and leaf salts
for every proof. The API creates a fresh commitment for each proof; commitment
reuse is not an exposed operation. The public prover and simulator draw every
coin directly from the OS random source; caller-selected deterministic seeds
are not accepted by the public full-ZK API.

## Algebraic privacy argument

The production code enforces the following gates before proving or verifying:

1. The outer blinded additive-RS encoder is linear, restricts to ordinary
   FLOCK when its padding is zero, and has a query budget no larger than its
   random-padding dimension.
2. Every opened initial coordinate projection has full padding rank. Repeated
   query positions are canonicalized and count once.
3. The nonzero VEIL fold coefficient makes the folded Ligerito input uniform.
   The implementation certificate jointly covers the fold, all initial opened
   columns, ring slices, and public direct functionals.
4. At the 256-slot floor, the 242 FLOCK transcript coordinates and 512 ring
   coordinates use 754 independent field one-time pads. Each circuit-size
   doubling adds two sumcheck coordinates and two independent pads, reaching
   760 pads at 2048 slots. The generated global mask matrix is surjective on
   every verifier-visible affine witness direction.
5. The exact F2-linear ring-switch matrix is checked against production field
   multiplication on all 128 basis vectors.
6. The live nonlinear multiplication is proved by VEIL Hadamard. Operand and
   product codes have separate ZK budgets; multiplicative containment and the
   reduction identity are tested on every basis pair.
7. One fresh witness commitment has exactly one batched opening. The manifest
   is fixed before batching challenges, claims are canonical, and the union of
   distinct initial queries stays within the padding budget.
8. After the uniform-fold boundary, recursive Ligerito is ordinary
   witness-independent post-processing. No recursive-round-specific privacy
   assumption is needed.

The simulator samples honest-distribution challenges first, constructs the
masked FLOCK transcript algebraically, and programs the exact SHA-256 squeeze
blocks. It uses an arbitrary public-fiber representative only to evaluate
post-processing whose distribution has already been proved independent of the
original witness. It never invokes an honest nonlinear prover on an
unsatisfied assignment.

## Merkle and transcript hashing

All random-oracle inputs have injective typed framing. Leaf and internal-node
domains are disjoint. Each witness-dependent initial leaf contains a fresh
256-bit salt. The outer witness, VEIL linear, and VEIL Hadamard trees each use
an independently sampled 256-bit tree nonce and a distinct channel. All three
tree nonces are transcript-bound before the first PIOP challenge. Recursive
Ligerito trees are generated after the uniform-fold boundary.

Fiat--Shamir sampling matches production block semantics: two `F128` values
share one 256-bit output where applicable, unused halves remain uniform, and
nonzero or not-zero-or-one challenges use exact rejection sampling. Grinding
uses the canonical first-success nonce and is capped at 1024 attempts.
Every Ligerito query/fold grind nonce is also capped at 1024; the ledger
conservatively reserves sixteen one-bit sites although the pinned profile has
only one live site.
The public prove and verify methods instantiate the pinned SHA-256 transcript
domain internally; substituting the test-only random challenger is not part of
their API.

## Soundness

`Blake3PreimageZkSetup::interactive_soundness_bound()` sums, rather than takes
the minimum of, the following concrete errors:

- FLOCK zerocheck, lincheck, ring-switch, and claim batching;
- VEIL dot-product and Hadamard binding;
- operand- and product-code proximity generation;
- Hadamard reduction and linkage;
- Secure-profile Ligerito whole-opening soundness.

The RS proximity terms use the finite-length unique-decoding backoff
`gamma = delta/2 - 3/(delta*N)` and union-bound every live binary fold. Fast
and Slim/list-decoding profiles are rejected by the production setup. The
pinned interactive aggregate is approximately 107 bits; the runtime returns
the exact computed value and fails closed below each component floor.

`rom_soundness_bound(Q, attempts)` additionally accounts for declared proof
attempts and oracle collisions. It is a classical-ROM statement and does not
turn SHA-256 into an information-theoretic primitive.

## Fail-closed relation and format

The verifier pins the exact circuit digest, mask count, witness layout, Secure
PCS profile, code geometry, query budget, and VEIL parameters. The canonical
bundle carries protocol, relation, and parameter-suite identifiers, has a
1 MiB decode limit, rejects trailing bytes, and rejects any identifier or
parameter mismatch.

No alternate or legacy ZK proof flavor is exported. The public ZK API is:

```text
Blake3PreimageZkSetup::new
Blake3PreimageZkSetup::prove
Blake3PreimageZkSetup::verify
Blake3PreimageZkSetup::simulate
```

## Operational caveats

The proof hides the messages and witness-dependent transcript, not batch
size, circuit shape, parameter suite, proof length, runtime, memory access,
allocator behavior, or host side channels. Independent cryptographic and
side-channel review remains required before production use.

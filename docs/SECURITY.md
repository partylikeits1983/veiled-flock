# Security target and scope

VEIL-FLOCK is a formally proved zero-knowledge protocol model for the pinned
64-byte BLAKE3-preimage relation in the classical programmable random-oracle
model (pROM), together with a corresponding Rust implementation. The Rust code
is kept aligned with the Lean model, but this repository does not yet contain a
mechanized correspondence proof from every executable Rust path to the model.
The implementation is unaudited; do not use it to protect production secrets.

## Target properties

| Property | Scope |
|---|---|
| Relation | Ordered batch of 1-4096 64-byte BLAKE3 preimages, padded to a registered 256/512/1024/2048/4096-slot shape |
| Completeness | Honest proofs verify |
| Zero knowledge | Proved for the finite Lean production model with distance `< 2^-126`; Rust correspondence not proved |
| Algebraic privacy | Perfect, conditioned on the public statement and accepted challenge history |
| Noninteractive privacy loss | Random-oracle prequery, collision, nonce-collision, and bounded-grinding events |
| Interactive soundness | Additive bound from FLOCK PIOP, VEIL constraints, and Secure Ligerito |
| Fiat--Shamir soundness | Classical-ROM assumption/reduction boundary |
| Argument of knowledge | Not claimed |
| QROM/post-quantum ZK | Not claimed |
| Concrete SHA-256 theorem | Not claimed; SHA-256 instantiates the modeled oracle |

Short batches are padded to a registered power-of-two shape before any
Fiat--Shamir challenge. The Rust checks bind that padding rule; a later
Lean/Rust correspondence proof should connect the padding adapter to the
exact-shape formal theorem.

## Lean formal theorem

`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126` proves that
every valid public statement and witness satisfying the pinned relation has a
real adaptive adversary view within `2^-126` statistical distance of a
witness-free simulated view in the finite classical pROM model.

The companion theorem
`VeiledFlock.ProductionFormalZK.productionSimulator_expected_polytime`
certifies the witness-free simulator under an explicit algebraic/pROM machine
cost model. These are theorems about the Lean production model; they are not a
mechanized proof that every Rust execution matches that model.

For `P` proofs, `J` programmed points per proof, and the implementation cap
`Q_P` on protocol oracle calls per proof, the executable conservative bound is

```text
P*J*Q_H/2^256
+ P*Q_P*Q_H/2^256
+ (Q_H + P*Q_P)^2/2^257
+ 4*P*(P-1)/2^257
+ P*((63/64)^8192 + 16*(31/32)^4096).
```

The terms respectively cover challenge prequeries, hidden initial-Merkle
inputs, oracle collisions, collisions in any of the four nonce domains (one
Fiat--Shamir proof nonce plus three initial-tree nonces), and failure of the
bounded outer or Ligerito grinds. `ClassicalPromZkBound` computes this sum.

The proved model requires fresh independent proof nonces, witness-code padding,
masking rows, PIOP masks, ring masks, VEIL padding, tree nonces, and leaf salts
for every proof. The API creates a fresh commitment for each proof; commitment
reuse is not an exposed operation. The public prover and simulator draw every
coin directly from the OS random source; caller-selected deterministic seeds
are not accepted by the public full-ZK API.

## Algebraic privacy chain

The Lean model discharges the following privacy chain, while the production
code enforces matching runtime checks. A mechanized Rust-to-model
correspondence proof remains future work:

1. The outer blinded additive-RS encoder is linear, restricts to ordinary
   FLOCK when its padding is zero, and has a query budget no larger than its
   random-padding dimension.
2. The structural RS argument says every opened initial coordinate projection
   has full padding rank. Repeated
   query positions are canonicalized and count once.
3. The nonzero VEIL fold coefficient makes the folded Ligerito input uniform in
   the formal model. Rust algebraic translation tests jointly cover the fold,
   initial opened columns, and public direct functionals.
4. At the 256-slot floor, the 242 FLOCK transcript coordinates and 512 ring
   coordinates consume 754 independent field one-time pads. Each circuit-size
   doubling adds two sumcheck coordinates and two independent pads, reaching
   762 pads at 4096 slots. The Lean `MaskLayout` and `ExactMaskTape` modules and
   the Rust prover/verifier all check this exact cursor and circuit inventory.
5. The exact F2-linear ring-switch matrix is checked against production field
   multiplication on all 128 basis vectors.
6. The live nonlinear multiplication is proved by VEIL Hadamard. Operand and
   product codes have separate ZK budgets; multiplicative containment and the
   reduction identity are tested on every basis pair.
7. One fresh witness commitment has exactly one batched opening. The manifest
   is fixed before batching challenges, claims are canonical, and the union of
   distinct initial queries stays within the padding budget.
8. After the uniform-fold boundary, recursive Ligerito is ordinary
   witness-independent post-processing. Recursive openings use the canonical
   unsalted Merkle domain; only the initial witness-dependent L0 opening carries
   leaf salts. No recursive-round-specific privacy assumption is needed.

The simulator samples honest-distribution challenges first, constructs the
masked FLOCK transcript algebraically, and programs the exact SHA-256 squeeze
blocks. It uses an arbitrary public-fiber representative only to evaluate
post-processing whose distribution is intended to be independent of the
original witness. It never invokes an honest nonlinear prover on an
unsatisfied assignment.

## Merkle and transcript hashing

All random-oracle inputs have injective typed framing. Leaf and internal-node
domains are disjoint. Each witness-dependent initial leaf contains a fresh
256-bit salt. The outer witness, VEIL linear, and VEIL Hadamard trees each use
an independently sampled 256-bit tree nonce and a distinct channel. All three
tree nonces are transcript-bound before the first PIOP challenge. Recursive
Ligerito trees are generated after the uniform-fold boundary and are verified
only in the unsalted domain; the verifier rejects non-empty recursive salts and
noncanonical recursive proof-vector lengths.

Fiat--Shamir sampling matches production block semantics: two `F128` values
share one 256-bit output where applicable, unused halves remain uniform, and
nonzero or not-zero-or-one challenges use exact rejection sampling. Outer
blinding grinding uses the canonical first-success nonce and accepts only the
first 8192 attempts. Every Ligerito query/fold grind nonce is limited to 4096;
the ledger conservatively reserves sixteen grind sites. At most three levels of
a registered full-ZK shape carry a positive fold grind, and such a shape emits
at most twelve fold-grind nonces. In slot order, the exact 256/512/1024/2048/
4096 schedules are `6×1`, `6×2 + 3×1`, `6×3 + 3×2`,
`6×4 + 3×3 + 3×1`, and `6×5 + 3×4 + 3×2` bits; the corresponding
preblinded L0 grinds use 2/3/4/5/6 bits.

The Secure profile is in the unique-decoding regime, where the fold-challenge
grind is flat: every fold round of a level grinds the full
`fold_grinding_bits`. The Johnson profiles taper the grind by one bit per fold
round, because their row-union factor makes each later round one bit stronger.
`LigeritoSecurityConfig::aggregate_soundness_bound` charges the worst-round
proximity error and the full grind in every round, so both regimes match the
ledger exactly.

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
bundle has a 1 MiB decode limit, rejects trailing bytes, and rejects any
parameter mismatch.

No alternate or legacy ZK proof flavor is exported. The public ZK API is:

```text
Blake3PreimageZkSetup::new
Blake3PreimageZkSetup::prove
Blake3PreimageZkSetup::verify
Blake3PreimageZkSetup::simulate
```

## Operational caveats

The construction is designed to hide the messages and witness-dependent
transcript, but not batch size, circuit shape, parameter suite, proof length,
runtime, memory access,
allocator behavior, or host side channels. Independent cryptographic and
side-channel review remains required before production use.

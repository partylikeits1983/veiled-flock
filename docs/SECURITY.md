# Security scope

VEIL-FLOCK has a Lean proof of statistical zero knowledge for a formal model
of the 64-byte BLAKE3-preimage protocol in the classical programmable
random-oracle model (pROM). The Rust code follows the same protocol, but is
not mechanically linked to the Lean model.

The Lean relation is broader than the Rust relation: it checks padded public
projection, while Rust also checks BLAKE3/R1CS satisfaction and computes public
constants. A mechanized Rust-to-Lean correspondence proof is not included. The
implementation is unaudited and should not be used for production secrets.

## Claims

| Property | Scope |
|---|---|
| Relation | Ordered batch of 1-4096 64-byte BLAKE3 preimages, padded to a registered 256/512/1024/2048/4096-slot shape |
| Completeness | Honest proofs verify |
| Zero knowledge | Proved for the finite Lean uniform coin model with distance `< 2^-126`; Rust correspondence and seeded XOF instantiation not proved |
| Algebraic privacy | Perfect in the formal uniform coin model, conditioned on the public statement and accepted challenge history |
| Noninteractive privacy loss | Random-oracle prequeries, collisions, nonce collisions, and bounded-grinding failures |
| Interactive soundness | Additive bound from FLOCK PIOP, VEIL constraints, and Secure Ligerito |
| Fiat-Shamir soundness | Classical-ROM assumption and reduction boundary |
| Argument of knowledge | Not claimed |
| QROM/post-quantum ZK | Not claimed |
| Concrete hash theorem | Not claimed; SHA-256 instantiates the modeled oracle and BLAKE3 XOF instantiates prover coin expansion |

Short batches are padded to a registered power-of-two shape before any
Fiat-Shamir challenge. The Lean statement model carries the unpadded digest
list, padding digest, and 32-byte transcript binding used by Rust. A future
correspondence proof still needs to show that Rust computes those values as
modeled.

## Lean theorem

`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126` proves that,
for every statement and witness satisfying the formal padded-public-projection
relation, the real adaptive adversary view is within `2^-126` statistical
distance of a witness-free simulated view in the finite classical pROM model.

Because the formal relation is broader than the Rust BLAKE3 relation, the
privacy result applies to the Rust relation once the missing correspondence
obligations are discharged.

Rust production provers sample a 32-byte OS seed and expand it with BLAKE3 XOF
for prover secret coins. This replaces direct OS sampling of every mask byte;
the concrete implementation therefore relies on the XOF as a PRG/ROM
instantiation, while the formal statistical ZK theorem still models those coins
as uniform.

The companion theorem
`VeiledFlock.ProductionFormalZK.productionSimulator_expected_polytime` gives an
explicit algebraic/pROM cost certificate for the simulator. It does not derive
runtime from Lean evaluation semantics and does not certify Rust runtime.

For `P` proofs, `J` programmed points per proof, and per-proof protocol oracle
budget `Q_P`, the accounting bound is:

```text
P*J*Q_H/2^256
+ P*Q_P*Q_H/2^256
+ (Q_H + P*Q_P)^2/2^257
+ 4*P*(P-1)/2^257
+ P*((63/64)^8192 + 16*(31/32)^4096)
```

The terms cover challenge prequeries, hidden initial-Merkle inputs, oracle
collisions, collisions in the four nonce domains, and bounded-grinding failure.
`ClassicalPromZkBound` computes this sum.

Every proof needs fresh proof nonces, randomizer witness rows, witness-code
padding, PIOP masks, ring masks, VEIL padding, tree nonces, and leaf salts. The
public full-ZK API draws a fresh OS seed for coin expansion and does not accept
caller-selected deterministic seeds.

## Privacy chain

The Lean model proves the privacy chain below. Rust enforces matching runtime
checks, but a mechanized Rust-to-model proof remains future work.

1. The outer blinded additive-RS encoder is linear, reduces to ordinary FLOCK
   when padding is zero, and opens no more positions than its random-padding
   dimension.
2. Every opened initial coordinate projection has full padding rank. Repeated
   query positions are canonicalized before counting.
3. The nonzero VEIL fold coefficient makes the folded Ligerito input uniform in
   the formal model. Rust tests cover the fold, initial opened columns, and
   public direct functionals together.
4. At the 256-slot floor, 242 FLOCK transcript coordinates and 512 ring
   coordinates consume 754 independent field one-time pads. The registered
   512/1024/2048/4096-slot shapes consume 756/758/760/762 pads.
5. The `GF(2)` ring-switch matrix is checked against field multiplication on
   all 128 basis vectors.
6. VEIL Hadamard proves the live nonlinear multiplication. Operand and product
   codes have separate ZK budgets; containment and reduction identities are
   tested on every basis pair.
7. Each proof uses one fresh witness commitment and one batched opening for AB,
   C, and the public digest functional. The manifest is fixed before batching
   challenges.
8. After the hiding fold, recursive Ligerito is witness-independent
   post-processing. Recursive openings use the unsalted Merkle domain; only the
   initial witness-dependent L0 opening carries leaf salts.

The simulator samples challenges from the honest distributions, builds the
masked FLOCK transcript algebraically, and programs the SHA-256 squeeze blocks.
It uses an arbitrary public-fiber representative only for post-processing whose
distribution is meant to be witness-independent. It does not run the honest
nonlinear prover on an unsatisfied assignment.

The formal Fiat-Shamir trace is literal through the statement, prelude,
zerocheck, and outer/VEIL sampling suffix. After the hiding fold, the formal
trace is a privacy ledger rather than the byte-for-byte Rust transcript:
witness-independent Ligerito roots, sumcheck messages, ordinary challenges,
and zero-bit grinds are omitted. `FormalVeilFlockProof.finalTranscript` should
be read in that sense.

## Hashing and grinding

Random-oracle inputs use typed framing. Leaf and internal-node domains are
separate. Each witness-dependent initial leaf has a fresh 256-bit salt. The
outer witness, VEIL-linear, and VEIL-Hadamard trees use independent 256-bit
tree nonces and distinct channels. Recursive Ligerito trees are generated after
the hiding fold and are verified only in the unsalted domain.

Fiat-Shamir sampling in the modeled prefix and suffix matches the production
block layout: two `F128` values can share one 256-bit output, unused halves
remain uniform, and rejection-sampled values keep rejected blocks in the
transcript.

Outer blinding grinding is modeled as first success within 8192 attempts. Each
positive Ligerito fold grind is modeled as first success within 4096 attempts,
with sixteen reserved grind sites. The Lean-backed registered schedules
currently checked into the repo are:

| Slots | Rust profile | Levels | Final `yr_log_n` |
|---:|---|---|---:|
| 256 | `m23_secure.toml` | `(1,10,6,294,1); (2,7,3,182,0); (4,4,3,137,0)` | 4 |
| 512 | `m24_secure.toml` | `(1,11,6,292,2); (2,8,3,180,1); (3,5,3,151,0)` | 5 |
| 1024 | `m25_secure.toml` | `(1,12,6,291,3); (2,9,3,179,2); (3,6,3,148,0); (5,3,3,131,0)` | 3 |
| 2048 | `m26_secure.toml` | `(1,13,6,290,4); (2,10,3,178,3); (3,7,3,147,1); (4,4,3,137,0)` | 4 |
| 4096 | `m27_secure.toml` | `(1,14,6,290,5); (2,11,3,178,4); (3,8,3,146,2); (4,5,3,134,0)` | 5 |

Each level tuple is
`(log_inv_rate, log_msg_cols, fold width, queries, fold_grinding_bits)`.
Query-phase grinding, tapering, and OOD sampling are zero in these profiles.

The Rust prover and simulator currently check returned grind nonces against
the caps, but some search and rejection loops are not bounded while they run.
The executable must enforce per-loop caps and the cumulative oracle-call budget
during execution before those values can be treated as deterministic
implementation bounds.

The public prove and verify methods instantiate the pinned SHA-256 transcript
domain internally; the test-only random challenger is not part of their API.

## Soundness

For a registered PCS, `Blake3PreimageZkSetup::interactive_soundness_bound()`
adds these errors:

- FLOCK zerocheck, lincheck, ring-switch, and claim batching
- VEIL dot-product and Hadamard binding
- operand- and product-code proximity generation
- Hadamard reduction and linkage
- Secure-profile Ligerito whole-opening soundness

The RS proximity terms use the finite-length unique-decoding backoff
`gamma = delta/2 - 3/(delta*N)` and union-bound every live binary fold. Fast
and Slim/list-decoding profiles are rejected by the full-ZK setup. Missing or
mismatched PCS registry entries fail closed instead of falling back to ad hoc
parameters.

`rom_soundness_bound(Q, attempts)` also accounts for proof attempts and oracle
collisions. It is a classical-ROM statement and does not make SHA-256
information-theoretic.

## Format and API

The verifier checks the circuit digest, mask count, witness layout, Secure PCS
profile marker, registered code geometry, query budget, and VEIL parameters.
The canonical bundle has a 1 MiB decode limit, rejects trailing bytes, and
rejects parameter mismatches.

No alternate or legacy ZK proof flavor is exported. The public ZK API is:

```text
Blake3PreimageZkSetup::new
Blake3PreimageZkSetup::prove
Blake3PreimageZkSetup::verify
Blake3PreimageZkSetup::simulate
```

## Operational caveats

The construction hides messages and witness-dependent transcript data. It does
not hide batch size, circuit shape, parameter suite, proof length, runtime,
memory access, allocator behavior, or host side channels. Independent
cryptographic and side-channel review is required before production use.

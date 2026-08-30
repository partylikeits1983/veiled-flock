# Security target and scope

VEIL-FLOCK is a formally proven zero-knowledge implementation of FLOCK using
VEIL for the pinned 64-byte BLAKE3-preimage relation in the classical
programmable random-oracle model (pROM). The Rust implementation has been kept
aligned with the Lean proof logic as closely as possible, but this repository
does not yet contain a mechanized correspondence proof that every Rust
execution path matches the Lean math 1:1. The implementation is unaudited; do
not use it to protect production secrets.

## Claim status

| Property | Current status |
|---|---|
| Exact 64-byte BLAKE3 relation | Implemented and differentially tested |
| Honest prove/verify completeness | Implemented and tested at batch 256 |
| Raw messages absent from proof types | Checked by serialization tests and code review |
| Mutation rejection | Tested for statement and major proof components |
| Public-input-only simulated acceptance | Implemented with one programmable oracle for Fiat--Shamir, PCS, and VEIL hashing |
| Distributional zero knowledge | Proved for the Lean formal production model with bound `< 2^-126`; Rust correspondence not proved |
| Composed adversarial soundness | Not proved; only component evidence and estimates |
| Argument of knowledge/extraction | Partial components exist; no active end-to-end theorem |
| Classical-ROM composition | Proved for the finite Lean formal model; concrete SHA-256 instantiation not proved |
| QROM security | Not claimed |

## Lean formal theorem

The Lean endpoint
`VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126` proves that,
for the formal production protocol model, every valid public statement and
witness satisfying the pinned relation has a real adversary view within
`2^-126` statistical distance of a witness-free simulated view. The adversary
is classical and adaptive, all coins are finite, and the oracle is the modeled
programmable random oracle.

The companion theorem
`VeiledFlock.ProductionFormalZK.productionSimulator_expected_polytime`
certifies the witness-free simulator by an explicit algebraic/pROM machine
cost model.

This is a formal proof of zero knowledge for FLOCK using VEIL in the Lean model.
The Rust implementation follows the Lean logic as closely as possible, but the
repository does not yet provide a 100% mechanized guarantee that Rust matches
the formal model 1:1.

## Active path

`Blake3PreimageZkSetup::prove_succinct` commits to a randomized witness, masks
the FLOCK PIOP transcript, and proves the shifted verifier with `veil-f128`.
Verification checks the shifted circuit, hiding PCS opening, and public digest
claim. The proof type omits messages, witness values, masks, and private
padding. It includes public digests, masked messages, evaluation claims,
commitments, openings, and the VEIL certificate.

## Simulator boundary

`simulate_succinct` accepts public digests without a preimage and produces a
proof accepted by the generic verifier. Fiat--Shamir, PCS, and inner VEIL
hashing all query the same programmable oracle under disjoint encodings. This
executable check does not prove that simulated and real transcripts have the
same distribution.

## Input bounds

The CLI accepts at most 256 public digests and decodes proof bundles with a
640 KiB resource limit. The limit is enforced while reading and by the bincode
decoder before proof vectors are constructed.

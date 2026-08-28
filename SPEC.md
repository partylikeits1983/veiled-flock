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

## 15. Diagrams

This section is informative. It describes the code, not the protocol.
Sections 1 to 14 hold the normative rules.

The section has three groups. Subsections 15.1 to 15.8 hold sequence
diagrams for `flock-core`, `veil-f128`, and `flock-prover`. Subsections 15.9
to 15.13 hold class diagrams. Subsection 15.14 lists omissions and
deviations.

Legend for the sequence diagrams: each lane pipe holds a fixed column on
every row. A `*` marks a call that stays inside its own lane. An arrowhead
lands one column short of the target lane, so no pipe is erased. An `Err`
row marks an early return; no later message follows it.

Legend for the class diagrams:

| Edge | Meaning |
|---|---|
| `A ---> B` | A uses or calls B |
| `A ---\|> T` | A implements trait T |
| `A *--- B` | A owns B by value |
| `A o--- B` | A holds a reference to B |
| `A ..> B` | A converts into or produces B |

`+` and `-` show the Rust visibility of a member. A private field with a
`pub fn` accessor shows `-` for the field and `+` for the accessor. Free
functions are not methods, so they appear in the anchors tables only.

Anchors have the form `crates/<crate>/src/<file>.rs:LINE`. An anchor points
at a definition. The suffix `(call site)` marks a call. The text `same as N`
repeats the anchor of message N.

### 15.1 flock-core prover

`flock-core` owns the FLOCK PIOP, the PCS, the Merkle and random-oracle
layers, the transcript, and the verifier. It depends on no sibling crate. It
has no internal orchestrator. The driver imposes the order of `zerocheck`,
`lincheck`, and `pcs`.

| Lane | Symbol | Anchor |
|---|---|---|
| `caller` | `prove_succinct_veil_r1cs` (the driver) | `crates/flock-prover/src/succinct_veil.rs:596` |
| `r1cs` | `BlockR1cs` | `crates/flock-core/src/r1cs.rs:56` |
| `ZC` | `zerocheck::prove_packed_padded_capture_s_hat_v_c` | `crates/flock-core/src/zerocheck.rs:406` |
| `LC` | `lincheck::prove_padded_capture_z_vec` | `crates/flock-core/src/lincheck.rs:1250` |
| `PCS` | `pcs::commit::commit_zk_with_ro` and `pcs::open_batch_*` | `crates/flock-core/src/pcs/commit.rs:286` |
| `CH` | `Challenger` | `crates/flock-core/src/challenger.rs:30` |

```text
  caller  r1cs    ZC      LC      PCS     CH
  |       |       |       |       |       |
  |------------------------------>|       |     1 commit_zk_with_ro
  |-------------------------------------->|     2 bind_statement (ends by observing commitment.root)
  |-------------------------------------->|     3 observe_label + observe_bytes (VEIL mask root)
  |------>|       |       |       |       |     4 padding_spec
  |-------------->|       |       |       |     5 prove_packed_padded_capture_s_hat_v_c
  |       |       |*      |       |       |     6 univariate-skip round 1 (skip branch)
  |       |       |---------------------->|     7 observe_f128_slice (round poly)
  |       |       |<----------------------|     8 sample_f128 (round challenge)
  |<--------------|       |       |       |     9 ZerocheckClaim
  |------>|       |       |       |       |     10 x_ab_from_mlv
  |---------------------->|       |       |     11 prove_padded_capture_z_vec
  |       |       |       |-------------->|     12 observe_f128_slice (round poly)
  |       |       |       |<--------------|     13 sample_f128 (round challenge)
  |<----------------------|       |       |     14 LincheckClaim + z_vec
  |------------------------------>|       |     15 open_batch_..._s_hat_v_ro
  |<------------------------------|       |     16 BatchOpeningProofLigerito
```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `pcs::commit::commit_zk_with_ro` | `crates/flock-core/src/pcs/commit.rs:286` |
| 2 | `bind_statement`; its last step is `observe_bytes(&commitment.root)` at `crates/flock-core/src/proof.rs:60` | `crates/flock-core/src/proof.rs:51` |
| 3 | `Challenger::observe_label`, then `observe_bytes`; `crates/flock-prover/src/succinct_veil.rs:642` (call site) | `crates/flock-core/src/challenger.rs:34` |
| 4 | `BlockR1cs::padding_spec` | `crates/flock-core/src/r1cs.rs:235` |
| 5 | `zerocheck::prove_packed_padded_capture_s_hat_v_c` | `crates/flock-core/src/zerocheck.rs:406` |
| 6 | `univariate_skip::build_eq`; entry at `crates/flock-core/src/zerocheck.rs:118` | `crates/flock-core/src/zerocheck/univariate_skip.rs:31` |
| 7 | `Challenger::observe_f128_slice` | `crates/flock-core/src/challenger.rs:42` |
| 8 | `Challenger::sample_f128` | `crates/flock-core/src/challenger.rs:54` |
| 9 | `ZerocheckClaim` | `crates/flock-core/src/zerocheck.rs:293` |
| 10 | `BlockR1cs::x_ab_from_mlv` | `crates/flock-core/src/r1cs.rs:253` |
| 11 | `lincheck::prove_padded_capture_z_vec` | `crates/flock-core/src/lincheck.rs:1250` |
| 12 | return of message 7 | same as 7 |
| 13 | return of message 8 | same as 8 |
| 14 | `LincheckClaim` | `crates/flock-core/src/lincheck.rs:394` |
| 15 | `pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v_ro` | `crates/flock-core/src/pcs.rs:165` |
| 16 | `pcs::BatchOpeningProofLigerito` | `crates/flock-core/src/pcs.rs:51` |

Message 6 is a branch on the skip parameter, not a separate protocol. Small
instances take the multilinear path in
`crates/flock-core/src/zerocheck/multilinear.rs`. Subsection 15.14 lists the
four skip modules and their anchors.

### 15.2 flock-core verifier

The verifier mirrors 15.1. It replays `bind_statement` first, then each
sub-protocol replays its own rounds. A different absorb order derives
different challenges, and the verifier rejects.

| Lane | Symbol | Anchor |
|---|---|---|
| `caller` | the driver | `crates/flock-core/src/verifier.rs:60` |
| `VC` | `verifier::verify_core` | `crates/flock-core/src/verifier.rs:288` |
| `ZC` | `zerocheck::verify` | `crates/flock-core/src/zerocheck.rs:687` |
| `LC` | `lincheck::verify` | `crates/flock-core/src/lincheck.rs:1551` |
| `PCS` | `pcs::verify_opening_batch_ligerito_mixed_ro` | `crates/flock-core/src/pcs.rs:848` |
| `CH` | `Challenger` | `crates/flock-core/src/challenger.rs:30` |

```text
  caller  VC      ZC      LC      PCS     CH
  |       |       |       |       |       |
  |------>|       |       |       |       |     1 verify_core
  |       |------------------------------>|     2 bind_statement
  |       |------>|       |       |       |     3 zerocheck::verify
  |       |       |---------------------->|     4 observe / sample (replayed)
  |       |<------|       |       |       |     5 Err(VerifyError::Zerocheck) -> abort
  |       |<------|       |       |       |     6 ZerocheckClaim
  |       |*      |       |       |       |     7 x_ab_from_mlv
  |       |-------------->|       |       |     8 lincheck::verify
  |       |<--------------|       |       |     9 Err(VerifyError::Lincheck) -> abort
  |       |<--------------|       |       |     10 LincheckClaim
  |<------|       |       |       |       |     11 Ok((ab, c))
  |------------------------------>|       |     12 verify_opening_batch_ligerito_mixed_ro
  |<------------------------------|       |     13 Err(pcs::VerifyError) or Ok
```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `verifier::verify_core` | `crates/flock-core/src/verifier.rs:288` |
| 2 | `bind_statement`, called from `verify_core` | `crates/flock-core/src/proof.rs:51` |
| 3 | `zerocheck::verify` | `crates/flock-core/src/zerocheck.rs:687` |
| 4 | `Challenger::observe_f128_slice` and `Challenger::sample_f128` | `crates/flock-core/src/challenger.rs:42` |
| 5 | `zerocheck::VerifyError` | `crates/flock-core/src/zerocheck.rs:331` |
| 6 | `ZerocheckClaim` | `crates/flock-core/src/zerocheck.rs:293` |
| 7 | `BlockR1cs::x_ab_from_mlv` | `crates/flock-core/src/r1cs.rs:253` |
| 8 | `lincheck::verify` | `crates/flock-core/src/lincheck.rs:1551` |
| 9 | `lincheck::VerifyError` | `crates/flock-core/src/lincheck.rs:478` |
| 10 | `LincheckClaim` | `crates/flock-core/src/lincheck.rs:394` |
| 11 | return of message 1 | same as 1 |
| 12 | `pcs::verify_opening_batch_ligerito_mixed_ro` | `crates/flock-core/src/pcs.rs:848` |
| 13 | `pcs::VerifyError` | `crates/flock-core/src/pcs.rs:71` |

### 15.3 flock-core PCS internals

This diagram expands the `PCS` lane of 15.1.

| Lane | Symbol | Anchor |
|---|---|---|
| `call` | the driver; entry points `crates/flock-core/src/pcs/commit.rs:286` and `crates/flock-core/src/pcs.rs:165` | `crates/flock-prover/src/succinct_veil.rs:596` |
| `cmt` | `pcs::commit` | `crates/flock-core/src/pcs/commit.rs:286` |
| `rsw` | `pcs::ring_switch` | `crates/flock-core/src/pcs/ring_switch.rs:2298` |
| `lig` | `pcs::ligerito` | `crates/flock-core/src/pcs/ligerito.rs:3068` |
| `mrk` | `merkle` | `crates/flock-core/src/merkle.rs:288` |
| `ro` | `ro::RoContext` | `crates/flock-core/src/ro.rs:83` |

```text
  call    cmt     rsw     lig     mrk     ro
  |       |       |       |       |       |
  |------>|       |       |       |       |      1 commit_zk_with_ro
  |       |*      |       |       |       |      2 replicate_message_fill_zk
  |       |*      |       |       |       |      3 finalize_commit (interleaved NTT encode)
  |       |---------------------->|       |      4 merkle_tree_framed
  |       |       |       |       |------>|      5 RoContext + RoChannel separation
  |<------|       |       |       |       |      6 Commitment + ProverData
  |-------------->|       |       |       |      7 prove_batched_padded_with_precomputed
  |<--------------|       |       |       |      8 RingSwitchProof + s_hat_v
  |---------------------->|       |       |      9 recursive_prover_..._round0_zk_with_ro
  |       |       |       |------>|       |      10 merkle_tree_framed (per round)
  |       |       |       |------>|       |      11 merkle_multi_proof (queries)
  |<----------------------|       |       |      12 LigeritoProof + ZkBlindOpening
```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `pcs::commit::commit_zk_with_ro` | `crates/flock-core/src/pcs/commit.rs:286` |
| 2 | `replicate_message_fill_zk`; `crates/flock-core/src/pcs/commit.rs:304` (call site) | `crates/flock-core/src/pcs/commit.rs:286` |
| 3 | `finalize_commit`, the private tail of every commit path; `crates/flock-core/src/pcs/commit.rs:305` (call site) | `crates/flock-core/src/pcs/commit.rs:377` |
| 4 | `merkle::merkle_tree_framed` | `crates/flock-core/src/merkle.rs:288` |
| 5 | `ro::RoContext` | `crates/flock-core/src/ro.rs:83` |
| 6 | `pcs::commit::Commitment` and `pcs::commit::ProverData` | `crates/flock-core/src/pcs/commit.rs:123` |
| 7 | `ring_switch::prove_batched_padded_with_precomputed`; `crates/flock-core/src/pcs.rs:436` (call site) | `crates/flock-core/src/pcs/ring_switch.rs:2298` |
| 8 | `RingSwitchProof`, re-exported at `crates/flock-core/src/pcs.rs:40` | `crates/flock-core/src/pcs/ring_switch.rs:2034` |
| 9 | `ligerito::recursive_prover_with_basis_precomputed_round0_zk_with_ro`, the zk twin | `crates/flock-core/src/pcs/ligerito.rs:3068` |
| 10 | `merkle::merkle_tree_framed`; `crates/flock-core/src/pcs/ligerito.rs:2375` (call site) | `crates/flock-core/src/merkle.rs:288` |
| 11 | `merkle::merkle_multi_proof`; `crates/flock-core/src/pcs/ligerito.rs:2826` (call site) | `crates/flock-core/src/merkle.rs:705` |
| 12 | `pcs::ZkBlindOpening` | `crates/flock-core/src/pcs.rs:65` |

The non-zk twin of message 3, `commit_into_with_ro`
(`crates/flock-core/src/pcs/commit.rs:229`), is not on this path. The non-zk
twin of message 9,
`recursive_prover_with_basis_precomputed_round0_with_ro`
(`crates/flock-core/src/pcs/ligerito.rs:3138`), is not on this path.
`pcs::pack::pack_witness` (`crates/flock-core/src/pcs/pack.rs:40`) is not
on the succinct path; the witness arrives packed, and the only non-test
caller is `crates/flock-prover/src/prover.rs:866`.

`merkle` selects a kernel at compile time from
`crates/flock-core/src/merkle/aarch64.rs` and
`crates/flock-core/src/merkle/x86_64.rs`. The `_framed` variants carry an
`RoContext` and an `RoChannel` for domain separation. The unframed twins
serve the non-zk paths, and a wrong choice changes the hash domain.

### 15.4 veil-f128 masked transcript

`veil-f128` is the native GF(2^128) VEIL backend. It proves that a masked
FLOCK verifier transcript, expressed as an arithmetic circuit, is satisfied.
It depends only on `flock-core` with `features = ["zk"]`. It re-exports
`F128` at `crates/veil-f128/src/lib.rs:32`. Upstream VEIL needs a two-adic
multiplicative subgroup, and GF(2^128) has none. `AdditiveRsCode` supplies
an additive-domain code instead; see `docs/DECISIONS.md` D002.

The flow has two phases. `commit_constraint_inputs` (messages 1 to 8)
commits before any challenge exists. `prove_constraints_from_commitment`
(messages 9 to 22) runs the reduction against that commitment. The split
lets the caller bind the commitment root into an outer transcript first.

| Lane | Symbol | Anchor |
|---|---|---|
| `call` | `prove_succinct_veil_r1cs` (the driver) | `crates/flock-prover/src/succinct_veil.rs:596` |
| `cons` | `constraints` | `crates/veil-f128/src/constraints.rs:418` |
| `dot` | `dot_product` | `crates/veil-f128/src/dot_product.rs:131` |
| `had` | `hadamard` | `crates/veil-f128/src/hadamard.rs:75` |
| `code` | `AdditiveRsCode` | `crates/veil-f128/src/code.rs:95` |
| `ntt` | `AdditiveCosetNtt` | `crates/veil-f128/src/ntt.rs:167` |
| `cmt` | `MerkleMatrix` | `crates/veil-f128/src/commitment.rs:14` |
| `CH` | `Challenger` (from `flock-core`) | `crates/flock-core/src/challenger.rs:30` |

```text
  call  cons  dot   had   code  ntt   cmt   CH
  |     |     |     |     |     |     |     |
  |---->|     |     |     |     |     |     |     1 commit_constraint_inputs
  |     |*    |     |     |     |     |     |     2 parameters.validate + shape checks
  |     |*    |     |     |     |     |     |     3 rng.fill_f128 -> [r, s, t] padding
  |     |---->|     |     |     |     |     |     4 commit_vectors
  |     |     |---------->|     |     |     |     5 encode_batch
  |     |     |     |     |---->|     |     |     6 forward / inverse
  |     |     |---------------------->|     |     7 MerkleMatrix::new
  |<----|     |     |     |     |     |     |     8 ConstraintCommitment
  |---->|     |     |     |     |     |     |     9 prove_constraints_from_commitment
  |     |*    |     |     |     |     |     |     10 padded_circuit + is_satisfied
  |     |---------------------------------->|     11 observe_label + observe_bytes(root)
  |     |*    |     |     |     |     |     |     12 multiplication_vectors
  |     |---------->|     |     |     |     |     13 commit_hadamard
  |     |     |     |---->|     |     |     |     14 encode_square (square code)
  |     |     |     |---------------->|     |     15 MerkleMatrix::new
  |     |---------------------------------->|     16 observe_bytes(hadamard root)
  |     |<----------------------------------|     17 sample_f128 x2 (mult + constraint rlc)
  |     |---------->|     |     |     |     |     18 prove_hadamard_and_dots
  |     |     |     |---------------->|     |     19 MerkleMatrix::open
  |     |---->|     |     |     |     |     |     20 prove_dot_product (linear)
  |     |     |---------------------->|     |     21 MerkleMatrix::open
  |<----|     |     |     |     |     |     |     22 ConstraintProof
```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `commit_constraint_inputs` | `crates/veil-f128/src/constraints.rs:418` |
| 2 | `ConstraintParameters::validate`; `crates/veil-f128/src/constraints.rs:424` (call site) | `crates/veil-f128/src/constraints.rs:304` |
| 3 | `MaskSampler::fill_f128`; `crates/veil-f128/src/constraints.rs:441` (call site) | `crates/flock-core/src/zk.rs:36` |
| 4 | `commit_vectors`, the unframed entry point | `crates/veil-f128/src/dot_product.rs:131` |
| 5 | `AdditiveRsCode::encode_batch` | `crates/veil-f128/src/code.rs:144` |
| 6 | `AdditiveCosetNtt::forward` | `crates/veil-f128/src/ntt.rs:196` |
| 7 | `MerkleMatrix::new`; `commit_vectors` resolves `framed = None` | `crates/veil-f128/src/commitment.rs:29` |
| 8 | `ConstraintCommitment`; constructed at `crates/veil-f128/src/constraints.rs:458` | `crates/veil-f128/src/constraints.rs:290` |
| 9 | `prove_constraints_from_commitment` | `crates/veil-f128/src/constraints.rs:468` |
| 10 | `padded_circuit`; `crates/veil-f128/src/constraints.rs:487` (call site); `ArithmeticCircuit::is_satisfied` at `crates/veil-f128/src/constraints.rs:483` | `crates/veil-f128/src/constraints.rs:596` |
| 11 | `Challenger::observe_label`, then `observe_bytes`; `crates/veil-f128/src/constraints.rs:500` (call site) | `crates/flock-core/src/challenger.rs:34` |
| 12 | `multiplication_vectors` | `crates/veil-f128/src/constraints.rs:631` |
| 13 | `commit_hadamard`, the unframed entry point | `crates/veil-f128/src/hadamard.rs:75` |
| 14 | `AdditiveRsCode::encode_square` | `crates/veil-f128/src/code.rs:162` |
| 15 | `MerkleMatrix::new` | `crates/veil-f128/src/commitment.rs:29` |
| 16 | `Challenger::observe_bytes`; `crates/veil-f128/src/constraints.rs:513` (call site) | `crates/flock-core/src/challenger.rs:49` |
| 17 | `Challenger::sample_f128`, twice: `multiplication_rlc` at `crates/veil-f128/src/constraints.rs:514`, `constraint_rlc` at `crates/veil-f128/src/constraints.rs:522` | `crates/flock-core/src/challenger.rs:54` |
| 18 | `prove_hadamard_and_dots` | `crates/veil-f128/src/hadamard.rs:151` |
| 19 | `MerkleMatrix::open` | `crates/veil-f128/src/commitment.rs:84` |
| 20 | `prove_dot_product` | `crates/veil-f128/src/dot_product.rs:199` |
| 21 | return of message 19 | same as 19 |
| 22 | `ConstraintProof` | `crates/veil-f128/src/constraints.rs:277` |

The verifier mirror is `verify_constraints`
(`crates/veil-f128/src/constraints.rs:539`). It uses
`verify_hadamard_and_dots_framed` (`crates/veil-f128/src/hadamard.rs:244`)
and `verify_dot_product_framed` (`crates/veil-f128/src/dot_product.rs:276`).
The block-R1CS entry points `prove_block_r1cs_framed`
(`crates/veil-f128/src/block_r1cs.rs:118`) and `verify_block_r1cs_framed`
(`crates/veil-f128/src/block_r1cs.rs:261`) are not on the succinct path.

This path commits unframed. Messages 7 and 15 use `MerkleMatrix::new`
(`crates/veil-f128/src/commitment.rs:29`), not `new_framed`
(`crates/veil-f128/src/commitment.rs:33`). Message 5 produces base codewords,
and message 14 produces the square code. `crates/veil-f128/src/ntt.rs` is a
separate NTT with two disjoint domains, and it is slower by design. Only
`CodeError` implements `Display` and `std::error::Error`
(`crates/veil-f128/src/code.rs:66`).

### 15.5 veil-f128 simulator

The simulator produces a transcript without a witness. It samples in the
same order as the prover.

| Lane | Symbol | Anchor |
|---|---|---|
| `call` | the driver | `crates/veil-f128/src/simulator.rs:60` |
| `sim` | `simulate_block_r1cs` | `crates/veil-f128/src/simulator.rs:60` |
| `prog` | `OracleProgrammer` | `crates/veil-f128/src/simulator.rs:32` |
| `had` | `simulate_hadamard` | `crates/veil-f128/src/simulator.rs:193` |
| `code` | `AdditiveRsCode` | `crates/veil-f128/src/code.rs:95` |
| `CH` | `Challenger` | `crates/flock-core/src/challenger.rs:30` |

```text
  call  sim   prog  had   code  CH
  |     |     |     |     |     |
  |---->|     |     |     |     |     1 simulate_block_r1cs
  |     |*    |     |     |     |     2 validate_public + vector_parameters
  |     |*    |     |     |     |     3 random_hash (roots, no witness)
  |     |---------------------->|     4 observe_bytes (fake roots)
  |     |<----------------------|     5 sample_not_zero_or_one
  |     |*    |     |     |     |     6 powers -> dot_vector
  |     |---------->|     |     |     7 simulate_hadamard
  |     |     |<----|     |     |     8 program oracle answers
  |     |     |---->|     |     |     9 Err(OracleProgrammingError) -> abort
  |     |     |     |---->|     |     10 decode_square / square_to_base
  |     |*    |     |     |     |     11 simulate_dot_product
  |<----|     |     |     |     |     12 BlockR1csProof (indistinguishable)

```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `simulate_block_r1cs` | `crates/veil-f128/src/simulator.rs:60` |
| 2 | `validate_public` at `crates/veil-f128/src/block_r1cs.rs:353`; `vector_parameters` | `crates/veil-f128/src/block_r1cs.rs:327` |
| 3 | `random_hash` | `crates/veil-f128/src/simulator.rs:384` |
| 4 | `Challenger::observe_bytes` | `crates/flock-core/src/challenger.rs:49` |
| 5 | `sample_not_zero_or_one`, a `pub(crate)` helper of `block_r1cs` | `crates/veil-f128/src/block_r1cs.rs:452` |
| 6 | `powers`, a `pub(crate)` helper of `block_r1cs` | `crates/veil-f128/src/block_r1cs.rs:438` |
| 7 | `simulate_hadamard` | `crates/veil-f128/src/simulator.rs:193` |
| 8 | `OracleProgrammer` | `crates/veil-f128/src/simulator.rs:32` |
| 9 | `OracleProgrammingError` | `crates/veil-f128/src/simulator.rs:37` |
| 10 | `AdditiveRsCode::decode_square` at `crates/veil-f128/src/code.rs:153`; `AdditiveRsCode::square_to_base` | `crates/veil-f128/src/code.rs:179` |
| 11 | `simulate_dot_product` | `crates/veil-f128/src/simulator.rs:120` |
| 12 | `BlockR1csProof` | `crates/veil-f128/src/block_r1cs.rs:68` |

The simulator calls `pub(crate)` helpers of `block_r1cs`:
`build_link_claim` (`crates/veil-f128/src/block_r1cs.rs:366`), `powers`,
`sample_not_zero_or_one`, `validate_public`, and `vector_parameters`. This
dependency is intentional. A simulator with a different sample order is
unsound.

### 15.6 flock-prover prove

`flock-prover` is the top tier. It holds the two binaries, the R1CS hash
circuits, proof I/O, the succinct VEIL glue, and the ZK certificate. It
re-exports `flock-core` at `crates/flock-prover/src/lib.rs:15`. It depends on
`veil-f128` only under the `veil` feature. The active statement is
`Blake3PreimageZkSetup` at
`crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:413`. Its entry
points are `prove_succinct`, `verify_succinct`, and `simulate_succinct`.

| Lane | Symbol | Anchor |
|---|---|---|
| `CLI` | `veiled_flock::prove` | `crates/flock-prover/src/bin/veiled_flock.rs:117` |
| `SETUP` | `Blake3PreimageZkSetup` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:413` |
| `WIT` | `generate_witness_with_ab_packed_and_lincheck_zk_pinned` | `crates/flock-prover/src/r1cs_hashes/blake3.rs:1545` |
| `SV` | `prove_succinct_veil_r1cs` | `crates/flock-prover/src/succinct_veil.rs:596` |
| `CORE` | `flock_core` crate root; `pcs` at `:27`, `lincheck` at `:24`, `zerocheck` at `:36` | `crates/flock-core/src/lib.rs:1` |
| `VEIL` | `veil_f128::constraints` | `crates/veil-f128/src/constraints.rs:1` |

```text
  CLI    SETUP  WIT    SV     CORE   VEIL
  |      |      |      |      |      |
  |----->|      |      |      |      |     1 prove_succinct
  |      |*     |      |      |      |     2 statement
  |      |----->|      |      |      |     3 generate_witness_with_ab_packed_and_lincheck_zk_pinned
  |      |<-----|      |      |      |     4 (z, a, b, z_lincheck)
  |      |------------------->|      |     5 absorb_statement
  |      |------------>|      |      |     6 prove_succinct_veil_r1cs
  |      |      |      |*     |      |     7 MaskLayout::new
  |      |      |      |------------>|     8 commit_constraint_inputs
  |      |      |      |----->|      |     9 commit_zk_with_ro
  |      |      |      |----->|      |     10 bind_statement
  |      |      |      |----->|      |     11 prove_packed_padded_capture_s_hat_v_c
  |      |      |      |----->|      |     12 prove_padded_capture_z_vec
  |      |      |      |*     |      |     13 mask_proofs
  |      |      |      |*     |      |     14 shifted_verifier_circuit
  |      |      |      |*     |      |     15 fork veil_challenger
  |      |      |      |----->|      |     16 open_claims_with_precomputed_ligerito_pd_ro
  |      |      |      |------------>|     17 prove_constraints_from_commitment
  |      |<------------|      |      |     18 SuccinctVeilProof
  |<-----|      |      |      |      |     19 (SuccinctVeilProof, Commitment)
  |*     |      |      |      |      |     20 Bundle encode and write
```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `Blake3PreimageZkSetup::prove_succinct` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:528` |
| 2 | `Blake3PreimageZkSetup::statement` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:509` |
| 3 | `generate_witness_with_ab_packed_and_lincheck_zk_pinned` | `crates/flock-prover/src/r1cs_hashes/blake3.rs:1545` |
| 4 | return of message 3 | same as 3 |
| 5 | `absorb_statement`, the active path; the legacy twin is `crates/flock-prover/src/veiled_preimage.rs:347` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:896` |
| 6 | `prove_succinct_veil_r1cs` | `crates/flock-prover/src/succinct_veil.rs:596` |
| 7 | `MaskLayout::new` | `crates/flock-prover/src/succinct_veil.rs:613` (call site) |
| 8 | `commit_constraint_inputs`; `crates/flock-prover/src/succinct_veil.rs:622` (call site) | `crates/veil-f128/src/constraints.rs:418` |
| 9 | `pcs::commit::commit_zk_with_ro`; `crates/flock-prover/src/succinct_veil.rs:633` (call site) | `crates/flock-core/src/pcs/commit.rs:286` |
| 10 | `bind_statement`; `crates/flock-prover/src/succinct_veil.rs:641` (call site) | `crates/flock-core/src/proof.rs:51` |
| 11 | `zerocheck::prove_packed_padded_capture_s_hat_v_c`; `crates/flock-prover/src/succinct_veil.rs:680` (call site) | `crates/flock-core/src/zerocheck.rs:406` |
| 12 | `lincheck::prove_padded_capture_z_vec`; `crates/flock-prover/src/succinct_veil.rs:708` (call site) | `crates/flock-core/src/lincheck.rs:1250` |
| 13 | `mask_proofs`; `crates/flock-prover/src/succinct_veil.rs:735` (call site) | `crates/flock-prover/src/succinct_veil.rs:382` |
| 14 | `shifted_verifier_circuit`; `crates/flock-prover/src/succinct_veil.rs:738` (call site) | `crates/flock-prover/src/succinct_veil.rs:456` |
| 15 | `veil_challenger` fork, before the terminal Ligerito protocol | `crates/flock-prover/src/succinct_veil.rs:764` (call site) |
| 16 | `open_claims_with_precomputed_ligerito_pd_ro`; `crates/flock-prover/src/succinct_veil.rs:774` (call site) | `crates/flock-prover/src/prover.rs:114` |
| 17 | `prove_constraints_from_commitment`; `crates/flock-prover/src/succinct_veil.rs:787` (call site); consumes the commitment of message 8 | `crates/veil-f128/src/constraints.rs:468` |
| 18 | `SuccinctVeilProof` | `crates/flock-prover/src/succinct_veil.rs:33` |
| 19 | return of message 1 | same as 1 |
| 20 | `Bundle` | `crates/flock-prover/src/bin/veiled_flock.rs:18` |

Message 20 is the write side of `proof_io`. The helpers are
`write_bytes_to_file` (`crates/flock-prover/src/proof_io.rs:264`) and
`read_bytes_from_file` (`crates/flock-prover/src/proof_io.rs:280`). The
`veiled_flock` binary has its own `Bundle` encoder with magic `VFLK0003`
(`crates/flock-prover/src/bin/veiled_flock.rs:15`).

The `pd` argument of message 16 is produced between messages 14 and 15.
`observe_claims` runs at `crates/flock-prover/src/succinct_veil.rs:758`, and
`packed_direct` runs at `crates/flock-prover/src/succinct_veil.rs:759`.
Message 16 consumes `pd` at `crates/flock-prover/src/succinct_veil.rs:780`.
`packed_direct` is a closure from the caller, declared at
`crates/flock-prover/src/succinct_veil.rs:606`, so it has no lane.

`absorb_statement` exists twice: the active one at
`crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:896` and the legacy
one at `crates/flock-prover/src/veiled_preimage.rs:347`. An unqualified
reference resolves to the module in scope. `crates/flock-prover/src/prover.rs`
is the orchestration hub; 16 of the 30 source files reference `prover::`.
New protocol glue belongs there, not in a binary.

### 15.7 flock-prover verify

| Lane | Symbol | Anchor |
|---|---|---|
| `CLI` | `veiled_flock::verify` | `crates/flock-prover/src/bin/veiled_flock.rs:138` |
| `SETUP` | `Blake3PreimageZkSetup::verify_succinct` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:597` |
| `SV` | `verify_succinct_veil_r1cs` | `crates/flock-prover/src/succinct_veil.rs:808` |
| `CORE` | `flock_core::verifier` | `crates/flock-core/src/verifier.rs:199` |
| `VEIL` | `veil_f128::constraints::verify_constraints` | `crates/veil-f128/src/constraints.rs:539` |

```text
  CLI    SETUP  SV     CORE   VEIL
  |      |      |      |      |
  |*     |      |      |      |     1 read bundle + magic VFLK0003 check
  |*     |      |      |      |     2 re-serialize and byte-compare (canonicality)
  |----->|      |      |      |     3 verify_succinct
  |      |*     |      |      |     4 statement + validate
  |      |------------>|      |     5 absorb_statement
  |      |----->|      |      |     6 verify_succinct_veil_r1cs
  |      |      |*     |      |     7 parameter check -> InvalidParameters
  |      |      |----->|      |     8 bind_statement
  |      |      |----->|      |     9 observe_label + observe_bytes(mask root)
  |      |      |*     |      |     10 shifted_verifier_circuit (re-derived)
  |      |      |*     |      |     11 observe_claims + packed_direct
  |      |      |*     |      |     12 fork veil_challenger
  |      |      |----->|      |     13 verify_claims_ligerito_with_config_pd_ro
  |      |      |<-----|      |     14 Err(pcs::VerifyError) -> abort
  |      |      |------------>|     15 verify_constraints
  |      |      |<------------|     16 Err(ConstraintError) -> abort
  |<------------|      |      |     17 Ok(())
```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `MAGIC` = `VFLK0003` | `crates/flock-prover/src/bin/veiled_flock.rs:15` |
| 2 | `Bundle`; re-serialized and compared byte for byte | `crates/flock-prover/src/bin/veiled_flock.rs:18` |
| 3 | `Blake3PreimageZkSetup::verify_succinct` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:597` |
| 4 | `Blake3PreimageZkSetup::statement` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:509` |
| 5 | `absorb_statement` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:896` |
| 6 | `verify_succinct_veil_r1cs` | `crates/flock-prover/src/succinct_veil.rs:808` |
| 7 | `SuccinctVeilError::InvalidParameters` | `crates/flock-prover/src/succinct_veil.rs:48` |
| 8 | `bind_statement` | `crates/flock-core/src/proof.rs:51` |
| 9 | `Challenger::observe_label` | `crates/flock-core/src/challenger.rs:34` |
| 10 | `shifted_verifier_circuit` | `crates/flock-prover/src/succinct_veil.rs:456` |
| 11 | `pcs::PackedDirectClaimRef` | `crates/flock-core/src/pcs.rs:804` |
| 12 | `veil_challenger` fork; mirrors message 15 of 15.6 | `crates/flock-prover/src/succinct_veil.rs:764` |
| 13 | `verifier::verify_claims_ligerito_with_config_pd_ro` | `crates/flock-core/src/verifier.rs:199` |
| 14 | `From<pcs::VerifyError> for SuccinctVeilError` | `crates/flock-prover/src/succinct_veil.rs:286` |
| 15 | `verify_constraints` | `crates/veil-f128/src/constraints.rs:539` |
| 16 | `From<ConstraintError> for SuccinctVeilError` | `crates/flock-prover/src/succinct_veil.rs:280` |
| 17 | return of message 6 | same as 6 |

The verifier re-derives the shifted circuit (message 10). It does not trust
a circuit from the proof. It forks `veil_challenger` at the same transcript
point as the prover (message 12). Both steps are essential.

Both binaries parse `argv` by hand. `veiled_flock` needs
`required-features = ["veil"]`, and `flock_chain` builds with default
features. `RandomChallenger` (`crates/flock-core/src/challenger.rs:101`)
ignores observed messages. It is gated behind
`cfg(any(test, feature = "unsound-challenger"))`. Never enable it for a
build that produces real proofs.

### 15.8 flock-prover simulator and certificate

The simulator path makes the zero-knowledge claim checkable. It produces a
transcript without a witness. `SealedStatement` makes the witness unreachable
by type.

| Lane | Symbol | Anchor |
|---|---|---|
| `call` | the driver (test or certificate harness) | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:641` |
| `SETUP` | `Blake3PreimageZkSetup::simulate_succinct` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:641` |
| `SEAL` | `SealedStatement` | `crates/flock-prover/src/sim_seal.rs:10` |
| `ORC` | `sim_oracle` | `crates/flock-prover/src/sim_oracle.rs:58` |
| `SIM` | `RomZerocheckSimulator` and `preimage_simulator` | `crates/flock-prover/src/succinct_veil.rs:80` |
| `CERT` | `zk_certificate` | `crates/flock-prover/src/zk_certificate.rs:52` |

```text
  call   SETUP   SEAL    ORC    SIM    CERT
  |      |       |       |      |      |
  |----->|       |       |      |      |      1 simulate_succinct
  |      |------>|       |      |      |      2 SealedStatement (witness barrier)
  |      |*      |       |      |      |      3 ZkRng::from_seed + fork pseudo-messages
  |      |-------------->|      |      |      4 SharedOracle / ProgrammableOracle
  |      |       |       |*     |      |      5 ro_context(nonce, oracle)
  |      |--------------------->|      |      6 RomZerocheckSimulator::new
  |      |       |       |<-----|      |      7 OracleChallenger (programmed answers)
  |      |       |       |      |*     |      8 SuccinctZerocheckSource::emit
  |      |<---------------------|      |      9 SimulatedProof
  |      |---------------------------->|      10 ZkCertificate / require_certified
  |      |<----------------------------|      11 Err(ZkGateError) -> abort
  |<-----------------------------------|      12 certified transcript

```

| # | Symbol | Anchor |
|---|---|---|
| 1 | `Blake3PreimageZkSetup::simulate_succinct` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:641` |
| 2 | `SealedStatement` | `crates/flock-prover/src/sim_seal.rs:10` |
| 3 | `zk::ZkRng` | `crates/flock-core/src/zk.rs:56` |
| 4 | `ProgrammableOracle` at `crates/flock-prover/src/sim_oracle.rs:58`; `sim_oracle::shared_oracle` | `crates/flock-prover/src/sim_oracle.rs:166` |
| 5 | `sim_oracle::ro_context` | `crates/flock-prover/src/sim_oracle.rs:192` |
| 6 | `RomZerocheckSimulator::new` | `crates/flock-prover/src/succinct_veil.rs:87` |
| 7 | `sim_oracle::OracleChallenger` | `crates/flock-prover/src/sim_oracle.rs:206` |
| 8 | `SuccinctZerocheckSource::emit`, the only trait method (`crates/flock-prover/src/succinct_veil.rs:69`); impl at `crates/flock-prover/src/succinct_veil.rs:113`; `crates/flock-prover/src/succinct_veil.rs:668` (call site) | `crates/flock-prover/src/succinct_veil.rs:68` |
| 9 | `preimage_simulator::SimulatedProof`; produced by `simulate` at `crates/flock-prover/src/preimage_simulator.rs:454` | `crates/flock-prover/src/preimage_simulator.rs:442` |
| 10 | `zk_certificate::ZkCertificate`; `require_certified` at `crates/flock-prover/src/zk_certificate.rs:223` | `crates/flock-prover/src/zk_certificate.rs:52` |
| 11 | `zk_certificate::ZkGateError` | `crates/flock-prover/src/zk_certificate.rs:79` |
| 12 | `sim_game::SimGameLedger` records the hop sequence behind the claim | `crates/flock-prover/src/sim_game.rs:58` |

### 15.9 Class diagram: crate dependencies

The three manifests define the direction. `crates/flock-core/Cargo.toml`
lists no workspace dependency. `crates/veil-f128/Cargo.toml` lists
`flock-core = { path = "../flock-core", features = ["zk"] }`.
`crates/flock-prover/Cargo.toml` lists `flock-core` without a gate and
`veil-f128 = { path = "../veil-f128", optional = true }`, enabled by
`veil = ["zk", "dep:veil-f128"]`.

```text
  +----------------+          +----------------+          +----------------+
  |  flock-core    |<---------|   veil-f128    |<---------|  flock-prover  |
  |  (tier 0)      |          |   (tier 1)     |  opt.    |   (tier 2)     |
  |  no workspace  |          | features=["zk"]|  "veil"  |  has [[bin]]   |
  |  dependencies  |          |                |          |                |
  +----------------+          +----------------+          +----------------+
          ^                                                        |
          |                    always (no feature gate)            |
          +--------------------------------------------------------+

  re-exports:
    flock-prover ..> flock_core::*              (crates/flock-prover/src/lib.rs:15)
    veil-f128    ..> flock_core::field::F128    (crates/veil-f128/src/lib.rs:32)
```

Arrows point from the dependent crate to its dependency. Cargo enforces the
direction at compile time, so no cycle across crates is possible.

### 15.10 Class diagram: flock-core

```text
+----------------------------------+    +------------------------------------+
| F128                             |    | BlockR1cs                          |
|----------------------------------|    |------------------------------------|
| + lo: u64                        |    | + layout: WitnessLayout            |
| + hi: u64   repr(C, align(16))   |    | + k_log: usize                     |
|----------------------------------|    | + zk: Option<ZkBlockLayout>        |
| + ZERO / ONE                     |    |------------------------------------|
| + inv(self) -> Self              |    | + padding_spec() -> PaddingSpec    |
+----------------------------------+    | + x_ab_from_mlv(..) -> F128        |
                                        | + csc_lincheck_circuit()           |
                                        +------------------------------------+

+----------------------------------+    +------------------------------------+
| PcsParams                        |    | Commitment / ProverData            |
|----------------------------------|    |------------------------------------|
| + m: usize                       |    | + root: Hash                       |
| + log_inv_rate, log_batch_size   |    | + zk_mask, zk_blind                |
|----------------------------------|    |------------------------------------|
| + zk: bool, profile              |    | (commit_zk_with_ro: free fn)       |
+----------------------------------+    +------------------------------------+

+----------------------------------+    +------------------------------------+
| ZerocheckProof / ZerocheckClaim  |    | LincheckProof / LincheckClaim      |
|----------------------------------|    |------------------------------------|
| + z: F128                        |    | + rounds: Vec<(F128, F128)>        |
| + mlv_challenges: Vec<F128>      |    | + z_partial, r_inner_rest, w       |
+----------------------------------+    +------------------------------------+

+----------------------------------+    +------------------------------------+
| <<trait>> Challenger             |    | <<trait>> MaskSampler              |
|----------------------------------|    |------------------------------------|
|----------------------------------|    |------------------------------------|
| + observe_label / observe_bytes  |    | + fill_u64s(&mut [u64])            |
| + observe_f128(_slice)           |    +------------------------------------+
| + sample_f128(_vec)              |    
+----------------------------------+    
```

| Type | Anchor |
|---|---|
| `F128`; re-exported at `crates/flock-core/src/field.rs:14` | `crates/flock-core/src/field/gf2_128.rs:24` |
| `F256Unreduced` | `crates/flock-core/src/field/gf2_128.rs:141` |
| `BlockR1cs` | `crates/flock-core/src/r1cs.rs:56` |
| `WitnessLayout` | `crates/flock-core/src/r1cs.rs:39` |
| `SparseBinaryMatrix` | `crates/flock-core/src/r1cs.rs:14` |
| `PcsParams` | `crates/flock-core/src/pcs/commit.rs:32` |
| `Commitment` | `crates/flock-core/src/pcs/commit.rs:123` |
| `ProverData` | `crates/flock-core/src/pcs/commit.rs:134` |
| `BatchOpeningProofLigerito` | `crates/flock-core/src/pcs.rs:51` |
| `ZkBlindOpening` | `crates/flock-core/src/pcs.rs:65` |
| `pcs::VerifyError` | `crates/flock-core/src/pcs.rs:71` |
| `ZerocheckProof` | `crates/flock-core/src/zerocheck.rs:313` |
| `ZerocheckClaim` | `crates/flock-core/src/zerocheck.rs:293` |
| `PaddingSpec` | `crates/flock-core/src/zerocheck.rs:258` |
| `zerocheck::VerifyError` | `crates/flock-core/src/zerocheck.rs:331` |
| `LincheckProof` | `crates/flock-core/src/lincheck.rs:379` |
| `LincheckClaim` | `crates/flock-core/src/lincheck.rs:394` |
| `QuirkyPoint` | `crates/flock-core/src/lincheck.rs:361` |
| `lincheck::VerifyError` | `crates/flock-core/src/lincheck.rs:478` |
| `R1csProofLigerito` | `crates/flock-core/src/proof.rs:18` |
| `ZClaim` | `crates/flock-core/src/proof.rs:26` |
| `RoContext` | `crates/flock-core/src/ro.rs:83` |
| `RoChannel` | `crates/flock-core/src/ro.rs:56` |
| `ZkRng` | `crates/flock-core/src/zk.rs:56` |
| trait `Challenger` | `crates/flock-core/src/challenger.rs:30` |
| trait `ByteOracle` | `crates/flock-core/src/ro.rs:204` |
| trait `MaskSampler` | `crates/flock-core/src/zk.rs:36` |
| trait `LincheckCircuit` | `crates/flock-core/src/lincheck.rs:173` |
| `FsChallenger`, implements `Challenger` | `crates/flock-core/src/challenger.rs:184` |
| `RandomChallenger`, implements `Challenger` | `crates/flock-core/src/challenger.rs:101` |
| `CscCircuit`, implements `LincheckCircuit` | `crates/flock-core/src/lincheck.rs:249` |
| `SparseMatrixCircuit`, implements `LincheckCircuit` | `crates/flock-core/src/lincheck.rs:197` |
| `PlaybackSampler`, implements `MaskSampler` | `crates/flock-core/src/zk.rs:124` |
| `ZeroSampler`, implements `MaskSampler` | `crates/flock-core/src/zk.rs:148` |

`ZkRng` also implements `MaskSampler`.

### 15.11 Class diagram: veil-f128

```text
+------------------------------------+    +--------------------------------------+
| AdditiveRsCode                     |    | CodeParameters                       |
|------------------------------------|    |--------------------------------------|
| - parameters: CodeParameters       |    | + message_length: usize              |
|------------------------------------|    | + code_length: usize                 |
| + encode / encode_batch            |    |--------------------------------------|
| + encode_square / decode_square    |    | + new(..) -> Result<_, CodeError>    |
| + square_to_base                   |    | + square_message_length()            |
+------------------------------------+    +--------------------------------------+

+------------------------------------+    +--------------------------------------+
| MerkleMatrix                       |    | ArithmeticCircuit / CircuitBuilder   |
|------------------------------------|    |--------------------------------------|
| - rows, columns                    |    | - num_inputs, num_variables          |
|------------------------------------|    | - multiplications, linear_cons       |
| + new_framed(..)                   |    |--------------------------------------|
| + root() -> Hash                   |    | + num_inputs(), num_variables()      |
| + open(&[usize])                   |    | + is_satisfied(&self, witness)       |
+------------------------------------+    +--------------------------------------+

+------------------------------------+    +--------------------------------------+
| ConstraintProof                    |    | <<trait>> OracleProgrammer           |
|------------------------------------|    |--------------------------------------|
| + parameters: ConstraintParameters |    |--------------------------------------|
| + linear: DotProductProof          |    | + program_fresh(point, value)        |
| + hadamard: Option<HadamardProof>  |    |     -> Result<(), OracleProgErr>     |
+------------------------------------+    +--------------------------------------+
```

| Type | Anchor |
|---|---|
| `AdditiveRsCode` | `crates/veil-f128/src/code.rs:95` |
| `CodeParameters` | `crates/veil-f128/src/code.rs:18` |
| `CodeError`; `Display` and `std::error::Error` at `crates/veil-f128/src/code.rs:66` | `crates/veil-f128/src/code.rs:57` |
| `AdditiveCosetNtt` | `crates/veil-f128/src/ntt.rs:167` |
| `MerkleMatrix` | `crates/veil-f128/src/commitment.rs:14` |
| `MerkleMatrixOpening` | `crates/veil-f128/src/commitment.rs:22` |
| `VectorParameters` | `crates/veil-f128/src/dot_product.rs:28` |
| `DotProductProverData` | `crates/veil-f128/src/dot_product.rs:93` |
| `DotProductProof` | `crates/veil-f128/src/dot_product.rs:102` |
| `DotProductError` | `crates/veil-f128/src/dot_product.rs:113` |
| `HadamardProverData` | `crates/veil-f128/src/hadamard.rs:24` |
| `HadamardProof` | `crates/veil-f128/src/hadamard.rs:37` |
| `HadamardError` | `crates/veil-f128/src/hadamard.rs:50` |
| `BlockR1csParameters` | `crates/veil-f128/src/block_r1cs.rs:36` |
| `BlockR1csProof` | `crates/veil-f128/src/block_r1cs.rs:68` |
| `BlockR1csError` | `crates/veil-f128/src/block_r1cs.rs:76` |
| `PublicEquality` | `crates/veil-f128/src/block_r1cs.rs:62` |
| `LinearCombination` | `crates/veil-f128/src/constraints.rs:29` |
| `ArithmeticCircuit` | `crates/veil-f128/src/constraints.rs:119` |
| `CircuitBuilder` | `crates/veil-f128/src/constraints.rs:191` |
| `ConstraintProof` | `crates/veil-f128/src/constraints.rs:277` |
| `ConstraintCommitment` | `crates/veil-f128/src/constraints.rs:290` |
| `ConstraintParameters` | `crates/veil-f128/src/constraints.rs:304` |
| `ConstraintError` | `crates/veil-f128/src/constraints.rs:362` |
| `SimulationError` | `crates/veil-f128/src/simulator.rs:40` |
| trait `OracleProgrammer` | `crates/veil-f128/src/simulator.rs:32` |
| `From<DotProductError> for BlockR1csError` | `crates/veil-f128/src/block_r1cs.rs:89` |
| `From<HadamardError> for BlockR1csError` | `crates/veil-f128/src/block_r1cs.rs:95` |
| `From<CodeError> for DotProductError` | `crates/veil-f128/src/dot_product.rs:125` |
| `From<CodeError> for HadamardError` | `crates/veil-f128/src/hadamard.rs:63` |
| `From<BlockR1csError> for SimulationError` | `crates/veil-f128/src/simulator.rs:47` |
| `From<CodeError> for SimulationError` | `crates/veil-f128/src/simulator.rs:53` |

### 15.12 Class diagram: flock-prover

```text
+--------------------------------------+    +----------------------------------------+
| SealedStatement<'a>                  |    | ZkCertificate                          |
|--------------------------------------|    |----------------------------------------|
| - witness is unreachable by type     |    | + family: StatementFamily              |
+--------------------------------------+    |----------------------------------------|
                                            | (require_certified is a free fn)       |
                                            +----------------------------------------+
```

| Type | Anchor |
|---|---|
| `Blake3PreimageZkSetup` | `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:413` |
| `SuccinctVeilProof` | `crates/flock-prover/src/succinct_veil.rs:33` |
| `SuccinctVeilError` | `crates/flock-prover/src/succinct_veil.rs:48` |
| `SuccinctZerocheckInputs<'a>` | `crates/flock-prover/src/succinct_veil.rs:57` |
| `RomZerocheckSimulator` | `crates/flock-prover/src/succinct_veil.rs:80` |
| trait `SuccinctZerocheckSource` | `crates/flock-prover/src/succinct_veil.rs:68` |
| `SealedStatement<'a>` | `crates/flock-prover/src/sim_seal.rs:10` |
| `SimCoins` | `crates/flock-prover/src/sim_seal.rs:57` |
| `ZkCertificate` | `crates/flock-prover/src/zk_certificate.rs:52` |
| `StatementFamily` | `crates/flock-prover/src/zk_certificate.rs:45` |
| `ZkGateError` | `crates/flock-prover/src/zk_certificate.rs:79` |
| `SimGameLedger` | `crates/flock-prover/src/sim_game.rs:58` |
| `SimGameHop` | `crates/flock-prover/src/sim_game.rs:8` |
| `ProgrammableOracle` | `crates/flock-prover/src/sim_oracle.rs:58` |
| `OracleChallenger` | `crates/flock-prover/src/sim_oracle.rs:206` |
| `SimulatedProof` | `crates/flock-prover/src/preimage_simulator.rs:442` |
| `SimError` | `crates/flock-prover/src/preimage_simulator.rs:160` |
| `HashKind` | `crates/flock-prover/src/proof_io.rs:56` |
| `DeserializeError` | `crates/flock-prover/src/proof_io.rs:103` |
| `BundleReadError` | `crates/flock-prover/src/proof_io.rs:303` |
| `R1csProofBundleLigerito` | `crates/flock-prover/src/proof_io.rs:150` |
| `ChainProofBundleLigerito` | `crates/flock-prover/src/proof_io.rs:161` |
| `R1csProofBundleZkA1` | `crates/flock-prover/src/proof_io.rs:191` |

### 15.13 Class diagram: cross-crate relations

Only edges that cross a crate boundary appear.

```text
  flock-prover                         veil-f128                     flock-core
  ------------                         ---------                     ----------
  Blake3PreimageZkSetup *--- BlockR1cs -----------------------------------> (owns)
  Blake3PreimageZkSetup *--- PcsParams -----------------------------------> (owns)
  prove_succinct_veil_r1cs ---> commit_constraint_inputs
  prove_succinct_veil_r1cs ---> prove_constraints_from_commitment
  prove_succinct_veil_r1cs -------------------------------> zerocheck::prove_*
  prove_succinct_veil_r1cs -------------------------------> lincheck::prove_*
  prove_succinct_veil_r1cs -------------------------------> pcs::commit::commit_zk_*
  SuccinctVeilProof     *--- ConstraintProof
  SuccinctVeilProof     *------------------------------------ ZerocheckProof
  ConstraintError       ..> SuccinctVeilError    (From, never leaked bare)
  pcs::VerifyError      ..>-------------------------------->  SuccinctVeilError
  RomZerocheckSimulator ---|> SuccinctZerocheckSource
  AdditiveRsCode        ---------------------------------> F128 (re-exported)
  MerkleMatrix          ---------------------------------> merkle::Hash
  block_r1cs / hadamard / dot_product ---> Challenger  (generic bound C)
```

Review enforces the wrapper rule; the compiler does not. Do not put a `veil-f128`
error type in a `flock-prover` signature without a `veil` gate.
`SuccinctVeilError` wraps it (`From<ConstraintError>` at
`crates/flock-prover/src/succinct_veil.rs:280`). `VeiledPreimageError` wraps
it on the legacy path.

### 15.14 Omissions and deviations

| Item | Anchor | Status |
|---|---|---|
| `pcs/jagged.rs` | declared at `crates/flock-core/src/pcs.rs:23`; doc comment at `crates/flock-core/src/r1cs.rs:28` | No call sites in the workspace. Absent from 15.3 and 15.10. |
| `ArithmeticCircuit::complete_witness` | `crates/veil-f128/src/constraints.rs:143` | No call sites in the workspace. Absent from 15.4. |
| `pcs` imports from `zerocheck` | `crates/flock-core/src/pcs.rs:44`; `crates/flock-core/src/pcs/ring_switch.rs:63` | Layer inversion: PCS sits below the PIOP by design. Drawn as is. Do not deepen. |
| `ro` and `merkle` cycle | `crates/flock-core/src/ro.rs:83`; `crates/flock-core/src/merkle.rs:288` | `Hash` lives in `merkle` and is the oracle output type. Drawn as is. Do not deepen. |
| Univariate-skip modules | declared at `crates/flock-core/src/zerocheck.rs:24` to `crates/flock-core/src/zerocheck.rs:27`; import at `crates/flock-core/src/zerocheck.rs:34` | Message 6 of 15.1 is a branch. `_naive` and `_optimized` twins compute the same round-1 polynomial. The optimized module runs. |
| `univariate_skip.rs` reference path | `build_eq` at `crates/flock-core/src/zerocheck/univariate_skip.rs:31`; `round1_naive` at `crates/flock-core/src/zerocheck/univariate_skip.rs:68`; `round1_extract_c_packed` at `crates/flock-core/src/zerocheck/univariate_skip.rs:277` | Readable reference. |
| `univariate_skip_deg4.rs` | `round1_deg4_naive` at `crates/flock-core/src/zerocheck/univariate_skip_deg4.rs:85` | Degree-4 twin. |
| `univariate_skip_optimized.rs`, `univariate_skip_deg4_optimized.rs` | `crates/flock-core/src/zerocheck/univariate_skip_optimized.rs`; `crates/flock-core/src/zerocheck/univariate_skip_deg4_optimized.rs` | Production path. Drawn as one participant. |
| `veil` feature | `.github/workflows/lint.yml`; `.github/workflows/test.yml`; `scripts/zk-certify.sh` | No CI workflow builds it. `simulator.rs` has no inline tests, and `crates/veil-f128/tests/` does not exist. Subsections 15.4 to 15.8 come from a read of the source. |
| `flock-core` numeric kernels | `field/gf2_128.rs`, `field/gf2_8.rs`, `field/phi8.rs`, `field/f128_slice.rs`, `ntt/additive_ntt_f128.rs`, `ntt/parallel_f128.rs`, `ntt/inv_table.rs`, `ntt/inv_table_deg4.rs`, `merkle/aarch64.rs`, `merkle/x86_64.rs`, `linalg.rs`, `bits.rs`, `scratch.rs`, `permutation.rs` | Hand-tuned arithmetic with no outward relations. Absent from 15.10. |
| `pcs/ligerito.rs` | `crates/flock-core/src/pcs/ligerito.rs:3068` | 7498 lines. Drawn as one participant in 15.3. Internal types absent from 15.10. |
| `symbolic` feature | `pcs/tensor_algebra.rs`, `pcs/symbolic_opening.rs`, `pcs/zk_audit.rs`; trait `SymScalar` at `crates/flock-core/src/symbolic/scalar.rs:6` | Offline audit and symbolic execution. Not on the prove or verify path. |
| `flock-prover` primitives with fan-out 0 to 1 | `chain.rs`, `merkle_path.rs`, `digest_bind.rs`, `ligerito_decode.rs`, `sim_ext.rs`, `zk_audit_support.rs`, `zk_rank_check.rs`, `transcript_schema.rs`; `r1cs_hashes/{blake3,sha2,keccak,keccak3,common}.rs` | Absent from 15.12. |
| `veiled_preimage.rs` | `crates/flock-prover/src/veiled_preimage.rs:347` | Legacy whole-R1CS path, 504 lines. Not dead. Shown only where a name collides with the active path. |

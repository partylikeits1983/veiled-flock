# Architecture of succinct VEIL-FLOCK

## Implemented statement

```text
public:  BLAKE3 digests y_0, ..., y_(b-1)
private: 64-byte messages x_0, ..., x_(b-1)
claim:   BLAKE3(x_i) = y_i for every i
```

The circuit is FLOCK's pinned Boolean BLAKE3 R1CS. Short batches use the same
statement with deterministic padding up to the 256-slot hiding-PCS floor.

## Proof flow

```text
randomized FLOCK witness z
       |
       +--> hiding Ligerito commitment Com(z)
       |
       +--> ordinary zerocheck + lincheck messages v
                 |
                 +--> send v' = v + h
                      challenges are derived from v'

precommit h before those challenges
       |
       +--> VEIL proof of C(v' + h) = 0
              - all zerocheck recurrences
              - final a * b identity
              - all lincheck recurrences
              - output values equal public PCS claims

Com(z) + the two output claims
       |
       +--> one hiding ring-switch/Ligerito opening
              also binds the public digest claim
```

Subtraction is addition in characteristic two. The shifted verifier has 242
masked inputs at the batch-256 shape, one statement product row, and VEIL's two
dummy masking rows. Its size is logarithmic in the FLOCK witness size.

## Transcript split

- Exposed then VEIL-masked: every F128 value observed from zerocheck and
  lincheck.
- Shielded by the hiding PCS: ring-switch values, opened code rows, recursive
  Ligerito messages, Merkle paths, and the terminal residual.
- Explicit linkage values: the AB and C evaluation claims. FLOCK's zk
  randomizer rows move these values; the shifted circuit binds them to the
  masked PIOP, and Ligerito binds them to the commitment.
- Public: statement, circuit/PCS shape, batch size, commitment roots, nonce,
  and digest claim.

## Two-phase VEIL commitment

The mask commitment must exist before masked FLOCK messages determine their
Fiat--Shamir challenges. `veil-f128::commit_constraint_inputs` commits to `h`
and six private product-padding values first. After FLOCK fixes the shifted
verifier circuit, `prove_constraints_from_commitment` proves that circuit
against the same commitment.

The generic compiler appends
`(r,s,rs,r+1,t,(r+1)t)`. The two dummy products and the linear relation
`r+(r+1)+1=0` hide the three Hadamard linkage claims; these values never appear
in the proof.

## Characteristic-two code

`crates/veil-f128` supplies additive-domain Reed--Solomon base and product
codes over `GF(2^128)`, the reduction map, code-padded Merkle commitments, and
VEIL dot/Hadamard proofs. The succinct profile uses inverse rate 8 and 160
random padding symbols/queries.

## Simulator

`Blake3PreimageZkSetup::simulate_succinct` accepts public digests, simulator
coins, and a programmable random oracle—no message or preimage.

It creates an unrelated randomized pseudo-witness, patches only its public
digest cells, and commits to it with the normal hiding PCS. Because this vector
does not satisfy the hash R1CS, the simulator samples zerocheck messages and
programs the fold challenges, solving the final coefficient to land on the
pseudo-witness's true terminal evaluations. Lincheck, the PCS opening, and the
VEIL shifted-verifier proof then run unchanged. The production succinct
verifier accepts the result through the programmed oracle.

## User-facing entry points

- `Blake3PreimageZkSetup::{prove_succinct,verify_succinct}`
- `Blake3PreimageZkSetup::simulate_succinct`
- `veiled_flock demo`
- `veiled_flock prove/verify`

The older direct whole-R1CS VEIL mode remains in `veiled_preimage.rs` as a
correctness/reference implementation; it is no longer the CLI or benchmark
path.

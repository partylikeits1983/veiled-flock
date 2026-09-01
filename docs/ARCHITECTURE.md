# Architecture

VEIL-FLOCK has one zero-knowledge path built from three layers.

| Layer | Role |
|---|---|
| FLOCK PIOP | Reduce the pinned Boolean R1CS to witness evaluations |
| Shielded FLOCK PCS | Commit once and batch-open AB, C, and digest claims |
| VEIL | Prove the masked verifier relations |

The public entry point is
`Blake3PreimageZkSetup::{new,prove,verify,simulate}`. There is no alternate ZK
proof flavor or legacy masking API.

## Relation

The public statement is an ordered list of BLAKE3 digests. The witness contains
one 64-byte message per digest. The circuit fixes the BLAKE3 IV, counter zero,
block length 64, and `CHUNK_START|CHUNK_END|ROOT` flags.

Short batches are padded to the next registered power-of-two shape. The ZK
path supports a 256-slot floor and a 4096-slot ceiling. The verifier checks the
circuit digest and Secure PCS parameters for the selected shape.

## Shielded PCS

The witness is packed over `GF(2^128)` and committed with a blinded additive-RS
encoder. Per lane, the committed message is `[mu || z]`: `mu` is a uniform low
block and `z` is the packed witness. The image is an `RS[N,2k]` code.

The low block hides any union of at most `k` opened positions. A separate
blinder `g` is folded in with a nonzero challenge, producing the virtual
message `[mu || z] + c*g`. Claims are evaluated against `[0 || b]`, so the
opening still proves claims about `z`.

The witness, VEIL-linear, and VEIL-Hadamard initial trees have independent
256-bit tree nonces and fresh 256-bit salts per leaf. The proof nonce and tree
nonces are bound into the transcript. Recursive Ligerito trees are unsalted
because they are built after the witness-hiding fold.

## Masked FLOCK Transcript

At the 256-slot floor, the FLOCK PIOP exposes 242 field coordinates. The two
ring-switch claims expose another 512 coordinates. Each coordinate is one-time
padded. The registered 256/512/1024/2048/4096-slot shapes use
754/756/758/760/762 masks.

At a fixed challenge history, the visible affine transcript has the form:

```text
Y = A*w + B*r + d(public)
```

Every visible coordinate is serialized as `private + fresh_mask`. The prover
and verifier check that the mask cursor consumes the expected number of masks
in the expected order. The Lean masking theorem proves the relevant
surjectivity in the formal model; a Rust-to-Lean conformance proof is future
work.

Ring switching is checked over `GF(2)`: the 128-by-128 matrix for a field
challenge is derived from the production field multiplication routine and
tested on all basis vectors. The masked witness, blinder, and folded slices
obey the same committed `q = z + c*g` relation.

## VEIL Linkage

The VEIL mask commitment is made before FLOCK derives challenges. After the
masked transcript is known, the shifted verifier circuit reconstructs each
hidden value from its public masked coordinate and private pad. It checks the
zerocheck and lincheck recurrences, terminal multiplication, AB/C linkage,
ring-switch linkage, and public digest functional.

VEIL uses additive-domain Reed-Solomon codes over `GF(2^128)`. Operand and
product codes have separate ZK projection, distance, and query budgets.
Pointwise products lie in `RS[N,2K-1]`. The reduction map is checked on every
pair of basis vectors, which suffices by bilinearity.

Simulation constructs a shifted circuit satisfied by simulator-owned masks, so
the VEIL prover is called only on a satisfied assignment.

## Batched Opening

The claim manifest is fixed before batching challenges. One fresh witness
commitment produces one opening containing AB, C, and the public digest
functional. Claim identifiers are canonical, duplicates are rejected, and the
union of opened initial positions is checked against the code-padding budget.

The public digest functional is derived from the public statement and
Fiat-Shamir challenges sampled after the prefix is bound. Equal public
statements induce witness differences in the functional's kernel; the PCS
translation tests check this condition for the registered construction.

## Simulator Boundary

Before the hiding fold, the simulator uses algebraic FLOCK and VEIL simulators
with challenges sampled from the honest distributions. It uses an arbitrary
representative of the public affine fiber only for linear post-processing. That
representative is not required to satisfy BLAKE3.

After the fold, recursive Ligerito and post-processing are witness-independent.
Fiat-Shamir programming follows the 256-bit block layout, including rejection
sampling and unused digest halves.

## Random Oracle

One lazy classical random oracle serves Fiat-Shamir, Merkle, VEIL, and grinding
through role-separated encodings. The simulator shares one table across
adaptive proofs and programs only undefined points. Fresh proof nonces, tree
channels, leaf salts, and masks give the composition its privacy margin, even
for correlated witnesses. The pROM bound and limitations are in
[SECURITY.md](SECURITY.md).

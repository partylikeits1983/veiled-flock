# Security audit status

This implementation is a VEIL+FLOCK research prototype. It is unaudited,
unsuitable for production secrets, and is not supported by an end-to-end
zero-knowledge or argument-of-knowledge theorem.

## Security claim

It is accurate to describe the repository to a reviewer as an experimental
prototype that applies VEIL to FLOCK's verifier transcript. It is not yet
accurate to present it as a cryptographically established zero-knowledge
version of FLOCK.

Privacy depends on three components:

1. VEIL hides and proves the zerocheck and lincheck verifier equations;
2. the witness commitment and Ligerito opening use a hiding PCS; and
3. randomized R1CS rows are intended to hide the explicit AB and C evaluation
   claims and the two 128-element ring-switch vectors serialized by the PCS.

Removing either mechanism exposes data that the shifted VEIL circuit does not
hide.

## What VEIL covers

At the pinned 256-slot shape, the active path masks exactly 242 field
elements:

```text
128  zerocheck round-one values
 32  remaining zerocheck round values
  2  terminal zerocheck values
 16  lincheck round values
 64  lincheck partial-witness values
---
242
```

The masks are committed before the dependent Fiat--Shamir challenges. The
shifted verifier reconstructs each unmasked value and checks every zerocheck
fold, the terminal multiplication, every lincheck fold, the terminal
lincheck identity, and equality with the AB/C claims opened by the PCS.

The test suite checks:

- the one-to-one order between observed transcript values, serialized fields,
  and masks;
- acceptance of the shifted circuit by the exact mask vector committed before
  zerocheck.

`final_c_eval` is derived locally rather than observed by Fiat--Shamir. It is
therefore deliberately not a masked wire field; its unique public copy is the
C opening value.

## Component status

| Component | Evidence in this repository | Remaining gap |
|---|---|---|
| Exact 64-byte BLAKE3 relation | Pinned IV, counter, block length, flags, public digest claim, differential and mutation tests | Independent review |
| Zerocheck/lincheck masking | Complete wire-order and shifted-equivalence regressions | Include in composed privacy proof |
| Additive `GF(2^128)` RS code | Independent Lagrange-interpolation test, exhaustive tiny projection test, and sampled production projection-rank tests | Formal proof that the implemented LCH transform realizes the stated RS map |
| VEIL dot/Hadamard protocols | Completeness, mutation, product-code, and simulator component tests | Active-compiler distribution and soundness proof |
| Hiding witness PCS | Exact small-instance rank audit with a negative control; structural L0 replacement translator and production query-capacity check | End-to-end hiding proof for recursive Ligerito and Merkle/RO boundary |
| Explicit AB/C and ring-switch values | Fresh-randomizer regression shows that AB, C, and both 128-element `s_hat_v` vectors move | All-challenge proof that their joint distribution is witness-independent, conditioned on the public statement |
| Transcript fork | Fork occurs after all shared roots and AB/C/digest linkage is bound | Composition theorem for the two terminal branches |
| Public-input-only simulation | Generic verifier accepts a proof generated without a preimage using one programmable oracle | Bound the statistical distance between real and simulated views |
| Adversarial soundness | Component parameter checks and mutation rejection | One theorem with every algebraic, proximity, hash, and Fiat--Shamir error term |
| Argument of knowledge | FLOCK/Ligerito component machinery exists | Extractor for this active composition |
| Side channels | No raw witness field is serialized; input and decode sizes are bounded | Timing/cache audit and reliable erasure of secret scratch buffers |

## Additive-code argument and parameters

The VEIL paper's prime-field implementation is not the implementation in this
repository. `veil-f128` stays in FLOCK's binary extension field and replaces a
multiplicative-domain RS code with an additive-domain RS code over
`GF(2^128)`. Consequently, upstream implementation proofs cannot be imported
unchanged.

The masking argument is as follows. Let `X` be the base
domain, let `P` be the subset assigned uniform padding, and let `Y` be any set
of distinct output queries. The output affine coset is disjoint from `X`. For
`x in P`, the Lagrange basis value at `y in Y` is

```text
L_x(y) = Z_X(y) / (Z_X'(x) * (y - x)).
```

For `|Y| <= |P|`, a square submatrix of this evaluation map is a diagonally
scaled Cauchy matrix. Its determinant is non-zero because all points within a
domain are distinct and the two domains are disjoint. Uniform padding
therefore makes every allowed query view uniform. The implementation tests
the resulting matrix at both production geometries and exhaustively checks
all allowed query sets for a small code.

For both active VEIL commitments, the conservative square-code rate is at most
`1/4`. A word outside its unique-decoding radius passes 160 spot checks with
probability at most

```text
((1 + 1/4) / 2)^160 = (5/8)^160 < 2^-108.49.
```

The implementation samples distinct positions without replacement, which can
only improve that bound. This is one component bound, not a claim of 108-bit
end-to-end security. Field identity tests, random-linear-combination tests,
Ligerito proximity checks, hash binding, and Fiat--Shamir composition must be
union-bounded as well. The registered Ligerito `Fast` profile targets 100 bits
per level, but no active composed 100-bit theorem is claimed.

## Statistical zero knowledge and succinctness

A statistical zero-knowledge theorem for this construction would be stated in
the classical random-oracle model and would include algebraic bad-event and
oracle prequery/collision terms. No such theorem currently exists. Replacing
the ideal oracle by concrete SHA-256 is an implementation assumption, not
unconditional statistical zero knowledge in the standard model.

Statistical zero knowledge does not imply a large proof and does not prevent a
succinct proof. "Statistical" describes the distance between the real and
simulated verifier-view distributions; "succinct" describes communication and
verification cost. They are independent properties.

The same distinction applies to Lean: statistical distance over finite
distributions can be formalized. The Lean files in this repository do not
formalize the active protocol, the `GF(2^128)` additive-code port, recursive
Ligerito hiding, or the random-oracle composition. The upstream VEIL
formalization is useful reference material but does not certify this Rust
composition.

## Proof-size attribution

The release benchmark serializes the commitment and proof for the same
batch-256 BLAKE3-preimage relation in both modes; the public digest list and
setup are excluded from both totals. A current one-run sample produced sizes of
271,814 bytes for ordinary FLOCK and 580,526 bytes for VEIL+FLOCK:

| Serialized component | Ordinary FLOCK | VEIL+FLOCK | Delta |
|---|---:|---:|---:|
| Commitment object | 61 | 61 | 0 |
| Zerocheck + lincheck wire | 3,928 | 3,912 | -16 |
| Witness PCS opening | 267,825 | 502,785 | +234,960 |
| Nonce and AB/C outputs | 0 | 64 | +64 |
| VEIL Hadamard + linear + metadata | 0 | 73,704 | +73,704 |
| **Total** | **271,814** | **580,526** | **+308,712** |

About 76% of the size increase comes from the hiding witness PCS, and about
24% comes from the VEIL certificate. The hiding PCS doubles the committed
message dimension and doubles each initial Merkle leaf width. At this shape,
the encoded commitment grows from 65,536 to 262,144 `F128` elements; the leaf
count grows from 1,024 to 2,048 and the leaf width from 1,024 to 2,048 bytes.
The active port performs no prime-field conversion, so field conversion does
not contribute to the proof-size overhead.

Reproduce timings and the complete JSON component report with:

```sh
VEIL_BENCH_BATCH=256 VEIL_BENCH_RUNS=10 \
  cargo bench --locked -p flock-prover --features veil --bench veil_vs_flock
```

## Simulator boundary

`simulate_succinct` accepts public digests without a preimage and produces a
proof accepted by the generic verifier. Fiat--Shamir, PCS, and inner VEIL
hashing all query the same programmable oracle under role-separated encodings.
This demonstrates simulated acceptance, not equality of distributions.

## Input bounds

The CLI accepts at most 256 public digests and decodes proof bundles with a
640 KiB resource limit. The limit is enforced while reading and by the bincode
decoder before proof vectors are constructed.

## Release gates

Before upgrading the claim, the project needs:

1. an active-protocol privacy proof covering transcript masks, AB/C and
   ring-switch randomizers, the hiding PCS, Merkle openings, and the
   transcript fork;
2. a composed soundness and argument-of-knowledge proof with explicit error
   terms for the registered parameters;
3. a formal or independently checked proof of the additive LCH/RS
   correspondence used by `veil-f128`;
4. side-channel and secret-erasure work; and
5. independent cryptographic review.

The supported description is "VEIL+FLOCK research prototype." An end-to-end
ZK FLOCK claim is not supported.

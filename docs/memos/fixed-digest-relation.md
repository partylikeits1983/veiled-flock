# Memo: the fixed-digest BLAKE3 preimage relation

**Intended theorem.** For public digests `y_1..y_n`, the Flock argument is a
noninteractive argument of knowledge for
`R = {((y_i), (x_i)) : BLAKE3(x_i) = y_i for all i}`, and — once the
obligations in `security-definitions.md` and `interactive-simulator-design.md`
are discharged — computational zero-knowledge for it in the classical ROM.

**Status: implemented candidate for the knowledge claim; research design for
the zero-knowledge claim.** Prove/verify exist and are tested
(`crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs`); the extractor and
simulator do not.

---

## 1. Why the previous statement was not enough

The batch statement's public input is the batch size. Its digest covers the
matrices and layout; the verifier takes no caller-supplied value and compares
the accepted claim against nothing. So it asserts "there exist `2^n` valid
compressions" — satisfiable by anyone, with no reference to any digest. Every
zero-knowledge result proved for it inherits that weakness: the simulator is
the honest prover on a witness it picks itself, which is legitimate *only*
because nothing constrains the witness.

Binding a digest breaks that simulator by construction (a simulator that could
produce a witness for a given `y` would be inverting BLAKE3), which is why the
fixed-digest statement is a genuinely new object rather than a parameter
change.

## 2. The relation, exactly

**Public statement** (`DigestStatement`, hashed by `public_digest()` under the
tag `flock-digest-statement-v1`):

| field | meaning |
|---|---|
| `digests[0..n]` | ordered BLAKE3 digests, physical within-slot bit order |
| `n_log` | batch is `2^n_log` instances |
| `padding`, `padding_bits` | what padding instances carry (see §5) |
| `layout` | `k_log`, `region_log`, `region_bits`, `output_byte_off` |

plus the circuit's own `statement_digest` (matrices, shape, zk layout) and the
PCS parameters, both already bound by `bind_statement`.

**Witness.** The messages `x_i` (semantic), the compression traces and
auxiliary R1CS wires (derived), and — in zk mode — the randomizer rows and
mask cubes (proof randomness, not part of the relation).

**Relation.** `BLAKE3(x_i) = y_i`, enforced in two halves:

1. the circuit computes a BLAKE3 *hash* rather than an arbitrary compression
   (§3), and
2. its output region equals the public digest list (§4).

## 3. Message-length policy — M0 is exactly 64 bytes

BLAKE3 of a message fitting one 64-byte block is a single compression with
`cv = IV`, `counter = 0`, `block_len = 64`,
`flags = CHUNK_START|CHUNK_END|ROOT`. `ParamPinning::RootHash64` pins those
wires; the message words stay free. `root_hash_pinning_matches_the_blake3_crate`
checks the constants against the `blake3` crate, so "the circuit computes
BLAKE3" is a checked statement, not a convention.

Pinning is per-bit row surgery on `A_0`/`B_0`. `C = I` means row `i` asserts
`(A·z)_i·(B·z)_i = z_i`, so `1·1 = z_s` forces one and `0·1 = z_s` forces
zero.

> **Implementation note that cost a debugging cycle.** The zero case must keep
> the constant wire on the b-side. `0·0 = z_s` pins equally well and satisfies
> the R1CS, but the witness generator emits `b[s] = 1` for every parameter
> slot; the Hadamard product still matched while the `B·z` *vector* did not,
> and the lincheck — which checks the matrix-vector products — rejected every
> honest proof. Any future pinning must preserve the generator's `a`/`b`
> values, not merely their product.

**Staging.** M0 = exactly 64 bytes (implemented). M0.1 = uniform `ℓ ≤ 64` per
statement (`block_len` pinned per statement; one certified circuit per `ℓ`).
M1 = one chunk, ≤1024 B (intra-chunk chaining; the chain-mask slots already
exist in the zk layout). M2 = arbitrary length (tree). The statement encoding
carries the length policy from M0 onward, so a proof for one policy can never
be read as a proof for another.

## 4. Binding the digests

One **public-target packed-direct claim** in the existing batched Ligerito
opening:

```
ẑ_packed(τ_pos, sel = OUT_SLOT, ι) == ŷ(τ_pos, ι)
```

`ŷ` is the MLE of the public digest array; the **verifier computes the target
itself**, so it is not a proof field and there is no prover-supplied value to
attack. Soundness is Schwartz–Zippel over `n_log + 1` free coordinates plus
one batching term: `≤ (n_log + 2)/2^128`, given that the challenges are drawn
after the commitment is bound.

Why not open at Boolean digest indices: a ring-switched claim at a Boolean
point publishes `s_hat_v`, whose entries are then the 128 raw bits of the
witness word; a packed-direct claim at a Boolean point reveals that whole
word. Evaluating at a random point reveals only `ŷ(τ)`, which is public — and
that is what makes the claim compatible with a hiding mode, where conditioning
the argument on a public value is legitimate rather than a concession.

Why not the generalized lincheck β-fold: it would need one β per pinned column
(256 for `out_lo`), surgery inside the *masked* lincheck, and re-derivation of
A2's ordering argument, for a union-bounded soundness term no better than the
single claim's. The packed-direct route touches only the already-batched PCS
layer.

## 5. Padding instances

The batch is padded to `2^n_log`. Padding slots are not free: the
constant-wire pin already required them to carry a valid compression, and
under a pinning they must satisfy the pinned rows too. So a padding slot holds
the hash of the all-zero message and its digest is **`BLAKE3(0u8 × 64)`, not
zero** — `padding_digest_is_the_hash_of_zeros_not_zero` pins this against the
`blake3` crate and against the generated witness. A verifier using the wrong
padding rule computes a different target and rejects honest proofs, which is
why the rule is part of the statement hash.

`n` need not be a power of two, digests may repeat, and both are recorded in
the statement hash.

## 6. Transcript binding

`absorb_statement` observes `flock-blake3-preimage-v1` and the statement hash
**before any challenge**, so every challenge in the proof is specific to this
digest list, order, and padding rule. Tested: a one-bit change to any digest,
a permutation of the list, and a proof of a different party's preimages are
all rejected.

This closes a gap the older chain statement still has — its public endpoints
are checked arithmetically but never absorbed, so its challenges do not depend
on them.

## 7. Assumptions and unresolved questions

- The knowledge claim rests on the base system's PCS extraction, which **is
  not written down anywhere** (see `knowledge-extraction.md`): the repository
  argues knowledge soundness by proximity to the Ligerito theorems plus prose
  that the mask channels do not disturb it. Specifying the base extractor is a
  prerequisite, not a detail.
- Zero knowledge for this relation is unproven; the masked path carries no ZK
  claim and is not certificate-gated.
- Only the enumerated shape is exercised (m = 22, 256 instances,
  `log_inv_rate = 1`, `log_batch_size = 6`); other shapes have no registered
  Ligerito config.

## 8. Go/no-go

**Go** for the relation and its binding: implemented, tested, and the
soundness accounting is closed-form. **No-go** on any zero-knowledge language
for this statement until the simulator exists and its hypotheses are
certified.

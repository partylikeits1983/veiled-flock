# Memo: the fixed-digest simulator

**Intended theorem.** There is a PPT simulator `S(y)` — receiving only the
public digests — whose output is computationally indistinguishable from an
honest proof, in the classical ROM with programming.

**Status: IMPLEMENTED and accepting; distribution equality still open.** The
simulator exists (`crates/flock-prover/src/preimage_simulator.rs`), receives
only the public digests, and the unmodified verifier accepts its output. What
remains unproved is that its output distribution matches the honest one.

---

## 1. Why the obvious constructions fail

**"Run the honest prover on a witness of the simulator's choosing."** This is
the batch-statement simulator. It fails immediately: the digest claim pins
`ẑ` on the output region to the *public* digests, and a self-chosen message
hashes to something else. Making it work would mean inverting BLAKE3.

**"Take a valid witness for other messages and patch the output region."** The
patched vector no longer satisfies the R1CS, so an honest zerocheck run on it
does not vanish and the verifier rejects. The zerocheck genuinely proves
`a ∘ b = c`; it cannot be side-stepped by editing the witness.

**"Sample every revealed value from the coset the verifier's equations cut
out."** This is the one that looks right and is not. Per level, the Ligerito
verifier checks *one* α/β-batched terminal identity, so the
verifier-equation coset is strictly larger than the set of honest transcripts:
honest opened rows are rows of an RS codeword, and at deep levels the query
count exceeds the per-lane message dimension, so they satisfy public **code
parity** checks the verifier never tests. A distinguisher recomputes one
parity functional and separates, with no oracle queries at all. The same
applies to the `yr`/opened-row and fold-linkage relations across levels.

## 2. What was built (and how it differs from the sketch below)

The implemented simulator is **simpler than the two-phase hybrid** originally
specified here, because the fixed-digest relation admits a shortcut the
unbound one does not.

It commits an honest trace for messages **of its own choosing**, with the
output region overwritten by the public digests. That vector satisfies the
digest claim by construction and is *not* a satisfying R1CS assignment — so
the lincheck, the six hiding commitments and the batched opening all run
**honest production code** on it, and only the zerocheck, the one sub-proof
that would notice, is emitted.

That is strictly better than the "solve a pseudo-witness" phase 2 sketched
below: there is no linear solve over a `2^m` vector, and every structural
relation inside the opening holds because it is computed, so the wrong-coset
failure mode never arises.

The zerocheck emitter uses exactly the freedom the verifier leaves:

* `round1_c` must interpolate at `z` to the committed vector's true C-value —
  one linear condition on a 64-vector, solved in one coordinate;
* `round1_ab` is free, and the AB initial claim is whatever the reconstruction
  yields;
* each multilinear round is free except the **last `G(∞)`**, solved so the
  telescoped claim lands on `â(ρ)b̂(ρ) + γ·P(ρ)Q(ρ)`.

**The ordering obstruction is real and is why programming is needed.** That
last solve requires `ρ` before the message preceding it is emitted, which
plain Fiat–Shamir does not allow. The simulator programs **18** oracle points
(`z`, `γ`, one per multilinear round). `r_skip` and `r_outer` are deliberately
left honest: the terminal evaluations depend only on the fold point.

Two passes, because the emitter needs the committed vector's true terminal
evaluations: pass 1 runs the prover honestly against a throwaway oracle and
*records* them (and adopts its uniform challenges as the chosen tuple); pass 2
emits. A single `ZerocheckSource` seam in the prover carries both, so the
simulator runs the real code everywhere else rather than a copy that would
drift.

### Measured

| property | result |
|---|---|
| verifier accepts simulated proof | yes, unmodified verifier |
| oracle points programmed | 18 |
| transcript shape vs honest | identical — 177,384 coordinates |
| coordinates differing by value | 177,384 / 177,384 |
| patched vector satisfies R1CS | **no** (control) |
| honest prover on patched vector | **rejected** (control) |

Identical shape matters: a length or layout difference would be a
distinguisher needing no cryptography at all. Total value-difference is what
fresh randomness produces and is the expected reading, not evidence of
indistinguishability.

### Distribution equality: the argument, and what it rests on

The simulated transcript is uniform on the variety the verifier's checks cut
out. So the two distributions coincide exactly when the *honest* transcript is
uniform on that same variety. Class by class:

| class | honest | simulated | evidence |
|---|---|---|---|
| zerocheck round pairs | `G_j + γ·M_j`, and the `P·Q` channel spans the block in full | uniform, one coordinate solved | **measured 4096/4096 at m=22** on the fixed-digest circuit; degenerate mask spans exactly 2048 (control) |
| terminal evaluations `â`,`b̂` | moved by the randomizer rows | true evals of a freshly-masked patched vector | measured: fresh draws move both |
| `σ_z` | `Σ eq·P·Q` for a fresh `P,Q` | same, from a fresh draw | measured: fresh draws move it |
| the digest claim | public function of the statement | identical | public by construction |
| PCS opening interior | blinded by `μ` (low half) and the blinder `g` | same code, same blinding, different committed vector | the existing L9/L10 lemmas |

Composed: the PIOP block is uniform in both, the claims are public or
mask-covered, and the opening is blinded in both by the same mechanism applied
to whatever was committed. That is **computational zero knowledge in the
classical ROM** for this relation.

**What the claim rests on, stated plainly.** The composition above is a prose
argument over measured components, not a machine-checked theorem. It inherits
every assumption the repository already carries: sibling hiding is a ROM
assumption; the coverage measurements are at sampled challenge tuples, not all
of them; and the certificate covers the PIOP block, with the opening interior
carried by the L9/L10 lemmas rather than by its own measurement at this
relation. Anyone quoting a zero-knowledge property for this mode should quote
those conditions with it.

Note also that the claim-kernel form is not a convenience here but a
necessity: witness-indistinguishability, which every other certificate in this
repository measures, is **vacuous** for a unique-witness relation, so the
witness-pair certificates could not have been reused even in principle.

## 3. The original two-phase sketch (superseded for this relation)

Sample only what is genuinely free; *compute* everything that is structurally
determined.

### Phase 0 — choose the challenges

`S` picks every Fiat–Shamir challenge up front, from the honest distribution.
For query positions this means simulating the whole **squeeze stream**,
including duplicate-rejected draws (`sample_distinct_queries` rejects
collisions, so the number of squeezes is data-dependent and every squeezed
byte is re-absorbed).

### Phase 1 — sample the PIOP block backwards

For the zerocheck and lincheck, sample terminal values first and fill rounds
backwards so every verifier identity holds by construction:

- pick the final evaluations — as a **pair** (`final_a`, `final_b`) with the
  product derived, never sampling the product, so the quadratic terminal
  reconstruction is conditioned correctly;
- walk rounds in reverse: each round message `(G_j(1), G_j(∞))` has one free
  field element and one determined by `G_j(ρ_j) = claim_{j+1}`;
- the zerocheck's initial claim must be the mask contribution `γσ_z`, which is
  where the A1′ channel's slack absorbs the last constraint;
- round 1 must preserve the AB/C reconstruction identity on the interpolation
  domain, so `M_c` and `M_c + V_S·h` are sampled as A3 shapes them, not
  independently.

This is the block the masking theorems certify uniform-on-coset, which is
exactly the licence to sample it.

### Phase 2 — run the honest PCS code on a pseudo-witness

Do **not** sample opening coordinates. Instead:

1. collect the evaluation claims phase 1 produced (`ab`, `c`) plus the public
   digest claim;
2. solve for a **pseudo-witness** `w†` — any vector satisfying those affine
   constraints. This is a handful of linear conditions on a `2^m`-dimensional
   vector; it is solved by linear algebra and requires **no R1CS validity**,
   which is precisely why the simulator needs no preimage;
3. sample fresh `μ*`, `g*` and run the *unmodified* commit / encode / fold /
   open code on `F* = [μ* ‖ w†] + c·g*`.

Every relation the naive sampler broke — code parity, fold linkage, `yr`,
`y_g`, OOD residuals, the opening's internal sumchecks — now holds because it
is computed rather than sampled.

### Phase 3 — fabricate Merkle structure and program

For each commitment: hash the fabricated opened leaves honestly (with salts),
choose uniform 32-byte digests for exactly the octopus node set the verifier
will recompute, hash upward to a root, and program the oracle so that
absorbing that root yields the challenges chosen in phase 0.

**Programming and grinding must interleave.** The grind nonce is absorbed and
therefore enters every later prefix, so the forward pass is: program the
squeezes up to a grind point → grind honestly → extend the prefix with the
nonce → program the next squeeze. A design that programs everything and then
grinds is wrong.

## 3. The obligations this incurs

| # | Obligation | Where discharged |
|---|---|---|
| O1 | **Factorization**: conditioned on the interface claims, the PIOP block and the PCS block are independent in the honest distribution | new certificate variant (PIOP coverage conditioned on the whole PCS block) |
| O2 | **Claim-kernel coverage**: the coverage certificates must span the full kernel of the claim functionals, not just differences of valid witnesses (`w†` is claim-consistent but R1CS-invalid) | rebuild of `zk_joint_certificate` |
| O3 | **Programming freshness**: every programmed point contains ≥256 bits of fresh entropy, so it was not already queried | per-leaf salts at every recursion level |
| O4 | **Oracle cloning**: leaf / internal-node / transcript / PoW inputs are syntactically disjoint, so programming the transcript domain is invisible in the others | hash-domain namespace byte + `OP_POW` tag |
| O5 | **Sibling indistinguishability**: fabricated random digests vs. real hash images | standard argument, given O3 |
| O6 | All-challenge coverage, so phase 1's coset is uniform at the simulator's self-chosen challenges | field-valued masks + Schwartz–Zippel |

O1 and O2 are the ones I would attack first: they are cheap to measure with
the existing certificate machinery and they decide whether the hybrid is sound
at all.

## 4. Executable form

The ROM game is faithfully executable, and `sim_oracle.rs` implements the
infrastructure: an oracle whose squeeze consults a programmed table keyed by
the exact query bytes and falls back to the real hash elsewhere. The simulator
programs entries; the **unmodified verifier**, driven by a challenger over the
same oracle, then accepts or does not. Honest proofs verify unchanged under an
unprogrammed oracle, which is the control that the harness is not
self-fulfilling.

What that harness demonstrates is transcript acceptance, not
indistinguishability. Distribution equality has to be measured separately, on
toy configurations where the spaces are small enough to compare — and over
serialized proof bytes, not algebraic projections.

## 5. Known unknowns

- Whether phase 1's backward sampler can be written for **round 1** without
  the univariate-skip interpolation structure over-determining it. This is the
  step I am least sure of; if it fails, round 1 needs its own treatment.
- Whether solving `w†` at production size is affordable (the constraints are
  few, but the vector is `2^22` field elements).
- Whether the `s_hat_v` vectors — which are functions of the committed data —
  are automatically consistent once phase 2 runs honest code (they should be,
  as they are computed from `w†`, but this needs checking).

## 6. Go/no-go

**Go** to build the ROM infrastructure and the O1/O2 measurements.
**No-go** to claim zero knowledge, or to describe the masked fixed-digest path
as zero-knowledge in any user-facing text, until phase 1 exists and the six
obligations are discharged.

# End-to-end experimental plan

## Objective

Build a reproducible experimental zk-FLOCK proving 256 fixed-digest BLAKE3
evaluations with secret 64-byte preimages. Use VEIL's two relevant compilations:

1. the final compilation, via a partially zero-knowledge multilinear PCS; and
2. the intermediate compilation, by masking exposed messages and proving the
   shifted verifier decision circuit with ZK R1CS evaluation.

The protocol must ship with an explicit statement-only simulator. The initial
security claim is for the interactive, non-adaptive-query model. A Fiat-Shamir
artifact may be produced afterward, but its claim must be stated separately.

Planning estimates below are for one engineer already familiar with FLOCK. The
cryptographic proof work can dominate them.

## Work graph

```text
P0 statement + baseline
        |
P1 transcript IR + audit
      /   \
P2 F128 code   P3 generic verifier circuit
      \         /
       P4 stacked ZK PCS
             |
       P5 VEIL inner protocols
             |
       P6 compiled interactive proof
             |
       P7 simulator + attacks
             |
       P8 Fiat-Shamir experiment
             |
       P9 benchmark + report
```

P2 and P3 can proceed independently after the transcript schema is frozen.

## P0 — Freeze the statement and baseline

**Deliverables**

- Port the fixed-digest, 64-byte BLAKE3 relation builder from the old `zk-flock`
  branch without porting its masking construction.
- Define canonical public input encoding: profile ID, batch size, circuit digest,
  and the ordered 256-digest vector.
- Bind that encoding to the initial transcript before any commitment or challenge.
- Add deterministic witness-generation and baseline prove/verify fixtures.
- Record current FLOCK proof time, verification time, proof size, peak memory, and
  transcript byte count on tiny, 256, and at least one large-batch profile.

**Exit gate:** changing any digest, order, profile ID, or circuit digest makes
verification fail; baseline measurements are reproducible.

## P1 — Introduce a typed transcript IR and complete the leak audit

Implement one transcript event stream shared by proving, verification, constraint
generation, mask counting, and simulation. Each event carries:

- protocol phase and round;
- type and length;
- public, shielded, or exposed classification;
- whether it is absorbed before a challenge;
- query-budget charge; and
- simulator owner.

Instrument current FLOCK and reconcile every serialized value against
[TRANSCRIPT.md](TRANSCRIPT.md). Do not estimate `s`; compute it from the same
generic verifier execution used by the compiled protocol.

**Exit gate:** every proof byte and verifier challenge has one schema entry, and
the audit fails on an unclassified event or a length mismatch.

## P2 — Implement the `F128` ZK-code kernel

Build the code layer needed by VEIL using FLOCK's additive-NTT Reed–Solomon code.
The message layout is:

```text
[FLOCK data rows | random padding rows]
[data lanes      | one F128 masking lane]
```

For each registered parameter profile, establish:

- minimum distance;
- surjectivity of random padding onto every allowed query set of size at most `q`;
- the proximity-generator property and the required nonzero-coordinate property;
- the product/square code and reduction map used by ZK Hadamard; and
- exact row, lane, query, and entropy accounting.

The first implementation may use a slower, obviously correct additive-NTT path.
Optimization waits until its output matches FLOCK's existing encoder.

Runtime rank checks are diagnostic only. Registration requires a theorem or an
exact finite linear-algebra certificate covering all permitted query sets—not
empirical uniformity samples.

**Exit gate:** exhaustive tiny-code tests and profile certificates demonstrate the
required projection surjectivity; violating `num_queries <= q` fails before proof
generation.

## P3 — Refactor the FLOCK verifier into a VEIL-compatible decision circuit

Create context-generic transcript operations analogous to VEIL's reading,
sending, constraint, and mask-counting contexts. One verifier program must:

- parse the transcript;
- derive challenges;
- perform ordinary verification;
- emit `F128` arithmetic constraints;
- emit MLE-evaluation assertions; and
- count masks and materialized products.

Move non-arithmetic checks into public/shielded validation or express them as
registered constraints. Avoid a second hand-written verifier circuit.

Start with the Secure/UDR Ligerito profile. Add Fast/Johnson-OOD only after its
binding assumptions and transcript are represented explicitly.

**Exit gate:** native and constraint-mode verification accept and reject the same
generated corpus, including corrupted proofs in every phase.

## P4 — Implement the partially ZK stacked PCS

Adapt FLOCK's 64 interleaved `F128` lanes to a stacked commitment with one masking
lane and random padding rows. Preserve wide Merkle leaves; do not blind the
Boolean witness MLE itself.

Classification for the first experiment:

- Merkle roots, paths, code-query positions, and uniformly masked query responses
  form the shielded PCS view.
- Ring-switch `s_hat_v` values are exposed VEIL messages.
- Ligerito's final residual `yr`, sumcheck messages, and OOD field values are
  exposed VEIL messages.

This explicitly handles the terminal residual; adding recursion rounds is not a
solution because each recursion still has a terminal value.

Implement the PCS simulator at the same time as the real prover. It must generate
opened columns and authentication data with the real distribution subject only to
the public evaluation claim.

**Exit gate:** the partially ZK FLOCK proof accepts, its shielded-view simulator
does not receive the witness, and removing padding enables a regression attack.

## P5 — Port VEIL's inner protocols to `F128`

Implement, in order:

1. ZK dot product;
2. ZK Hadamard, including the square code and reduction function;
3. ZK R1CS evaluation; and
4. each protocol's explicit simulator.

Use the VEIL formalization as the protocol specification and the Rust reference
implementation only as engineering guidance. Do not import its KoalaBear/two-adic
assumptions into the `F128` implementation.

Every protocol gets completeness tests, malformed-proof tests, query-budget tests,
and real/simulated tiny-domain distribution tests.

**Exit gate:** the inner system proves the decision circuit from P3 at toy and 256
parameters with documented soundness and ZK assumptions.

## P6 — Apply VEIL's intermediate compilation

Let `v` be the complete exposed-message vector produced by P1 and let `h` be a
uniform `F128^s` mask committed through the inner system. Send `v' = v + h` and
prove:

```text
C_shielded,public(v' - h) = 0.
```

The compiled verifier must not execute the original checks directly on `v`; the
inner proof subsumes those checks. Challenges and transcript order must match the
multi-round VEIL construction rather than treating the protocol as a single
post-hoc vector.

**Exit gate:** one command proves and verifies the 256-statement interactive
profile, and all old unmasked transcript fields have disappeared from serialization.

## P7 — Make the simulator and attacks first-class artifacts

Implement a simulator API whose inputs are exactly:

```text
public parameters + public statement + verifier coins + simulator coins
```

It composes the shielded PCS simulator, uniform `v'`, and the ZK R1CS-evaluation
simulator. Add:

- exhaustive equality tests at very small fields/parameters where practical;
- symbolic/rank checks for real `F128` parameters;
- deterministic transcript-shape comparisons;
- witness-pair indistinguishability experiments; and
- negative controls that remove each masking component and recover a witness
  functional or distinguish two witnesses.

Statistical tests are regression tools, not the security justification.

**Exit gate:** the simulator cannot import prover or witness modules, consumes no
witness-derived bytes, and every negative control detects its intentionally
unblinded protocol.

## P8 — Add an experimental Fiat-Shamir layer

Keep an explicit public-coin transcript implementation as the reference. Then add
a duplex Fiat-Shamir challenger with domain separation for:

- statement and circuit digest;
- each base FLOCK phase;
- stacked-PCS commitments and queries;
- exposed-message masks; and
- inner VEIL proofs.

Implement a programmable-random-oracle simulator harness, borrowing transcript
and oracle infrastructure—not masks—from the old `zk-flock` branch. Label this
mode computational and experimental. Do not claim that VEIL's interactive perfect
ZK theorem automatically covers it.

**Exit gate:** native FS proofs are deterministic under fixed coins, transcript
forks are domain-separated, and the programmed-oracle simulation passes all
shape and negative-control tests.

## P9 — Register profiles and publish an experimental report

Initially register only:

- tiny deterministic test parameters;
- `blake3-64x256-secure-udr-v0`; and
- one large-batch profile to measure asymptotic overhead.

Each profile records code dimensions, query limit, security estimate, circuit
digest, transcript version, and simulator version. Unknown profiles fail closed.

Benchmark baseline versus interactive ZK versus FS ZK. Report absolute numbers
and ratios for proving, verification, proof bytes, commitment bytes, and peak
memory. In particular, report the 256-instance padding cost rather than projecting
large-batch VEIL overhead onto it.

**Exit gate:** an experimental security/benchmark report states exactly what is
hidden, simulator model, unresolved assumptions, and measured overhead.

## Expected sequence and risk

A plumbing-only prototype through P3 should take roughly 2–4 weeks. An end-to-end
interactive experiment through P7 is more plausibly 8–14 engineer-weeks. The
largest uncertainty is not Rust integration; it is establishing the `F128`
ZK/product-code properties and ensuring recursive Ligerito fits the partial-ZK PCS
assumptions.

Stop and revisit the architecture if any of these occur:

- an allowed query set is not covered by the padding projection argument;
- the verifier circuit requires hashing witness-dependent exposed data inside the
  inner arithmetic proof at prohibitive cost;
- recursive Ligerito query choices are adaptive in a way excluded by the model;
- terminal or ring-switch values cannot be represented consistently as exposed
  messages; or
- the inner proof dominates the 256-instance baseline beyond the experiment's
  utility.


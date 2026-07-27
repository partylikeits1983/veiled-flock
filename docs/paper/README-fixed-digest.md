# Zero-Knowledge Proofs of BLAKE3 Preimage Knowledge in Flock (v6)

**The statement changed.** Everything before v5.2 was about the BLAKE3 *batch*
statement, which binds no public input and therefore asserts only that some
valid compressions exist. v6 is about the statement applications actually ask
for:

```
public   y_1 … y_n     BLAKE3 digests
private  x_1 … x_n     64-byte messages
claim    BLAKE3(x_i) = y_i   for every i
```

**Status: both halves of the property are implemented and tested.** A simulator
that receives only the public digests and whose output the *unmodified*
verifier accepts, and an extractor that recovers real preimages and **fails on
the simulator's own commitment**. Subject to the conditions below, this is a
computational zero-knowledge argument of knowledge in the classical ROM for the
certified configuration.

## Why the old statement was not enough

The batch statement's simulator is the honest prover on a witness it chooses
itself — legitimate *precisely* because nothing constrains the witness. Pin a
digest and two things break at once: a simulator that could produce a matching
witness would be inverting BLAKE3, and the preimage becomes essentially unique,
so **witness-indistinguishability — what every earlier certificate measures —
is vacuous**. The fixed-digest statement is a new object, and none of the
earlier evidence transfers unexamined.

## What was built

| piece | what it does |
|---|---|
| `ParamPinning::RootHash64` | pins `cv=IV`, `counter=0`, `block_len=64`, `flags=ROOT\|CHUNK_*` so one compression **is** a full BLAKE3 hash |
| `digest_bind` | binds the public digest list with one verifier-computed packed-direct claim inside the existing opening |
| `Blake3PreimageSetup` / `…ZkSetup` | plain and masked provers for the relation |
| `sim_oracle` | a programmable random oracle — the ROM game made executable |
| `preimage_simulator` | the simulator: accepting proof from the digests alone |
| `preimage_extractor` | recovers preimages, verified **outside** the circuit |
| `preimage_zk_certificate` | the coverage measurements behind distribution equality |

## Results

| property | result |
|---|---|
| unmodified verifier accepts simulated proof | yes |
| oracle points programmed | 18 |
| transcript shape, simulated vs honest | identical — 177,384 coordinates |
| P·Q channel on the round-pair block (m=22) | **4096 / 4096 bits** |
| degenerate mask (control) | 2048 / 4096 |
| patched vector satisfies the R1CS | **no** (control) |
| honest prover on the patched vector | **rejected** (control) |
| extraction from an honest commitment | recovers the real preimages |
| extraction from the simulator's commitment | **fails** (control) |

## The methodology, in six lines

1. **Take the verifier's checks as the specification** — classify each
   coordinate as determined or free, fill the free ones, solve the rest. This
   is what surfaced the ordering obstruction that makes oracle programming
   necessary rather than decorative.
2. **Every claim gets a control that must fail.** These caught real errors,
   including a desynchronised proof-of-work nonce that six unit tests missed
   because none of them grind.
3. **Keep the demonstration on the real code path** — one seam in the prover,
   not a parallel orchestration that would drift.
4. **Make the model executable** where feasible; RO programming is an object
   here, not a sentence.
5. **Prefer the witness-free statement** when the witness is unique.
6. **Write down what breaks.** Three plausible simulator constructions failed;
   all three are recorded, because a development that records only successes
   cannot be audited.

## What this rests on — quote these with the result

- **Sibling hiding is a ROM assumption**, not a derivation.
- **Coverage is measured at sampled challenge tuples**, not all of them.
- **The opening interior** is carried by the existing low-mask/blinder lemmas
  rather than measured at this relation.
- **The extractor's ROM-observation half is cited** (BCS, ePrint 2016/116), not
  executed.
- **Simulation-extractability is not proved**; plain ZK and plain AoK do not
  compose in the ROM.
- No quantitative extraction bound. 64-byte messages only. Classical ROM only.
- **No independent cryptographic review.**

## Reading order

1. `zk-flock-fixed-digest.tex` — the paper: relation, simulator, distribution,
   extraction, methodology, limits.
2. `zk-flock.tex` — the earlier batch-statement work, which supplies the mask
   channels this builds on.
3. `CHANGES-v6.md` — what moved from v5.2 to v6, including the findings that
   changed the design. (`CHANGES.md` is the superseded v5.2 record.)

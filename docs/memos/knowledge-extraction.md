# Memo: knowledge extraction for the fixed-digest relation

**Intended theorem.** The fixed-digest Flock argument is an argument of
knowledge in the classical ROM: any efficient prover producing accepting
proofs for public digests `y_1..y_n` with non-negligible probability yields
`x_1..x_n` with `BLAKE3(x_i) = y_i`.

**Status: implemented for the system-specific half; the ROM observation step
is the standard BCS argument and is cited, not re-proved.**

---

## 1. Why this memo exists

Zero knowledge and knowledge soundness pull against each other, and it is easy
to satisfy one while quietly losing the other. This repository had a simulator
before it had an extractor, which is the dangerous order: a protocol that
hides everything and proves nothing passes every ZK test.

The check that separates them is concrete and is now in the test suite:
**extraction must fail on the simulator's output**. The simulator knows no
preimage; if the extractor recovered one from its commitment, the extractor
would be recovering something else — a mask column, an opening claim, an
assignment untied to the digests — and the knowledge claim would be empty.

## 2. The extractor, in two halves

**Half one — recover the committed message (standard, cited).** In the
classical ROM the extractor is straightline. Every Merkle leaf the prover
commits is a random-oracle query, so an extractor watching the query
transcript reconstructs the committed codeword and decodes it. This is the BCS
compilation's extraction argument (Ben-Sasson–Chiesa–Spooner, *Interactive
Oracle Proofs*, ePrint 2016/116) applied to Flock's commitment, and this memo
does not re-derive it.

Two conditions it carries, both already tracked elsewhere:

* the hash-domain separation obligations (`pcs-simulation-options.md`), so
  leaf queries are distinguishable from transcript queries;
* the proximity/decoding regime of the Ligerito opening
  (`pcs/ligerito.rs` records which theorem each configuration was derived
  under), which is what makes "the committed codeword decodes to a unique
  message" true rather than assumed.

**Half two — turn the committed message into preimages (implemented).** This
is the system-specific part and where a mistake would hide. It is
`crates/flock-prover/src/preimage_extractor.rs`:

1. read the message region — bits `[M_BASE, M_BASE+512)` of each block, in the
   packed layout — for each instance;
2. hash each candidate with the `blake3` crate, **outside the circuit**;
3. compare against the public digest; any mismatch is an extraction failure.

Step 3 is the whole content of the claim. It refers to no circuit wire, no
claim value, and no part of the proof, so an extractor that had recovered the
wrong region cannot pass it.

## 3. What the tests establish

| test | establishes |
|---|---|
| `extractor_recovers_the_preimages_from_an_honest_commitment` | the recovered bytes ARE the preimages, and hash to the digests |
| `extraction_fails_on_the_simulators_commitment` | the extractor is not vacuous — it distinguishes knowledge from simulation |
| `extraction_ignores_the_mask_columns` | perturbing the randomizer sections changes the commitment but not one extracted byte |

The middle one is the load-bearing test of this memo.

## 4. What the mask amendments do to extraction

Each mask channel has to be shown not to disturb the argument, and each is a
one-line statement given the layout:

* **randomizer rows** occupy positions above `useful_bits` and satisfy
  `u·1 = u` / `1·u′ = u′`, which constrain nothing else; the extractor never
  reads them (tested).
* **`P`, `Q`, `S`, `S_c`, `S_h`** live in *separate commitments*. They are
  never part of the witness vector the extractor decodes, so they cannot be
  returned in its place.
* **`μ` (low-half mask) and `g` (blinder)** are part of the committed message
  and the blinded fold respectively; the extractor reads the witness half,
  whose offset is fixed by the layout.

Under a pinning, the compression parameters are also constants of the
relation, so an extracted assignment that satisfies the circuit necessarily
used `cv = IV`, `counter = 0`, `block_len = 64`, `flags = ROOT|CHUNK_*` —
which is what makes "the circuit computed BLAKE3" transfer to the extracted
bytes.

## 5. Open

* **Simulation-extractability.** Plain ZK plus plain AoK do not compose in the
  ROM. The target is *weak* simulation-extractability — extraction for
  statements never queried to the simulation oracle — with the
  divergence-at-`absorb_statement` lemma of `security-definitions.md` §4 as
  the mechanism. Not proved.
* **A quantitative bound.** No extraction probability or running-time bound is
  stated here; the BCS argument supplies the shape, but instantiating it with
  this system's parameters is not done.
* **An executable straightline extractor.** Half one is cited rather than run.
  Making it executable would mean routing the commitment's leaf hashing
  through the recording oracle of `sim_oracle.rs`, which is a plumbing change
  to a performance-critical path — worth doing, not done.

## 6. Go/no-go

**Go** to describe the mode as an argument of knowledge *for the certified
configuration, in the classical ROM, with the BCS extraction step cited and
the system-specific step implemented and tested*.

**No-go** on an unqualified "argument of knowledge" claim, on any
simulation-extractability claim, and on any quantitative extraction bound,
until §5 closes.

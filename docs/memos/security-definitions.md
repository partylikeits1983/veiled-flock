# Memo: security definitions for the fixed-digest statement

> **Historical design memo.** The definitions remain useful, but the status
> discussion below predates the implemented field-valued simulator and
> extractor. Current claim status is controlled by `docs/paper/zk-flock.tex`
> and `docs/memos/knowledge-extraction.md`.

**Intended theorem.** The Flock argument for
`R = {((y_i), (x_i)) : BLAKE3(x_i) = y_i}` is a noninteractive zero-knowledge
argument of knowledge in the classical random-oracle model.

**Status: research design.** These are the definitions the construction must
meet. Nothing here is proved yet; the point of writing them first is that the
two properties pull in opposite directions and the protocol must satisfy both
*simultaneously*, which is exactly what the earlier batch-statement work never
had to arrange.

---

## 1. Model

- **Classical ROM**, one random oracle `H`, used for Fiat–Shamir, Merkle
  commitments, and proof-of-work grinding. Domain separation between those
  uses is a protocol obligation, not an assumption (see
  `pcs-simulation-options.md`); today all three are SHA-256 with only
  incidental input-shape separation.
- **Transparent**: no CRS, no trapdoor, no structured setup. This is a hard
  requirement — a trapdoor-CRS variant is out of scope for this program, and
  if the transparent route fails the honest outcome is "open problem", not a
  quiet change of trust model.
- Statements may be chosen **adaptively**; multiple proofs share the oracle.
- QROM: not claimed, for either property.
- Side channels (timing, memory access, retry counts): out of scope.

## 2. Zero knowledge

> **Definition (NIZK).** There is a PPT simulator `S` such that for every
> statement `y` and every witness `x` with `(y, x) ∈ R`, the distributions
>
> ```
>   { π ← P^H(y, x) }        and        { π ← S^{H[·]}(y) }
> ```
>
> are computationally indistinguishable to a distinguisher with oracle access
> to `H`, where `S` may program `H` at points of its choosing.

`S` receives **only** `y`. It gets no preimage, no compression trace, no
witness commitment, and no trapdoor — there is none to give.

**Why the existing simulator does not port.** The batch-statement simulator is
the honest prover on a witness it generates itself; witness-indistinguishability
plus self-generatability gave ZK for free. Here:

- the preimages are essentially **unique**, so witness-indistinguishability is
  *vacuous* — there is no second witness to be indistinguishable from;
- a simulator that could produce any valid witness for a given `y` would be
  inverting BLAKE3.

So the masking work does not by itself give zero knowledge for this statement.
What it gives is the input to the real argument: the honest transcript's
witness-dependent coordinates are uniform on an explicit affine coset given
public values, which is what lets a simulator *sample* them. The construction
that turns that into a simulator is in `interactive-simulator-design.md`.

**Consequence for the coverage certificates.** Their witness-pair form
(`f(w) − f(w′) ∈ Im A` over pairs of valid witnesses) is unusable for a
unique-witness relation. The certificates must be restated in the witness-free
**quotient** form — the mask image covers the whole witness-dependent
coordinate space modulo the public claims — which is strictly stronger and
does not quantify over witness pairs at all.

## 3. Knowledge soundness

> **Definition (argument of knowledge, straightline in the ROM).** There is a
> PPT extractor `E` which, given a prover `P*`'s random-oracle query
> transcript and an accepting proof `π` for `y`, outputs `x_1..x_n` with
> `BLAKE3(x_i) = y_i`, except with negligible probability.

Three things this must NOT be satisfied by, each of which is a real failure
mode for this codebase:

1. extracting *mask* columns (the randomizer rows, `P`, `Q`, `S`, `S_c`,
   `S_h`) instead of witness columns;
2. extracting an assignment that satisfies the R1CS but is not tied to the
   public digests;
3. extracting an "opening claim" rather than the committed polynomial.

The extractor must produce **byte strings** that the caller can hash outside
the circuit and compare to `y` — implemented as a deterministic projection
from a satisfying assignment to the message words, with an external BLAKE3
recheck.

**Prerequisite that is currently missing.** The repository has no extractor
and no extraction argument: knowledge soundness of the base system is asserted
by proximity to the Ligerito paper's theorems plus prose that the mask
channels do not disturb it. Specifying the *base* extractor is step one of
`knowledge-extraction.md`; the amendment-preservation arguments only make
sense on top of it.

## 4. Simulation-extractability (the multi-proof obligation)

Plain ZK plus plain AoK do not compose in the ROM: once an adversary has seen
simulated proofs, its own forgery may reuse programmed oracle points, and the
straightline extractor's reconstruction is no longer sound at those points.

> **Definition (weak simulation-extractability).** For an adversary with
> access to a simulation oracle for statements of its choice, any accepting
> proof it outputs for a statement **never queried to that oracle** yields a
> witness via `E`.

The mechanism that makes this reachable is the statement absorption of
`fixed-digest-relation.md` §6: a proof for a statement never simulated
diverges from every programmed prefix at `absorb_statement`, so all of its
challenges are honest oracle values and straightline extraction applies. That
is the **divergence lemma**, and it is the reason statement absorption is a
security requirement rather than hygiene.

Statements the adversary *did* query are excluded by the definition — correct
for this application, where the point is knowledge of preimages of digests the
adversary did not obtain a proof for.

## 5. What each property forbids

| | ZK requires | AoK requires |
|---|---|---|
| commitment | simulatable without a witness | binding, extractable |
| openings | fabricable at chosen points | tied to one committed polynomial |
| challenges | simulator may program | prover may not predict |
| masks | must hide the witness | must not be extractable *as* the witness |

Every row is a tension, and each is discharged in a different memo. The reason
to write them down before building is that a construction satisfying either
column alone is easy and worthless.

## 6. Open questions

1. Is the marginal distribution of the honest PIOP block, conditioned on the
   interface claims, independent of the PCS block? (The **factorization
   lemma** — the hybrid simulator samples them separately.)
2. Does the straightline extractor survive the *masked* prover, i.e. can mask
   columns be separated from witness columns at extraction time by a
   syntactic argument on the layout, or does it need the R1CS structure?
3. Does the adaptive-statement setting need full (rather than weak)
   simulation-extractability for the intended applications?

## 7. Go/no-go

**Go** to write the simulator design against these definitions.
**No-go** on publishing any ZK or AoK claim for the fixed-digest statement
until §2 and §3 have constructions and §4 has a proof — and in particular, no
claim may be inherited from the batch-statement results, whose simulator is
invalid here for a stated reason.

# Memo: knowledge extraction for the fixed-digest relation

**Intended theorem.** The fixed-digest Flock argument is an argument of
knowledge in the classical ROM: any efficient prover producing accepting
proofs for public digests `y_1..y_n` with non-negligible probability yields
`x_1..x_n` with `BLAKE3(x_i) = y_i`.

**Status: the recording-oracle Merkle recovery and system-specific preimage
check are executable. The standalone Fiat-Shamir knowledge claim is explicitly
dual-labelled: about 56 provable bits at `Q = 2^64`, and 100-bit conjectured
classical knowledge security.**

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

**Half one — recover the committed message.** Every framed Merkle leaf is a
random-oracle query. `RecordingOracle` records those points by commitment
channel; `recover_witness_from_leaf_queries` reconstructs the complete wide
codeword; and `ligerito_decode::decode_zk_codeword` inverse-transforms,
re-encodes, checks the unique-radius condition, and returns the witness half
without the low mask or blinder. It is an exact-word decoder and candidate
validator, not a complete Reed--Solomon correction algorithm for every noisy
word inside the theoretical radius. Duplicate, missing, malformed, and
non-decoding transcripts fail closed; the general noisy-word step remains a
theorem-level Ligerito obligation.

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
* **`P`, `S`, `S_c`, `S_h`** live in *separate commitments*. They are
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

## 5. Quantitative knowledge bound

The recursive opening is treated as a Gamma-special-sound public-coin
protocol and Fiat-Shamir extraction uses the classical-ROM `(Q+1) * kappa`
loss. The L0 fold access structure alone contributes
`kappa >= 257 / 2^128`; therefore it alone caps the standalone theorem at
`119.994 - log2(Q+1)` bits. At `Q = 2^64` this is 55.994 bits.

`scripts/knowledge-ledger.py` pins the three deployment profiles and checks
`docs/artifacts/knowledge-ledger.json`:

| profile | provable knowledge | label |
|---|---:|---|
| standalone FS, F2^128 | ~56 bits at Q=2^64 | 100-bit conjectured classical knowledge security |
| unbiased post-commitment beacon, F2^128 | ~120 bits | provable 100-bit, not standalone |
| standalone FS, challenge-only F2^256 | ~184 bits at Q=2^64 | engineering follow-up; not implemented |

This is a classical Fiat-Shamir loss. The shipped standalone theorem column
must remain 55.994 bits at `Q = 2^64`.

## 6. Simulation extractability

`sim_ext::SimulatedPrefixSet` records
`(statement_digest, proof_nonce, protocol_version)`. The executable extractor
runs only for a fresh tuple and refuses a tuple returned by the simulation
oracle. This is the claimed fresh-prefix weak simulation-extractability
notion. Same-statement, same-nonce simulation extractability remains open and
is not claimed.

## 7. Go/no-go

**Go** on computational ZK, the executable recording-oracle extractor, and
fresh-prefix weak simulation extractability for certified configurations.

**No-go** on a 100-bit standalone theorem over F2^128, straightline RBR
knowledge, or same-prefix simulation extractability.

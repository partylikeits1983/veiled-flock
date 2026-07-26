# zk-Flock design log: every step, and why it was made

The paper will be written **once, at the end, after the ZK property is
actually established** — no per-revision restamps. Until then this log is the
paper's source material: one entry per design step, in order, each recording
*what* was done and *why it was forced* — by a measurement, a broken proof, or
a reviewer's argument. Detailed, not verbose. Keep it append-only; a step that
is later reversed gets a new entry saying so and why, the old entry stays.

## 1. Randomizer witness rows

Extra R1CS rows `u·1 = u` / `1·u′ = u′` filled with fresh coin flips, inside
the committed witness. **Why:** the affine transcript classes (round-1
vectors, final evaluations, lincheck rounds, `z_partial`, `s_hat_v`) are
linear in the witness at fixed challenges, so uniform bits riding inside the
witness blind them; because the randomness is committed with the witness, it
is bound before every challenge automatically and the hand-optimized sumcheck
kernels need zero changes. The textbook additive masking polynomial does not
work here: over a binary field the standard separable mask sums to zero on
the cube.

## 2. Hiding PCS commitment (μ) and recursive blinder (g)

Committed message becomes `[μ ‖ witness]` with μ in the LOW coefficient
slots; a second fully-random polynomial `g` shares the wide Merkle leaves;
the opening runs the unchanged Ligerito recursion on `F = m′ + c·g` with the
order `y_g observed → PoW grind → c sampled`. **Why μ low:** the LCH/additive
NTT basis is degree-graded — low slots span all degrees < t, so any t opened
positions receive a surjective mask→symbol map; a top-half mask is multiplied
by a subspace-vanishing polynomial and contributes nothing on half the
domain. **Why g:** every opened row, internal opening-sumcheck message, and
the residual are F₂¹²⁸-linear in the committed data, so one uniform blinder
masks them all at every recursion level. **Why the ordering:** a prover that
chose `y_g` after seeing `c` could shift the combined target and prove a
false claim; the PoW prices re-grinding attempts against a degree-1-in-c
identity.

## 3. A1′: the degree-2 P·Q zerocheck channel

Run the AB sumcheck on `â·b̂ + γ·P·Q` with P, Q fresh witness-free committed
cubes; combined round messages `G_j + γM_j`; final check
`â(ρ)b̂(ρ) + γ·P(ρ)Q(ρ)`. **Why degree 2:** the round message `G_j(∞)` is
the leading coefficient of a degree-2 polynomial — no degree-1 mask can move
it, and in characteristic 2 the classical separable mask vanishes on the cube
entirely. **Why the openings of P, Q must be hiding:** a plain opening
reveals ~queries×rows additional P-functionals; by the `dim R(ker L)`
accounting those un-cover claim-preserving witness directions — measured, a
real leak. With hiding openings the only leaked P-functionals are `P(ρ)`,
`Q(ρ)`, `σ_z`, and conditioning on them removes exactly the public ab-claim
direction.

## 4. The lesson that forced everything after: joint, not marginal

The real-statement certificate (m=20, 64 blocks) initially FAILED with one
F₂¹²⁸ claim-preserving direction escaping — while `round1_c` passed its
marginal test at 8,192/8,192 the entire time. **Why it matters:** per-class
(marginal) coverage does not compose into joint coverage; and the broken
assumption ("the randomizer rows cover the affine classes") had never been
written down as an assumption. It is true on the synthetic fixture (~81%
randomizer rows) and false on a real witness (~5.5%). A certificate run only
on the vehicle would have reported success indefinitely.

## 5. A2: the additive lincheck mask S

The lincheck sumcheck runs on `z + γ_lc·S` with S a committed witness-free
cube; the claim is un-shifted at the end via `Ŝ(ρ)`. **Why additive, not
degree-2:** the lincheck deficit was measured to be STRUCTURAL (a sizing
repair — 2.3× randomizer entropy — changed nothing), and the lincheck's
messages are linear in the table, so an additive shift suffices. **Why a new
channel at all:** the escaping direction localized to the lincheck layer; the
randomizer rows cannot reach it on a real witness (see step 4).

## 6. A3: the round-1 mask pair (M_c, M_c + V_S·h)

Round-1 messages gain `round1_c += M_c`, `round1_ab += M_c + V_S·h`, with
`mc_at_z`, `h_at_z` bound by hiding openings at the c-claim point. **Why the
pair shape:** the verifier's round-1 reconstruction identity must keep
holding; `V_S·h` vanishes on S, so the combined polynomial's zerocheck
assumption is preserved. **Why not the cheap diagonal design:** the measured
`round1_c` residual is off-diagonal — construction (a) was ruled out by
measurement before (b) was built (`docs/round1c-mask-channel.md`).

## 7. Composition repair: coprod → triangular

The intended composition (`coprod_covers`: sum of channel images) is INVALID
for this transcript: it needs both channels additive, and the randomizer
channel is certifiably bilinear on exactly the round-pair coordinates it was
needed for (`final_b_eval` has an identically-zero inner-mask derivative —
the coordinate that also disproved the earlier flat-mixture argument).
**Replacement:** the triangular/quotient composition
(`MaskingTriangular.lean`): constant inner image (H1), outer-affine offset in
the quotient (H2), outer coverage of the residue (H3) — each hypothesis
discharged by a measurement on the real prover.

## 8. ε_rank: Schwartz–Zippel withdrawn, per-proof check instead

The claimed `ε_rank ≤ deg/2¹²⁸` bound was WITHDRAWN: the implemented P, Q are
Boolean bit-cubes, so the bound's "uniform entries in F₂¹²⁸" hypothesis is
false, and SZ over {0,1} is vacuous at these degrees. **Replacement:** a
per-proof coverage self-check with resample-on-failure
(`prove_zk_a1_checked`), making ε_rank = 0 for emitted proofs — at the cost
of ~4×10³ full-cube fold passes per proof, and with the caveat recorded in
step 10 below.

## 9. Phase 0 (2026-07-26): the evidence pipeline is repaired, label A → B

The branch had promoted the status to label A on the strength of passing
certificates. Review found the *pipeline* those certificates ran under
overstated itself, and the label was withdrawn pending one green run of the
hardened runner. What was found and fixed, and why each guard exists:

- `scripts/zk-certify.sh` recorded a failure of the flagship
  complete-transcript certificate in its manifest but **exited 0** — a
  certificate runner that cannot fail is not evidence. Now fail-fatal, with
  the (incomplete) manifest printed on abort.
- Three `--lib` gates (the m=22 A1′ and fast-path roundtrips, the A3 staged
  roundtrip) addressed module-scoped tests by bare name under `--exact`,
  matching **zero tests** — those roundtrips were never executed by the
  runner at all. Now addressed by full module path, and `run()` fails any
  gate whose filter matches no tests, so a renamed test can never turn a
  gate vacuous again.
- The registry's evidence check (`zk_certificate_evidence_matches_script`)
  matched test names by **substring** into the script text — it passes for a
  name that only appears in a comment, and cannot notice tests the script
  runs but the registry does not vouch for. Now exact-name and bidirectional.
- The PCS rank audit and its negative control
  (`pcs::zk_audit::pcs_rank_audit_negative_control_without_g`) were cited by
  the joint certificate's conditioning argument but absent from the evidence
  set and the runner. Now both are evidence and both run.
- The joint certificate's header advertised six negative controls; two
  existed. The **mask-reuse control** is now implemented
  (`mask_reuse_across_proofs_is_a_leak`): with a reused mask draw the
  observable pair-difference of two proofs is a deterministic witness
  functional (measured: nonzero on 210/526 affine coordinates, bit-identical
  across draws), while a fresh draw moves all 526 — fresh-per-proof masks
  are load-bearing, which is what the multi-proof composition argument
  needs. The remaining advertised controls are genuinely owned by other
  tests (no-P → H1's control; constant-Q → the P-channel image control;
  no-μ/g → the PCS audit's control) and the header now says so by name
  instead of advertising them here.
- A3's cubes stay UNPROBED in the flagship certificate on purpose: their
  leakage is conditioned on while their coverage is not credited, which is
  the strictly stronger direction; the A3 channel's own image is probed
  where A3 is load-bearing (the real-statement certificate). The comment now
  records the delegation.

## 10. Phase 0 (2026-07-26): the FS-circularity caveat is stated

The per-proof check's rationale claimed the resample event "depends only on
(Q, challenges), both witness-independent". Under Fiat–Shamir that is not
literally true: the check runs after `bind_statement`, so the challenges are
derived from the witness commitment root — a function of the witness. The
witness-independence is **computational**, via the commitment's hiding, and
that step must appear as an explicit lemma in the proof document rather than
as an unstated assumption. (The planned move to field-valued small-domain
masks would delete the rejection-sampling mechanism and reduce this to the
same commitment-hiding lemma the FS lift already needs.)

## 11. Fixed-digest re-scope (2026-07-27): the statement becomes useful

The batch statement binds nothing, so every ZK result proved for it is a
result about "there exist valid compressions". The target became the statement
applications ask for: **public digests `y_i`, private preimages `x_i`,
`BLAKE3(x_i) = y_i`**. Three steps, each forced:

**Pin the compression parameters.** BLAKE3 of a ≤64-byte message is one
compression with `cv = IV`, `counter = 0`, `block_len = 64`,
`flags = CHUNK_START|CHUNK_END|ROOT`. `ParamPinning::RootHash64` pins those
rows so the circuit computes a *hash* rather than *a* compression; the message
words stay free as the witness. **Why per-bit row surgery:** `C = I` already
gives `(A·z)_i·(B·z)_i = z_i`, so `1·1 = z_s` and `0·1 = z_s` pin without any
new mechanism, and the choice lands in `statement_digest` automatically.

**Why the zero case keeps the constant wire on the b-side.** `0·0 = z_s` pins
just as well and satisfies the R1CS. It also breaks every honest proof: the
witness generator emits `b[s] = 1` for parameter slots, so the Hadamard
product matched while the `B·z` *vector* did not, and the lincheck — which
checks the matrix-vector products — rejected. Cost: one debugging cycle.
Recorded because any future pinning has the same trap.

**Bind the digests with one public-target packed-direct claim.** The verifier
computes `ŷ(τ)` itself from the public list and demands
`ẑ_packed(τ, sel=OUT, ι) = ŷ(τ, ι)` inside the *existing* batched opening.
**Why a random point and not the digest's Boolean indices:** a ring-switched
claim at a Boolean point publishes `s_hat_v`, whose entries are then the 128
raw bits of the witness word — the naive binding would leak the witness it is
supposed to constrain. **Why not a lincheck β-fold:** 256 β's and surgery
inside the masked lincheck, for no better soundness.

**Padding is not free.** The const-pin already required padding slots to hold
a valid compression; under a pinning they must satisfy the pinned rows too, so
their digest is `BLAKE3(0⁶⁴)` rather than zero. A statement assuming
zero-padding computes the wrong target and rejects honest proofs, so the
padding rule is part of the statement hash.

**Statement absorption.** The digest list enters the transcript before any
challenge. This also closes a gap the chain statement still has: its public
endpoints are checked arithmetically but never absorbed.

## 12. The simulator problem, stated honestly (2026-07-27)

Masking the fixed-digest transcript is nearly free — the digest claim adds only
a public value — and `Blake3PreimageZkSetup` does it. **That is not zero
knowledge.** For a fixed digest the preimage is essentially unique, so
witness-indistinguishability — the property every certificate in this
repository measures — is *vacuous*, and the batch mode's simulator (the honest
prover on a self-chosen witness) would have to invert BLAKE3 to run.

What the masking work does provide is the input to a real simulator: the
witness-dependent coordinates are uniform on an explicit coset given public
values. The construction that turns that into a simulator is the two-phase
hybrid in `docs/memos/interactive-simulator-design.md` — sample the PIOP block
backwards, then run the *honest* PCS code on a claim-consistent pseudo-witness,
because naively sampling the opening coordinates lands outside the honest
support (deep-level opened rows satisfy RS code-parity relations the verifier
never checks but a distinguisher can).

**The ROM game is now executable.** `sim_oracle.rs` gives a programmable oracle
whose unprogrammed behaviour is byte-identical to Fiat–Shamir — verified by a
real proof that verifies both through the harness and under `FsChallenger`.
That control immediately caught the harness absorbing the PoW nonce untagged
where the real challenger tags it; six unit tests had missed it because none of
them grind. Acceptance under a programmed oracle will be necessary but not
sufficient: distribution equality is a separate measurement.

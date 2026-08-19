# flock-prover Sequence Diagrams

`flock-prover` is the top tier: the two binaries, the R1CS hash circuits, proof I/O, the
succinct VEIL glue, and the ZK certificate machinery. It re-exports all of `flock-core`
(`crates/flock-prover/src/lib.rs:15`) and depends on `veil-f128` only under the `veil`
feature. It owns no protocol of its own — it composes the two crates below it.

The active statement is `Blake3PreimageZkSetup` at
`crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:413`, whose three entry points
are `prove_succinct`, `verify_succinct`, and `simulate_succinct`.
`crates/flock-prover/src/veiled_preimage.rs` is the **legacy** direct whole-R1CS path and
is not on the active path; it appears here only where a name collides with it.

Lane pipes hold a fixed column on every row; `*` marks a call that stays inside its own
lane. An arrowhead lands one column short of the receiving lane so no pipe is erased.

## Diagram 1 — prove

Lane pipes sit at columns 3, 10, 17, 24, 31, 38 and the label column starts at 44.

Participants:

- `CLI` = `veiled_flock::prove`
  `crates/flock-prover/src/bin/veiled_flock.rs:117`
- `SETUP` = `Blake3PreimageZkSetup`
  `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:413`
- `WIT` = `generate_witness_with_ab_packed_and_lincheck_zk_pinned`
  `crates/flock-prover/src/r1cs_hashes/blake3.rs:1545`
- `SV` = `prove_succinct_veil_r1cs`
  `crates/flock-prover/src/succinct_veil.rs:596`
- `CORE` = `flock_core` crate root (`pcs` at `:27`, `lincheck` at `:24`, `zerocheck` at
  `:36`)
  `crates/flock-core/src/lib.rs:1`
- `VEIL` = `veil_f128::constraints`
  `crates/veil-f128/src/constraints.rs:1`

```text
  CLI    SETUP  WIT    SV     CORE   VEIL
  |      |      |      |      |      |
  |----->|      |      |      |      |     1 prove_succinct
  |      |*     |      |      |      |     2 statement
  |      |----->|      |      |      |     3 generate_witness_with_ab_packed_and_lincheck_zk_pinned
  |      |<-----|      |      |      |     4 (z, a, b, z_lincheck)
  |      |------------------->|      |     5 absorb_statement
  |      |------------>|      |      |     6 prove_succinct_veil_r1cs
  |      |      |      |*     |      |     7 MaskLayout::new
  |      |      |      |------------>|     8 commit_constraint_inputs
  |      |      |      |----->|      |     9 commit_zk_with_ro
  |      |      |      |----->|      |     10 bind_statement
  |      |      |      |----->|      |     11 prove_packed_padded_capture_s_hat_v_c
  |      |      |      |----->|      |     12 prove_padded_capture_z_vec
  |      |      |      |*     |      |     13 mask_proofs
  |      |      |      |*     |      |     14 shifted_verifier_circuit
  |      |      |      |*     |      |     15 fork veil_challenger
  |      |      |      |----->|      |     16 open_claims_with_precomputed_ligerito_pd_ro
  |      |      |      |------------>|     17 prove_constraints_from_commitment
  |      |<------------|      |      |     18 SuccinctVeilProof
  |<-----|      |      |      |      |     19 (SuccinctVeilProof, Commitment)
  |*     |      |      |      |      |     20 Bundle encode and write
```

Anchors (every message, returns included; a return reuses its call's anchor):

1. `Blake3PreimageZkSetup::prove_succinct`
   `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:528`
2. `Blake3PreimageZkSetup::statement`
   `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:509`
3. `generate_witness_with_ab_packed_and_lincheck_zk_pinned`
   `crates/flock-prover/src/r1cs_hashes/blake3.rs:1545`
4. return of message 3 — same definition
   `crates/flock-prover/src/r1cs_hashes/blake3.rs:1545`
5. `absorb_statement` — active path, not the legacy twin at
   `crates/flock-prover/src/veiled_preimage.rs:347`
   `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:896`
6. `prove_succinct_veil_r1cs`
   `crates/flock-prover/src/succinct_veil.rs:596`
7. `MaskLayout::new` — call site
   `crates/flock-prover/src/succinct_veil.rs:613`
8. `commit_constraint_inputs` — called at
   `crates/flock-prover/src/succinct_veil.rs:622`
   `crates/veil-f128/src/constraints.rs:418`
9. `pcs::commit::commit_zk_with_ro` — called at
   `crates/flock-prover/src/succinct_veil.rs:633`
   `crates/flock-core/src/pcs/commit.rs:286`
10. `bind_statement` — called at
    `crates/flock-prover/src/succinct_veil.rs:641`
    `crates/flock-core/src/proof.rs:51`
11. `zerocheck::prove_packed_padded_capture_s_hat_v_c` — called at
    `crates/flock-prover/src/succinct_veil.rs:680`
    `crates/flock-core/src/zerocheck.rs:406`
12. `lincheck::prove_padded_capture_z_vec` — called at
    `crates/flock-prover/src/succinct_veil.rs:708`
    `crates/flock-core/src/lincheck.rs:1250`
13. `mask_proofs` — called at
    `crates/flock-prover/src/succinct_veil.rs:735`
    `crates/flock-prover/src/succinct_veil.rs:382`
14. `shifted_verifier_circuit` — called at
    `crates/flock-prover/src/succinct_veil.rs:738`
    `crates/flock-prover/src/succinct_veil.rs:456`
15. `veil_challenger` fork, before the terminal Ligerito protocol — call site
    `crates/flock-prover/src/succinct_veil.rs:764`
16. `open_claims_with_precomputed_ligerito_pd_ro` — called at
    `crates/flock-prover/src/succinct_veil.rs:774`
    `crates/flock-prover/src/prover.rs:114`
17. `prove_constraints_from_commitment` — called at
    `crates/flock-prover/src/succinct_veil.rs:787`, consuming the `veil_commitment`
    produced by message 8
    `crates/veil-f128/src/constraints.rs:468`
18. `SuccinctVeilProof`
    `crates/flock-prover/src/succinct_veil.rs:33`
19. return of message 1 — same definition
    `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:528`
20. `Bundle`
    `crates/flock-prover/src/bin/veiled_flock.rs:18`

Message 20 is the `proof_io` write side. Serialization helpers live in
`crates/flock-prover/src/proof_io.rs:264` (`write_bytes_to_file`) and
`crates/flock-prover/src/proof_io.rs:280` (`read_bytes_from_file`); the `veiled_flock`
binary carries its own `Bundle` encoding with magic `VFLK0003`
(`crates/flock-prover/src/bin/veiled_flock.rs:15`).

## Diagram 2 — verify

Participants:

- `CLI` = `veiled_flock::verify`
  `crates/flock-prover/src/bin/veiled_flock.rs:138`
- `SETUP` = `Blake3PreimageZkSetup::verify_succinct`
  `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:597`
- `SV` = `verify_succinct_veil_r1cs`
  `crates/flock-prover/src/succinct_veil.rs:808`
- `CORE` = `flock_core::verifier`
  `crates/flock-core/src/verifier.rs:199`
- `VEIL` = `veil_f128::constraints::verify_constraints`
  `crates/veil-f128/src/constraints.rs:539`

```text
  CLI    SETUP  SV     CORE   VEIL
  |      |      |      |      |
  |*     |      |      |      |     1 read bundle + magic VFLK0003 check
  |*     |      |      |      |     2 re-serialize and byte-compare (canonicality)
  |----->|      |      |      |     3 verify_succinct
  |      |*     |      |      |     4 statement + validate
  |      |------------>|      |     5 absorb_statement
  |      |----->|      |      |     6 verify_succinct_veil_r1cs
  |      |      |*     |      |     7 parameter check -> InvalidParameters
  |      |      |----->|      |     8 bind_statement
  |      |      |----->|      |     9 observe_label + observe_bytes(mask root)
  |      |      |*     |      |     10 shifted_verifier_circuit (re-derived)
  |      |      |*     |      |     11 observe_claims + packed_direct
  |      |      |*     |      |     12 fork veil_challenger
  |      |      |----->|      |     13 verify_claims_ligerito_with_config_pd_ro
  |      |      |<-----|      |     14 Err(pcs::VerifyError) -> abort
  |      |      |------------>|     15 verify_constraints
  |      |      |<------------|     16 Err(ConstraintError) -> abort
  |<------------|      |      |     17 Ok(())
```

Anchors:

1. `MAGIC` = `VFLK0003`
   `crates/flock-prover/src/bin/veiled_flock.rs:15`
2. `Bundle`, re-serialized and byte-compared to reject non-canonical encodings
   `crates/flock-prover/src/bin/veiled_flock.rs:18`
3. `Blake3PreimageZkSetup::verify_succinct`
   `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:597`
4. `Blake3PreimageZkSetup::statement`
   `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:509`
5. `absorb_statement`
   `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:896`
6. `verify_succinct_veil_r1cs`
   `crates/flock-prover/src/succinct_veil.rs:808`
7. `SuccinctVeilError::InvalidParameters`
   `crates/flock-prover/src/succinct_veil.rs:48`
8. `bind_statement`
   `crates/flock-core/src/proof.rs:51`
9. `Challenger::observe_label`
   `crates/flock-core/src/challenger.rs:34`
10. `shifted_verifier_circuit`
    `crates/flock-prover/src/succinct_veil.rs:456`
11. `pcs::PackedDirectClaimRef`
    `crates/flock-core/src/pcs.rs:804`
12. `veil_challenger` fork — mirrors prove message 15
    `crates/flock-prover/src/succinct_veil.rs:764`
13. `verifier::verify_claims_ligerito_with_config_pd_ro`
    `crates/flock-core/src/verifier.rs:199`
14. `From<pcs::VerifyError> for SuccinctVeilError`
    `crates/flock-prover/src/succinct_veil.rs:286`
15. `verify_constraints`
    `crates/veil-f128/src/constraints.rs:539`
16. `From<ConstraintError> for SuccinctVeilError`
    `crates/flock-prover/src/succinct_veil.rs:280`
17. return of message 6 — same definition
    `crates/flock-prover/src/succinct_veil.rs:808`

The verifier re-derives the shifted circuit (message 10) rather than trusting one from
the proof, and forks `veil_challenger` at the same transcript point the prover did
(message 12). Both are load-bearing: a verifier that accepted a supplied circuit, or
forked at a different point, would accept proofs the protocol does not.

## Diagram 3 — simulator and ZK certificate

The simulator path exists to make the zero-knowledge claim checkable. It produces a
transcript without a witness, and `SealedStatement` makes that a type-level guarantee
rather than a convention.

Participants:

- `call` = the driver (test or certificate harness)
  `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:641`
- `SETUP` = `Blake3PreimageZkSetup::simulate_succinct`
  `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:641`
- `SEAL` = `SealedStatement`
  `crates/flock-prover/src/sim_seal.rs:10`
- `ORC` = `sim_oracle`
  `crates/flock-prover/src/sim_oracle.rs:58`
- `SIM` = `RomZerocheckSimulator` / `preimage_simulator`
  `crates/flock-prover/src/succinct_veil.rs:80`
- `CERT` = `zk_certificate`
  `crates/flock-prover/src/zk_certificate.rs:52`

```text
  call   SETUP   SEAL    ORC    SIM    CERT
  |      |       |       |      |      |
  |----->|       |       |      |      |      1 simulate_succinct
  |      |------>|       |      |      |      2 SealedStatement (witness barrier)
  |      |*      |       |      |      |      3 ZkRng::from_seed + fork pseudo-messages
  |      |-------------->|      |      |      4 SharedOracle / ProgrammableOracle
  |      |       |       |*     |      |      5 ro_context(nonce, oracle)
  |      |--------------------->|      |      6 RomZerocheckSimulator::new
  |      |       |       |<-----|      |      7 OracleChallenger (programmed answers)
  |      |       |       |      |*     |      8 SuccinctZerocheckSource::emit
  |      |<---------------------|      |      9 SimulatedProof
  |      |---------------------------->|      10 ZkCertificate / require_certified
  |      |<----------------------------|      11 Err(ZkGateError) -> abort
  |<-----------------------------------|      12 certified transcript

```

Anchors:

1. `Blake3PreimageZkSetup::simulate_succinct`
   `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:641`
2. `SealedStatement`
   `crates/flock-prover/src/sim_seal.rs:10`
3. `zk::ZkRng`
   `crates/flock-core/src/zk.rs:56`
4. `ProgrammableOracle` (`crates/flock-prover/src/sim_oracle.rs:58`) and
   `sim_oracle::shared_oracle`
   `crates/flock-prover/src/sim_oracle.rs:166`
5. `sim_oracle::ro_context`
   `crates/flock-prover/src/sim_oracle.rs:192`
6. `RomZerocheckSimulator::new`
   `crates/flock-prover/src/succinct_veil.rs:87`
7. `sim_oracle::OracleChallenger`
   `crates/flock-prover/src/sim_oracle.rs:206`
8. `SuccinctZerocheckSource::emit` — the trait's only method
   (`crates/flock-prover/src/succinct_veil.rs:69`), implemented for
   `RomZerocheckSimulator` at `crates/flock-prover/src/succinct_veil.rs:113` and called
   at `crates/flock-prover/src/succinct_veil.rs:668`
   `crates/flock-prover/src/succinct_veil.rs:68`
9. `preimage_simulator::SimulatedProof`, produced by `simulate` at
   `crates/flock-prover/src/preimage_simulator.rs:454`
   `crates/flock-prover/src/preimage_simulator.rs:442`
10. `zk_certificate::ZkCertificate` and `require_certified` at
    `crates/flock-prover/src/zk_certificate.rs:223`
    `crates/flock-prover/src/zk_certificate.rs:52`
11. `zk_certificate::ZkGateError`
    `crates/flock-prover/src/zk_certificate.rs:79`
12. `sim_game::SimGameLedger` records the hop sequence backing the claim
    `crates/flock-prover/src/sim_game.rs:58`

## Notes

- `crates/flock-prover/src/veiled_preimage.rs` (504 lines) is **legacy** — the older
  direct whole-R1CS path, superseded by the succinct path drawn above. It is not
  dead: `absorb_statement` is defined twice, actively at
  `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:896` and legacy at
  `crates/flock-prover/src/veiled_preimage.rs:347`, so an unqualified reference to that
  name resolves to whichever module is in scope.
- `crates/flock-prover/src/prover.rs` is a single orchestration hub: 16 of the crate's
  30 source files reference `prover::` (`grep -rl 'prover::' crates/flock-prover/src`). That is
why its lane would carry most messages if it were drawn
  separately, and why new protocol glue belongs there rather than in either binary.
- The terminal opening's `pd` argument is produced between drawn messages 14 and 15 —
  `observe_claims` at `crates/flock-prover/src/succinct_veil.rs:758`, then
  `let pd = packed_direct(challenger)` at
  `crates/flock-prover/src/succinct_veil.rs:759` — and is consumed by message 16 at
  `crates/flock-prover/src/succinct_veil.rs:780`. `packed_direct` is a caller-injected
  `&mut dyn FnMut(&mut Ch) -> Vec<pcs::PackedDirectClaim>` declared at
  `crates/flock-prover/src/succinct_veil.rs:606`, so it gets a note rather than a lane: a
  closure supplied by the caller is not a participant. Without this, message 16's `&pd`
  argument is unexplained.
- Both binaries hand-roll argv parsing; `crates/flock-prover/src/bin/flock_chain.rs`
  says so explicitly ("tiny, no clap dep"). `veiled_flock` requires
  `required-features = ["veil"]`; `flock_chain` builds with default features.
- `RandomChallenger` (`crates/flock-core/src/challenger.rs:101`) is a seeded SplitMix64
  that ignores observed messages — no Fiat-Shamir binding at all. It is gated behind
  `cfg(any(test, feature = "unsound-challenger"))` and enabled only as a
  dev-dependency, so a normal build cannot name the type. Never enable it for a build
  that produces real proofs.

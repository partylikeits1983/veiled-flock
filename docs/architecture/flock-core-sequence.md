# flock-core Sequence Diagrams

`flock-core` owns the FLOCK PIOP (zerocheck, lincheck), the polynomial commitment
scheme, the Merkle and random-oracle layers, the Fiat-Shamir transcript, and the
verifier. It depends on no sibling crate. It delegates nothing: everything below the
statement level lives here.

The crate has no internal orchestrator. The order in which `zerocheck`, `lincheck`, and
`pcs` are driven is imposed by the caller — on the active path that is
`prove_succinct_veil_r1cs` at `crates/flock-prover/src/succinct_veil.rs:596`. The `caller`
lane below stands for that driver rather than inventing a flock-core-internal one.

Lane pipes hold a fixed column on every row; `*` marks a call that stays inside its own
lane. An arrowhead lands one column short of the receiving lane so no pipe is erased.

## Diagram 1 — prover

Participants:

- `caller` = the driver, on the active path `prove_succinct_veil_r1cs`
  `crates/flock-prover/src/succinct_veil.rs:596`
- `r1cs` = `BlockR1cs`
  `crates/flock-core/src/r1cs.rs:56`
- `ZC` = `zerocheck::prove_packed_padded_capture_s_hat_v_c`
  `crates/flock-core/src/zerocheck.rs:406`
- `LC` = `lincheck::prove_padded_capture_z_vec`
  `crates/flock-core/src/lincheck.rs:1250`
- `PCS` = `pcs::commit::commit_zk_with_ro` and `pcs::open_batch_...`
  `crates/flock-core/src/pcs/commit.rs:286`
- `CH` = `Challenger`
  `crates/flock-core/src/challenger.rs:30`

```text
  caller  r1cs    ZC      LC      PCS     CH
  |       |       |       |       |       |
  |------------------------------>|       |     1 commit_zk_with_ro
  |-------------------------------------->|     2 bind_statement (ends by observing commitment.root)
  |-------------------------------------->|     3 observe_label + observe_bytes (VEIL mask root)
  |------>|       |       |       |       |     4 padding_spec
  |-------------->|       |       |       |     5 prove_packed_padded_capture_s_hat_v_c
  |       |       |*      |       |       |     6 univariate-skip round 1 (skip branch)
  |       |       |---------------------->|     7 observe_f128_slice (round poly)
  |       |       |<----------------------|     8 sample_f128 (round challenge)
  |<--------------|       |       |       |     9 ZerocheckClaim
  |------>|       |       |       |       |     10 x_ab_from_mlv
  |---------------------->|       |       |     11 prove_padded_capture_z_vec
  |       |       |       |-------------->|     12 observe_f128_slice (round poly)
  |       |       |       |<--------------|     13 sample_f128 (round challenge)
  |<----------------------|       |       |     14 LincheckClaim + z_vec
  |------------------------------>|       |     15 open_batch_..._s_hat_v_ro
  |<------------------------------|       |     16 BatchOpeningProofLigerito
```

Anchors:

1. `pcs::commit::commit_zk_with_ro`
   `crates/flock-core/src/pcs/commit.rs:286`
2. `bind_statement` — its last act is `observe_bytes(&commitment.root)` at
   `crates/flock-core/src/proof.rs:60`, so the commitment must already exist
   `crates/flock-core/src/proof.rs:51`
3. `Challenger::observe_label` then `Challenger::observe_bytes`, issued by the caller at
   `crates/flock-prover/src/succinct_veil.rs:642`
   `crates/flock-core/src/challenger.rs:34`
4. `BlockR1cs::padding_spec`
   `crates/flock-core/src/r1cs.rs:235`
5. `zerocheck::prove_packed_padded_capture_s_hat_v_c`
   `crates/flock-core/src/zerocheck.rs:406`
6. `univariate_skip::build_eq`, entered at `crates/flock-core/src/zerocheck.rs:118`
   `crates/flock-core/src/zerocheck/univariate_skip.rs:31`
7. `Challenger::observe_f128_slice`
   `crates/flock-core/src/challenger.rs:42`
8. `Challenger::sample_f128`
   `crates/flock-core/src/challenger.rs:54`
9. `ZerocheckClaim`
   `crates/flock-core/src/zerocheck.rs:293`
10. `BlockR1cs::x_ab_from_mlv`
    `crates/flock-core/src/r1cs.rs:253`
11. `lincheck::prove_padded_capture_z_vec`
    `crates/flock-core/src/lincheck.rs:1250`
12. return of message 7 — same definition
    `crates/flock-core/src/challenger.rs:42`
13. return of message 8 — same definition
    `crates/flock-core/src/challenger.rs:54`
14. `LincheckClaim`
    `crates/flock-core/src/lincheck.rs:394`
15. `pcs::open_batch_mixed_ligerito_with_precomputed_s_hat_v_ro`
    `crates/flock-core/src/pcs.rs:165`
16. `pcs::BatchOpeningProofLigerito`
    `crates/flock-core/src/pcs.rs:51`

### Univariate-skip dispatch

Message 6 is a branch, not a separate protocol. The skip family is four modules declared
together at `crates/flock-core/src/zerocheck.rs:24` through
`crates/flock-core/src/zerocheck.rs:27`:

- `crates/flock-core/src/zerocheck/univariate_skip.rs` — reference round-1 path:
  `build_eq` at `crates/flock-core/src/zerocheck/univariate_skip.rs:31`, `round1_naive`
  at `crates/flock-core/src/zerocheck/univariate_skip.rs:68`,
  `round1_extract_c_packed` at
  `crates/flock-core/src/zerocheck/univariate_skip.rs:277`
- `crates/flock-core/src/zerocheck/univariate_skip_deg4.rs` — degree-4 twin,
  `round1_deg4_naive` at
  `crates/flock-core/src/zerocheck/univariate_skip_deg4.rs:85`
- `crates/flock-core/src/zerocheck/univariate_skip_optimized.rs` and
  `crates/flock-core/src/zerocheck/univariate_skip_deg4_optimized.rs` — the production
  path; `zerocheck.rs` imports from the optimized module at
  `crates/flock-core/src/zerocheck.rs:34`, while the naive twins remain as the
  readable reference the optimized kernels are checked against

The `_naive` and `_optimized` pairs compute the same round-1 polynomial. Read the naive
one to understand the protocol; the optimized one is what runs.

## Diagram 2 — verifier

The mirror of Diagram 1. Every `VerifyError` return is drawn, because an early return
changes the call order: no later message is sent.

Participants:

- `caller` = the driver
  `crates/flock-core/src/verifier.rs:60`
- `VC` = `verifier::verify_core`
  `crates/flock-core/src/verifier.rs:288`
- `ZC` = `zerocheck::verify`
  `crates/flock-core/src/zerocheck.rs:687`
- `LC` = `lincheck::verify`
  `crates/flock-core/src/lincheck.rs:1551`
- `PCS` = `pcs::verify_opening_batch_ligerito_mixed_ro`
  `crates/flock-core/src/pcs.rs:848`
- `CH` = `Challenger`
  `crates/flock-core/src/challenger.rs:30`

```text
  caller  VC      ZC      LC      PCS     CH
  |       |       |       |       |       |
  |------>|       |       |       |       |     1 verify_core
  |       |------------------------------>|     2 bind_statement
  |       |------>|       |       |       |     3 zerocheck::verify
  |       |       |---------------------->|     4 observe / sample (replayed)
  |       |<------|       |       |       |     5 Err(VerifyError::Zerocheck) -> abort
  |       |<------|       |       |       |     6 ZerocheckClaim
  |       |*      |       |       |       |     7 x_ab_from_mlv
  |       |-------------->|       |       |     8 lincheck::verify
  |       |<--------------|       |       |     9 Err(VerifyError::Lincheck) -> abort
  |       |<--------------|       |       |     10 LincheckClaim
  |<------|       |       |       |       |     11 Ok((ab, c))
  |------------------------------>|       |     12 verify_opening_batch_ligerito_mixed_ro
  |<------------------------------|       |     13 Err(pcs::VerifyError) or Ok
```

Anchors:

1. `verifier::verify_core`
   `crates/flock-core/src/verifier.rs:288`
2. `bind_statement`, called from `verify_core`
   `crates/flock-core/src/proof.rs:51`
3. `zerocheck::verify`
   `crates/flock-core/src/zerocheck.rs:687`
4. `Challenger::observe_f128_slice` and `Challenger::sample_f128`
   `crates/flock-core/src/challenger.rs:42`
5. `zerocheck::VerifyError`
   `crates/flock-core/src/zerocheck.rs:331`
6. `ZerocheckClaim`
   `crates/flock-core/src/zerocheck.rs:293`
7. `BlockR1cs::x_ab_from_mlv`
   `crates/flock-core/src/r1cs.rs:253`
8. `lincheck::verify`
   `crates/flock-core/src/lincheck.rs:1551`
9. `lincheck::VerifyError`
   `crates/flock-core/src/lincheck.rs:478`
10. `LincheckClaim`
    `crates/flock-core/src/lincheck.rs:394`
11. return of message 1 — same definition
    `crates/flock-core/src/verifier.rs:288`
12. `pcs::verify_opening_batch_ligerito_mixed_ro`
    `crates/flock-core/src/pcs.rs:848`
13. `pcs::VerifyError`
    `crates/flock-core/src/pcs.rs:71`

The transcript is absorbed and squeezed in exactly the prover's order. `bind_statement`
is replayed first (message 2), then each sub-protocol replays its own rounds. A verifier
that reordered a single absorb would derive different challenges and reject.

## Diagram 3 — PCS internals

Expands the single `PCS` lane of Diagram 1.

Participants:

- `call` = the flock-prover driver, as in Diagram 1 — the two entry points it uses here
  are `crates/flock-core/src/pcs/commit.rs:286` and `crates/flock-core/src/pcs.rs:165`
- `cmt` = `pcs::commit`
  `crates/flock-core/src/pcs/commit.rs:286`
- `rsw` = `pcs::ring_switch`
  `crates/flock-core/src/pcs/ring_switch.rs:2298`
- `lig` = `pcs::ligerito`
  `crates/flock-core/src/pcs/ligerito.rs:3068`
- `mrk` = `merkle`
  `crates/flock-core/src/merkle.rs:288`
- `ro` = `ro::RoContext`
  `crates/flock-core/src/ro.rs:83`

```text
  call    cmt     rsw     lig     mrk     ro
  |       |       |       |       |       |
  |------>|       |       |       |       |      1 commit_zk_with_ro
  |       |*      |       |       |       |      2 replicate_message_fill_zk
  |       |*      |       |       |       |      3 finalize_commit (interleaved NTT encode)
  |       |---------------------->|       |      4 merkle_tree_framed
  |       |       |       |       |------>|      5 RoContext + RoChannel separation
  |<------|       |       |       |       |      6 Commitment + ProverData
  |-------------->|       |       |       |      7 prove_batched_padded_with_precomputed
  |<--------------|       |       |       |      8 RingSwitchProof + s_hat_v
  |---------------------->|       |       |      9 recursive_prover_..._round0_zk_with_ro
  |       |       |       |------>|       |      10 merkle_tree_framed (per round)
  |       |       |       |------>|       |      11 merkle_multi_proof (queries)
  |<----------------------|       |       |      12 LigeritoProof + ZkBlindOpening
```

Anchors:

1. `pcs::commit::commit_zk_with_ro`
   `crates/flock-core/src/pcs/commit.rs:286`
2. `replicate_message_fill_zk`, called at `crates/flock-core/src/pcs/commit.rs:304`
   `crates/flock-core/src/pcs/commit.rs:286`
3. `finalize_commit`, called at `crates/flock-core/src/pcs/commit.rs:305` — the private
   tail shared by every commit path; the non-zk twin `commit_into_with_ro`
   (`crates/flock-core/src/pcs/commit.rs:229`) is not on this path
   `crates/flock-core/src/pcs/commit.rs:377`
4. `merkle::merkle_tree_framed`
   `crates/flock-core/src/merkle.rs:288`
5. `ro::RoContext`
   `crates/flock-core/src/ro.rs:83`
6. `pcs::commit::Commitment` and `pcs::commit::ProverData`
   `crates/flock-core/src/pcs/commit.rs:123`
7. `ring_switch::prove_batched_padded_with_precomputed`, called at
   `crates/flock-core/src/pcs.rs:436`
   `crates/flock-core/src/pcs/ring_switch.rs:2298`
8. `RingSwitchProof`, re-exported at `crates/flock-core/src/pcs.rs:40`
   `crates/flock-core/src/pcs/ring_switch.rs:2034`
9. `ligerito::recursive_prover_with_basis_precomputed_round0_zk_with_ro` — the zk twin,
   which is what returns `ZkBlindOpening`; the non-zk
   `recursive_prover_with_basis_precomputed_round0_with_ro` is at
   `crates/flock-core/src/pcs/ligerito.rs:3138`
   `crates/flock-core/src/pcs/ligerito.rs:3068`
10. `merkle::merkle_tree_framed`, called at
    `crates/flock-core/src/pcs/ligerito.rs:2375`
    `crates/flock-core/src/merkle.rs:288`
11. `merkle::merkle_multi_proof`, called at
    `crates/flock-core/src/pcs/ligerito.rs:2826`
    `crates/flock-core/src/merkle.rs:705`
12. `pcs::ZkBlindOpening`
    `crates/flock-core/src/pcs.rs:65`

## Notes

- `pcs::pack::pack_witness` (`crates/flock-core/src/pcs/pack.rs:40`) is **not** on the
  succinct path and is deliberately absent from Diagram 3. The witness arrives already
  packed from `generate_witness_with_ab_packed_and_lincheck_zk_pinned`; the only
  non-test caller is `crates/flock-prover/src/prover.rs:866`.
- `pcs/jagged.rs` is **not on any path**. It is declared at
  `crates/flock-core/src/pcs.rs:23` and referenced once in a doc comment at
  `crates/flock-core/src/r1cs.rs:28`; a workspace-wide search for `jagged::` call sites
  returns none. It is deliberately absent from Diagram 3 rather than drawn as a step
  that does not execute.
- Two dependency deviations are documented in `.claude/PROJECT-KNOWLEDGE.md` and are
  drawn as they are, not smoothed away. `pcs` imports from `zerocheck`
  (`crates/flock-core/src/pcs.rs:44` and `crates/flock-core/src/pcs/ring_switch.rs:63`),
  inverting the intended PCS-below-PIOP order; and `ro` and `merkle` form a genuine
  two-node cycle, because `Hash` lives in `merkle` but is the random oracle's output
  type. Do not deepen either.
- `merkle` dispatches to architecture-specific kernels —
  `crates/flock-core/src/merkle/aarch64.rs` and
  `crates/flock-core/src/merkle/x86_64.rs` — chosen at compile time. The dispatch is
  invisible in the call order, which is why it is a note and not a lane.
- The `_framed` variants (`merkle_tree_framed`, `verify_merkle_proof_framed`) carry an
  `RoContext` and an `RoChannel` for domain separation. The unframed twins still exist
  and are used by the non-zk paths; picking the wrong one silently changes the hash
  domain.
- Message 6 in Diagram 1 is a branch on the skip parameter, not an unconditional step.
  Small instances take the general multilinear path in
  `crates/flock-core/src/zerocheck/multilinear.rs`.
